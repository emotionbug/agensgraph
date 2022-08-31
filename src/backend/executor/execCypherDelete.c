/*
 * execCypherDelete.c
 *	  routines to handle ModifyGraph delete nodes.
 *
 * Copyright (c) 2022 by Bitnine Global, Inc.
 *
 * IDENTIFICATION
 *	  src/backend/executor/execCypherDelete.c
 */

#include "postgres.h"

#include "executor/execCypherDelete.h"
#include "executor/executor.h"
#include "executor/nodeModifyGraph.h"
#include "nodes/nodeFuncs.h"
#include "access/tableam.h"
#include "utils/lsyscache.h"
#include "access/heapam.h"
#include "pgstat.h"
#include "utils/arrayaccess.h"
#include "access/xact.h"
#include "commands/trigger.h"
#include "utils/fmgroids.h"

#define DatumGetItemPointer(X)		((ItemPointer) DatumGetPointer(X))
#define ItemPointerGetDatum(X)		PointerGetDatum(X)

static void enterDelPropTable(ModifyGraphState *mgstate, Datum elem, Oid type);

static bool deleteElement(ModifyGraphState *mgstate, Datum element, Oid type);
static bool deleteEdgeHeapTuple(ModifyGraphState *mgstate,
								ResultRelInfo *resultRelInfo,
								Graphid graphid, HeapTuple tuple);

static void find_connected_edges_internal(ModifyGraphState *mgstate,
										  ModifyGraph *plan,
										  EState *estate,
										  ResultRelInfo *resultRelInfo,
										  AttrNumber attr,
										  Datum vertex_id)
{
	Relation relation = resultRelInfo->ri_RelationDesc;
	HeapTuple tup;
	TableScanDesc scanDesc;
	ScanKeyData skey;
	ScanKeyInit(&skey, attr,
				BTEqualStrategyNumber,
				F_GRAPHID_EQ, vertex_id);
	scanDesc = table_beginscan(relation, estate->es_snapshot, 1, &skey);
	while ((tup = heap_getnext(scanDesc, ForwardScanDirection)) != NULL)
	{
		bool isnull;
		Graphid gid;
		if (!plan->detach)
		{
			table_endscan(scanDesc);
			elog(ERROR, "vertices with edges can not be removed");
		}
		gid = DatumGetGraphid(heap_getattr(tup,
										   Anum_table_edge_id,
										   RelationGetDescr(relation),
										   &isnull));
		deleteEdgeHeapTuple(mgstate, resultRelInfo, gid, tup);
	}
	table_endscan(scanDesc);
}

static void find_connected_edges(ModifyGraphState *mgstate, Graphid vertex_id)
{
	ModifyGraph *plan = (ModifyGraph *) mgstate->ps.plan;
	EState *estate = mgstate->ps.state;
	Datum datum_vertex_id = GraphidGetDatum(vertex_id);
	ListCell *lc;
	CommandId	saved_command_id;

	saved_command_id = estate->es_snapshot->curcid;
	estate->es_snapshot->curcid =
			mgstate->modify_cid + MODIFY_CID_NLJOIN_MATCH;

	foreach(lc, mgstate->edge_labels)
	{
		ResultRelInfo *resultRelInfo = makeNode(ResultRelInfo);
		Oid relid = lfirst_oid(lc);
		Relation relation = table_open(relid, RowExclusiveLock);

		InitResultRelInfo(resultRelInfo,
						  relation,
						  0,		/* dummy rangetable index */
						  NULL,
						  estate->es_instrument);
		find_connected_edges_internal(mgstate, plan, estate, resultRelInfo,
									  Anum_table_edge_start, datum_vertex_id);
		find_connected_edges_internal(mgstate, plan, estate, resultRelInfo,
									  Anum_table_edge_end, datum_vertex_id);
		table_close(relation, RowExclusiveLock);
	}

	estate->es_snapshot->curcid = saved_command_id;
}

TupleTableSlot *
ExecDeleteGraph(ModifyGraphState *mgstate, TupleTableSlot *slot)
{
	ModifyGraph *plan = (ModifyGraph *) mgstate->ps.plan;
	ExprContext *econtext = mgstate->ps.ps_ExprContext;
	TupleDesc	tupDesc = slot->tts_tupleDescriptor;
	ListCell   *le;

	ResetExprContext(econtext);

	foreach(le, mgstate->exprs)
	{
		GraphDelElem *gde = castNode(GraphDelElem, lfirst(le));
		Oid			type;
		Datum		elem;
		bool		isNull;
		AttrNumber	attno = findAttrInSlotByName(slot, gde->variable);

		type = exprType((Node *) gde->elem);
		if (!(type == VERTEXOID || type == EDGEOID ||
			  type == VERTEXARRAYOID || type == EDGEARRAYOID))
			ereport(ERROR,
					(errcode(ERRCODE_DATATYPE_MISMATCH),
					 errmsg("expected node, relationship, or path")));

		econtext->ecxt_scantuple = slot;
		elem = ExecEvalExpr(gde->es_elem, econtext, &isNull);
		if (isNull)
		{
			/*
			 * This assumes that there are only variable references in the
			 * target list.
			 */
			if (type == EDGEARRAYOID)
				continue;
			else
				ereport(NOTICE,
						(errcode(ERRCODE_NULL_VALUE_NOT_ALLOWED),
						 errmsg("skipping deletion of NULL graph element")));

			continue;
		}

		/*
		 * NOTE: After all the graph elements to be removed are collected,
		 * they will be removed.
		 */
		enterDelPropTable(mgstate, elem, type);

		/*
		 * The graphpath must be passed to the next plan for deleting vertex
		 * array of the graphpath.
		 */
		if (type == EDGEARRAYOID &&
			TupleDescAttr(tupDesc, attno - 1)->atttypid == GRAPHPATHOID)
			continue;

		setSlotValueByAttnum(slot, (Datum) 0, attno);
	}

	return (plan->last ? NULL : slot);
}

/*
 * deleteElement
 * Delete the graph element.
 */
static bool
deleteEdgeHeapTuple(ModifyGraphState *mgstate, ResultRelInfo *resultRelInfo,
					Graphid graphid, HeapTuple tuple)
{
	EPQState   *epqstate = &mgstate->mt_epqstate;
	EState	   *estate = mgstate->ps.state;
	ResultRelInfo *savedResultRelInfo;
	Relation	resultRelationDesc;
	TM_Result	result;
	TM_FailureData tmfd;
	bool		hash_found;
	ItemPointer	tupleid;

	tupleid = &tuple->t_self;

	hash_search(mgstate->elemTable, &graphid, HASH_FIND, &hash_found);
	if (hash_found)
		return false;

	savedResultRelInfo = estate->es_result_relation_info;
	estate->es_result_relation_info = resultRelInfo;
	resultRelationDesc = resultRelInfo->ri_RelationDesc;

	/* BEFORE ROW DELETE Triggers */
	if (resultRelInfo->ri_TrigDesc &&
		resultRelInfo->ri_TrigDesc->trig_delete_before_row)
	{
		bool		dodelete;

		dodelete = ExecBRDeleteTriggers(estate, epqstate, resultRelInfo,
										tupleid, tuple, NULL);

		if (!dodelete)			/* "do nothing" */
			return false;
	}

	/* see ExecDelete() */
	result = table_tuple_delete(resultRelationDesc,
								tupleid,
								mgstate->modify_cid + MODIFY_CID_OUTPUT,
								estate->es_snapshot,
								estate->es_crosscheck_snapshot,
								true,
								&tmfd,
								false);

	switch (result)
	{
		case TM_SelfModified:
			ereport(ERROR,
					(errcode(ERRCODE_INTERNAL_ERROR),
							errmsg("modifying the same element more than once cannot happen")));
		case TM_Ok:
			break;

		case TM_Updated:
			/* TODO: A solution to concurrent update is needed. */
			ereport(ERROR,
					(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
							errmsg("could not serialize access due to concurrent update")));
		default:
			elog(ERROR, "unrecognized heap_update status: %u", result);
	}

	/* AFTER ROW DELETE Triggers */
	ExecARDeleteTriggers(estate, resultRelInfo, tupleid, tuple,
						 NULL);

	/*
	 * NOTE: VACUUM will delete index tuples associated with the heap tuple
	 * later.
	 */


	graphWriteStats.deleteEdge++;
//		if (auto_gather_graphmeta)
//		{
//			agstat_count_edge_delete(
//					GraphidGetLabid(graphid),
//					DatumGetGraphid(
//							DatumGetGraphid(elemTupleSlot->tts_values[1])),
//					DatumGetGraphid(
//							DatumGetGraphid(elemTupleSlot->tts_values[2]))
//			);
//		}

	estate->es_result_relation_info = savedResultRelInfo;
	hash_search(mgstate->elemTable, &graphid, HASH_ENTER, &hash_found);

	return true;
}


/*
 * deleteElement
 * Delete the graph element.
 */
static bool
deleteElement(ModifyGraphState *mgstate, Datum element, Oid type)
{
	EPQState   *epqstate = &mgstate->mt_epqstate;
	TupleTableSlot *elemTupleSlot = mgstate->elemTupleSlot;
	EState	   *estate = mgstate->ps.state;
	Oid			relid;
	ResultRelInfo *resultRelInfo;
	ResultRelInfo *savedResultRelInfo;
	Relation	resultRelationDesc;
	TM_Result	result;
	TM_FailureData tmfd;
	bool		hash_found;
	ItemPointer	tupleid;
	Graphid		graphid;

	if (type == VERTEXOID)
	{
		graphid = DatumGetGraphid(getVertexIdDatum(element));
		find_connected_edges(mgstate, graphid);

	}
	else
	{
		Assert(type == EDGEOID);
		graphid = DatumGetGraphid(getEdgeIdDatum(element));
//		elog(INFO, "normal ""%hu." UINT64_FORMAT,  GraphidGetLabid(graphid),
//			 GraphidGetLocid(graphid));

	}

	hash_search(mgstate->elemTable, &graphid, HASH_FIND, &hash_found);
	if (hash_found)
		return false;

	relid = get_labid_relid(mgstate->graphid, GraphidGetLabid(graphid));
	resultRelInfo = getResultRelInfo(mgstate, relid);

	savedResultRelInfo = estate->es_result_relation_info;
	estate->es_result_relation_info = resultRelInfo;
	resultRelationDesc = resultRelInfo->ri_RelationDesc;

	ExecClearTuple(elemTupleSlot);

	ExecSetSlotDescriptor(elemTupleSlot,
						  RelationGetDescr(resultRelInfo->ri_RelationDesc));

//	elemTupleSlot->tts_values[0] = GraphidGetDatum(graphid);
//
	if (type == VERTEXOID)
	{
		tupleid = DatumGetItemPointer(getVertexTidDatum(element));
		elemTupleSlot->tts_values[1] = getVertexPropDatum(element);
	}
	else
	{
		Assert(type == EDGEOID);
		tupleid = DatumGetItemPointer(getEdgeTidDatum(element));
		elemTupleSlot->tts_values[1] = getEdgeStartDatum(element);
		elemTupleSlot->tts_values[2] = getEdgeEndDatum(element);
		elemTupleSlot->tts_values[3] = getEdgePropDatum(element);
	}
//
//	MemSet(elemTupleSlot->tts_isnull, false,
//		   elemTupleSlot->tts_tupleDescriptor->natts * sizeof(bool));
//	ExecStoreVirtualTuple(elemTupleSlot);
//
//	ExecMaterializeSlot(elemTupleSlot);
//	elemTupleSlot->tts_tableOid = RelationGetRelid(resultRelInfo->ri_RelationDesc);

//	/* BEFORE ROW DELETE Triggers */
//	if (resultRelInfo->ri_TrigDesc &&
//		resultRelInfo->ri_TrigDesc->trig_delete_before_row)
//	{
//		bool		dodelete;
//
//		dodelete = ExecBRDeleteTriggers(estate, epqstate, resultRelInfo,
//										tupleid, elemTupleSlot, NULL);
//
//		if (!dodelete)			/* "do nothing" */
//			return false;
//	}

	/* see ExecDelete() */
	result = table_tuple_delete(resultRelationDesc,
								tupleid,
								mgstate->modify_cid + MODIFY_CID_OUTPUT,
								estate->es_snapshot,
								estate->es_crosscheck_snapshot,
								true,
								&tmfd,
								false);

	switch (result)
	{
		case TM_SelfModified:
			ereport(ERROR,
					(errcode(ERRCODE_INTERNAL_ERROR),
					 errmsg("modifying the same element more than once cannot happen")));
		case TM_Ok:
			break;

		case TM_Updated:
			/* TODO: A solution to concurrent update is needed. */
			ereport(ERROR,
					(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
					 errmsg("could not serialize access due to concurrent update")));
		default:
			elog(ERROR, "unrecognized heap_update status: %u", result);
	}

//	/* AFTER ROW DELETE Triggers */
//	ExecARDeleteTriggers(estate, resultRelInfo, tupleid, NULL,
//						 NULL);

	/*
	 * NOTE: VACUUM will delete index tuples associated with the heap tuple
	 * later.
	 */

	if (type == VERTEXOID)
		graphWriteStats.deleteVertex++;
	else
	{
		Assert(type == EDGEOID);

		graphWriteStats.deleteEdge++;
//		if (auto_gather_graphmeta)
//		{
//			agstat_count_edge_delete(
//					GraphidGetLabid(graphid),
//					DatumGetGraphid(
//							DatumGetGraphid(elemTupleSlot->tts_values[1])),
//					DatumGetGraphid(
//							DatumGetGraphid(elemTupleSlot->tts_values[2]))
//			);
//		}
	}

	estate->es_result_relation_info = savedResultRelInfo;
	hash_search(mgstate->elemTable, &graphid, HASH_ENTER, &hash_found);

	return true;
}

static void
enterDelPropTable(ModifyGraphState *mgstate, Datum elem, Oid type)
{
	if (type == VERTEXOID)
	{
		deleteElement(mgstate, elem, type);
	}
	else if (type == EDGEOID)
	{
		deleteElement(mgstate, elem, type);
	}
	else if (type == VERTEXARRAYOID)
	{
		AnyArrayType *vertices;
		int			nvertices;
		int16		typlen;
		bool		typbyval;
		char		typalign;
		array_iter	it;
		int			i;
		Datum		vtx;
		bool		isnull;

		vertices = DatumGetAnyArrayP(elem);
		nvertices = ArrayGetNItems(AARR_NDIM(vertices), AARR_DIMS(vertices));

		get_typlenbyvalalign(AARR_ELEMTYPE(vertices), &typlen,
							 &typbyval, &typalign);

		array_iter_setup(&it, vertices);
		for (i = 0; i < nvertices; i++)
		{
			vtx = array_iter_next(&it, &isnull, i, typlen, typbyval, typalign);
			if (!isnull)
				deleteElement(mgstate, vtx, VERTEXOID);
		}
	}
	else if (type == EDGEARRAYOID)
	{
		AnyArrayType *edges;
		int			nedges;
		int16		typlen;
		bool		typbyval;
		char		typalign;
		array_iter	it;
		int			i;
		Datum		edge;
		bool		isnull;

		edges = DatumGetAnyArrayP(elem);
		nedges = ArrayGetNItems(AARR_NDIM(edges), AARR_DIMS(edges));

		get_typlenbyvalalign(AARR_ELEMTYPE(edges), &typlen,
							 &typbyval, &typalign);

		array_iter_setup(&it, edges);
		for (i = 0; i < nedges; i++)
		{
			edge = array_iter_next(&it, &isnull, i, typlen, typbyval, typalign);
			if (!isnull)
				deleteElement(mgstate, edge, EDGEOID);
		}
	}
	else
	{
		elog(ERROR, "unexpected graph type %d", type);
	}
}
