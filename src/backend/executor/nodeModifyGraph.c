/*
 * nodeModifyGraph.c
 *	  routines to handle ModifyGraph nodes.
 *
 * Copyright (c) 2022 by Bitnine Global, Inc.
 *
 * IDENTIFICATION
 *	  src/backend/executor/nodeModifyGraph.c
 */

#include "postgres.h"

#include "access/htup_details.h"
#include "access/xact.h"
#include "catalog/ag_graph_fn.h"
#include "catalog/pg_type.h"
#include "executor/executor.h"
#include "executor/nodeModifyGraph.h"
#include "miscadmin.h"
#include "nodes/nodeFuncs.h"
#include "parser/parse_relation.h"
#include "pgstat.h"
#include "utils/arrayaccess.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"
#include "access/table.h"
#include "access/heapam.h"
#include "executor/execCypherCreate.h"
#include "executor/execCypherSet.h"
#include "executor/execCypherDelete.h"
#include "executor/execCypherMerge.h"

bool		enable_multiple_update = true;
bool		auto_gather_graphmeta = false;

static TupleTableSlot *ExecModifyGraph(PlanState *pstate);
static void initGraphWRStats(ModifyGraphState *mgstate, GraphWriteOp op);
static List *ExecInitGraphPattern(List *pattern, ModifyGraphState *mgstate);
static List *ExecInitGraphSets(List *sets, ModifyGraphState *mgstate);
static List *ExecInitGraphDelExprs(List *exprs, ModifyGraphState *mgstate);

/* eager */
static void reflectModifiedProp(ModifyGraphState *mgstate);

/* common */
static bool isEdgeArrayOfPath(List *exprs, char *variable);

static void fitEStateRangeTable(EState* estate, int n);
static void fitEStateRelations(EState *estate, int newsize);

ModifyGraphState *
ExecInitModifyGraph(ModifyGraph *mgplan, EState *estate, int eflags)
{
	TupleTableSlot *slot;
	ModifyGraphState *mgstate;

	Assert(!(eflags & (EXEC_FLAG_BACKWARD | EXEC_FLAG_MARK)));

	mgstate = makeNode(ModifyGraphState);
	mgstate->ps.plan = (Plan *) mgplan;
	mgstate->ps.state = estate;
	mgstate->ps.ExecProcNode = ExecModifyGraph;

	/* Tuple desc for result is the same as the subplan. */
	slot = ExecAllocTableSlot(&estate->es_tupleTable, NULL, &TTSOpsMinimalTuple);
	mgstate->ps.ps_ResultTupleSlot = slot;

	/*
	 * We don't use ExecInitResultTypeTL because we need to get the
	 * information of the subplan, not the current plan.
	 */
	mgstate->ps.ps_ResultTupleDesc = ExecTypeFromTL(mgplan->subplan->targetlist);
	ExecSetSlotDescriptor(slot, mgstate->ps.ps_ResultTupleDesc);
	ExecAssignExprContext(estate, &mgstate->ps);

	mgstate->done = false;
	mgstate->child_done = false;
	mgstate->eagerness = mgplan->eagerness;
	mgstate->subplan = ExecInitNode(mgplan->subplan, estate, eflags);
	AssertArg(mgplan->operation != GWROP_MERGE ||
			  IsA(mgstate->subplan, NestLoopState));

	mgstate->elemTupleSlot = ExecInitExtraTupleSlot(estate, NULL, &TTSOpsMinimalTuple);

	mgstate->graphid = get_graph_path_oid();

	mgstate->pattern = ExecInitGraphPattern(mgplan->pattern, mgstate);

	/* Check to see if we have RTEs to add to the es_range_table. */
	if (mgplan->targets != NIL)
	{
		/*
		 * If the ert_base_index is equal to es_range_table_size then we need
		 * to add our RTEs to the end of the es_range_table. Otherwise, we just
		 * need to link the resultRels to their RTEs. In the later case we
		 * don't need to search the es_range_table for our RTEs because we
		 * already know the order and the base offset.
		 */
		bool build_new_range_table;
		ResultRelInfo *resultRelInfos;
		ParseState *pstate;
		ListCell   *lt;
		int targets_length = list_length(mgplan->targets);
		int rtindex;

		/*
		 * RTEs need to be added to the es_range_table using the
		 * proper memory context due to cached plans. So, we need to
		 * retrieve the context of the ModifyGraph plan and use that
		 * for adding RTEs.
		 */
		MemoryContext rtemctx = GetMemoryChunkContext((void *) mgplan);

		/* Allocate our stuff in the Executor memory context. */
		resultRelInfos = palloc(targets_length * sizeof(ResultRelInfo));
		pstate = make_parsestate(NULL);

		/*
		 * If we added RTEs to the es_range_table, but not all of them,
		 * free and truncate the es_range_table from this point. This will
		 * not effect parent plans, as they would not have added RTEs yet.
		 */
		if (mgplan->ert_rtes_added != targets_length &&
			mgplan->ert_rtes_added != -1 &&
			mgplan->ert_base_index > 0)
		{
			fitEStateRangeTable(estate, (int) mgplan->ert_base_index);
		}

		/* save the es_range_table index where we start adding our RTEs */
		if (mgplan->ert_base_index == -1)
			mgplan->ert_base_index = estate->es_range_table_size;

		build_new_range_table =
				(mgplan->ert_base_index == estate->es_range_table_size) && targets_length > 0;

		if (build_new_range_table)
		{
			fitEStateRelations(estate, (int) estate->es_range_table_size +
									   targets_length);
		}

		rtindex = 0;
		/* Process each new RTE to add. */
		foreach(lt, mgplan->targets)
		{
			Oid			relid = lfirst_oid(lt);
			/* open relation in Executor context */
			Relation	relation = table_open(relid, RowExclusiveLock);
			/* Switch to the memory context for building RTEs */
			MemoryContext oldmctx = MemoryContextSwitchTo(rtemctx);

			/*
			 * If the ert_base_index is equal to numOldRtable then we need
			 * to add our RTEs to the end of the es_range_table. Otherwise,
			 * we just need to link the resultRels to their RTEs. In the later
			 * case we don't need to search the es_range_table for our RTEs
			 * because we already know the order and the base offset.
			 */
			if (build_new_range_table)
			{
				ParseNamespaceItem *our_nsitem = addRangeTableEntryForRelation
						(pstate,
						 relation,
						 AccessShareLock,
						 NULL,
						 false,
						 false);
				RangeTblEntry *our_rte = our_nsitem->p_rte;

				/*
				 * remove the cell containing the RTE from pstate and reset
				 * the list p_rtable to NIL
				 */
				list_free(pstate->p_rtable);
				pstate->p_rtable = NIL;

				our_rte->requiredPerms = ACL_INSERT;

				/* Now add in our RTE */
				estate->es_range_table = lappend(estate->es_range_table, our_rte);
				estate->es_relations[mgplan->ert_base_index + rtindex] = NULL;
				if (our_rte->rtekind == RTE_RELATION)
				{
					ExecGetRangeTableRelation(estate, mgplan->ert_base_index + rtindex +1);
				}

				/* increment the number of RTEs we've added */
				if (mgplan->ert_rtes_added == -1)
					mgplan->ert_rtes_added = 1;
				else
					mgplan->ert_rtes_added++;
				pfree(our_nsitem);
			}

			/*
			 * Now switch back to the Executor context to finish building
			 * our structures. We need to do this so that our stuff gets
			 * cleaned up after an abrupt exit, at the end of the Executor
			 * context, or in ExecEndModifyGraph.
			 */
			MemoryContextSwitchTo(oldmctx);

			InitResultRelInfo(&resultRelInfos[rtindex],
							  relation,
							  (mgplan->ert_base_index + rtindex) + 1,
							  NULL,
							  estate->es_instrument);

			ExecOpenIndices(&resultRelInfos[rtindex], false);
			rtindex++;
		}

		mgstate->resultRelations = resultRelInfos;
		mgstate->numResultRelations = targets_length;

		/* es_result_relation_info is NULL except ModifyTable case */
		estate->es_result_relation_info = NULL;

		free_parsestate(pstate);
	}

	mgstate->exprs = ExecInitGraphDelExprs(mgplan->exprs, mgstate);
	mgstate->sets = ExecInitGraphSets(mgplan->sets, mgstate);

	initGraphWRStats(mgstate, mgplan->operation);

	mgstate->elemTable = NULL;
//	if (mgstate->eagerness ||
//		(mgstate->sets != NIL && enable_multiple_update) ||
//		mgstate->exprs != NIL)
//	{
//		HASHCTL ctl;
//
//		memset(&ctl, 0, sizeof(ctl));
//		ctl.keysize = sizeof(Graphid);
//		ctl.entrysize = sizeof(ModifiedElemEntry);
//		ctl.hcxt = CurrentMemoryContext;
//
//		mgstate->elemTable =
//				hash_create("modified object table", 128, &ctl,
//							HASH_ELEM | HASH_BLOBS | HASH_CONTEXT);
//	}
//	else
//	{
//		mgstate->elemTable = NULL;
//	}

	mgstate->tuplestorestate = tuplestore_begin_heap(false, false, eager_mem);

	switch (mgplan->operation)
	{
		case GWROP_CREATE:
			mgstate->execProc = ExecCreateGraph;
			break;
		case GWROP_DELETE:
			mgstate->execProc = ExecDeleteGraph;
			break;
		case GWROP_SET:
			mgstate->execProc = ExecSetGraph;
			break;
		case GWROP_MERGE:
			mgstate->execProc = ExecMergeGraph;
			break;
		default:
			elog(ERROR, "unknown operation");
	}


	EvalPlanQualInit(&mgstate->mt_epqstate, estate, NULL, NIL,
					 mgplan->epqParam);
	mgstate->mt_arowmarks = (List **) palloc0(sizeof(List *) * 1);
	EvalPlanQualSetPlan(&mgstate->mt_epqstate, mgplan->subplan,
						mgstate->mt_arowmarks[0]);
    Increment_Estate_CommandId(estate);
	return mgstate;
}

static TupleTableSlot *
ExecModifyGraph(PlanState *pstate)
{
	ModifyGraphState *mgstate = castNode(ModifyGraphState, pstate);
	ModifyGraph *plan = (ModifyGraph *) mgstate->ps.plan;
	EState	   *estate = mgstate->ps.state;

	if (mgstate->done)
		return NULL;

	if (!mgstate->child_done)
	{
		for (;;)
		{
			TupleTableSlot *slot;

			/* ExecInsertIndexTuples() uses per-tuple context. Reset it here. */
			ResetPerTupleExprContext(estate);

			switch (plan->operation)
			{
				case GWROP_MERGE:
				case GWROP_DELETE:
					Increment_Estate_CommandId(estate);
					break;
				default:
					Decrement_Estate_CommandId(estate);
					break;
			}

			slot = ExecProcNode(mgstate->subplan);

			switch (plan->operation)
			{
				case GWROP_MERGE:
				case GWROP_DELETE:
					Decrement_Estate_CommandId(estate);
					break;
				default:
					Increment_Estate_CommandId(estate);
					break;
			}

			if (TupIsNull(slot))
				break;

			if (plan->operation == GWROP_SET)
			{
				AssignSetKinds(mgstate, GSP_NORMAL, slot);
			}

			slot = mgstate->execProc(mgstate, slot);

			if (mgstate->eagerness)
			{
				Assert(slot != NULL);

				tuplestore_puttupleslot(mgstate->tuplestorestate, slot);
			}
			else if (slot != NULL)
			{
				return slot;
			}
			else
			{
				Assert(plan->last == true);
			}
		}

		CommandCounterIncrement();
		mgstate->child_done = true;

		if (mgstate->elemTable != NULL)
			reflectModifiedProp(mgstate);
	}

	if (mgstate->eagerness)
	{
		TupleTableSlot *result;
		TupleDesc	tupDesc;
		int			natts;
		int			i;

		/* don't care about scan direction */
		result = mgstate->ps.ps_ResultTupleSlot;
		tuplestore_gettupleslot(mgstate->tuplestorestate, true, false, result);

		if (TupIsNull(result))
			return result;

		slot_getallattrs(result);

		if (mgstate->elemTable == NULL ||
			hash_get_num_entries(mgstate->elemTable) < 1)
			return result;

		tupDesc = result->tts_tupleDescriptor;
		natts = tupDesc->natts;
		for (i = 0; i < natts; i++)
		{
			Oid			type;
			Datum		elem;

			if (result->tts_isnull[i])
				continue;

			type = TupleDescAttr(tupDesc, i)->atttypid;
			if (type == VERTEXOID)
			{
				elem = getVertexFinal(mgstate, result->tts_values[i]);
			}
			else if (type == EDGEOID)
			{
				elem = getEdgeFinal(mgstate, result->tts_values[i]);
			}
			else if (type == GRAPHPATHOID)
			{
				/*
				 * When deleting the graphpath, edge array of graphpath is
				 * deleted first and vertex array is deleted in the next plan.
				 * So, the graphpath must be passed to the next plan for
				 * deleting vertex array of the graphpath.
				 */
				if (isEdgeArrayOfPath(mgstate->exprs,
									  NameStr(TupleDescAttr(tupDesc, i)->attname)))
					continue;

				elem = getPathFinal(mgstate, result->tts_values[i]);
			}
			else if (type == EDGEARRAYOID && plan->operation == GWROP_DELETE)
			{
				/*
				 * The edges are used only for removal,
				 * not for result output.
				 *
				 * This assumes that there are only variable references in the
				 * target list.
				 */
				continue;
			}
			else
			{
				continue;
			}

			setSlotValueByAttnum(result, elem, i + 1);
		}

		return result;
	}

	mgstate->done = true;

	return NULL;
}

void
ExecEndModifyGraph(ModifyGraphState *mgstate)
{
	ResultRelInfo *resultRelInfo;
	int			i;

	if (mgstate->tuplestorestate != NULL)
		tuplestore_end(mgstate->tuplestorestate);
	mgstate->tuplestorestate = NULL;

	if (mgstate->elemTable != NULL)
		hash_destroy(mgstate->elemTable);

	resultRelInfo = mgstate->resultRelations;
	for (i = mgstate->numResultRelations; i > 0; i--)
	{
		ExecCloseIndices(resultRelInfo);
		table_close(resultRelInfo->ri_RelationDesc, NoLock);

		resultRelInfo++;
	}

	/*
	 * clean out the tuple table
	 */
	ExecClearTuple(mgstate->ps.ps_ResultTupleSlot);

	ExecEndNode(mgstate->subplan);
	ExecFreeExprContext(&mgstate->ps);

	CommandCounterIncrement();
}

static void
initGraphWRStats(ModifyGraphState *mgstate, GraphWriteOp op)
{
	if (mgstate->pattern != NIL)
	{
		Assert(op == GWROP_CREATE || op == GWROP_MERGE);

		graphWriteStats.insertVertex = 0;
		graphWriteStats.insertEdge = 0;
	}
	if (mgstate->exprs != NIL)
	{
		Assert(op == GWROP_DELETE);

		graphWriteStats.deleteVertex = 0;
		graphWriteStats.deleteEdge = 0;
	}
	if (mgstate->sets != NIL)
	{
		Assert(op == GWROP_SET || op == GWROP_MERGE);

		graphWriteStats.updateProperty = 0;
	}
}

static List *
ExecInitGraphPattern(List *pattern, ModifyGraphState *mgstate)
{
	ModifyGraph *plan = (ModifyGraph *) mgstate->ps.plan;
	GraphPath  *gpath;
	ListCell   *le;

	if (plan->operation != GWROP_MERGE)
		return pattern;

	AssertArg(list_length(pattern) == 1);

	gpath = linitial(pattern);

	foreach(le, gpath->chain)
	{
		Node *elem = lfirst(le);

		if (IsA(elem, GraphVertex))
		{
			GraphVertex *gvertex = (GraphVertex *) elem;

			gvertex->es_expr = ExecInitExpr((Expr *) gvertex->expr,
											(PlanState *) mgstate);
		}
		else
		{
			GraphEdge *gedge = (GraphEdge *) elem;

			Assert(IsA(elem, GraphEdge));

			gedge->es_expr = ExecInitExpr((Expr *) gedge->expr,
										  (PlanState *) mgstate);
		}
	}

	return pattern;
}

static List *
ExecInitGraphSets(List *sets, ModifyGraphState *mgstate)
{
	ListCell *ls;

	foreach(ls, sets)
	{
		GraphSetProp *gsp = lfirst(ls);

		gsp->es_elem = ExecInitExpr((Expr *) gsp->elem, (PlanState *) mgstate);
		gsp->es_expr = ExecInitExpr((Expr *) gsp->expr, (PlanState *) mgstate);
	}

	return sets;
}

static List *
ExecInitGraphDelExprs(List *exprs, ModifyGraphState *mgstate)
{
	ListCell *lc;

	foreach(lc, exprs)
	{
		GraphDelElem *gde = lfirst(lc);

		gde->es_elem = ExecInitExpr((Expr *) gde->elem, (PlanState *) mgstate);
	}

	return exprs;
}


Datum
getVertexFinal(ModifyGraphState *mgstate, Datum origin)
{
	ModifyGraph *plan = (ModifyGraph *) mgstate->ps.plan;
	ModifiedElemEntry *entry;
	Datum		gid = getVertexIdDatum(origin);
	bool		found;

	entry = hash_search(mgstate->elemTable, &gid, HASH_FIND, &found);

	/* unmodified vertex */
	if (!found)
		return origin;

	if (plan->operation == GWROP_DELETE)
		return (Datum) 0;
	else
		return entry->data.elem;
}

Datum
getEdgeFinal(ModifyGraphState *mgstate, Datum origin)
{
	ModifyGraph *plan = (ModifyGraph *) mgstate->ps.plan;
	Datum		gid = getEdgeIdDatum(origin);
	bool		found;
	ModifiedElemEntry *entry;

	entry = hash_search(mgstate->elemTable, &gid, HASH_FIND, &found);

	/* unmodified edge */
	if (!found)
		return origin;

	if (plan->operation == GWROP_DELETE)
		return (Datum) 0;
	else
		return entry->data.elem;
}

Datum
getPathFinal(ModifyGraphState *mgstate, Datum origin)
{
	Datum		vertices_datum;
	Datum		edges_datum;
	AnyArrayType *arrVertices;
	AnyArrayType *arrEdges;
	int			nvertices;
	int			nedges;
	Datum	   *vertices;
	Datum	   *edges;
	int16		typlen;
	bool		typbyval;
	char		typalign;
	array_iter	it;
	int			i;
	Datum		value;
	bool		isnull;
	bool		modified = false;
	bool		isdeleted = false;
	Datum		result;

	getGraphpathArrays(origin, &vertices_datum, &edges_datum);

	arrVertices = DatumGetAnyArrayP(vertices_datum);
	arrEdges = DatumGetAnyArrayP(edges_datum);

	nvertices = ArrayGetNItems(AARR_NDIM(arrVertices), AARR_DIMS(arrVertices));
	nedges = ArrayGetNItems(AARR_NDIM(arrEdges), AARR_DIMS(arrEdges));
	Assert(nvertices == nedges + 1);

	vertices = palloc(nvertices * sizeof(Datum));
	edges = palloc(nedges * sizeof(Datum));

	get_typlenbyvalalign(AARR_ELEMTYPE(arrVertices), &typlen,
						 &typbyval, &typalign);
	array_iter_setup(&it, arrVertices);
	for (i = 0; i < nvertices; i++)
	{
		Datum		vertex;

		value = array_iter_next(&it, &isnull, i, typlen, typbyval, typalign);
		Assert(!isnull);

		vertex = getVertexFinal(mgstate, value);

		if (vertex == (Datum) 0)
		{
			if (i == 0)
				isdeleted = true;

			if (isdeleted)
				continue;
			else
				elog(ERROR, "cannot delete a vertex in graphpath");
		}

		if (vertex != value)
			modified = true;

		vertices[i] = vertex;
	}

	get_typlenbyvalalign(AARR_ELEMTYPE(arrEdges), &typlen,
						 &typbyval, &typalign);
	array_iter_setup(&it, arrEdges);
	for (i = 0; i < nedges; i++)
	{
		Datum		edge;

		value = array_iter_next(&it, &isnull, i, typlen, typbyval, typalign);
		Assert(!isnull);

		edge = getEdgeFinal(mgstate, value);

		if (edge == (Datum) 0)
		{
			if (isdeleted)
				continue;
			else
				elog(ERROR, "cannot delete a edge in graphpath.");
		}

		if (edge != value)
			modified = true;

		edges[i] = edge;
	}

	if (isdeleted)
		result = (Datum) 0;
	else if (modified)
		result = makeGraphpathDatum(vertices, nvertices, edges, nedges);
	else
		result = origin;

	pfree(vertices);
	pfree(edges);

	return result;
}

static void
reflectModifiedProp(ModifyGraphState *mgstate)
{
	ModifyGraph	*plan = (ModifyGraph *) mgstate->ps.plan;
	HASH_SEQ_STATUS	seq;
	ModifiedElemEntry *entry;

	Assert(mgstate->elemTable != NULL);

	hash_seq_init(&seq, mgstate->elemTable);
	while ((entry = hash_seq_search(&seq)) != NULL)
	{
		Datum	gid = PointerGetDatum(entry->key);
		Oid		type;

		type = get_labid_typeoid(mgstate->graphid,
								 GraphidGetLabid(DatumGetGraphid(gid)));

		/* write the object to heap */
		if (plan->operation == GWROP_DELETE)
			deleteElem(mgstate, gid, &entry->data.tid, type);
		else
		{
			ItemPointer	ctid;

			ctid = updateElemProp(mgstate, type, gid, entry->data.elem);

			if (mgstate->eagerness)
			{
				Datum		property;
				Datum		newelem;

				if (type == VERTEXOID)
					property = getVertexPropDatum(entry->data.elem);
				else if (type == EDGEOID)
					property = getEdgePropDatum(entry->data.elem);
				else
					elog(ERROR, "unexpected graph type %d", type);

				newelem = makeModifiedElem(entry->data.elem, type, gid,property,
										   PointerGetDatum(ctid));

				pfree(DatumGetPointer(entry->data.elem));
				entry->data.elem = newelem;
			}
		}
	}
}

ResultRelInfo *
getResultRelInfo(ModifyGraphState *mgstate, Oid relid)
{
	ResultRelInfo *resultRelInfo;
	int			i;

	resultRelInfo = mgstate->resultRelations;
	for (i = 0; i < mgstate->numResultRelations; i++)
	{
		if (RelationGetRelid(resultRelInfo->ri_RelationDesc) == relid)
			break;

		resultRelInfo++;
	}

	if (i >= mgstate->numResultRelations)
	elog(ERROR, "invalid object ID %u for the target label", relid);

	return resultRelInfo;
}

Datum
findVertex(TupleTableSlot *slot, GraphVertex *gvertex, Graphid *vid)
{
	bool		isnull;
	Datum		vertex;

	if (gvertex->resno == InvalidAttrNumber)
		return (Datum) 0;

	vertex = slot_getattr(slot, gvertex->resno, &isnull);
	if (isnull)
		return (Datum) 0;

	if (vid != NULL)
		*vid = DatumGetGraphid(getVertexIdDatum(vertex));

	return vertex;
}

Datum
findEdge(TupleTableSlot *slot, GraphEdge *gedge, Graphid *eid)
{
	bool		isnull;
	Datum		edge;

	if (gedge->resno == InvalidAttrNumber)
		return (Datum) 0;

	edge = slot_getattr(slot, gedge->resno, &isnull);
	if (isnull)
		return (Datum) 0;

	if (eid != NULL)
		*eid = DatumGetGraphid(getEdgeIdDatum(edge));

	return edge;
}

AttrNumber
findAttrInSlotByName(TupleTableSlot *slot, char *name)
{
	TupleDesc	tupDesc = slot->tts_tupleDescriptor;
	int			i;

	for (i = 0; i < tupDesc->natts; i++)
	{
		Form_pg_attribute attr = TupleDescAttr(tupDesc, i);
		if (namestrcmp(&(attr->attname), name) == 0 && !attr->attisdropped)
			return attr->attnum;
	}

	ereport(ERROR,
			(errcode(ERRCODE_INVALID_NAME),
					errmsg("variable \"%s\" does not exist", name)));
	return InvalidAttrNumber;
}

void
setSlotValueByName(TupleTableSlot *slot, Datum value, char *name)
{
	AttrNumber attno;

	if (slot == NULL)
		return;

	attno = findAttrInSlotByName(slot, name);

	setSlotValueByAttnum(slot, value, attno);
}

void
setSlotValueByAttnum(TupleTableSlot *slot, Datum value, int attnum)
{
	if (slot == NULL)
		return;

	AssertArg(attnum > 0 && attnum <= slot->tts_tupleDescriptor->natts);

	slot->tts_values[attnum - 1] = value;
	slot->tts_isnull[attnum - 1] = (value == (Datum) 0) ? true : false;
}

Datum *
makeDatumArray(ExprContext *econtext, int len)
{
	if (len == 0)
		return NULL;

	return palloc(len * sizeof(Datum));
}

/*
 * Remove elements from range table.
 */
static void
fitEStateRangeTable(EState* estate, int n)
{
	ListCell *lc;

	foreach(lc, estate->es_range_table)
	{
		RangeTblEntry *es_rte = lfirst(lc);
		int idx = foreach_current_index(lc);

		if (idx < n)
			continue;
		foreach_delete_current(estate->es_range_table, lc);
		pfree(es_rte);
		table_close(estate->es_relations[idx], NoLock);
	}
	estate->es_range_table_size = n;
}

static void
fitEStateRelations(EState *estate, int newsize)
{
	Relation *saved_relations = estate->es_relations;

	estate->es_range_table_size = newsize;

	estate->es_relations = (Relation *)
			palloc0(estate->es_range_table_size * sizeof(Relation));

	memcpy(estate->es_relations, saved_relations,
		   estate->es_range_table_size * sizeof(Relation));

	pfree(saved_relations);
}

static bool
isEdgeArrayOfPath(List *exprs, char *variable)
{
	ListCell   *lc;

	foreach(lc, exprs)
	{
		GraphDelElem *gde = castNode(GraphDelElem, lfirst(lc));

		if (exprType(gde->elem) == EDGEARRAYOID &&
			strcmp(gde->variable, variable) == 0)
			return true;
	}

	return false;
}
