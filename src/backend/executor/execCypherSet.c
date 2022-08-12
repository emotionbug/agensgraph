/*
 * execCypherSet.c
 *	  routines to handle ModifyGraph set nodes.
 *
 * Copyright (c) 2022 by Bitnine Global, Inc.
 *
 * IDENTIFICATION
 *	  src/backend/executor/execCypherSet.c
 */

#include "postgres.h"

#include "executor/execCypherSet.h"
#include "nodes/nodeFuncs.h"
#include "executor/executor.h"
#include "executor/nodeModifyGraph.h"
#include "utils/datum.h"
#include "access/tableam.h"
#include "utils/lsyscache.h"
#include "access/xact.h"
#include "catalog/ag_vertex_d.h"
#include "catalog/ag_edge_d.h"
#include "utils/jsonb.h"

#define DatumGetItemPointer(X)	 ((ItemPointer) DatumGetPointer(X))

static TupleTableSlot *copyVirtualTupleTableSlot(TupleTableSlot *dstslot,
												 TupleTableSlot *srcslot);
static void findAndReflectNewestValue(ModifyGraphState *mgstate,
									  TupleTableSlot *slot);
static void updateElementTable(ModifyGraphState *mgstate, Datum gid,
							   Datum newelem);
static Datum GraphTableTupleUpdate(ModifyGraphState *mgstate,
								   Oid tts_value_type, Datum tts_value);

/*
 * LegacyExecSetGraph
 *
 * It is used for Merge statements or Eager.
 */
TupleTableSlot *
LegacyExecSetGraph(ModifyGraphState *mgstate, TupleTableSlot *slot, GSPKind kind)
{
	ModifyGraph *plan = (ModifyGraph *) mgstate->ps.plan;
	ExprContext *econtext = mgstate->ps.ps_ExprContext;
	ListCell   *ls;
	TupleTableSlot *result = mgstate->ps.ps_ResultTupleSlot;

	/*
	 * The results of previous clauses should be preserved. So, shallow
	 * copying is used.
	 */
	copyVirtualTupleTableSlot(result, slot);

	/*
	 * Reflect the newest value all types of scantuple before evaluating
	 * expression.
	 */
	findAndReflectNewestValue(mgstate, econtext->ecxt_scantuple);
	findAndReflectNewestValue(mgstate, econtext->ecxt_innertuple);
	findAndReflectNewestValue(mgstate, econtext->ecxt_outertuple);

	foreach(ls, mgstate->sets)
	{
		GraphSetProp *gsp = lfirst(ls);
		Oid			elemtype;
		Datum		elem_datum;
		Datum		expr_datum;
		bool		isNull;
		Datum		gid;
		Datum		tid;
		Datum		newelem;
		MemoryContext oldmctx;
		AttrNumber	attnum;

		if (gsp->kind != kind)
		{
			Assert(kind != GSP_NORMAL);
			continue;
		}

		elemtype = exprType((Node *) gsp->es_elem->expr);
		if (elemtype != VERTEXOID && elemtype != EDGEOID)
			elog(ERROR, "expected node or relationship");

		/* store intermediate results in tuple memory context */
		oldmctx = MemoryContextSwitchTo(econtext->ecxt_per_tuple_memory);

		/* get original graph element */
		attnum = ((Var *) gsp->es_elem->expr)->varattno;
		elem_datum = ExecEvalExpr(gsp->es_elem, econtext, &isNull);
		if (isNull)
			ereport(ERROR,
					(errcode(ERRCODE_NULL_VALUE_NOT_ALLOWED),
					 errmsg("updating NULL is not allowed")));

		/* evaluate SET expression */
		if (elemtype == VERTEXOID)
		{
			gid = getVertexIdDatum(elem_datum);
			tid = getVertexTidDatum(elem_datum);
		}
		else
		{
			Assert(elemtype == EDGEOID);

			gid = getEdgeIdDatum(elem_datum);
			tid = getEdgeTidDatum(elem_datum);
		}

		expr_datum = ExecEvalExpr(gsp->es_expr, econtext, &isNull);
		if (isNull)
			ereport(ERROR,
					(errcode(ERRCODE_NULL_VALUE_NOT_ALLOWED),
					 errmsg("property map cannot be NULL")));

		newelem = makeModifiedElem(elem_datum, elemtype, gid, expr_datum, tid);

		MemoryContextSwitchTo(oldmctx);

		updateElementTable(mgstate, gid, newelem);

		/*
		 * To use the modified data in the next iteration, modifying the data
		 * in the ExprContext.
		 */
		setSlotValueByAttnum(econtext->ecxt_scantuple, newelem, attnum);
		setSlotValueByAttnum(econtext->ecxt_innertuple, newelem, attnum);
		setSlotValueByAttnum(econtext->ecxt_outertuple, newelem, attnum);
		setSlotValueByAttnum(result, newelem, attnum);
	}

	return (plan->last ? NULL : result);
}

static void debugFor(TupleTableSlot *slot)
{
	int i;
	if (slot)
	{
		for (i = 0; i < slot->tts_tupleDescriptor->natts; i++)
		{
			Oid type_oid = slot->tts_tupleDescriptor
					->attrs[i].atttypid;
			elog(INFO, "Current x %d", i);
			switch (type_oid) {
				case GRAPHIDOID:
				{
					Datum id = slot->tts_values[i];
					elog(INFO, "GRAPHID" "%hu." UINT64_FORMAT "",
						 GraphidGetLabid(id), GraphidGetLocid(id));
				}
					break;
				case JSONBOID:
				{
					// 1, 2, 3 이건 id properties tid. 이건 Vertex네 ?
					Jsonb* jsonb = DatumGetJsonbP(slot
														  ->tts_values[i]);
					elog(INFO, "JSONB %s", JsonbToCString(NULL, &jsonb->root,
														  VARSIZE(jsonb)));
				}
					;; // tidout
				default:
					elog(INFO, "TypeOid %d", type_oid);
					break;
			}
//			appendStringInfo(&si, "%s[" GRAPHID_FMTSTR "]",
//					NameStr(my_extra->label),
//					GraphidGetLabid(id), GraphidGetLocid(id));
		}

	}

}

/*
 * ExecSetGraph
 */
TupleTableSlot *
ExecSetGraph(ModifyGraphState *mgstate, TupleTableSlot *slot)
{
	ModifyGraph *plan = (ModifyGraph *) mgstate->ps.plan;
	bool	   *update_cols = mgstate->set_update_cols;
	int			i;
	ListCell   *lc;

	if (update_cols == NULL)
	{
		update_cols = palloc0(sizeof(bool) * slot->tts_tupleDescriptor->natts);
		mgstate->set_update_cols = update_cols;
		mgstate->num_update_cols = slot->tts_tupleDescriptor->natts;

		for (i = 0; i < slot->tts_tupleDescriptor->natts; i++)
		{
			foreach(lc, mgstate->sets)
			{
				char	   *attr_name =
				NameStr(slot->tts_tupleDescriptor->attrs[i].attname);
				GraphSetProp *gsp = lfirst(lc);
	
				if (strcmp(gsp->variable, attr_name) == 0)
				{
					update_cols[i] = true;
					break;
				}
			}
		}
	}

	/*==========================
	 * Case #1. ecxt_scantuple != NULL
	 * SubPlan is Scan expr.
	 * 
	 * Case #2. ecxt_innertuple != NULL && ecxt_outertuple != NULL
	 * SubPlan is join expr.
	 */

	ExprContext *subplan_econtext = mgstate->subplan->ps_ExprContext;
	elog(INFO, "INNER");
	debugFor(subplan_econtext->ecxt_innertuple);
	elog(INFO, "OUTER");
	debugFor(subplan_econtext->ecxt_outertuple);
	elog(INFO, "SCAN");
	debugFor(subplan_econtext->ecxt_scantuple);
	for (i = 0; i < slot->tts_tupleDescriptor->natts; i++)
	{
		if (update_cols[i])
		{
			Datum		curDatum = slot->tts_values[i];
			Oid			element_type = slot->tts_tupleDescriptor->attrs[i].atttypid;
			Datum		affectedDatum = GraphTableTupleUpdate(mgstate, element_type,
															  curDatum);

			slot->tts_values[i] = affectedDatum;
		}
	}

	return (plan->last ? NULL : slot);
}

static TupleTableSlot *
copyVirtualTupleTableSlot(TupleTableSlot *dstslot, TupleTableSlot *srcslot)
{
	int			natts = srcslot->tts_tupleDescriptor->natts;

	ExecClearTuple(dstslot);
	ExecSetSlotDescriptor(dstslot, srcslot->tts_tupleDescriptor);

	/* shallow copy */
	memcpy(dstslot->tts_values, srcslot->tts_values, natts * sizeof(Datum));
	memcpy(dstslot->tts_isnull, srcslot->tts_isnull, natts * sizeof(bool));

	ExecStoreVirtualTuple(dstslot);

	return dstslot;
}

/*
 * findAndReflectNewestValue
 *
 * If a tuple with already updated exists, the data is taken from the elemTable
 * in ModifyGraphState and reflecting in the tuple data currently working on.
 */
static void
findAndReflectNewestValue(ModifyGraphState *mgstate, TupleTableSlot *slot)
{
	int			i;

	if (slot == NULL)
		return;

	for (i = 0; i < slot->tts_tupleDescriptor->natts; i++)
	{
		Datum		finalValue;

		if (slot->tts_isnull[i] ||
			slot->tts_tupleDescriptor->attrs[i].attisdropped)
			continue;

		switch (slot->tts_tupleDescriptor->attrs[i].atttypid)
		{
			case VERTEXOID:
				finalValue = getVertexFinal(mgstate, slot->tts_values[i]);
				break;
			case EDGEOID:
				finalValue = getEdgeFinal(mgstate, slot->tts_values[i]);
				break;
			case GRAPHPATHOID:
				finalValue = getPathFinal(mgstate, slot->tts_values[i]);
				break;
			default:
				continue;
		}

		/*
		 * Make a copy of finalValue to avoid the slot's copy getting freed
		 * when the mgstate->elemTable hash table entries are indepenently
		 * freed.
		 */
		setSlotValueByAttnum(slot, finalValue, i + 1);
	}
}

/*
 * GraphTableTupleUpdate
 * 		Update the tuple in the graph table.
 *
 * See ExecUpdate()
 */
static Datum
GraphTableTupleUpdate(ModifyGraphState *mgstate, Oid tts_value_type,
					  Datum tts_value)
{
	EState	   *estate = mgstate->ps.state;
	TupleTableSlot *elemTupleSlot = mgstate->elemTupleSlot;
	Datum	   *tts_values;
	ResultRelInfo *resultRelInfo;
	ResultRelInfo *savedResultRelInfo;
	Relation	resultRelationDesc;
	LockTupleMode lockmode;
	TM_Result	result;
	TM_FailureData tmfd;
	bool		update_indexes;
	Datum		gid;
	Oid			relid;
	ItemPointer ctid;

	if (tts_value_type == VERTEXOID)
	{
		gid = getVertexIdDatum(tts_value);
	}
	else
	{
		gid = getEdgeIdDatum(tts_value);
	}

	relid = get_labid_relid(mgstate->graphid,
							GraphidGetLabid(DatumGetGraphid(gid)));
	resultRelInfo = getResultRelInfo(mgstate, relid);

	savedResultRelInfo = estate->es_result_relation_info;
	estate->es_result_relation_info = resultRelInfo;
	resultRelationDesc = resultRelInfo->ri_RelationDesc;

	/*
	 * Create a tuple to store. Attributes of vertex/edge label are not the
	 * same with those of vertex/edge.
	 */
	ExecClearTuple(elemTupleSlot);
	ExecSetSlotDescriptor(elemTupleSlot,
						  RelationGetDescr(resultRelInfo->ri_RelationDesc));
	tts_values = elemTupleSlot->tts_values;

	if (tts_value_type == VERTEXOID)
	{
		ctid = DatumGetItemPointer(getVertexTidDatum(tts_value));

		tts_values[Anum_ag_vertex_id - 1] = gid;
		tts_values[Anum_ag_vertex_properties - 1] = getVertexPropDatum(tts_value);
	}
	else
	{
		Assert(tts_value_type == EDGEOID);

		ctid = DatumGetItemPointer(getEdgeTidDatum(tts_value));

		tts_values[Anum_ag_edge_id - 1] = gid;
		tts_values[Anum_ag_edge_start - 1] = getEdgeStartDatum(tts_value);
		tts_values[Anum_ag_edge_end - 1] = getEdgeEndDatum(tts_value);
		tts_values[Anum_ag_edge_properties - 1] = getEdgePropDatum(tts_value);
	}
	MemSet(elemTupleSlot->tts_isnull, false,
		   elemTupleSlot->tts_tupleDescriptor->natts * sizeof(bool));
	ExecStoreVirtualTuple(elemTupleSlot);

	ExecMaterializeSlot(elemTupleSlot);
	elemTupleSlot->tts_tableOid = RelationGetRelid(resultRelationDesc);

	if (resultRelationDesc->rd_att->constr)
		ExecConstraints(resultRelInfo, elemTupleSlot, estate);

	result = table_tuple_update(resultRelationDesc, ctid, elemTupleSlot,
								GetCurrentCommandId(true),
								estate->es_snapshot,
								estate->es_crosscheck_snapshot,
								true /* wait for commit */ ,
								&tmfd, &lockmode, &update_indexes);

	switch (result)
	{
		case TM_SelfModified:
			return tts_value;
		case TM_Ok:
			break;
		case TM_Invisible:
			elog(INFO, "Warn");
			break;
		case TM_Updated:
			/* TODO: A solution to concurrent update is needed. */
			ereport(ERROR,
					(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
					 errmsg("could not serialize access due to concurrent update")));
		default:
			elog(ERROR, "unrecognized heap_update status: %u", result);
	}

	if (resultRelInfo->ri_NumIndices > 0 && update_indexes)
		ExecInsertIndexTuples(elemTupleSlot, estate, false, NULL, NIL);

	graphWriteStats.updateProperty++;

	estate->es_result_relation_info = savedResultRelInfo;

	if (tts_value_type == VERTEXOID)
	{
		return makeGraphVertexDatum(gid,
									tts_values[Anum_ag_vertex_properties - 1],
									PointerGetDatum(&elemTupleSlot->tts_tid));
	}
	else
	{
		return makeGraphEdgeDatum(gid,
								  tts_values[Anum_ag_edge_start - 1],
								  tts_values[Anum_ag_edge_end - 1],
								  tts_values[Anum_ag_edge_properties - 1],
								  PointerGetDatum(&elemTupleSlot->tts_tid));
	}
}

/* See ExecUpdate() */
ItemPointer
LegacyUpdateElemProp(ModifyGraphState *mgstate, Oid elemtype, Datum gid,
					 Datum elem_datum)
{
	EState	   *estate = mgstate->ps.state;
	TupleTableSlot *elemTupleSlot = mgstate->elemTupleSlot;
	Oid			relid;
	ItemPointer ctid;
	ResultRelInfo *resultRelInfo;
	ResultRelInfo *savedResultRelInfo;
	Relation	resultRelationDesc;
	LockTupleMode lockmode;
	TM_Result	result;
	TM_FailureData tmfd;
	bool		update_indexes;

	relid = get_labid_relid(mgstate->graphid,
							GraphidGetLabid(DatumGetGraphid(gid)));
	resultRelInfo = getResultRelInfo(mgstate, relid);

	savedResultRelInfo = estate->es_result_relation_info;
	estate->es_result_relation_info = resultRelInfo;
	resultRelationDesc = resultRelInfo->ri_RelationDesc;

	/*
	 * Create a tuple to store. Attributes of vertex/edge label are not the
	 * same with those of vertex/edge.
	 */
	ExecClearTuple(elemTupleSlot);
	ExecSetSlotDescriptor(elemTupleSlot,
						  RelationGetDescr(resultRelInfo->ri_RelationDesc));
	if (elemtype == VERTEXOID)
	{
		elemTupleSlot->tts_values[0] = gid;
		elemTupleSlot->tts_values[1] = getVertexPropDatum(elem_datum);

		ctid = (ItemPointer) DatumGetPointer(getVertexTidDatum(elem_datum));
	}
	else
	{
		Assert(elemtype == EDGEOID);

		elemTupleSlot->tts_values[0] = gid;
		elemTupleSlot->tts_values[1] = getEdgeStartDatum(elem_datum);
		elemTupleSlot->tts_values[2] = getEdgeEndDatum(elem_datum);
		elemTupleSlot->tts_values[3] = getEdgePropDatum(elem_datum);

		ctid = (ItemPointer) DatumGetPointer(getEdgeTidDatum(elem_datum));
	}
	MemSet(elemTupleSlot->tts_isnull, false,
		   elemTupleSlot->tts_tupleDescriptor->natts * sizeof(bool));
	ExecStoreVirtualTuple(elemTupleSlot);

	ExecMaterializeSlot(elemTupleSlot);
	elemTupleSlot->tts_tableOid = RelationGetRelid(resultRelationDesc);

	if (resultRelationDesc->rd_att->constr)
		ExecConstraints(resultRelInfo, elemTupleSlot, estate);

	result = table_tuple_update(resultRelationDesc, ctid, elemTupleSlot,
								GetCurrentCommandId(true),
								estate->es_snapshot,
								estate->es_crosscheck_snapshot,
								true /* wait for commit */ ,
								&tmfd, &lockmode, &update_indexes);

	switch (result)
	{
		case TM_SelfModified:
			ereport(ERROR,
					(errcode(ERRCODE_INTERNAL_ERROR),
					 errmsg("graph element(%hu," UINT64_FORMAT ") has been SET multiple times",
							GraphidGetLabid(DatumGetGraphid(gid)),
							GraphidGetLocid(DatumGetGraphid(gid)))));
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

	if (resultRelInfo->ri_NumIndices > 0 && update_indexes)
		ExecInsertIndexTuples(elemTupleSlot, estate, false, NULL, NIL);

	graphWriteStats.updateProperty++;

	estate->es_result_relation_info = savedResultRelInfo;

	return &elemTupleSlot->tts_tid;
}

Datum
makeModifiedElem(Datum elem, Oid elemtype,
				 Datum id, Datum prop_map, Datum tid)
{
	Datum		result;

	if (elemtype == VERTEXOID)
	{
		result = makeGraphVertexDatum(id, prop_map, tid);
	}
	else
	{
		Datum		start;
		Datum		end;

		start = getEdgeStartDatum(elem);
		end = getEdgeEndDatum(elem);

		result = makeGraphEdgeDatum(id, start, end, prop_map, tid);
	}

	return result;
}

static void
updateElementTable(ModifyGraphState *mgstate, Datum gid, Datum newelem)
{
	ModifiedElemEntry *entry;
	bool		found;

	entry = hash_search(mgstate->elemTable, &gid, HASH_ENTER, &found);
	if (found)
	{
		if (enable_multiple_update)
			pfree(DatumGetPointer(entry->data.elem));
		else
			ereport(ERROR,
					(errcode(ERRCODE_INTERNAL_ERROR),
					 errmsg("graph element(%hu," UINT64_FORMAT ") has been SET multiple times",
							GraphidGetLabid(entry->key),
							GraphidGetLocid(entry->key))));
	}

	entry->data.elem = datumCopy(newelem, false, -1);
}
