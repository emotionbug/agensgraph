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

static void openResultRelInfosIndices(ModifyGraphState *mgstate);

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

	mgstate->elemTupleSlot = ExecInitExtraTupleSlot(estate, NULL,
													&TTSOpsMinimalTuple);

	mgstate->done = false;
	mgstate->child_done = false;
	mgstate->eagerness = mgplan->eagerness;
	mgstate->subplan = ExecInitNode(mgplan->subplan, estate, eflags);
	AssertArg(mgplan->operation != GWROP_MERGE ||
			  IsA(mgstate->subplan, NestLoopState));

	mgstate->graphid = get_graph_path_oid();
	mgstate->pattern = ExecInitGraphPattern(mgplan->pattern, mgstate);
	mgstate->exprs = ExecInitGraphDelExprs(mgplan->exprs, mgstate);

	/*
	 * Initialize Set operator state.
	 */
	mgstate->sets = ExecInitGraphSets(mgplan->sets, mgstate);
	mgstate->set_update_cols = NULL;
	mgstate->num_update_cols = 0;

	mgstate->resultRelInfo = estate->es_result_relations + mgplan->resultRelIndex;
	mgstate->numResultRelInfo = list_length(mgplan->resultRelations);
	openResultRelInfosIndices(mgstate);

	EvalPlanQualInit(&mgstate->mt_epqstate, estate, NULL, NIL,
					 mgplan->epqParam);
	mgstate->mt_arowmarks = (List **) palloc0(sizeof(List *) * 1);
	EvalPlanQualSetPlan(&mgstate->mt_epqstate, mgplan->subplan,
						mgstate->mt_arowmarks[0]);

	/* Fill eager action information */
	if ((mgstate->eagerness ||
		(mgstate->sets != NIL && enable_multiple_update) ||
		mgstate->exprs != NIL) &&
		mgplan->operation != GWROP_SET)
	{
		HASHCTL		ctl;

		memset(&ctl, 0, sizeof(ctl));
		ctl.keysize = sizeof(Graphid);
		ctl.entrysize = sizeof(ModifiedElemEntry);
		ctl.hcxt = CurrentMemoryContext;

		mgstate->elemTable =
			hash_create("modified object table", 128, &ctl,
						HASH_ELEM | HASH_BLOBS | HASH_CONTEXT);
		mgstate->tuplestorestate = tuplestore_begin_heap(false, false, eager_mem);
	}
	else
	{
		/* We will not use eager action */
		mgstate->elemTable = NULL;
		mgstate->tuplestorestate = NULL;
	}

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

	initGraphWRStats(mgstate, mgplan->operation);
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
				case GWROP_SET:
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
				case GWROP_SET:
					Decrement_Estate_CommandId(estate);
					break;
				default:
					Increment_Estate_CommandId(estate);
					break;
			}

			if (TupIsNull(slot))
				break;

			slot = mgstate->execProc(mgstate, slot);

			if (mgstate->tuplestorestate && mgstate->eagerness)
			{
				Assert(slot != NULL);

				tuplestore_puttupleslot(mgstate->tuplestorestate, slot);
			}
			else if (slot != NULL)
			{
				CommandCounterIncrement();
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
		{
			reflectModifiedProp(mgstate);
			CommandCounterIncrement();
		}
	}

	if (mgstate->eagerness && mgstate->tuplestorestate)
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
		{

			CommandCounterIncrement();
			return result;
		}

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
				 * The edges are used only for removal, not for result output.
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

		CommandCounterIncrement();
		return result;
	}

	mgstate->done = true;

	return NULL;
}

void
ExecEndModifyGraph(ModifyGraphState *mgstate)
{
	if (mgstate->tuplestorestate != NULL)
		tuplestore_end(mgstate->tuplestorestate);
	mgstate->tuplestorestate = NULL;

	if (mgstate->elemTable != NULL)
		hash_destroy(mgstate->elemTable);

	if (mgstate->set_update_cols != NULL)
		pfree(mgstate->set_update_cols);

	/*
	 * clean out the tuple table
	 */
	ExecClearTuple(mgstate->ps.ps_ResultTupleSlot);

	ExecEndNode(mgstate->subplan);
	ExecFreeExprContext(&mgstate->ps);
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
		Node	   *elem = lfirst(le);

		if (IsA(elem, GraphVertex))
		{
			GraphVertex *gvertex = (GraphVertex *) elem;

			gvertex->es_expr = ExecInitExpr((Expr *) gvertex->expr,
											(PlanState *) mgstate);
		}
		else
		{
			GraphEdge  *gedge = (GraphEdge *) elem;

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
	ListCell   *ls;

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
	ListCell   *lc;

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
	ModifyGraph *plan = (ModifyGraph *) mgstate->ps.plan;
	HASH_SEQ_STATUS seq;
	ModifiedElemEntry *entry;

	Assert(mgstate->elemTable != NULL);

	hash_seq_init(&seq, mgstate->elemTable);
	while ((entry = hash_seq_search(&seq)) != NULL)
	{
		Datum		gid = PointerGetDatum(entry->key);
		Oid			type;

		type = get_labid_typeoid(mgstate->graphid,
								 GraphidGetLabid(DatumGetGraphid(gid)));

		/* write the object to heap */
		if (plan->operation == GWROP_DELETE)
			deleteElem(mgstate, gid, &entry->data.tid, type);
		else
		{
			ItemPointer ctid;

			ctid = LegacyUpdateElemProp(mgstate, type, gid, entry->data.elem);

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

				newelem = makeModifiedElem(entry->data.elem, type, gid, property,
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
	ResultRelInfo *resultRelInfo = mgstate->resultRelInfo;
	int			i;

	for (i = 0; i < mgstate->numResultRelInfo; i++)
	{
		if (RelationGetRelid(resultRelInfo->ri_RelationDesc) == relid)
			return resultRelInfo;
		resultRelInfo++;
	}

	elog(ERROR, "invalid object ID %u for the target label", relid);
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
}

void
setSlotValueByName(TupleTableSlot *slot, Datum value, char *name)
{
	AttrNumber	attno;

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
makeDatumArray(int len)
{
	if (len == 0)
		return NULL;

	return palloc(len * sizeof(Datum));
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

/*
 * openResultRelInfosIndices
 */
static void
openResultRelInfosIndices(ModifyGraphState *mgstate)
{
	int			index;
	ResultRelInfo *resultRelInfo = mgstate->resultRelInfo;

	for (index = 0; index < mgstate->numResultRelInfo; index++)
	{
		ExecOpenIndices(resultRelInfo, false);
		resultRelInfo++;
	}
}
