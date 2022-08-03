/*
 * nodeModifyGraph.h
 *
 * Copyright (c) 2022 by Bitnine Global, Inc.
 *
 * src/include/executor/nodeModifyGraph.h
 */

#ifndef NODEMODIFYGRAPH_H
#define NODEMODIFYGRAPH_H

#include "nodes/execnodes.h"

extern bool enable_multiple_update;

extern ModifyGraphState *ExecInitModifyGraph(ModifyGraph *mgplan,
											 EState *estate, int eflags);
extern void ExecEndModifyGraph(ModifyGraphState *mgstate);

/* global variable - see postgres.c */
extern GraphWriteStats graphWriteStats;
/* hash entry */
typedef struct ModifiedElemEntry
{
	Graphid		key;
	union
	{
		Datum			elem;	/* modified graph element */
		ItemPointerData	tid;	/* use to find tuple in delete plan */
	} data;
} ModifiedElemEntry;

/* for visibility between Cypher clauses */
typedef enum ModifyCid
{
	MODIFY_CID_LOWER_BOUND,		/* for previous clause */
	MODIFY_CID_OUTPUT,			/* for CREATE, MERGE, DELETE */
	MODIFY_CID_SET,				/* for SET, ON MATCH SET, ON CREATE SET */
	MODIFY_CID_NLJOIN_MATCH,	/* for DELETE JOIN, MERGE JOIN */
	MODIFY_CID_MAX
} ModifyCid;

extern ResultRelInfo *getResultRelInfo(ModifyGraphState *mgstate, Oid relid);
extern Datum findVertex(TupleTableSlot *slot, GraphVertex *gvertex, Graphid *vid);
extern Datum findEdge(TupleTableSlot *slot, GraphEdge *gedge, Graphid *eid);
extern AttrNumber findAttrInSlotByName(TupleTableSlot *slot, char *name);
extern void setSlotValueByName(TupleTableSlot *slot, Datum value, char *name);
extern void setSlotValueByAttnum(TupleTableSlot *slot, Datum value, int attnum);
extern Datum *makeDatumArray(ExprContext *econtext, int len);

extern Datum getVertexFinal(ModifyGraphState *mgstate, Datum origin);
extern Datum getEdgeFinal(ModifyGraphState *mgstate, Datum origin);
extern Datum getPathFinal(ModifyGraphState *mgstate, Datum origin);

#endif
