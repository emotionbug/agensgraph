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
		Datum		elem;		/* modified graph element */
		ItemPointerData tid;	/* use to find tuple in delete plan */
	}			data;
} ModifiedElemEntry;

#define Increment_Estate_CommandId(estate) \
	((estate)->es_output_cid++);		   \
    ((estate)->es_snapshot->curcid++)

#define Decrement_Estate_CommandId(estate) \
	((estate)->es_output_cid--);           \
	((estate)->es_snapshot->curcid--)

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
