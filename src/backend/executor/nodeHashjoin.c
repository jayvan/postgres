/*-------------------------------------------------------------------------
 *
 * nodeHashjoin.c
 *	  Routines to handle hash join nodes
 *
 * Portions Copyright (c) 1996-2013, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/nodeHashjoin.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "access/htup_details.h"
#include "executor/executor.h"
#include "executor/hashjoin.h"
#include "executor/nodeHash.h"
#include "executor/nodeHashjoin.h"
#include "miscadmin.h"
#include "utils/memutils.h"


/*
 * States of the ExecHashJoin state machine
 */
#define HJ_BUILD_HASHTABLE		1
#define HJ_NEED_NEW_TUPLE		2
#define HJ_SCAN_BUCKET			3
#define HJ_DONE_SOURCE		6

/* Returns true if doing null-fill on outer relation */
#define HJ_FILL_OUTER(hjstate)	((hjstate)->hj_NullInnerTupleSlot != NULL)
/* Returns true if doing null-fill on inner relation */
#define HJ_FILL_INNER(hjstate)	((hjstate)->hj_NullOuterTupleSlot != NULL)

static TupleTableSlot *ExecHashJoinInnerGetTuple(HashJoinState *hjstate,
						  uint32 *hashvalue);
static TupleTableSlot *ExecHashJoinOuterGetTuple(HashJoinState *hjstate,
						  uint32 *hashvalue);


/* ----------------------------------------------------------------
 *		ExecHashJoin
 *
 *		This function implements the Hybrid Hashjoin algorithm.
 *
 *		Note: the relation we build hash table on is the "inner"
 *			  the other one is "outer".
 * ----------------------------------------------------------------
 */
TupleTableSlot *				/* return: a tuple or NULL */
ExecHashJoin(HashJoinState *node)
{
	HashState  *outerNode;
	HashState  *innerNode;
	List	   *joinqual;
	List	   *otherqual;
	ExprContext *econtext;
	ExprDoneCond isDone;
	HashJoinTable hashtableInner;
	HashJoinTable hashtableOuter;
	TupleTableSlot *outerTupleSlot;
	uint32		hashvalue;
  TupleTableSlot *hashSlot;

	/*
	 * get information from HashJoin node
	 */
	joinqual = node->js.joinqual;
	otherqual = node->js.ps.qual;
	innerNode = (HashState *) innerPlanState(node);
	outerNode = (HashState *) outerPlanState(node);
	hashtableInner = node->hj_InnerHashTable;
	hashtableOuter = node->hj_OuterHashTable;
	econtext = node->js.ps.ps_ExprContext;

	/*
	 * Check to see if we're still projecting out tuples from a previous join
	 * tuple (because there is a function-returning-set in the projection
	 * expressions).  If so, try to project another one.
	 */
	if (node->js.ps.ps_TupFromTlist)
	{
		TupleTableSlot *result;

		result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);
		if (isDone == ExprMultipleResult)
			return result;
		/* Done with that source tuple... */
		node->js.ps.ps_TupFromTlist = false;
	}

	/*
	 * Reset per-tuple memory context to free any expression evaluation
	 * storage allocated in the previous tuple cycle.  Note this can't happen
	 * until we're done projecting out tuples from a join tuple.
	 */
	ResetExprContext(econtext);

	/*
	 * run the hash join state machine
	 */
	for (;;)
	{
		switch (node->hj_JoinState)
		{
      // CS448: This stage builds a hashtable for both the inner/outer nodes
      // but does not populate them like the original hash join
			case HJ_BUILD_HASHTABLE:

				/*
				 * First time through: build hash table for inner/outer relation.
				 */
				Assert(hashtableInner == NULL);
				Assert(hashtableOuter == NULL);
        node->hj_FirstOuterTupleSlot = NULL;

				/*
				 * create the hash tables
				 */
				hashtableInner = ExecHashTableCreate((Hash *) innerNode->ps.plan,
												node->hj_HashOperators,
												HJ_FILL_INNER(node));
				node->hj_InnerHashTable = hashtableInner;

				hashtableOuter = ExecHashTableCreate((Hash *) outerNode->ps.plan,
												node->hj_HashOperators,
												HJ_FILL_OUTER(node));
				node->hj_OuterHashTable = hashtableOuter;

				/*
				 * execute the Hash node, to build the hash table
				 */
				innerNode->hashtable = hashtableInner;
        outerNode->hashtable = hashtableOuter;

				/*
				 * need to remember whether nbatch has increased since we
				 * began scanning the outer relation
				 */
				hashtableInner->nbatch_outstart = hashtableInner->nbatch;
				hashtableOuter->nbatch_outstart = hashtableOuter->nbatch;

				/*
				 * Reset OuterNotEmpty for scan.  (It's OK if we fetched a
				 * tuple above, because ExecHashJoinOuterGetTuple will
				 * immediately set it again.)
				 */
				node->hj_OuterNotEmpty = false;

				node->hj_JoinState = HJ_NEED_NEW_TUPLE;

				/* FALL THRU */

      // CS448: This stage switches the node we're pulling from,
      // then pulls, and checks the other hash table
      // Of course, we don't switch nodes if the other is
      // exhausted
			case HJ_NEED_NEW_TUPLE:
        if (!node->hj_OneDone) {
          node->hj_PullInner = !node->hj_PullInner;
        }

				/*
				 * We don't have an outer tuple, try to get the next one
				 */
        if (node->hj_PullInner)
          outerTupleSlot = ExecHashJoinInnerGetTuple(node, &hashvalue);
        else
          outerTupleSlot = ExecHashJoinOuterGetTuple(node, &hashvalue);

				if (TupIsNull(outerTupleSlot))
				{
          node->hj_JoinState = HJ_DONE_SOURCE;
					continue;
				}

				econtext->ecxt_innertuple = outerTupleSlot;
				node->hj_MatchedOuter = false;

				/*
				 * Find the corresponding bucket for this tuple in the main
				 * hash table or skew hash table.
				 */
				node->hj_CurHashValue = hashvalue;
				ExecHashGetBucket(hashtableInner, hashvalue, &node->hj_CurBucketNo);
				node->hj_CurSkewBucketNo = INVALID_SKEW_BUCKET_NO;
				node->hj_CurTuple = NULL;


        // CS448: Tuple always belongs to the current batch (batching removed)
				/* OK, let's scan the bucket for matches */
				node->hj_JoinState = HJ_SCAN_BUCKET;

				/* FALL THRU */

			case HJ_SCAN_BUCKET:
        /*
         * CS448: I moved the voodoo. I don't entirely understand the voodoo,
         * it was crafted before I was even born. I embraced the vodooo. It works
         */
        {
          HashState *hashstate;
          if (node->hj_PullInner)
            hashstate = (HashState *) outerPlanState(node);
          else
            hashstate = (HashState *) innerPlanState(node);

          TupleTableSlot *slot = hashstate->ps.ps_ResultTupleSlot;

          node->hj_InnerHashTupleSlot = slot;
        }

				/*
				 * We check for interrupts here because this corresponds to
				 * where we'd fetch a row from a child plan node in other join
				 * types.
				 */
				CHECK_FOR_INTERRUPTS();

				/*
				 * Scan the selected hash bucket for matches to current outer
				 */
				if (!ExecScanHashBucket(node, econtext))
				{
					/* out of matches; */
					node->hj_JoinState = HJ_NEED_NEW_TUPLE;
					continue;
				}

				/*
				 * We've got a match, but still need to test non-hashed quals.
				 * ExecScanHashBucket already set up all the state needed to
				 * call ExecQual.
				 *
				 * If we pass the qual, then save state for next call and have
				 * ExecProject form the projection, store it in the tuple
				 * table, and return the slot.
				 *
				 * Only the joinquals determine tuple match status, but all
				 * quals must pass to actually return the tuple.
				 */
        if (joinqual == NIL || ExecQual(joinqual, econtext, false))
        {
					node->hj_MatchedOuter = true;
					HeapTupleHeaderSetMatch(HJTUPLE_MINTUPLE(node->hj_CurTuple));

          if (otherqual == NIL || ExecQual(otherqual, econtext, false))
          {
            TupleTableSlot *result;

            result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);

            if (isDone != ExprEndResult)
            {
              node->js.ps.ps_TupFromTlist =
                (isDone == ExprMultipleResult);
              return result;
            }
          }
          else
            InstrCountFiltered2(node, 1);
        }
        else
          InstrCountFiltered1(node, 1);
				break;

			case HJ_DONE_SOURCE:
        if (node->hj_OneDone) {
          return NULL;
        } else {
          node->hj_PullInner = !node->hj_PullInner;
          node->hj_JoinState = HJ_NEED_NEW_TUPLE;
          node->hj_OneDone = true;
          continue;
        }
				break;

			default:
				elog(ERROR, "unrecognized hashjoin state: %d",
					 (int) node->hj_JoinState);
		}
	}
}

/* ----------------------------------------------------------------
 *		ExecInitHashJoin
 *
 *		Init routine for HashJoin node.
 * ----------------------------------------------------------------
 */
HashJoinState *
ExecInitHashJoin(HashJoin *node, EState *estate, int eflags)
{
	HashJoinState *hjstate;
  Hash     *outerNode;
	Hash	   *innerNode;
	List	   *lclauses;
	List	   *rclauses;
	List	   *hoperators;
	ListCell   *l;

	/* check for unsupported flags */
	Assert(!(eflags & (EXEC_FLAG_BACKWARD | EXEC_FLAG_MARK)));

	/*
	 * create state structure
	 */
	hjstate = makeNode(HashJoinState);
	hjstate->js.ps.plan = (Plan *) node;
	hjstate->js.ps.state = estate;

	/*
	 * Miscellaneous initialization
	 *
	 * create expression context for node
	 */
	ExecAssignExprContext(estate, &hjstate->js.ps);

	/*
	 * initialize child expressions
	 */
	hjstate->js.ps.targetlist = (List *)
		ExecInitExpr((Expr *) node->join.plan.targetlist,
					 (PlanState *) hjstate);
	hjstate->js.ps.qual = (List *)
		ExecInitExpr((Expr *) node->join.plan.qual,
					 (PlanState *) hjstate);
	hjstate->js.jointype = node->join.jointype;
	hjstate->js.joinqual = (List *)
		ExecInitExpr((Expr *) node->join.joinqual,
					 (PlanState *) hjstate);
	hjstate->hashclauses = (List *)
		ExecInitExpr((Expr *) node->hashclauses,
					 (PlanState *) hjstate);

	/*
	 * initialize child nodes
	 *
	 * Note: we could suppress the REWIND flag for the inner input, which
	 * would amount to betting that the hash will be a single batch.  Not
	 * clear if this would be a win or not.
	 */
	outerNode = (Hash *) outerPlan(node);
	innerNode = (Hash *) innerPlan(node);

	outerPlanState(hjstate) = ExecInitNode((Plan *) outerNode, estate, eflags);
	innerPlanState(hjstate) = ExecInitNode((Plan *) innerNode, estate, eflags);

	/*
	 * tuple table initialization
	 */
	ExecInitResultTupleSlot(estate, &hjstate->js.ps);
	hjstate->hj_OuterTupleSlot = ExecInitExtraTupleSlot(estate);

	/* set up null tuples for outer joins, if needed */
	switch (node->join.jointype)
	{
		case JOIN_INNER:
		case JOIN_SEMI:
			break;
		case JOIN_LEFT:
		case JOIN_ANTI:
			hjstate->hj_NullInnerTupleSlot =
				ExecInitNullTupleSlot(estate,
								 ExecGetResultType(innerPlanState(hjstate)));
			break;
		case JOIN_RIGHT:
			hjstate->hj_NullOuterTupleSlot =
				ExecInitNullTupleSlot(estate,
								 ExecGetResultType(outerPlanState(hjstate)));
			break;
		case JOIN_FULL:
			hjstate->hj_NullOuterTupleSlot =
				ExecInitNullTupleSlot(estate,
								 ExecGetResultType(outerPlanState(hjstate)));
			hjstate->hj_NullInnerTupleSlot =
				ExecInitNullTupleSlot(estate,
								 ExecGetResultType(innerPlanState(hjstate)));
			break;
		default:
			elog(ERROR, "unrecognized join type: %d",
				 (int) node->join.jointype);
	}

	/*
	 * initialize tuple type and projection info
	 */
	ExecAssignResultTypeFromTL(&hjstate->js.ps);
	ExecAssignProjectionInfo(&hjstate->js.ps, NULL);

	ExecSetSlotDescriptor(hjstate->hj_OuterTupleSlot,
						  ExecGetResultType(outerPlanState(hjstate)));

	/*
	 * initialize hash-specific info
	 */
	hjstate->hj_InnerHashTable = NULL;
	hjstate->hj_OuterHashTable = NULL;
	hjstate->hj_FirstOuterTupleSlot = NULL;

	hjstate->hj_CurHashValue = 0;
	hjstate->hj_CurBucketNo = 0;
	hjstate->hj_CurSkewBucketNo = INVALID_SKEW_BUCKET_NO;
	hjstate->hj_CurTuple = NULL;

	/*
	 * Deconstruct the hash clauses into outer and inner argument values, so
	 * that we can evaluate those subexpressions separately.  Also make a list
	 * of the hash operator OIDs, in preparation for looking up the hash
	 * functions to use.
	 */
	lclauses = NIL;
	rclauses = NIL;
	hoperators = NIL;
	foreach(l, hjstate->hashclauses)
	{
		FuncExprState *fstate = (FuncExprState *) lfirst(l);
		OpExpr	   *hclause;

		Assert(IsA(fstate, FuncExprState));
		hclause = (OpExpr *) fstate->xprstate.expr;
		Assert(IsA(hclause, OpExpr));
		lclauses = lappend(lclauses, linitial(fstate->args));
		rclauses = lappend(rclauses, lsecond(fstate->args));
		hoperators = lappend_oid(hoperators, hclause->opno);
	}
	hjstate->hj_OuterHashKeys = lclauses;
	hjstate->hj_InnerHashKeys = rclauses;
	hjstate->hj_HashOperators = hoperators;
	/* child Hash node needs to evaluate inner hash keys, too */
	((HashState *) innerPlanState(hjstate))->hashkeys = rclauses;
	((HashState *) outerPlanState(hjstate))->hashkeys = rclauses;

	hjstate->js.ps.ps_TupFromTlist = false;
	hjstate->hj_JoinState = HJ_BUILD_HASHTABLE;
	hjstate->hj_MatchedOuter = false;
	hjstate->hj_OuterNotEmpty = false;
  hjstate->hj_PullInner = true;
  hjstate->hj_OneDone = false;

	return hjstate;
}

/* ----------------------------------------------------------------
 *		ExecEndHashJoin
 *
 *		clean up routine for HashJoin node
 * ----------------------------------------------------------------
 */
void
ExecEndHashJoin(HashJoinState *node)
{
	/*
	 * Free hash tables
	 */
	if (node->hj_InnerHashTable)
	{
		ExecHashTableDestroy(node->hj_InnerHashTable);
		node->hj_InnerHashTable = NULL;
	}

  /*
   * CS448: Also free the outer hash table
   */
	if (node->hj_OuterHashTable)
	{
		ExecHashTableDestroy(node->hj_OuterHashTable);
		node->hj_OuterHashTable = NULL;
	}

	/*
	 * Free the exprcontext
	 */
	ExecFreeExprContext(&node->js.ps);

	/*
	 * clean out the tuple table
	 */
	ExecClearTuple(node->js.ps.ps_ResultTupleSlot);
	ExecClearTuple(node->hj_OuterTupleSlot);
	ExecClearTuple(node->hj_InnerHashTupleSlot);

	/*
	 * clean up subtrees
	 */
	ExecEndNode(outerPlanState(node));
	ExecEndNode(innerPlanState(node));
}

/*
 * CS448: Like ExecHashJoinOuterGetTuple, but for the inner
 * ExecHashJoinInnerGetTuple
 *		get the next inner tuple for hashjoin
 */
static TupleTableSlot *
ExecHashJoinInnerGetTuple(HashJoinState *hjstate, uint32 *hashvalue)
{
  HashState *innerNode = (HashState *)innerPlanState(hjstate);
	HashJoinTable hashtable = hjstate->hj_OuterHashTable;
	TupleTableSlot *slot;
  slot = ExecHash(innerNode);

  while (!TupIsNull(slot))
  {
    /*
     * We have to compute the tuple's hash value.
     */
    ExprContext *econtext = hjstate->js.ps.ps_ExprContext;

    econtext->ecxt_outertuple = slot;
    if (ExecHashGetHashValue(hashtable, econtext,
                 hjstate->hj_OuterHashKeys,
                 true,		/* outer tuple */
                 false,
                 hashvalue))
    {
      return slot;
    }

    /*
     * That tuple couldn't match because of a NULL, so discard it and
     * continue with the next one.
     */
    slot = ExecHash(innerNode);
  }

	/* End of this batch */
	return NULL;
}

/*
 * ExecHashJoinOuterGetTuple
 *		get the next outer tuple for hashjoin
 */
static TupleTableSlot *
ExecHashJoinOuterGetTuple(HashJoinState *hjstate, uint32 *hashvalue)
{
  HashState *outerNode = (HashState *)outerPlanState(hjstate);
	HashJoinTable hashtable = hjstate->hj_InnerHashTable;
	TupleTableSlot *slot;
  slot = ExecHash(outerNode);

  while (!TupIsNull(slot))
  {
    /*
     * We have to compute the tuple's hash value.
     */
    ExprContext *econtext = hjstate->js.ps.ps_ExprContext;

    econtext->ecxt_outertuple = slot;
    if (ExecHashGetHashValue(hashtable, econtext,
                 hjstate->hj_OuterHashKeys,
                 true,		/* outer tuple */
                 false,
                 hashvalue))
    {
      return slot;
    }

    /*
     * That tuple couldn't match because of a NULL, so discard it and
     * continue with the next one.
     */
    slot = ExecHash(outerNode);
  }

	/* End of this batch */
	return NULL;
}


// CS448: Removed ExecHashJoinSaveTuple
// CS448: Removed ExecHashJoinGetSavedTuple
// CS448: Removed ExecHashJoinNewBatch


void
ExecReScanHashJoin(HashJoinState *node)
{
	/*
	 * In a multi-batch join, we currently have to do rescans the hard way,
	 * primarily because batch temp files may have already been released. But
	 * if it's a single-batch join, and there is no parameter change for the
	 * inner subnode, then we can just re-use the existing hash table without
	 * rebuilding it.
	 */
	if (node->hj_InnerHashTable != NULL)
	{
    /*
     * Okay to reuse the hash table; needn't rescan inner, either.
     *
     * However, if it's a right/full join, we'd better reset the
     * inner-tuple match flags contained in the table.
     */
    if (HJ_FILL_INNER(node))
      ExecHashTableResetMatchFlags(node->hj_InnerHashTable);

    /*
     * Also, we need to reset our state about the emptiness of the
     * outer relation, so that the new scan of the outer will update
     * it correctly if it turns out to be empty this time. (There's no
     * harm in clearing it now because ExecHashJoin won't need the
     * info.  In the other cases, where the hash table doesn't exist
     * or we are destroying it, we leave this state alone because
     * ExecHashJoin will need it the first time through.)
     */
    node->hj_OuterNotEmpty = false;

    /* ExecHashJoin can skip the BUILD_HASHTABLE step */
    node->hj_JoinState = HJ_NEED_NEW_TUPLE;
	}

	/* Always reset intra-tuple state */
	node->hj_CurHashValue = 0;
	node->hj_CurBucketNo = 0;
	node->hj_CurSkewBucketNo = INVALID_SKEW_BUCKET_NO;
	node->hj_CurTuple = NULL;

	node->js.ps.ps_TupFromTlist = false;
	node->hj_MatchedOuter = false;
	node->hj_FirstOuterTupleSlot = NULL;

	/*
	 * if chgParam of subnode is not null then plan will be re-scanned by
	 * first ExecProcNode.
	 */
	if (node->js.ps.lefttree->chgParam == NULL)
		ExecReScan(node->js.ps.lefttree);
}
