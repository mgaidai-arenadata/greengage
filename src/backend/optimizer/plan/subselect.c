/*-------------------------------------------------------------------------
 *
 * subselect.c
 *	  Planning routines for subselects and parameters.
 *
 * Portions Copyright (c) 2005-2008, Greenplum inc
 * Portions Copyright (c) 2012-Present Pivotal Software, Inc.
 * Portions Copyright (c) 1996-2014, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/plan/subselect.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/htup_details.h"
#include "catalog/catalog.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_type.h"
#include "catalog/gp_policy.h"
#include "executor/executor.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/relation.h"
#include "optimizer/clauses.h"
#include "optimizer/cost.h"
#include "optimizer/planmain.h"
#include "optimizer/planner.h"
#include "optimizer/prep.h"
#include "optimizer/subselect.h"
#include "optimizer/var.h"
#include "parser/parse_relation.h"
#include "parser/parsetree.h"
#include "parser/parse_oper.h"
#include "rewrite/rewriteManip.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/syscache.h"

#include "cdb/cdbmutate.h"
#include "cdb/cdbsetop.h"
#include "cdb/cdbsubselect.h"
#include "cdb/cdbvars.h"


typedef struct convert_testexpr_context
{
	PlannerInfo *root;
	List	   *subst_nodes;	/* Nodes to substitute for Params */
} convert_testexpr_context;

typedef struct process_sublinks_context
{
	PlannerInfo *root;
	bool		isTopQual;
} process_sublinks_context;

typedef struct finalize_primnode_context
{
	PlannerInfo *root;
	Bitmapset  *paramids;		/* Non-local PARAM_EXEC paramids found */
} finalize_primnode_context;


static Node *build_subplan(PlannerInfo *root, Plan *plan, PlannerInfo *subroot,
			  List *plan_params,
			  SubLinkType subLinkType, Node *testexpr,
			  bool adjust_testexpr, bool unknownEqFalse);
static List *generate_subquery_params(PlannerInfo *root, List *tlist,
						 List **paramIds);
static Node *convert_testexpr_mutator(Node *node,
						 convert_testexpr_context *context);
static bool subplan_is_hashable(PlannerInfo *root, Plan *plan);
static bool testexpr_is_hashable(Node *testexpr);
static bool hash_ok_operator(OpExpr *expr);
static bool simplify_EXISTS_query(Query *query);
static Query *convert_EXISTS_to_ANY(PlannerInfo *root, Query *subselect,
					  Node **testexpr, List **paramIds);
static Node *replace_correlation_vars_mutator(Node *node, PlannerInfo *root);
static Node *process_sublinks_mutator(Node *node,
						 process_sublinks_context *context);
static Bitmapset *finalize_plan(PlannerInfo *root,
			  Plan *plan,
			  Bitmapset *valid_params,
			  Bitmapset *scan_params);
static bool finalize_primnode(Node *node, finalize_primnode_context *context);
static bool finalize_agg_primnode(Node *node, finalize_primnode_context *context);
static Node *remove_useless_EXISTS_sublink(PlannerInfo *root,
						Query *subselect, bool under_not);

extern	double global_work_mem(PlannerInfo *root);

/*
 * Select a PARAM_EXEC number to identify the given Var as a parameter for
 * the current subquery, or for a nestloop's inner scan.
 * If the Var already has a param in the current context, return that one.
 */
static int
assign_param_for_var(PlannerInfo *root, Var *var)
{
	ListCell   *ppl;
	PlannerParamItem *pitem;
	Index		levelsup;

	/* check multi-level correlated subquery in GPDB planner */
	check_multi_subquery_correlated(root, var);

	/* Find the query level the Var belongs to */
	for (levelsup = var->varlevelsup; levelsup > 0; levelsup--)
		root = root->parent_root;

	/* If there's already a matching PlannerParamItem there, just use it */
	foreach(ppl, root->plan_params)
	{
		pitem = (PlannerParamItem *) lfirst(ppl);
		if (IsA(pitem->item, Var))
		{
			Var		   *pvar = (Var *) pitem->item;

			/*
			 * This comparison must match _equalVar(), except for ignoring
			 * varlevelsup.  Note that _equalVar() ignores the location.
			 */
			if (pvar->varno == var->varno &&
				pvar->varattno == var->varattno &&
				pvar->vartype == var->vartype &&
				pvar->vartypmod == var->vartypmod &&
				pvar->varcollid == var->varcollid &&
				pvar->varnoold == var->varnoold &&
				pvar->varoattno == var->varoattno)
				return pitem->paramId;
		}
	}

	/* Nope, so make a new one */
	var = (Var *) copyObject(var);
	var->varlevelsup = 0;

	pitem = makeNode(PlannerParamItem);
	pitem->item = (Node *) var;
	pitem->paramId = root->glob->nParamExec++;

	root->plan_params = lappend(root->plan_params, pitem);

	return pitem->paramId;
}

/*
 * Generate a Param node to replace the given Var,
 * which is expected to have varlevelsup > 0 (ie, it is not local).
 */
static Param *
replace_outer_var(PlannerInfo *root, Var *var)
{
	Param	   *retval;
	int			i;

	Assert(var->varlevelsup > 0 && var->varlevelsup < root->query_level);

	/* Find the Var in the appropriate plan_params, or add it if not present */
	i = assign_param_for_var(root, var);

	retval = makeNode(Param);
	retval->paramkind = PARAM_EXEC;
	retval->paramid = i;
	retval->paramtype = var->vartype;
	retval->paramtypmod = var->vartypmod;
	retval->paramcollid = var->varcollid;
	retval->location = var->location;

	return retval;
}

/*
 * Generate a Param node to replace the given Var, which will be supplied
 * from an upper NestLoop join node.
 *
 * This is effectively the same as replace_outer_var, except that we expect
 * the Var to be local to the current query level.
 */
Param *
assign_nestloop_param_var(PlannerInfo *root, Var *var)
{
	Param	   *retval;
	int			i;

	Assert(var->varlevelsup == 0);

	i = assign_param_for_var(root, var);

	retval = makeNode(Param);
	retval->paramkind = PARAM_EXEC;
	retval->paramid = i;
	retval->paramtype = var->vartype;
	retval->paramtypmod = var->vartypmod;
	retval->paramcollid = var->varcollid;
	retval->location = var->location;

	return retval;
}

/*
 * Select a PARAM_EXEC number to identify the given PlaceHolderVar as a
 * parameter for the current subquery, or for a nestloop's inner scan.
 * If the PHV already has a param in the current context, return that one.
 *
 * This is just like assign_param_for_var, except for PlaceHolderVars.
 */
static int
assign_param_for_placeholdervar(PlannerInfo *root, PlaceHolderVar *phv)
{
	ListCell   *ppl;
	PlannerParamItem *pitem;
	Index		levelsup;

	/* Find the query level the PHV belongs to */
	for (levelsup = phv->phlevelsup; levelsup > 0; levelsup--)
		root = root->parent_root;

	/* If there's already a matching PlannerParamItem there, just use it */
	foreach(ppl, root->plan_params)
	{
		pitem = (PlannerParamItem *) lfirst(ppl);
		if (IsA(pitem->item, PlaceHolderVar))
		{
			PlaceHolderVar *pphv = (PlaceHolderVar *) pitem->item;

			/* We assume comparing the PHIDs is sufficient */
			if (pphv->phid == phv->phid)
				return pitem->paramId;
		}
	}

	/* Nope, so make a new one */
	phv = (PlaceHolderVar *) copyObject(phv);
	if (phv->phlevelsup != 0)
	{
		IncrementVarSublevelsUp((Node *) phv, -((int) phv->phlevelsup), 0);
		Assert(phv->phlevelsup == 0);
	}

	pitem = makeNode(PlannerParamItem);
	pitem->item = (Node *) phv;
	pitem->paramId = root->glob->nParamExec++;

	root->plan_params = lappend(root->plan_params, pitem);

	return pitem->paramId;
}

/*
 * Generate a Param node to replace the given PlaceHolderVar,
 * which is expected to have phlevelsup > 0 (ie, it is not local).
 *
 * This is just like replace_outer_var, except for PlaceHolderVars.
 */
static Param *
replace_outer_placeholdervar(PlannerInfo *root, PlaceHolderVar *phv)
{
	Param	   *retval;
	int			i;

	Assert(phv->phlevelsup > 0 && phv->phlevelsup < root->query_level);

	/* Find the PHV in the appropriate plan_params, or add it if not present */
	i = assign_param_for_placeholdervar(root, phv);

	retval = makeNode(Param);
	retval->paramkind = PARAM_EXEC;
	retval->paramid = i;
	retval->paramtype = exprType((Node *) phv->phexpr);
	retval->paramtypmod = exprTypmod((Node *) phv->phexpr);
	retval->paramcollid = exprCollation((Node *) phv->phexpr);
	retval->location = -1;

	return retval;
}

/*
 * Generate a Param node to replace the given PlaceHolderVar, which will be
 * supplied from an upper NestLoop join node.
 *
 * This is just like assign_nestloop_param_var, except for PlaceHolderVars.
 */
Param *
assign_nestloop_param_placeholdervar(PlannerInfo *root, PlaceHolderVar *phv)
{
	Param	   *retval;
	int			i;

	Assert(phv->phlevelsup == 0);

	i = assign_param_for_placeholdervar(root, phv);

	retval = makeNode(Param);
	retval->paramkind = PARAM_EXEC;
	retval->paramid = i;
	retval->paramtype = exprType((Node *) phv->phexpr);
	retval->paramtypmod = exprTypmod((Node *) phv->phexpr);
	retval->paramcollid = exprCollation((Node *) phv->phexpr);
	retval->location = -1;

	return retval;
}

/*
 * Generate a Param node to replace the given Aggref
 * which is expected to have agglevelsup > 0 (ie, it is not local).
 */
static Param *
replace_outer_agg(PlannerInfo *root, Aggref *agg)
{
	Param	   *retval;
	PlannerParamItem *pitem;
	Index		levelsup;

	Assert(agg->agglevelsup > 0 && agg->agglevelsup < root->query_level);

	/* Find the query level the Aggref belongs to */
	for (levelsup = agg->agglevelsup; levelsup > 0; levelsup--)
		root = root->parent_root;

	/*
	 * It does not seem worthwhile to try to match duplicate outer aggs. Just
	 * make a new slot every time.
	 */
	agg = (Aggref *) copyObject(agg);
	IncrementVarSublevelsUp((Node *) agg, -((int) agg->agglevelsup), 0);
	Assert(agg->agglevelsup == 0);

	pitem = makeNode(PlannerParamItem);
	pitem->item = (Node *) agg;
	pitem->paramId = root->glob->nParamExec++;

	root->plan_params = lappend(root->plan_params, pitem);

	retval = makeNode(Param);
	retval->paramkind = PARAM_EXEC;
	retval->paramid = pitem->paramId;
	retval->paramtype = agg->aggtype;
	retval->paramtypmod = -1;
	retval->paramcollid = agg->aggcollid;
	retval->location = agg->location;

	return retval;
}

/*
 * Generate a new Param node that will not conflict with any other.
 *
 * This is used to create Params representing subplan outputs.
 * We don't need to build a PlannerParamItem for such a Param, but we do
 * need to record the PARAM_EXEC slot number as being allocated.
 */
static Param *
generate_new_param(PlannerInfo *root, Oid paramtype, int32 paramtypmod,
				   Oid paramcollation)
{
	Param	   *retval;

	retval = makeNode(Param);
	retval->paramkind = PARAM_EXEC;
	retval->paramid = root->glob->nParamExec++;
	retval->paramtype = paramtype;
	retval->paramtypmod = paramtypmod;
	retval->paramcollid = paramcollation;
	retval->location = -1;

	return retval;
}


/*
 * Assign a (nonnegative) PARAM_EXEC ID for a special parameter (one that
 * is not actually used to carry a value at runtime).  Such parameters are
 * used for special runtime signaling purposes, such as connecting a
 * recursive union node to its worktable scan node or forcing plan
 * re-evaluation within the EvalPlanQual mechanism.  No actual Param node
 * exists with this ID, however.
 */
int
SS_assign_special_param(PlannerInfo *root)
{
	return root->glob->nParamExec++;
}

/*
 * Get the datatype/typmod/collation of the first column of the plan's output.
 *
 * This information is stored for ARRAY_SUBLINK execution and for
 * exprType()/exprTypmod()/exprCollation(), which have no way to get at the
 * plan associated with a SubPlan node.  We really only need the info for
 * EXPR_SUBLINK and ARRAY_SUBLINK subplans, but for consistency we save it
 * always.
 */
static void
get_first_col_type(Plan *plan, Oid *coltype, int32 *coltypmod,
				   Oid *colcollation)
{
	/* In cases such as EXISTS, tlist might be empty; arbitrarily use VOID */
	if (plan->targetlist)
	{
		TargetEntry *tent = (TargetEntry *) linitial(plan->targetlist);

		Assert(IsA(tent, TargetEntry));
		if (!tent->resjunk)
		{
			*coltype = exprType((Node *) tent->expr);
			*coltypmod = exprTypmod((Node *) tent->expr);
			*colcollation = exprCollation((Node *) tent->expr);
			return;
		}
	}
	*coltype = VOIDOID;
	*coltypmod = -1;
	*colcollation = InvalidOid;
}

/**
 * Returns true if query refers to a distributed table.
 */
bool QueryHasDistributedRelation(Query *q, bool recursive)
{
	ListCell   *rt = NULL;

	foreach(rt, q->rtable)
	{
		RangeTblEntry *rte = (RangeTblEntry *) lfirst(rt);

		if (rte->rtekind == RTE_SUBQUERY
				&& recursive
				&& QueryHasDistributedRelation(rte->subquery, true))
			return true;

		if (rte->relid != InvalidOid
				&& rte->rtekind == RTE_RELATION)
		{
			GpPolicy *policy = GpPolicyFetch(rte->relid);
			if (GpPolicyIsPartitioned(policy))
			{
				pfree(policy);
				return true;
			}
			pfree(policy);
		}
	}
	return false;
}

typedef struct CorrelatedVarWalkerContext
{
	int maxLevelsUpVar;
	int maxLevelsUpPlaceHolderVar;
} CorrelatedVarWalkerContext;

/**
 *  Walker finds the deepest correlation nesting i.e. maximum levelsup among all
 *  vars/placeholdervars in subquery.
 */
static bool
CorrelatedVarWalker(Node *node, CorrelatedVarWalkerContext *ctx)
{
	Assert(ctx);

	if (node == NULL)
	{
		return false;
	}
	else if (IsA(node, Var))
	{
		Var * v = (Var *) node;
		if (v->varlevelsup > ctx->maxLevelsUpVar)
		{
			ctx->maxLevelsUpVar = v->varlevelsup;
		}
		return false;
	}
	else if (IsA(node, PlaceHolderVar))
	{
		PlaceHolderVar * v = (PlaceHolderVar *) node;
		if (v->phlevelsup > ctx->maxLevelsUpPlaceHolderVar)
		{
			ctx->maxLevelsUpPlaceHolderVar = v->phlevelsup;
		}
		return false;
	}
	else if (IsA(node, Query))
	{
		return query_tree_walker((Query *) node, CorrelatedVarWalker, ctx, 0 /* flags */);
	}

	return expression_tree_walker(node, CorrelatedVarWalker, ctx);
}

/**
 * Returns true if subquery is correlated
 */
bool
IsSubqueryCorrelated(Query *sq)
{
	Assert(sq);
	CorrelatedVarWalkerContext ctx;
	ctx.maxLevelsUpVar = 0;
	ctx.maxLevelsUpPlaceHolderVar = 0;
	CorrelatedVarWalker((Node *) sq, &ctx);
	return (ctx.maxLevelsUpVar > 0 || ctx.maxLevelsUpPlaceHolderVar > 0);
}

/*
 * Check multi-level correlated subquery in Postgres legacy planner
 *
 * We could support one-level correlated subquery by adding
 * broadcast + result(param filter). For multi-level scenario
 * we should prevent planner from adding another motion above
 * result node which is from one-level correlated subquery.
 *
 * In this function, firstly we find the top root which refer
 * to Param, then check table distribution below current root
 * Not support if any distributed table exist.
 */
void
check_multi_subquery_correlated(PlannerInfo *root, Var *var)
{
	int levelsup;

	if (Gp_role != GP_ROLE_DISPATCH)
		return;
	if (var->varlevelsup <= 1)
		return;

	if (list_length(root->parse->rtable) == 0)
		return;

	for (levelsup = var->varlevelsup; levelsup > 0; levelsup--)
	{
		PlannerInfo *parent_root = root->parent_root;

		if (parent_root == NULL)
			elog(ERROR, "not found parent root when checking skip-level correlations");

		/*
		 * Only check sublink not include subquery
		 */
		if(parent_root->parse->hasSubLinks &&
			QueryHasDistributedRelation(root->parse, parent_root->is_correlated_subplan))
		{
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					errmsg("correlated subquery with skip-level correlations is not supported")));
		}

		root = root->parent_root;
	}

	return;
}

/*
 * Convert a SubLink (as created by the parser) into a SubPlan.
 *
 * We are given the SubLink's contained query, type, and testexpr.  We are
 * also told if this expression appears at top level of a WHERE/HAVING qual.
 *
 * Note: we assume that the testexpr has been AND/OR flattened (actually,
 * it's been through eval_const_expressions), but not converted to
 * implicit-AND form; and any SubLinks in it should already have been
 * converted to SubPlans.  The subquery is as yet untouched, however.
 *
 * The result is whatever we need to substitute in place of the SubLink
 * node in the executable expression.  This will be either the SubPlan
 * node (if we have to do the subplan as a subplan), or a Param node
 * representing the result of an InitPlan, or a row comparison expression
 * tree containing InitPlan Param nodes.
 */
static Node *
make_subplan(PlannerInfo *root, Query *orig_subquery, SubLinkType subLinkType,
			 Node *testexpr, bool isTopQual)
{
	Query	   *subquery;
	bool		simple_exists = false;
	double		tuple_fraction = 1.0;
	Plan	   *plan;
	PlannerInfo *subroot;
	List	   *plan_params;
	Node	   *result;

	/*
	 * Copy the source Query node.  This is a quick and dirty kluge to resolve
	 * the fact that the parser can generate trees with multiple links to the
	 * same sub-Query node, but the planner wants to scribble on the Query.
	 * Try to clean this up when we do querytree redesign...
	 */
	subquery = (Query *) copyObject(orig_subquery);

	/*
	 * If it's an EXISTS subplan, we might be able to simplify it.
	 */
	if (subLinkType == EXISTS_SUBLINK)
		simple_exists = simplify_EXISTS_query(subquery);

	/*
	 * For an EXISTS subplan, tell lower-level planner to expect that only the
	 * first tuple will be retrieved.  For ALL and ANY subplans, we will be
	 * able to stop evaluating if the test condition fails or matches, so very
	 * often not all the tuples will be retrieved; for lack of a better idea,
	 * specify 50% retrieval.  For EXPR and ROWCOMPARE subplans, use default
	 * behavior (we're only expecting one row out, anyway).
	 *
	 * NOTE: if you change these numbers, also change cost_subplan() in
	 * path/costsize.c.
	 *
	 * XXX If an ANY subplan is uncorrelated, build_subplan may decide to hash
	 * its output.  In that case it would've been better to specify full
	 * retrieval.  At present, however, we can only check hashability after
	 * we've made the subplan :-(.  (Determining whether it'll fit in work_mem
	 * is the really hard part.)  Therefore, we don't want to be too
	 * optimistic about the percentage of tuples retrieved, for fear of
	 * selecting a plan that's bad for the materialization case.
	 */
	if (subLinkType == EXISTS_SUBLINK)
		tuple_fraction = 1.0;	/* just like a LIMIT 1 */
	else if (subLinkType == ALL_SUBLINK ||
			 subLinkType == ANY_SUBLINK)
		tuple_fraction = 0.5;	/* 50% */
	else
		tuple_fraction = 0.0;	/* default behavior */

	/* plan_params should not be in use in current query level */
	Assert(root->plan_params == NIL);

	PlannerConfig *config = CopyPlannerConfig(root->config);

	if (Gp_role == GP_ROLE_DISPATCH)
	{
		/*
		 * This is a subquery, so it can possibly be correlated and depend
		 * on other parts of the plan
		 */
		config->is_under_subplan = true;

		/*
		 * Disable CTE sharing in subplan.
		 *
		 * fixup_subplans() copys duplicate subplan (subplan with same
		 * plan_id), but doesn't copy the subroot.
		 * If enable cte sharing here, it leads to mismatch of the length
		 * of subplans and subroots. And apply_shareinput_xslice() cannot
		 * make it correct when shared scan is in subplan, then an assert
		 * (or panic) error will happen in init_tuplestore_state().
		 *
		 * See github issue: https://github.com/GreengageDB/greengage/issues/12701
		 */
		config->gp_cte_sharing = false;
	}
	/*
	 * Strictly speaking, the order of rows in a subquery doesn't matter.
	 * Consider e.g. "WHERE IN (SELECT ...)". But in case of
	 * "ARRAY(SELECT foo ORDER BY bar)", we'd like to honor the ORDER BY,
	 * and construct the array in that order.
	 */
	if (subLinkType == ARRAY_SUBLINK)
		config->honor_order_by = true;
	else
		config->honor_order_by = false;

	plan = subquery_planner(root->glob, subquery,
							root,
							false,
							tuple_fraction,
							&subroot,
							config);

	/* Isolate the params needed by this specific subplan */
	plan_params = root->plan_params;
	root->plan_params = NIL;

	/* And convert to SubPlan or InitPlan format. */
	result = build_subplan(root, plan, subroot, plan_params,
						   subLinkType, testexpr, true, isTopQual);

	/*
	 * If it's a correlated EXISTS with an unimportant targetlist, we might be
	 * able to transform it to the equivalent of an IN and then implement it
	 * by hashing.  We don't have enough information yet to tell which way is
	 * likely to be better (it depends on the expected number of executions of
	 * the EXISTS qual, and we are much too early in planning the outer query
	 * to be able to guess that).  So we generate both plans, if possible, and
	 * leave it to the executor to decide which to use.
	 */
	if (simple_exists && IsA(result, SubPlan))
	{
		Node	   *newtestexpr;
		List	   *paramIds;

		/* Make a second copy of the original subquery */
		subquery = (Query *) copyObject(orig_subquery);
		/* and re-simplify */
		simple_exists = simplify_EXISTS_query(subquery);
		Assert(simple_exists);
		/* See if it can be converted to an ANY query */
		subquery = convert_EXISTS_to_ANY(root, subquery,
										 &newtestexpr, &paramIds);
		if (subquery)
		{
			/* Generate the plan for the ANY subquery; we'll need all rows */
			plan = subquery_planner(root->glob, subquery,
									root,
									false,
									0.0,
									&subroot,
									config);

			/* Isolate the params needed by this specific subplan */
			plan_params = root->plan_params;
			root->plan_params = NIL;

			/* Now we can check if it'll fit in work_mem */
			if (subplan_is_hashable(root, plan))
			{
				SubPlan    *hashplan;
				AlternativeSubPlan *asplan;

				/* OK, convert to SubPlan format. */
				hashplan = (SubPlan *) build_subplan(root, plan, subroot,
													 plan_params,
													 ANY_SUBLINK, newtestexpr,
													 false, true);
				/* Check we got what we expected */
				Assert(IsA(hashplan, SubPlan));
				Assert(hashplan->parParam == NIL);
				Assert(hashplan->useHashTable);
				/* build_subplan won't have filled in paramIds */
				hashplan->paramIds = paramIds;

				/* Leave it to the executor to decide which plan to use */
				asplan = makeNode(AlternativeSubPlan);
				asplan->subplans = list_make2(result, hashplan);
				result = (Node *) asplan;
			}
		}
	}

	return result;
}

/*
 * Build a SubPlan node given the raw inputs --- subroutine for make_subplan
 *
 * Returns either the SubPlan, or an expression using initplan output Params,
 * as explained in the comments for make_subplan.
 */
static Node *
build_subplan(PlannerInfo *root, Plan *plan, PlannerInfo *subroot,
			  List *plan_params,
			  SubLinkType subLinkType, Node *testexpr,
			  bool adjust_testexpr, bool unknownEqFalse)
{
	Node	   *result;
	SubPlan    *splan;
	ListCell   *lc;
	Bitmapset  *tmpset;
	Bitmapset  *plan_param_set;
	int         paramid;

	/*
	 * Initialize the SubPlan node.  Note plan_id, plan_name, and cost fields
	 * are set further down.
	 */
	splan = makeNode(SubPlan);
	splan->subLinkType = subLinkType;
    splan->qDispSliceId = 0;             /*CDB*/
	splan->testexpr = NULL;
	splan->paramIds = NIL;
	get_first_col_type(plan, &splan->firstColType, &splan->firstColTypmod,
					   &splan->firstColCollation);
	splan->useHashTable = false;
	splan->unknownEqFalse = unknownEqFalse;
	splan->is_initplan = false;
	splan->is_multirow = false;
	splan->is_parallelized = false;
	splan->initPlanParallel = false;
	splan->setParam = NIL;
	splan->parParam = NIL;
	splan->args = NIL;
	splan->extParam = NIL;

	plan_param_set  = NULL;
	/*
	 * Make parParam and args lists of param IDs and expressions that current
	 * query level will pass to this child plan.
	 */
	foreach(lc, plan_params)
	{
		PlannerParamItem *pitem = (PlannerParamItem *) lfirst(lc);
		Node	   *arg = pitem->item;

		/*
		 * The Var, PlaceHolderVar, or Aggref has already been adjusted to
		 * have the correct varlevelsup, phlevelsup, or agglevelsup.
		 *
		 * If it's a PlaceHolderVar or Aggref, its arguments might contain
		 * SubLinks, which have not yet been processed (see the comments for
		 * SS_replace_correlation_vars).  Do that now.
		 */
		if (IsA(arg, PlaceHolderVar) ||
			IsA(arg, Aggref))
			arg = SS_process_sublinks(root, arg, false);

		splan->parParam = lappend_int(splan->parParam, pitem->paramId);
		splan->args = lappend(splan->args, arg);
		plan_param_set = bms_add_member(plan_param_set, pitem->paramId);
	}

	/*
	 * For gpdb, we need extParam to evaluate if we can process initplan
	 * in ExecutorStart.
	 */
	if (plan->extParam)
	{
		tmpset = bms_difference(plan->extParam, plan_param_set);

		while ((paramid = bms_first_member(tmpset)) >= 0)
			splan->extParam = lappend_int(splan->extParam, paramid);

		pfree(tmpset);
	}

	/*
	 * Un-correlated or undirect correlated plans of EXISTS, EXPR, ARRAY, or
	 * ROWCOMPARE types can be used as initPlans.  For EXISTS, EXPR, or ARRAY,
	 * we just produce a Param referring to the result of evaluating the
	 * initPlan.  For ROWCOMPARE, we must modify the testexpr tree to contain
	 * PARAM_EXEC Params instead of the PARAM_SUBLINK Params emitted by the
	 * parser.
	 */
	if (splan->parParam == NIL && subLinkType == EXISTS_SUBLINK && Gp_role == GP_ROLE_DISPATCH)
	{
		Param	   *prm;

		Assert(testexpr == NULL);
		prm = generate_new_param(root, BOOLOID, -1, InvalidOid);
		splan->setParam = list_make1_int(prm->paramid);
		splan->is_initplan = true;
		result = (Node *) prm;
	}
	else if (splan->parParam == NIL && subLinkType == EXPR_SUBLINK && Gp_role == GP_ROLE_DISPATCH)
	{
		TargetEntry *te = linitial(plan->targetlist);
		Param	   *prm;

		Assert(!te->resjunk);
		Assert(testexpr == NULL);
		prm = generate_new_param(root,
								 exprType((Node *) te->expr),
								 exprTypmod((Node *) te->expr),
								 exprCollation((Node *) te->expr));
		splan->setParam = list_make1_int(prm->paramid);
		splan->is_initplan = true;
		result = (Node *) prm;
	}
	else if (splan->parParam == NIL && subLinkType == ARRAY_SUBLINK && Gp_role == GP_ROLE_DISPATCH)
	{
		TargetEntry *te = linitial(plan->targetlist);
		Oid			arraytype;
		Param	   *prm;

		Assert(!te->resjunk);
		Assert(testexpr == NULL);
		arraytype = get_array_type(exprType((Node *) te->expr));
		if (!OidIsValid(arraytype))
			elog(ERROR, "could not find array type for datatype %s",
				 format_type_be(exprType((Node *) te->expr)));
		prm = generate_new_param(root,
								 arraytype,
								 exprTypmod((Node *) te->expr),
								 exprCollation((Node *) te->expr));
		splan->setParam = list_make1_int(prm->paramid);
		splan->is_initplan = true;
		result = (Node *) prm;
	}
	else if (splan->parParam == NIL && subLinkType == ROWCOMPARE_SUBLINK && Gp_role == GP_ROLE_DISPATCH)
	{
		/* Adjust the Params */
		List	   *params;

		Assert(testexpr != NULL);
		params = generate_subquery_params(root,
										  plan->targetlist,
										  &splan->paramIds);
		result = convert_testexpr(root,
								  testexpr,
								  params);
		splan->setParam = list_copy(splan->paramIds);
		splan->is_initplan = true;

		/*
		 * The executable expression is returned to become part of the outer
		 * plan's expression tree; it is not kept in the initplan node.
		 */
	}
	else
	{
		/*
		 * Adjust the Params in the testexpr, unless caller said it's not
		 * needed.
		 */
		if (testexpr && adjust_testexpr)
		{
			List	   *params;

			params = generate_subquery_params(root,
											  plan->targetlist,
											  &splan->paramIds);
			splan->testexpr = convert_testexpr(root,
											   testexpr,
											   params);
		}
		else
			splan->testexpr = testexpr;

		splan->is_multirow = true; /* CDB: take note. */

		/*
		 * We can't convert subplans of ALL_SUBLINK or ANY_SUBLINK types to
		 * initPlans, even when they are uncorrelated or undirect correlated,
		 * because we need to scan the output of the subplan for each outer
		 * tuple.  But if it's a not-direct-correlated IN (= ANY) test, we
		 * might be able to use a hashtable to avoid comparing all the tuples.
		 *
		 * TODO siva - I believe we should've pulled these up to be NL joins.
		 * We may want to assert that this is never exercised.
		 */
		if (subLinkType == ANY_SUBLINK &&
			splan->parParam == NIL &&
			subplan_is_hashable(root, plan) &&
			testexpr_is_hashable(splan->testexpr))
			splan->useHashTable = true;

		/*
		 * Otherwise, we have the option to tack a Material node onto the top
		 * of the subplan, to reduce the cost of reading it repeatedly.  This
		 * is pointless for a direct-correlated subplan, since we'd have to
		 * recompute its results each time anyway.  For uncorrelated/undirect
		 * correlated subplans, we add Material unless the subplan's top plan
		 * node would materialize its output anyway.  Also, if enable_material
		 * is false, then the user does not want us to materialize anything
		 * unnecessarily, so we don't.
		 */
#if 0
		/*
		 * In GPDB, don't add a MATERIAL node here. We'll most likely add one
		 * later anyway, when the SubPlan reference is "parallelized" in
		 * ParallelizeCorrelatedSubPlan.
		 */
		else if (splan->parParam == NIL && enable_material &&
				 !ExecMaterializesOutput(nodeTag(plan)))
			plan = materialize_finished_plan(plan);
#endif

		result = (Node *) splan;
	}

	AssertEquivalent(splan->is_initplan, !splan->is_multirow && splan->parParam == NIL);

	/*
	 * Add the subplan and its PlannerInfo to the global lists.
	 */
	root->glob->subplans = lappend(root->glob->subplans, plan);
	root->glob->subroots = lappend(root->glob->subroots, subroot);
	splan->plan_id = list_length(root->glob->subplans);

	if (splan->is_initplan)
		root->init_plans = lappend(root->init_plans, splan);

	/*
	 * Executor passes EXEC_REWIND flag to the plan nodes in order to indicate
	 * that underlying node or subplan are likely to be rescanned. Moreover,
	 * for any SubPlan, except InitPlans, rescan is expected and EXEC_REWIND
	 * should be set for them. EXEC_REWIND also allows to delay the eager free.
	 */
	if (!splan->is_initplan)
		root->glob->rewindPlanIDs = bms_add_member(root->glob->rewindPlanIDs,
												   splan->plan_id);

	/* Label the subplan for EXPLAIN purposes */
	if (splan->is_initplan)
	{
		ListCell   *lc;

		StringInfo buf = makeStringInfo();

		appendStringInfo(buf, "InitPlan %d (returns ", splan->plan_id);

		foreach(lc, splan->setParam)
		{
			appendStringInfo(buf, "$%d%s",
							lfirst_int(lc),
							lnext(lc) ? "," : "");
		}
		appendStringInfoString(buf, ")");
		splan->plan_name = pstrdup(buf->data);
		pfree(buf->data);
		pfree(buf);
		buf = NULL;
	}
	else
		splan->plan_name = psprintf("SubPlan %d", splan->plan_id);

	/* Lastly, fill in the cost estimates for use later */
	cost_subplan(root, splan, plan);

	return result;
}

/*
 * generate_subquery_params: build a list of Params representing the output
 * columns of a sublink's sub-select, given the sub-select's targetlist.
 *
 * We also return an integer list of the paramids of the Params.
 */
static List *
generate_subquery_params(PlannerInfo *root, List *tlist, List **paramIds)
{
	List	   *result;
	List	   *ids;
	ListCell   *lc;

	result = ids = NIL;
	foreach(lc, tlist)
	{
		TargetEntry *tent = (TargetEntry *) lfirst(lc);
		Param	   *param;

		if (tent->resjunk)
			continue;

		param = generate_new_param(root,
								   exprType((Node *) tent->expr),
								   exprTypmod((Node *) tent->expr),
								   exprCollation((Node *) tent->expr));
		result = lappend(result, param);
		ids = lappend_int(ids, param->paramid);
	}

	*paramIds = ids;
	return result;
}

/*
 * generate_subquery_vars: build a list of Vars representing the output
 * columns of a sublink's sub-select, given the sub-select's targetlist.
 * The Vars have the specified varno (RTE index).
 */
List *
generate_subquery_vars(PlannerInfo *root, List *tlist, Index varno)
{
	List	   *result;
	ListCell   *lc;

	result = NIL;
	foreach(lc, tlist)
	{
		TargetEntry *tent = (TargetEntry *) lfirst(lc);
		Var		   *var;

		if (tent->resjunk)
			continue;

		var = makeVarFromTargetEntry(varno, tent);
		result = lappend(result, var);
	}

	return result;
}

/*
 * convert_testexpr: convert the testexpr given by the parser into
 * actually executable form.  This entails replacing PARAM_SUBLINK Params
 * with Params or Vars representing the results of the sub-select.  The
 * nodes to be substituted are passed in as the List result from
 * generate_subquery_params or generate_subquery_vars.
 */
Node *
convert_testexpr(PlannerInfo *root,
				 Node *testexpr,
				 List *subst_nodes)
{
	convert_testexpr_context context;

	context.root = root;
	context.subst_nodes = subst_nodes;
	return convert_testexpr_mutator(testexpr, &context);
}

static Node *
convert_testexpr_mutator(Node *node,
						 convert_testexpr_context *context)
{
	if (node == NULL)
		return NULL;
	if (IsA(node, Param))
	{
		Param	   *param = (Param *) node;

		if (param->paramkind == PARAM_SUBLINK)
		{
			if (param->paramid <= 0 ||
				param->paramid > list_length(context->subst_nodes))
				elog(ERROR, "unexpected PARAM_SUBLINK ID: %d", param->paramid);

			/*
			 * We copy the list item to avoid having doubly-linked
			 * substructure in the modified parse tree.  This is probably
			 * unnecessary when it's a Param, but be safe.
			 */
			return (Node *) copyObject(list_nth(context->subst_nodes,
												param->paramid - 1));
		}
	}
	if (IsA(node, SubLink))
	{
		/*
		 * If we come across a nested SubLink, it is neither necessary nor
		 * correct to recurse into it: any PARAM_SUBLINKs we might find inside
		 * belong to the inner SubLink not the outer. So just return it as-is.
		 *
		 * This reasoning depends on the assumption that nothing will pull
		 * subexpressions into or out of the testexpr field of a SubLink, at
		 * least not without replacing PARAM_SUBLINKs first.  If we did want
		 * to do that we'd need to rethink the parser-output representation
		 * altogether, since currently PARAM_SUBLINKs are only unique per
		 * SubLink not globally across the query.  The whole point of
		 * replacing them with Vars or PARAM_EXEC nodes is to make them
		 * globally unique before they escape from the SubLink's testexpr.
		 *
		 * Note: this can't happen when called during SS_process_sublinks,
		 * because that recursively processes inner SubLinks first.  It can
		 * happen when called from convert_ANY_sublink_to_join, though.
		 */
		return node;
	}
	return expression_tree_mutator(node,
								   convert_testexpr_mutator,
								   (void *) context);
}

/*
 * subplan_is_hashable: can we implement an ANY subplan by hashing?
 */
static bool
subplan_is_hashable(PlannerInfo *root, Plan *plan)
{
	double		subquery_size;

	/*
	 * The estimated size of the subquery result must fit in work_mem. (Note:
	 * we use sizeof(HeapTupleHeaderData) here even though the tuples will
	 * actually be stored as MinimalTuples; this provides some fudge factor
	 * for hashtable overhead.)
	 */
	subquery_size = plan->plan_rows *
		(MAXALIGN(plan->plan_width) + MAXALIGN(sizeof(HeapTupleHeaderData)));
	if (subquery_size > global_work_mem(root))
		return false;

	return true;
}

/*
 * testexpr_is_hashable: is an ANY SubLink's test expression hashable?
 */
static bool
testexpr_is_hashable(Node *testexpr)
{
	/*
	 * The testexpr must be a single OpExpr, or an AND-clause containing only
	 * OpExprs.
	 *
	 * The combining operators must be hashable and strict. The need for
	 * hashability is obvious, since we want to use hashing. Without
	 * strictness, behavior in the presence of nulls is too unpredictable.  We
	 * actually must assume even more than plain strictness: they can't yield
	 * NULL for non-null inputs, either (see nodeSubplan.c).  However, hash
	 * indexes and hash joins assume that too.
	 */
	if (testexpr && IsA(testexpr, OpExpr))
	{
		if (hash_ok_operator((OpExpr *) testexpr))
			return true;
	}
	else if (and_clause(testexpr))
	{
		ListCell   *l;

		foreach(l, ((BoolExpr *) testexpr)->args)
		{
			Node	   *andarg = (Node *) lfirst(l);

			if (!IsA(andarg, OpExpr))
				return false;
			if (!hash_ok_operator((OpExpr *) andarg))
				return false;
		}
		return true;
	}

	return false;
}

/*
 * Check expression is hashable + strict
 *
 * We could use op_hashjoinable() and op_strict(), but do it like this to
 * avoid a redundant cache lookup.
 */
static bool
hash_ok_operator(OpExpr *expr)
{
	Oid			opid = expr->opno;

	/* quick out if not a binary operator */
	if (list_length(expr->args) != 2)
		return false;
	if (opid == ARRAY_EQ_OP)
	{
		/* array_eq is strict, but must check input type to ensure hashable */
		/* XXX record_eq will need same treatment when it becomes hashable */
		Node	   *leftarg = linitial(expr->args);

		return op_hashjoinable(opid, exprType(leftarg));
	}
	else
	{
		/* else must look up the operator properties */
		HeapTuple	tup;
		Form_pg_operator optup;

		tup = SearchSysCache1(OPEROID, ObjectIdGetDatum(opid));
		if (!HeapTupleIsValid(tup))
			elog(ERROR, "cache lookup failed for operator %u", opid);
		optup = (Form_pg_operator) GETSTRUCT(tup);
		if (!optup->oprcanhash || !func_strict(optup->oprcode))
		{
			ReleaseSysCache(tup);
			return false;
		}
		ReleaseSysCache(tup);
		return true;
	}
}


#if 0
/*
 * GPDB doesn't use initplan + CteScan, so running SS_process_ctes will only
 * generate unused initplans. Keep commented out to avoid merge conflicts with
 * upstream.
 */

/*
 * SS_process_ctes: process a query's WITH list
 *
 * We plan each interesting WITH item and convert it to an initplan.
 * A side effect is to fill in root->cte_plan_ids with a list that
 * parallels root->parse->cteList and provides the subplan ID for
 * each CTE's initplan.
 */
void
SS_process_ctes(PlannerInfo *root)
{
	ListCell   *lc;

	Assert(root->cte_plan_ids == NIL);

	foreach(lc, root->parse->cteList)
	{
		CommonTableExpr *cte = (CommonTableExpr *) lfirst(lc);
		CmdType		cmdType = ((Query *) cte->ctequery)->commandType;
		Query	   *subquery;
		Plan	   *plan;
		PlannerInfo *subroot;
		SubPlan    *splan;
		int			paramid;

		/*
		 * Ignore SELECT CTEs that are not actually referenced anywhere.
		 */
		if (cte->cterefcount == 0 && cmdType == CMD_SELECT)
		{
			/* Make a dummy entry in cte_plan_ids */
			root->cte_plan_ids = lappend_int(root->cte_plan_ids, -1);
			continue;
		}

		/*
		 * Copy the source Query node.  Probably not necessary, but let's keep
		 * this similar to make_subplan.
		 */
		subquery = (Query *) copyObject(cte->ctequery);

		/* plan_params should not be in use in current query level */
		Assert(root->plan_params == NIL);

		/*
		 * Generate the plan for the CTE query.  Always plan for full
		 * retrieval --- we don't have enough info to predict otherwise.
		 */
		plan = subquery_planner(root->glob, subquery,
								root,
								cte->cterecursive, 0.0,
								&subroot,
								root->config);

		/*
		 * Since the current query level doesn't yet contain any RTEs, it
		 * should not be possible for the CTE to have requested parameters of
		 * this level.
		 */
		if (root->plan_params)
			elog(ERROR, "unexpected outer reference in CTE query");

		/*
		 * Make a SubPlan node for it.  This is just enough unlike
		 * build_subplan that we can't share code.
		 *
		 * Note plan_id, plan_name, and cost fields are set further down.
		 */
		splan = makeNode(SubPlan);
		splan->subLinkType = CTE_SUBLINK;
		splan->testexpr = NULL;
		splan->paramIds = NIL;
		get_first_col_type(plan, &splan->firstColType, &splan->firstColTypmod,
						   &splan->firstColCollation);
		splan->useHashTable = false;
		splan->unknownEqFalse = false;
		splan->setParam = NIL;
		splan->parParam = NIL;
		splan->args = NIL;

		/*
		 * The node can't have any inputs (since it's an initplan), so the
		 * parParam and args lists remain empty.  (It could contain references
		 * to earlier CTEs' output param IDs, but CTE outputs are not
		 * propagated via the args list.)
		 */

		/*
		 * Assign a param ID to represent the CTE's output.  No ordinary
		 * "evaluation" of this param slot ever happens, but we use the param
		 * ID for setParam/chgParam signaling just as if the CTE plan were
		 * returning a simple scalar output.  (Also, the executor abuses the
		 * ParamExecData slot for this param ID for communication among
		 * multiple CteScan nodes that might be scanning this CTE.)
		 */
		paramid = SS_assign_special_param(root);
		splan->setParam = list_make1_int(paramid);

		/*
		 * Add the subplan and its PlannerInfo to the global lists.
		 */
		root->glob->subplans = lappend(root->glob->subplans, plan);
		root->glob->subroots = lappend(root->glob->subroots, subroot);
		splan->plan_id = list_length(root->glob->subplans);

		root->init_plans = lappend(root->init_plans, splan);

		root->cte_plan_ids = lappend_int(root->cte_plan_ids, splan->plan_id);

		/* Label the subplan for EXPLAIN purposes */
		splan->plan_name = psprintf("CTE %s", cte->ctename);

		/* Lastly, fill in the cost estimates for use later */
		cost_subplan(root, splan, plan);
	}
}
#endif

/*
 * convert_ANY_sublink_to_join: try to convert an ANY SubLink to a join
 *
 * The caller has found an ANY SubLink at the top level of one of the query's
 * qual clauses, but has not checked the properties of the SubLink further.
 * Decide whether it is appropriate to process this SubLink in join style.
 * If so, form a JoinExpr and return it.  Return NULL if the SubLink cannot
 * be converted to a join.
 *
 * The only non-obvious input parameter is available_rels: this is the set
 * of query rels that can safely be referenced in the sublink expression.
 * (We must restrict this to avoid changing the semantics when a sublink
 * is present in an outer join's ON qual.)  The conversion must fail if
 * the converted qual would reference any but these parent-query relids.
 *
 * On success, the returned JoinExpr has larg = NULL and rarg = the jointree
 * item representing the pulled-up subquery.  The caller must set larg to
 * represent the relation(s) on the lefthand side of the new join, and insert
 * the JoinExpr into the upper query's jointree at an appropriate place
 * (typically, where the lefthand relation(s) had been).  Note that the
 * passed-in SubLink must also be removed from its original position in the
 * query quals, since the quals of the returned JoinExpr replace it.
 * (Notionally, we replace the SubLink with a constant TRUE, then elide the
 * redundant constant from the qual.)
 *
 * On success, the caller is also responsible for recursively applying
 * pull_up_sublinks processing to the rarg and quals of the returned JoinExpr.
 * (On failure, there is no need to do anything, since pull_up_sublinks will
 * be applied when we recursively plan the sub-select.)
 *
 * Side effects of a successful conversion include adding the SubLink's
 * subselect to the query's rangetable, so that it can be referenced in
 * the JoinExpr's rarg.
 */
JoinExpr *
convert_ANY_sublink_to_join(PlannerInfo *root, SubLink *sublink,
							Relids available_rels)
{
	JoinExpr   *result;
	Query	   *parse = root->parse;
	Query	   *subselect = (Query *) sublink->subselect;
	Relids		upper_varnos;
	int			rtindex;
	RangeTblEntry *rte;
	RangeTblRef *rtr;
	List	   *subquery_vars;
	Node	   *quals;
	bool		correlated;

	Assert(sublink->subLinkType == ANY_SUBLINK);
	Assert(IsA(subselect, Query));

	/* Delete ORDER BY and DISTINCT.
	 *
	 * There is no need to do the group-by or order-by inside the
	 * subquery, if we have decided to pull up the sublink. For the
	 * group-by case, after the sublink pull-up, there will be a semi-join
	 * plan node generated in top level, which will weed out duplicate
	 * tuples naturally. For the order-by case, after the sublink pull-up,
	 * the subquery will become a jointree, inside which the tuples' order
	 * doesn't matter. In a summary, it's safe to elimate the group-by or
	 * order-by causes here.
	*/
	cdbsubselect_drop_orderby(subselect);
	cdbsubselect_drop_distinct(subselect);

	/*
	 * If there are CTEs, then the transformation does not work. Don't attempt
	 * to pullup.
	 */
	if (parse->cteList)
		return NULL;

	/*
	 * If uncorrelated, and no Var nodes on lhs, the subquery will be executed
	 * only once.  It should become an InitPlan, but make_subplan() doesn't
	 * handle that case, so just flatten it for now.
	 * CDB TODO: Let it become an InitPlan, so its QEs can be recycled.
	 */
	correlated = contain_vars_of_level_or_above(sublink->subselect, 1);

	if (correlated)
	{
		/*
		 * Under certain conditions, we cannot pull up the subquery as a join.
		 */
		if (!is_simple_subquery(root, subselect, NULL, NULL))
			return NULL;

		/*
		 * Do not pull subqueries with correlation in a func expr in the from
		 * clause of the subselect
		 */
		if (has_correlation_in_funcexpr_rte(subselect->rtable))
			return NULL;

		if (contain_subplans(subselect->jointree->quals))
			return NULL;
	}

	/*
	 * The test expression must contain some Vars of the parent query,
	 * else it's not gonna be a join.  (Note that it won't have Vars
	 * referring to the subquery, rather Params.)
	 */
	upper_varnos = pull_varnos(sublink->testexpr);
	if (bms_is_empty(upper_varnos))
		return NULL;

	/*
	 * However, it can't refer to anything outside available_rels.
	 */
	if (!bms_is_subset(upper_varnos, available_rels))
		return NULL;

	/*
	 * The combining operators and left-hand expressions mustn't be volatile.
	 */
	if (contain_volatile_functions(sublink->testexpr))
		return NULL;

	/*
	 * Okay, pull up the sub-select into upper range table.
	 *
	 * We rely here on the assumption that the outer query has no references
	 * to the inner (necessarily true, other than the Vars that we build
	 * below). Therefore this is a lot easier than what pull_up_subqueries has
	 * to go through.
	 *
	 * If the subquery is correlated, i.e. it refers to any Vars of the
	 * parent query, mark it as lateral.
	 */
	rte = addRangeTableEntryForSubquery(NULL,
										subselect,
										makeAlias("ANY_subquery", NIL),
										correlated,	/* lateral */
										false);
	parse->rtable = lappend(parse->rtable, rte);
	rtindex = list_length(parse->rtable);

	/*
	 * Form a RangeTblRef for the pulled-up sub-select.
	 */
	rtr = makeNode(RangeTblRef);
	rtr->rtindex = rtindex;

	/*
	 * Build a list of Vars representing the subselect outputs.
	 */
	subquery_vars = generate_subquery_vars(root,
										   subselect->targetList,
										   rtindex);

	/*
	 * Build the new join's qual expression, replacing Params with these Vars.
	 */
	quals = convert_testexpr(root, sublink->testexpr, subquery_vars);

	result = makeNode(JoinExpr);
	result->jointype = JOIN_SEMI;
	result->isNatural = false;
	result->larg = NULL;		/* caller must fill this in */
	result->rarg = (Node *) rtr;
	result->usingClause = NIL;
	result->quals = quals;
	result->alias = NULL;
	result->rtindex = 0;

	return result;
}

/*
 * convert_EXISTS_sublink_to_join: try to convert an EXISTS SubLink to a join
 *
 * The API of this function is identical to convert_ANY_sublink_to_join's,
 * except that we also support the case where the caller has found NOT EXISTS,
 * so we need an additional input parameter "under_not".
 */
Node *
convert_EXISTS_sublink_to_join(PlannerInfo *root, SubLink *sublink,
							   bool under_not, Relids available_rels)
{
	JoinExpr   *result;
	Query	   *parse = root->parse;
	Query	   *subselect = (Query *) sublink->subselect;
	Node	   *whereClause;
	int			rtoffset;
	int			varno;
	Relids		clause_varnos;
	Relids		upper_varnos;
	Node	   *boolConst;

	Assert(sublink->subLinkType == EXISTS_SUBLINK);

	/*
	 * Can't flatten if it contains WITH.  (We could arrange to pull up the
	 * WITH into the parent query's cteList, but that risks changing the
	 * semantics, since a WITH ought to be executed once per associated query
	 * call.)  Note that convert_ANY_sublink_to_join doesn't have to reject
	 * this case, since it just produces a subquery RTE that doesn't have to
	 * get flattened into the parent query.
	 */
	if (subselect->cteList)
		return NULL;

	/*
	 * Copy the subquery so we can modify it safely (see comments in
	 * make_subplan).
	 */
	subselect = (Query *) copyObject(subselect);

	/*
	 * Check if the EXISTS sublink doesn't actually need to be executed at all,
	 * and return TRUE/FALSE directly for it in that case.
	 */
	if ((boolConst = remove_useless_EXISTS_sublink(root, subselect, under_not)))
		return boolConst;

	/*
	 * See if the subquery can be simplified based on the knowledge that it's
	 * being used in EXISTS().  If we aren't able to get rid of its
	 * targetlist, we have to fail, because the pullup operation leaves us
	 * with noplace to evaluate the targetlist.
	 */
	if (!simplify_EXISTS_query(subselect))
		return NULL;

	/*
	 * The subquery must have a nonempty jointree, else we won't have a join.
	 */
	if (subselect->jointree->fromlist == NIL)
		return NULL;

	/*
	 * Separate out the WHERE clause.  (We could theoretically also remove
	 * top-level plain JOIN/ON clauses, but it's probably not worth the
	 * trouble.)
	 */
	whereClause = subselect->jointree->quals;
	subselect->jointree->quals = NULL;

	/*
	 * The rest of the sub-select must not refer to any Vars of the parent
	 * query.  (Vars of higher levels should be okay, though.)
	 */
	if (contain_vars_of_level((Node *) subselect, 1))
		return NULL;

	/*
	 * On the other hand, the WHERE clause must contain some Vars of the
	 * parent query, else it's not gonna be a join.
	 */
	if (!contain_vars_of_level(whereClause, 1))
	{
		/*
		 * CDB: Add 'limit 1' in this case.
		 */
		((Query*)sublink->subselect)->limitCount =
			(Node *) makeConst(INT8OID, -1, InvalidOid, sizeof(int64),
								Int64GetDatum(1), false, true);
		return NULL;
	}

	/*
	 * We don't risk optimizing if the WHERE clause is volatile, either.
	 */
	if (contain_volatile_functions(whereClause))
		return NULL;

	/*
	 * Prepare to pull up the sub-select into top range table.
	 *
	 * We rely here on the assumption that the outer query has no references
	 * to the inner (necessarily true). Therefore this is a lot easier than
	 * what pull_up_subqueries has to go through.
	 *
	 * In fact, it's even easier than what convert_ANY_sublink_to_join has to
	 * do.  The machinations of simplify_EXISTS_query ensured that there is
	 * nothing interesting in the subquery except an rtable and jointree, and
	 * even the jointree FromExpr no longer has quals.  So we can just append
	 * the rtable to our own and use the FromExpr in our jointree. But first,
	 * adjust all level-zero varnos in the subquery to account for the rtable
	 * merger.
	 */
	rtoffset = list_length(parse->rtable);
	OffsetVarNodes((Node *) subselect, rtoffset, 0);
	OffsetVarNodes(whereClause, rtoffset, 0);

	/*
	 * Upper-level vars in subquery will now be one level closer to their
	 * parent than before; in particular, anything that had been level 1
	 * becomes level zero.
	 */
	IncrementVarSublevelsUp((Node *) subselect, -1, 1);
	IncrementVarSublevelsUp(whereClause, -1, 1);

	/*
	 * Now that the WHERE clause is adjusted to match the parent query
	 * environment, we can easily identify all the level-zero rels it uses.
	 * The ones <= rtoffset belong to the upper query; the ones > rtoffset do
	 * not.
	 */
	clause_varnos = pull_varnos(whereClause);
	upper_varnos = NULL;
	while ((varno = bms_first_member(clause_varnos)) >= 0)
	{
		if (varno <= rtoffset)
			upper_varnos = bms_add_member(upper_varnos, varno);
	}
	bms_free(clause_varnos);
	Assert(!bms_is_empty(upper_varnos));

	/*
	 * Now that we've got the set of upper-level varnos, we can make the last
	 * check: only available_rels can be referenced.
	 */
	if (!bms_is_subset(upper_varnos, available_rels))
		return NULL;

	/* Now we can attach the modified subquery rtable to the parent */
	parse->rtable = list_concat(parse->rtable, subselect->rtable);

	/*
	 * And finally, build the JoinExpr node.
	 */
	result = makeNode(JoinExpr);
	result->jointype = under_not ? JOIN_ANTI : JOIN_SEMI;
	result->isNatural = false;
	result->larg = NULL;		/* caller must fill this in */
	/* flatten out the FromExpr node if it's useless */
	if (list_length(subselect->jointree->fromlist) == 1)
		result->rarg = (Node *) linitial(subselect->jointree->fromlist);
	else
		result->rarg = (Node *) subselect->jointree;
	result->usingClause = NIL;
	result->quals = whereClause;
	result->alias = NULL;
	result->rtindex = 0;		/* we don't need an RTE for it */

	return (Node *) result;
}

/*
 * simplify_EXISTS_query: remove any useless stuff in an EXISTS's subquery
 *
 * The only thing that matters about an EXISTS query is whether it returns
 * zero or more than zero rows.  Therefore, we can remove certain SQL features
 * that won't affect that.  The only part that is really likely to matter in
 * typical usage is simplifying the targetlist: it's a common habit to write
 * "SELECT * FROM" even though there is no need to evaluate any columns.
 *
 * Note: by suppressing the targetlist we could cause an observable behavioral
 * change, namely that any errors that might occur in evaluating the tlist
 * won't occur, nor will other side-effects of volatile functions.  This seems
 * unlikely to bother anyone in practice.
 *
 * Returns TRUE if was able to discard the targetlist, else FALSE.
 */
static bool
simplify_EXISTS_query(Query *query)
{
	/*
	 * PostgreSQL:
	 *
	 * We don't try to simplify at all if the query uses set operations,
	 * aggregates, HAVING, LIMIT/OFFSET, or FOR UPDATE/SHARE; none of these
	 * seem likely in normal usage and their possible effects are complex.
	 *
	 * In GPDB, we try a bit harder: Try to demote HAVING to WHERE, in case
	 * there are no aggregates or volatile functions. If that fails, only
	 * then give up. Also, just discard any window functions; they
	 * shouldn't affect the number of rows returned.
	 */
	if (query->commandType != CMD_SELECT ||
		query->setOperations ||
#if 0
		query->hasAggs ||
		query->hasWindowFuncs ||
		query->havingQual ||
#endif
		query->hasModifyingCTE ||
		query->limitOffset ||
		query->limitCount ||
		query->rowMarks)
		return false;

	/*
	 * Mustn't throw away the targetlist if it contains set-returning
	 * functions; those could affect whether zero rows are returned!
	 */
	if (expression_returns_set((Node *) query->targetList))
		return false;

	if (query->havingQual)
	{
		/*
		 * If HAVING has no aggregates and volatile functions, demote
		 * it to WHERE.
		 * Note: In addition to these rules, subquery_planner() also
		 * checks if HAVING has subplans, which is not relevant here as
		 * there are not going to be any subplans at this stage.
		 */
		if (!contain_aggs_of_level(query->havingQual, 0) &&
		    !contain_volatile_functions(query->havingQual))
		{
			query->jointree->quals = make_and_qual(query->jointree->quals,
												   query->havingQual);
			query->havingQual = NULL;
			query->hasAggs = false;
		}
		else
			return false;
	}

	/*
	 * Otherwise, we can throw away the targetlist, as well as any GROUP,
	 * WINDOW, DISTINCT, and ORDER BY clauses; none of those clauses will
	 * change a nonzero-rows result to zero rows or vice versa.  (Furthermore,
	 * since our parsetree representation of these clauses depends on the
	 * targetlist, we'd better throw them away if we drop the targetlist.)
	 */
	query->targetList = NIL;

	/*
	 * Delete GROUP BY if no aggregates.
	 *
	 * Note: It's important that we don't clear hasAggs, even though we
	 * removed any possible aggregates from the targetList! If you have a
	 * subquery like "SELECT SUM(foo) ...", we don't need to compute the sum,
	 * but we must still aggregate all the rows, and return a single row,
	 * regardless of how many input rows there are. (In particular, even
	 * if there are no input rows).
	 */
	if (!query->hasAggs)
		query->groupClause = NIL;
	query->windowClause = NIL;
	query->distinctClause = NIL;
	query->sortClause = NIL;
	query->hasDistinctOn = false;

	return true;
}

/*
 * remove_useless_EXISTS_sublink
 * 		Check if the EXISTS sublink doesn't actually need to be executed at all,
 * 		and return TRUE/FALSE directly for it in that case. Otherwise return
 * 		NULL.
 */
static Node *
remove_useless_EXISTS_sublink(PlannerInfo *root, Query *subselect, bool under_not)
{
	/*
	 * 'LIMIT n' makes EXISTS false when n <= 0, and doesn't affect the
	 * outcome when n > 0.
	 */
	if (subselect->limitCount)
	{
		Node	*node = eval_const_expressions(root, subselect->limitCount);
		Const	*limit;

		subselect->limitCount = node;

		if (!IsA(node, Const))
			return NULL;

		limit = (Const *) node;
		Assert(limit->consttype == INT8OID);
		if (!limit->constisnull && DatumGetInt64(limit->constvalue) <= 0)
			return makeBoolConst(under_not, false);

		subselect->limitCount = NULL;
	}

	/*
	 * If subquery has aggregates without GROUP BY or HAVING, its result is
	 * exactly one row (assuming no errors), unless that row is discarded by
	 * LIMIT/OFFSET.
	 */
	if (subselect->hasAggs &&
		subselect->groupClause == NIL &&
		subselect->havingQual == NULL)
	{
		/*
		 * 'OFFSET m' falsifies EXISTS for m >= 1, and doesn't affect the
		 * outcome for m < 1, given that the subquery yields at most one row.
		 */
		if (subselect->limitOffset)
		{
			Node	*node = eval_const_expressions(root, subselect->limitOffset);
			Const	*limit;

			subselect->limitOffset = node;

			if (!IsA(node, Const))
				return NULL;

			limit = (Const *) node;
			Assert(limit->consttype == INT8OID);
			if (!limit->constisnull && DatumGetInt64(limit->constvalue) > 0)
				return makeBoolConst(under_not, false);
		}

		return makeBoolConst(!under_not, false);
	}

	return NULL;
}

/*
 * convert_EXISTS_to_ANY: try to convert EXISTS to a hashable ANY sublink
 *
 * The subselect is expected to be a fresh copy that we can munge up,
 * and to have been successfully passed through simplify_EXISTS_query.
 *
 * On success, the modified subselect is returned, and we store a suitable
 * upper-level test expression at *testexpr, plus a list of the subselect's
 * output Params at *paramIds.  (The test expression is already Param-ified
 * and hence need not go through convert_testexpr, which is why we have to
 * deal with the Param IDs specially.)
 *
 * On failure, returns NULL.
 */
static Query *
convert_EXISTS_to_ANY(PlannerInfo *root, Query *subselect,
					  Node **testexpr, List **paramIds)
{
	Node	   *whereClause;
	List	   *leftargs,
			   *rightargs,
			   *opids,
			   *opcollations,
			   *newWhere,
			   *tlist,
			   *testlist,
			   *paramids;
	ListCell   *lc,
			   *rc,
			   *oc,
			   *cc;
	AttrNumber	resno;

	/*
	 * Query must not require a targetlist, since we have to insert a new one.
	 * Caller should have dealt with the case already.
	 */
	Assert(subselect->targetList == NIL);

	/*
	 * Separate out the WHERE clause.  (We could theoretically also remove
	 * top-level plain JOIN/ON clauses, but it's probably not worth the
	 * trouble.)
	 */
	whereClause = subselect->jointree->quals;
	subselect->jointree->quals = NULL;

	/*
	 * The rest of the sub-select must not refer to any Vars of the parent
	 * query.  (Vars of higher levels should be okay, though.)
	 *
	 * Note: we need not check for Aggs separately because we know the
	 * sub-select is as yet unoptimized; any uplevel Agg must therefore
	 * contain an uplevel Var reference.  This is not the case below ...
	 */
	if (contain_vars_of_level((Node *) subselect, 1))
		return NULL;

	/*
	 * We don't risk optimizing if the WHERE clause is volatile, either.
	 */
	if (contain_volatile_functions(whereClause))
		return NULL;

	/*
	 * Clean up the WHERE clause by doing const-simplification etc on it.
	 * Aside from simplifying the processing we're about to do, this is
	 * important for being able to pull chunks of the WHERE clause up into the
	 * parent query.  Since we are invoked partway through the parent's
	 * preprocess_expression() work, earlier steps of preprocess_expression()
	 * wouldn't get applied to the pulled-up stuff unless we do them here. For
	 * the parts of the WHERE clause that get put back into the child query,
	 * this work is partially duplicative, but it shouldn't hurt.
	 *
	 * Note: we do not run flatten_join_alias_vars.  This is OK because any
	 * parent aliases were flattened already, and we're not going to pull any
	 * child Vars (of any description) into the parent.
	 *
	 * Note: passing the parent's root to eval_const_expressions is
	 * technically wrong, but we can get away with it since only the
	 * boundParams (if any) are used, and those would be the same in a
	 * subroot.
	 */
	whereClause = eval_const_expressions(root, whereClause);
	whereClause = (Node *) canonicalize_qual_ext((Expr *) whereClause, false);
	whereClause = (Node *) make_ands_implicit((Expr *) whereClause);

	/*
	 * We now have a flattened implicit-AND list of clauses, which we try to
	 * break apart into "outervar = innervar" hash clauses. Anything that
	 * can't be broken apart just goes back into the newWhere list.  Note that
	 * we aren't trying hard yet to ensure that we have only outer or only
	 * inner on each side; we'll check that if we get to the end.
	 */
	leftargs = rightargs = opids = opcollations = newWhere = NIL;
	foreach(lc, (List *) whereClause)
	{
		OpExpr	   *expr = (OpExpr *) lfirst(lc);

		if (IsA(expr, OpExpr) &&
			hash_ok_operator(expr))
		{
			Node	   *leftarg = (Node *) linitial(expr->args);
			Node	   *rightarg = (Node *) lsecond(expr->args);

			if (contain_vars_of_level(leftarg, 1))
			{
				leftargs = lappend(leftargs, leftarg);
				rightargs = lappend(rightargs, rightarg);
				opids = lappend_oid(opids, expr->opno);
				opcollations = lappend_oid(opcollations, expr->inputcollid);
				continue;
			}
			if (contain_vars_of_level(rightarg, 1))
			{
				/*
				 * We must commute the clause to put the outer var on the
				 * left, because the hashing code in nodeSubplan.c expects
				 * that.  This probably shouldn't ever fail, since hashable
				 * operators ought to have commutators, but be paranoid.
				 */
				expr->opno = get_commutator(expr->opno);
				if (OidIsValid(expr->opno) && hash_ok_operator(expr))
				{
					leftargs = lappend(leftargs, rightarg);
					rightargs = lappend(rightargs, leftarg);
					opids = lappend_oid(opids, expr->opno);
					opcollations = lappend_oid(opcollations, expr->inputcollid);
					continue;
				}
				/* If no commutator, no chance to optimize the WHERE clause */
				return NULL;
			}
		}
		/* Couldn't handle it as a hash clause */
		newWhere = lappend(newWhere, expr);
	}

	/*
	 * If we didn't find anything we could convert, fail.
	 */
	if (leftargs == NIL)
		return NULL;

	/*
	 * There mustn't be any parent Vars or Aggs in the stuff that we intend to
	 * put back into the child query.  Note: you might think we don't need to
	 * check for Aggs separately, because an uplevel Agg must contain an
	 * uplevel Var in its argument.  But it is possible that the uplevel Var
	 * got optimized away by eval_const_expressions.  Consider
	 *
	 * SUM(CASE WHEN false THEN uplevelvar ELSE 0 END)
	 */
	if (contain_vars_of_level((Node *) newWhere, 1) ||
		contain_vars_of_level((Node *) rightargs, 1))
		return NULL;
	if (root->parse->hasAggs &&
		(contain_aggs_of_level((Node *) newWhere, 1) ||
		 contain_aggs_of_level((Node *) rightargs, 1)))
		return NULL;

	/*
	 * And there can't be any child Vars in the stuff we intend to pull up.
	 * (Note: we'd need to check for child Aggs too, except we know the child
	 * has no aggs at all because of simplify_EXISTS_query's check. The same
	 * goes for window functions.)
	 */
	if (contain_vars_of_level((Node *) leftargs, 0))
		return NULL;

	/*
	 * Also reject sublinks in the stuff we intend to pull up.  (It might be
	 * possible to support this, but doesn't seem worth the complication.)
	 */
	if (contain_subplans((Node *) leftargs))
		return NULL;

	/*
	 * Okay, adjust the sublevelsup in the stuff we're pulling up.
	 */
	IncrementVarSublevelsUp((Node *) leftargs, -1, 1);

	/*
	 * Put back any child-level-only WHERE clauses.
	 */
	if (newWhere)
		subselect->jointree->quals = (Node *) make_ands_explicit(newWhere);

	/*
	 * Build a new targetlist for the child that emits the expressions we
	 * need.  Concurrently, build a testexpr for the parent using Params to
	 * reference the child outputs.  (Since we generate Params directly here,
	 * there will be no need to convert the testexpr in build_subplan.)
	 */
	tlist = testlist = paramids = NIL;
	resno = 1;
	/* there's no "forfour" so we have to chase one of the lists manually */
	cc = list_head(opcollations);
	forthree(lc, leftargs, rc, rightargs, oc, opids)
	{
		Node	   *leftarg = (Node *) lfirst(lc);
		Node	   *rightarg = (Node *) lfirst(rc);
		Oid			opid = lfirst_oid(oc);
		Oid			opcollation = lfirst_oid(cc);
		Param	   *param;

		cc = lnext(cc);
		param = generate_new_param(root,
								   exprType(rightarg),
								   exprTypmod(rightarg),
								   exprCollation(rightarg));
		tlist = lappend(tlist,
						makeTargetEntry((Expr *) rightarg,
										resno++,
										NULL,
										false));
		testlist = lappend(testlist,
						   make_opclause(opid, BOOLOID, false,
										 (Expr *) leftarg, (Expr *) param,
										 InvalidOid, opcollation));
		paramids = lappend_int(paramids, param->paramid);
	}

	/* Put everything where it should go, and we're done */
	subselect->targetList = tlist;
	*testexpr = (Node *) make_ands_explicit(testlist);
	*paramIds = paramids;

	return subselect;
}


/*
 * Replace correlation vars (uplevel vars) with Params.
 *
 * Uplevel PlaceHolderVars and aggregates are replaced, too.
 *
 * Note: it is critical that this runs immediately after SS_process_sublinks.
 * Since we do not recurse into the arguments of uplevel PHVs and aggregates,
 * they will get copied to the appropriate subplan args list in the parent
 * query with uplevel vars not replaced by Params, but only adjusted in level
 * (see replace_outer_placeholdervar and replace_outer_agg).  That's exactly
 * what we want for the vars of the parent level --- but if a PHV's or
 * aggregate's argument contains any further-up variables, they have to be
 * replaced with Params in their turn. That will happen when the parent level
 * runs SS_replace_correlation_vars.  Therefore it must do so after expanding
 * its sublinks to subplans.  And we don't want any steps in between, else
 * those steps would never get applied to the argument expressions, either in
 * the parent or the child level.
 *
 * Another fairly tricky thing going on here is the handling of SubLinks in
 * the arguments of uplevel PHVs/aggregates.  Those are not touched inside the
 * intermediate query level, either.  Instead, SS_process_sublinks recurses on
 * them after copying the PHV or Aggref expression into the parent plan level
 * (this is actually taken care of in build_subplan).
 */
Node *
SS_replace_correlation_vars(PlannerInfo *root, Node *expr)
{
	/* No setup needed for tree walk, so away we go */
	return replace_correlation_vars_mutator(expr, root);
}

static Node *
replace_correlation_vars_mutator(Node *node, PlannerInfo *root)
{
	if (node == NULL)
		return NULL;
	if (IsA(node, Var))
	{
		if (((Var *) node)->varlevelsup > 0)
			return (Node *) replace_outer_var(root, (Var *) node);
	}
	if (IsA(node, PlaceHolderVar))
	{
		if (((PlaceHolderVar *) node)->phlevelsup > 0)
			return (Node *) replace_outer_placeholdervar(root,
													(PlaceHolderVar *) node);
	}
	if (IsA(node, Aggref))
	{
		if (((Aggref *) node)->agglevelsup > 0)
			return (Node *) replace_outer_agg(root, (Aggref *) node);
	}
	return expression_tree_mutator(node,
								   replace_correlation_vars_mutator,
								   (void *) root);
}

/*
 * Expand SubLinks to SubPlans in the given expression.
 *
 * The isQual argument tells whether or not this expression is a WHERE/HAVING
 * qualifier expression.  If it is, any sublinks appearing at top level need
 * not distinguish FALSE from UNKNOWN return values.
 */
Node *
SS_process_sublinks(PlannerInfo *root, Node *expr, bool isQual)
{
	process_sublinks_context context;

	context.root = root;
	context.isTopQual = isQual;
	return process_sublinks_mutator(expr, &context);
}

static Node *
process_sublinks_mutator(Node *node, process_sublinks_context *context)
{
	process_sublinks_context locContext;

	locContext.root = context->root;

	if (node == NULL)
		return NULL;
	if (IsA(node, SubLink))
	{
		SubLink    *sublink = (SubLink *) node;
		Node	   *testexpr;

		/*
		 * First, recursively process the lefthand-side expressions, if any.
		 * They're not top-level anymore.
		 */
		locContext.isTopQual = false;
		testexpr = process_sublinks_mutator(sublink->testexpr, &locContext);

		/*
		 * Now build the SubPlan node and make the expr to return.
		 */
		return make_subplan(context->root,
							(Query *) sublink->subselect,
							sublink->subLinkType,
							testexpr,
							context->isTopQual);
	}

	/*
	 * Don't recurse into the arguments of an outer PHV or aggregate here. Any
	 * SubLinks in the arguments have to be dealt with at the outer query
	 * level; they'll be handled when build_subplan collects the PHV or Aggref
	 * into the arguments to be passed down to the current subplan.
	 */
	if (IsA(node, PlaceHolderVar))
	{
		if (((PlaceHolderVar *) node)->phlevelsup > 0)
			return node;
	}
	else if (IsA(node, Aggref))
	{
		if (((Aggref *) node)->agglevelsup > 0)
			return node;
	}

	/*
	 * We should never see a SubPlan expression in the input (since this is
	 * the very routine that creates 'em to begin with).  We shouldn't find
	 * ourselves invoked directly on a Query, either.
	 */
	Assert(!IsA(node, SubPlan));
	Assert(!IsA(node, AlternativeSubPlan));
	Assert(!IsA(node, Query));

	/*
	 * Because make_subplan() could return an AND or OR clause, we have to
	 * take steps to preserve AND/OR flatness of a qual.  We assume the input
	 * has been AND/OR flattened and so we need no recursion here.
	 *
	 * (Due to the coding here, we will not get called on the List subnodes of
	 * an AND; and the input is *not* yet in implicit-AND format.  So no check
	 * is needed for a bare List.)
	 *
	 * Anywhere within the top-level AND/OR clause structure, we can tell
	 * make_subplan() that NULL and FALSE are interchangeable.  So isTopQual
	 * propagates down in both cases.  (Note that this is unlike the meaning
	 * of "top level qual" used in most other places in Postgres.)
	 */
	if (and_clause(node))
	{
		List	   *newargs = NIL;
		ListCell   *l;

		/* Still at qual top-level */
		locContext.isTopQual = context->isTopQual;

		foreach(l, ((BoolExpr *) node)->args)
		{
			Node	   *newarg;

			newarg = process_sublinks_mutator(lfirst(l), &locContext);
			if (and_clause(newarg))
				newargs = list_concat(newargs, ((BoolExpr *) newarg)->args);
			else
				newargs = lappend(newargs, newarg);
		}
		return (Node *) make_andclause(newargs);
	}

	if (or_clause(node))
	{
		List	   *newargs = NIL;
		ListCell   *l;

		/* Still at qual top-level */
		locContext.isTopQual = context->isTopQual;

		foreach(l, ((BoolExpr *) node)->args)
		{
			Node	   *newarg;

			newarg = process_sublinks_mutator(lfirst(l), &locContext);
			if (or_clause(newarg))
				newargs = list_concat(newargs, ((BoolExpr *) newarg)->args);
			else
				newargs = lappend(newargs, newarg);
		}
		return (Node *) make_orclause(newargs);
	}

	/*
	 * If we recurse down through anything other than an AND or OR node, we
	 * are definitely not at top qual level anymore.
	 */
	locContext.isTopQual = false;

	return expression_tree_mutator(node,
								   process_sublinks_mutator,
								   (void *) &locContext);
}

/*
 * SS_finalize_plan - do final sublink and parameter processing for a
 * completed Plan.
 *
 * This recursively computes the extParam and allParam sets for every Plan
 * node in the given plan tree.  It also optionally attaches any previously
 * generated InitPlans to the top plan node.  (Any InitPlans should already
 * have been put through SS_finalize_plan.)
 *
 * Input:
 * 	root - PlannerInfo structure that is necessary for walking the tree
 * 	rtable - list of rangetable entries to look at for relids
 * 	attach_initplans - attach all initplans to the top plan node from root
 * Output:
 * 	plan->extParam and plan->allParam - attach params to top of the plan
 */
void
SS_finalize_plan(PlannerInfo *root, Plan *plan, bool attach_initplans)
{
	Bitmapset  *valid_params,
			   *initExtParam,
			   *initSetParam;
	Cost		initplan_cost;
	PlannerInfo *proot;
	ListCell   *l;

	/*
	 * Examine any initPlans to determine the set of external params they
	 * reference, the set of output params they supply, and their total cost.
	 * We'll use at least some of this info below.  (Note we are assuming that
	 * finalize_plan doesn't touch the initPlans.)
	 *
	 * In the case where attach_initplans is false, we are assuming that the
	 * existing initPlans are siblings that might supply params needed by the
	 * current plan.
	 */
	initExtParam = initSetParam = NULL;
	initplan_cost = 0;
	foreach(l, root->init_plans)
	{
		SubPlan    *initsubplan = (SubPlan *) lfirst(l);
		Plan	   *initplan = planner_subplan_get_plan(root, initsubplan);
		ListCell   *l2;

		initExtParam = bms_add_members(initExtParam, initplan->extParam);
		foreach(l2, initsubplan->setParam)
		{
			initSetParam = bms_add_member(initSetParam, lfirst_int(l2));
		}
		initplan_cost += initsubplan->startup_cost + initsubplan->per_call_cost;
	}

	/*
	 * Now determine the set of params that are validly referenceable in this
	 * query level; to wit, those available from outer query levels plus the
	 * output parameters of any local initPlans.  (We do not include output
	 * parameters of regular subplans.  Those should only appear within the
	 * testexpr of SubPlan nodes, and are taken care of locally within
	 * finalize_primnode.  Likewise, special parameters that are generated by
	 * nodes such as ModifyTable are handled within finalize_plan.)
	 */
	valid_params = bms_copy(initSetParam);
	for (proot = root->parent_root; proot != NULL; proot = proot->parent_root)
	{
		/* Include ordinary Var/PHV/Aggref params */
		foreach(l, proot->plan_params)
		{
			PlannerParamItem *pitem = (PlannerParamItem *) lfirst(l);

			valid_params = bms_add_member(valid_params, pitem->paramId);
		}
		/* Include any outputs of outer-level initPlans */
		foreach(l, proot->init_plans)
		{
			SubPlan    *initsubplan = (SubPlan *) lfirst(l);
			ListCell   *l2;

			foreach(l2, initsubplan->setParam)
			{
				valid_params = bms_add_member(valid_params, lfirst_int(l2));
			}
		}
		/* Include worktable ID, if a recursive query is being planned */
		if (proot->wt_param_id >= 0)
			valid_params = bms_add_member(valid_params, proot->wt_param_id);
	}

	/*
	 * Now recurse through plan tree.
	 */
	(void) finalize_plan(root, plan, valid_params, NULL);

	bms_free(valid_params);

	/*
	 * Finally, attach any initPlans to the topmost plan node, and add their
	 * extParams to the topmost node's, too.  However, any setParams of the
	 * initPlans should not be present in the topmost node's extParams, only
	 * in its allParams.  (As of PG 8.1, it's possible that some initPlans
	 * have extParams that are setParams of other initPlans, so we have to
	 * take care of this situation explicitly.)
	 *
	 * We also add the eval cost of each initPlan to the startup cost of the
	 * top node.  This is a conservative overestimate, since in fact each
	 * initPlan might be executed later than plan startup, or even not at all.
	 */
	if (attach_initplans)
	{
		/*
		 * If the topmost plan is a Motion, attach the InitPlan to the node
		 * below it, instead. The executor machinery that executes InitPlans
		 * in the QD node, and sends the resulting exec parameters to the QE
		 * nodes, gets confused if the InitPlan is attached to the Motion
		 * node, and fails to deliver the exec parameter value to where it's
		 * needed. I'm not sure why that fails, but historically the InitPlans
		 * have always been attached to the node below the Motion, so let's
		 * just keep that behavior for now.
		 */
		if (IsA(plan, Motion))
			plan = plan->lefttree;

		Insist(!plan->initPlan);
		plan->initPlan = root->init_plans;
		root->init_plans = NIL; /* make sure they're not attached twice */

		/* allParam must include all these params */
		plan->allParam = bms_add_members(plan->allParam, initExtParam);
		plan->allParam = bms_add_members(plan->allParam, initSetParam);
		/* extParam must include any child extParam */
		plan->extParam = bms_add_members(plan->extParam, initExtParam);
		/* but extParam shouldn't include any setParams */
		plan->extParam = bms_del_members(plan->extParam, initSetParam);
		/* ensure extParam is exactly NULL if it's empty */
		if (bms_is_empty(plan->extParam))
			plan->extParam = NULL;

		plan->startup_cost += initplan_cost;
		plan->total_cost += initplan_cost;
	}
}

/*
 * Recursive processing of all nodes in the plan tree
 *
 * valid_params is the set of param IDs considered valid to reference in
 * this plan node or its children.
 * scan_params is a set of param IDs to force scan plan nodes to reference.
 * This is for EvalPlanQual support, and is always NULL at the top of the
 * recursion.
 *
 * The return value is the computed allParam set for the given Plan node.
 * This is just an internal notational convenience.
 */
static Bitmapset *
finalize_plan(PlannerInfo *root, Plan *plan, Bitmapset *valid_params,
			  Bitmapset *scan_params)
{
	finalize_primnode_context context;
	int			locally_added_param;
	Bitmapset  *nestloop_params;
	Bitmapset  *child_params;

	if (plan == NULL)
		return NULL;

	context.root = root;
	context.paramids = NULL;	/* initialize set to empty */
	locally_added_param = -1;	/* there isn't one */
	nestloop_params = NULL;		/* there aren't any */

	/*
	 * When we call finalize_primnode, context.paramids sets are automatically
	 * merged together.  But when recursing to self, we have to do it the hard
	 * way.  We want the paramids set to include params in subplans as well as
	 * at this level.
	 */

	/* Find params in targetlist and qual */
	finalize_primnode((Node *) plan->targetlist, &context);
	finalize_primnode((Node *) plan->qual, &context);

	/* Check additional node-type-specific fields */
	switch (nodeTag(plan))
	{
		case T_Result:
			finalize_primnode(((Result *) plan)->resconstantqual,
							  &context);
			break;

		case T_SeqScan:
			context.paramids = bms_add_members(context.paramids, scan_params);
			break;

		case T_IndexScan:
			finalize_primnode((Node *) ((IndexScan *) plan)->indexqual,
							  &context);
			finalize_primnode((Node *) ((IndexScan *) plan)->indexorderby,
							  &context);

			/*
			 * we need not look at indexqualorig, since it will have the same
			 * param references as indexqual.  Likewise, we can ignore
			 * indexorderbyorig.
			 */
			context.paramids = bms_add_members(context.paramids, scan_params);
			break;

		case T_IndexOnlyScan:
			finalize_primnode((Node *) ((IndexOnlyScan *) plan)->indexqual,
							  &context);
			finalize_primnode((Node *) ((IndexOnlyScan *) plan)->indexorderby,
							  &context);

			/*
			 * we need not look at indextlist, since it cannot contain Params.
			 */
			context.paramids = bms_add_members(context.paramids, scan_params);
			break;

		case T_BitmapIndexScan:
			finalize_primnode((Node *) ((BitmapIndexScan *) plan)->indexqual,
							  &context);

			/*
			 * we need not look at indexqualorig, since it will have the same
			 * param references as indexqual.
			 */
			break;

		case T_BitmapHeapScan:
			finalize_primnode((Node *) ((BitmapHeapScan *) plan)->bitmapqualorig,
							  &context);
			context.paramids = bms_add_members(context.paramids, scan_params);
			break;

		case T_TidScan:
			finalize_primnode((Node *) ((TidScan *) plan)->tidquals,
							  &context);
			context.paramids = bms_add_members(context.paramids, scan_params);
			break;

		case T_SubqueryScan:

			/*
			 * In a SubqueryScan, SS_finalize_plan has already been run on the
			 * subplan by the inner invocation of subquery_planner, so there's
			 * no need to do it again.  Instead, just pull out the subplan's
			 * extParams list, which represents the params it needs from my
			 * level and higher levels.
			 */
			context.paramids = bms_add_members(context.paramids,
								 ((SubqueryScan *) plan)->subplan->extParam);
			/* We need scan_params too, though */
			context.paramids = bms_add_members(context.paramids, scan_params);
			break;

		case T_TableFunctionScan:
			{
				RangeTblEntry *rte;
				RangeTblFunction *rtfunc;

				rte = rt_fetch(((TableFunctionScan *) plan)->scan.scanrelid,
							   root->parse->rtable);
				Assert(rte->rtekind == RTE_TABLEFUNCTION);
				Assert(list_length(rte->functions) == 1);
				rtfunc = (RangeTblFunction *) linitial(rte->functions);
				finalize_primnode(rtfunc->funcexpr, &context);

				/*
				 * GPDB_94_MERGE_FIXME: should we do something about params in
				 * the function expressions, like for FunctionScan nodes below?
				 */
			}
			/* TableFunctionScan's lefttree is like SubqueryScan's subplan. */
			context.paramids = bms_add_members(context.paramids,
								 plan->lefttree->extParam);
			break;

		case T_FunctionScan:
			{
				FunctionScan *fscan = (FunctionScan *) plan;
				ListCell   *lc;

				/*
				 * Call finalize_primnode independently on each function
				 * expression, so that we can record which params are
				 * referenced in each, in order to decide which need
				 * re-evaluating during rescan.
				 */
				foreach(lc, fscan->functions)
				{
					RangeTblFunction *rtfunc = (RangeTblFunction *) lfirst(lc);
					finalize_primnode_context funccontext;

					funccontext = context;
					funccontext.paramids = NULL;

					finalize_primnode(rtfunc->funcexpr, &funccontext);

					/* remember results for execution */
					rtfunc->funcparams = funccontext.paramids;

					/* add the function's params to the overall set */
					context.paramids = bms_add_members(context.paramids,
													   funccontext.paramids);
				}

				context.paramids = bms_add_members(context.paramids,
												   scan_params);
			}
			break;

		case T_ValuesScan:
			finalize_primnode((Node *) ((ValuesScan *) plan)->values_lists,
							  &context);
			context.paramids = bms_add_members(context.paramids, scan_params);
			break;

		case T_CteScan:
			{
				/*
				 * You might think we should add the node's cteParam to
				 * paramids, but we shouldn't because that param is just a
				 * linkage mechanism for multiple CteScan nodes for the same
				 * CTE; it is never used for changed-param signaling.  What we
				 * have to do instead is to find the referenced CTE plan and
				 * incorporate its external paramids, so that the correct
				 * things will happen if the CTE references outer-level
				 * variables.  See test cases for bug #4902.
				 */
				int			plan_id = ((CteScan *) plan)->ctePlanId;
				Plan	   *cteplan;

				/* so, do this ... */
				if (plan_id < 1 || plan_id > list_length(root->glob->subplans))
					elog(ERROR, "could not find plan for CteScan referencing plan ID %d",
						 plan_id);
				cteplan = (Plan *) list_nth(root->glob->subplans, plan_id - 1);
				context.paramids =
					bms_add_members(context.paramids, cteplan->extParam);

#ifdef NOT_USED
				/* ... but not this */
				context.paramids =
					bms_add_member(context.paramids,
								   ((CteScan *) plan)->cteParam);
#endif

				context.paramids = bms_add_members(context.paramids,
												   scan_params);
			}
			break;

		case T_WorkTableScan:
			context.paramids =
				bms_add_member(context.paramids,
							   ((WorkTableScan *) plan)->wtParam);
			context.paramids = bms_add_members(context.paramids, scan_params);
			break;

		case T_ForeignScan:
			finalize_primnode((Node *) ((ForeignScan *) plan)->fdw_exprs,
							  &context);
			context.paramids = bms_add_members(context.paramids, scan_params);
			break;

		case T_ModifyTable:
			{
				ModifyTable *mtplan = (ModifyTable *) plan;
				ListCell   *l;

				/* Force descendant scan nodes to reference epqParam */
				locally_added_param = mtplan->epqParam;
				valid_params = bms_add_member(bms_copy(valid_params),
											  locally_added_param);
				scan_params = bms_add_member(bms_copy(scan_params),
											 locally_added_param);
				finalize_primnode((Node *) mtplan->returningLists,
								  &context);
				foreach(l, mtplan->plans)
				{
					context.paramids =
						bms_add_members(context.paramids,
										finalize_plan(root,
													  (Plan *) lfirst(l),
													  valid_params,
													  scan_params));
				}
			}
			break;

		case T_Append:
			{
				ListCell   *l;

				foreach(l, ((Append *) plan)->appendplans)
				{
					context.paramids =
						bms_add_members(context.paramids,
										finalize_plan(root,
													  (Plan *) lfirst(l),
													  valid_params,
													  scan_params));
				}
			}
			break;

		case T_MergeAppend:
			{
				ListCell   *l;

				foreach(l, ((MergeAppend *) plan)->mergeplans)
				{
					context.paramids =
						bms_add_members(context.paramids,
										finalize_plan(root,
													  (Plan *) lfirst(l),
													  valid_params,
													  scan_params));
				}
			}
			break;

		case T_BitmapAnd:
			{
				ListCell   *l;

				foreach(l, ((BitmapAnd *) plan)->bitmapplans)
				{
					context.paramids =
						bms_add_members(context.paramids,
										finalize_plan(root,
													  (Plan *) lfirst(l),
													  valid_params,
													  scan_params));
				}
			}
			break;

		case T_BitmapOr:
			{
				ListCell   *l;

				foreach(l, ((BitmapOr *) plan)->bitmapplans)
				{
					context.paramids =
						bms_add_members(context.paramids,
										finalize_plan(root,
													  (Plan *) lfirst(l),
													  valid_params,
													  scan_params));
				}
			}
			break;

		case T_NestLoop:
			{
				ListCell   *l;

				finalize_primnode((Node *) ((Join *) plan)->joinqual,
								  &context);
				/* collect set of params that will be passed to right child */
				foreach(l, ((NestLoop *) plan)->nestParams)
				{
					NestLoopParam *nlp = (NestLoopParam *) lfirst(l);

					nestloop_params = bms_add_member(nestloop_params,
													 nlp->paramno);
				}
			}
			break;

		case T_MergeJoin:
			finalize_primnode((Node *) ((Join *) plan)->joinqual,
							  &context);
			finalize_primnode((Node *) ((MergeJoin *) plan)->mergeclauses,
							  &context);
			break;

		case T_HashJoin:
			finalize_primnode((Node *) ((Join *) plan)->joinqual,
							  &context);
			finalize_primnode((Node *) ((HashJoin *) plan)->hashclauses,
							  &context);
			finalize_primnode((Node *) ((HashJoin *) plan)->hashqualclauses,
							  &context);
			break;

		case T_Motion:

			finalize_primnode((Node *) ((Motion *) plan)->hashExprs,
							  &context);
			break;

		case T_Limit:
			finalize_primnode(((Limit *) plan)->limitOffset,
							  &context);
			finalize_primnode(((Limit *) plan)->limitCount,
							  &context);
			break;

		case T_PartitionSelector:
			finalize_primnode((Node *) ((PartitionSelector *) plan)->levelEqExpressions,
							  &context);
			finalize_primnode((Node *) ((PartitionSelector *) plan)->levelExpressions,
							  &context);
			finalize_primnode(((PartitionSelector *) plan)->residualPredicate,
							  &context);
			finalize_primnode(((PartitionSelector *) plan)->propagationExpression,
							  &context);
			finalize_primnode(((PartitionSelector *) plan)->printablePredicate,
							  &context);
			finalize_primnode((Node *) ((PartitionSelector *) plan)->partTabTargetlist,
							  &context);
			break;

		case T_RecursiveUnion:
			/* child nodes are allowed to reference wtParam */
			locally_added_param = ((RecursiveUnion *) plan)->wtParam;
			valid_params = bms_add_member(bms_copy(valid_params),
										  locally_added_param);
			/* wtParam does *not* get added to scan_params */
			break;

		case T_LockRows:
			/* Force descendant scan nodes to reference epqParam */
			locally_added_param = ((LockRows *) plan)->epqParam;
			valid_params = bms_add_member(bms_copy(valid_params),
										  locally_added_param);
			scan_params = bms_add_member(bms_copy(scan_params),
										 locally_added_param);
			break;

		case T_Agg:
			{
				Agg		   *agg = (Agg *) plan;

				/*
				 * AGG_HASHED plans need to know which Params are referenced
				 * in aggregate calls.  Do a separate scan to identify them.
				 */
				if (agg->aggstrategy == AGG_HASHED)
				{
					finalize_primnode_context aggcontext;

					aggcontext.root = root;
					aggcontext.paramids = NULL;
					finalize_agg_primnode((Node *) agg->plan.targetlist,
										  &aggcontext);
					finalize_agg_primnode((Node *) agg->plan.qual,
										  &aggcontext);
					agg->aggParams = aggcontext.paramids;
				}
			}
			break;

		case T_WindowAgg:
			finalize_primnode(((WindowAgg *) plan)->startOffset,
							  &context);
			finalize_primnode(((WindowAgg *) plan)->endOffset,
							  &context);
			break;

		case T_Hash:
		case T_ExternalScan:
		case T_Material:
		case T_Sort:
		case T_ShareInputScan:
		case T_Unique:
		case T_SetOp:
		case T_Repeat:
		case T_SplitUpdate:
			break;

		default:
			elog(ERROR, "unrecognized node type: %d",
				 (int) nodeTag(plan));
	}

	/* Process left and right child plans, if any */
	/*
	 * In a TableFunctionScan, the 'lefttree' is more like a SubQueryScan's
	 * subplan, and contains a plan that's already been finalized by the
	 * inner invocation of subquery_planner(). So skip that.
	 */
	if (!IsA(plan, TableFunctionScan))
	{
		child_params = finalize_plan(root,
									 plan->lefttree,
									 valid_params,
									 scan_params);
		context.paramids = bms_add_members(context.paramids, child_params);
	}

	if (nestloop_params)
	{
		/* right child can reference nestloop_params as well as valid_params */
		child_params = finalize_plan(root,
									 plan->righttree,
									 bms_union(nestloop_params, valid_params),
									 scan_params);
		/* ... and they don't count as parameters used at my level */
		child_params = bms_difference(child_params, nestloop_params);
		bms_free(nestloop_params);
	}
	else
	{
		/* easy case */
		child_params = finalize_plan(root,
									 plan->righttree,
									 valid_params,
									 scan_params);
	}
	context.paramids = bms_add_members(context.paramids, child_params);

	/*
	 * Any locally generated parameter doesn't count towards its generating
	 * plan node's external dependencies.  (Note: if we changed valid_params
	 * and/or scan_params, we leak those bitmapsets; not worth the notational
	 * trouble to clean them up.)
	 */
	if (locally_added_param >= 0)
	{
		context.paramids = bms_del_member(context.paramids,
										  locally_added_param);
	}

	/* Now we have all the paramids */

	if (!bms_is_subset(context.paramids, valid_params))
		elog(ERROR, "plan should not reference subplan's variable");

	/*
	 * Note: by definition, extParam and allParam should have the same value
	 * in any plan node that doesn't have child initPlans.  We set them equal
	 * here, and later SS_finalize_plan will update them properly in node(s)
	 * that it attaches initPlans to.
	 *
	 * For speed at execution time, make sure extParam/allParam are actually
	 * NULL if they are empty sets.
	 */
	if (bms_is_empty(context.paramids))
	{
		plan->extParam = NULL;
		plan->allParam = NULL;
	}
	else
	{
		plan->extParam = context.paramids;
		plan->allParam = bms_copy(context.paramids);
	}

	return plan->allParam;
}

/*
 * finalize_primnode: add IDs of all PARAM_EXEC params appearing in the given
 * expression tree to the result set.
 */
static bool
finalize_primnode(Node *node, finalize_primnode_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Param))
	{
		if (((Param *) node)->paramkind == PARAM_EXEC)
		{
			int			paramid = ((Param *) node)->paramid;

			context->paramids = bms_add_member(context->paramids, paramid);
		}
		return false;			/* no more to do here */
	}
	if (IsA(node, SubPlan))
	{
		SubPlan    *subplan = (SubPlan *) node;
		Plan	   *plan = planner_subplan_get_plan(context->root, subplan);
		ListCell   *lc;
		Bitmapset  *subparamids;

		/* Recurse into the testexpr, but not into the Plan */
		finalize_primnode(subplan->testexpr, context);

		/*
		 * Remove any param IDs of output parameters of the subplan that were
		 * referenced in the testexpr.  These are not interesting for
		 * parameter change signaling since we always re-evaluate the subplan.
		 * Note that this wouldn't work too well if there might be uses of the
		 * same param IDs elsewhere in the plan, but that can't happen because
		 * generate_new_param never tries to merge params.
		 */
		foreach(lc, subplan->paramIds)
		{
			context->paramids = bms_del_member(context->paramids,
											   lfirst_int(lc));
		}

		/* Also examine args list */
		finalize_primnode((Node *) subplan->args, context);

		/*
		 * Add params needed by the subplan to paramids, but excluding those
		 * we will pass down to it.
		 */
		subparamids = bms_copy(plan->extParam);
		foreach(lc, subplan->parParam)
		{
			subparamids = bms_del_member(subparamids, lfirst_int(lc));
		}
		context->paramids = bms_join(context->paramids, subparamids);

		return false;			/* no more to do here */
	}
	return expression_tree_walker(node, finalize_primnode,
								  (void *) context);
}

/*
 * finalize_agg_primnode: find all Aggref nodes in the given expression tree,
 * and add IDs of all PARAM_EXEC params appearing within their aggregated
 * arguments to the result set.
 */
static bool
finalize_agg_primnode(Node *node, finalize_primnode_context *context)
{
	if (node == NULL)
		return false;
	if (IsA(node, Aggref))
	{
		Aggref	   *agg = (Aggref *) node;

		/* we should not consider the direct arguments, if any */
		finalize_primnode((Node *) agg->args, context);
		finalize_primnode((Node *) agg->aggfilter, context);
		return false;			/* there can't be any Aggrefs below here */
	}
	return expression_tree_walker(node, finalize_agg_primnode,
								  (void *) context);
}

/*
 * SS_make_initplan_from_plan - given a plan tree, make it an InitPlan
 *
 * The plan is expected to return a scalar value of the given type/collation.
 * We build an EXPR_SUBLINK SubPlan node and put it into the initplan
 * list for the current query level.  A Param that represents the initplan's
 * output is returned.
 *
 * We assume the plan hasn't been put through SS_finalize_plan.
 *
 * We treat root->init_plans like the old PlannerInitPlan global here.
 */
Param *
SS_make_initplan_from_plan(PlannerInfo *root, Plan *plan,
						   Oid resulttype, int32 resulttypmod,
						   Oid resultcollation, bool is_initplan_func_sublink)
{
	SubPlan    *node;
	Param	   *prm;

	/*
	 * We must run SS_finalize_plan(), since that's normally done before a
	 * subplan gets put into the initplan list.  Tell it not to attach any
	 * pre-existing initplans to this one, since they are siblings not
	 * children of this initplan.  (This is something else that could perhaps
	 * be cleaner if we did extParam/allParam processing in setrefs.c instead
	 * of here?  See notes for materialize_finished_plan.)
	 */

	/*
	 * Build extParam/allParam sets for plan nodes.
	 */
	SS_finalize_plan(root, plan, false);

	/*
	 * Add the subplan and its PlannerInfo to the global lists.
	 */
	root->glob->subplans = lappend(root->glob->subplans, plan);
	root->glob->subroots = lappend(root->glob->subroots, root);

	/*
	 * Create a SubPlan node and add it to the outer list of InitPlans. Note
	 * it has to appear after any other InitPlans it might depend on (see
	 * comments in ExecReScan).
	 */
	node = makeNode(SubPlan);
	if (is_initplan_func_sublink)
		node->subLinkType = INITPLAN_FUNC_SUBLINK;
	else
		node->subLinkType = EXPR_SUBLINK;
	get_first_col_type(plan, &node->firstColType, &node->firstColTypmod,
					   &node->firstColCollation);
    node->qDispSliceId = 0;             /*CDB*/
	node->plan_id = list_length(root->glob->subplans);
	node->is_initplan = true;
	root->init_plans = lappend(root->init_plans, node);

	/*
	 * The node can't have any inputs (since it's an initplan), so the
	 * parParam and args lists remain empty.
	 */

	/* NB PostgreSQL calculates subplan cost here, but GPDB does it elsewhere. */

	/*
	 * Make a Param that will be the subplan's output.
	 */
	prm = generate_new_param(root, resulttype, resulttypmod, resultcollation);
	node->setParam = list_make1_int(prm->paramid);

	/* Label the subplan for EXPLAIN purposes */
	node->plan_name = psprintf("InitPlan %d (returns $%d)",
							   node->plan_id, prm->paramid);

	return prm;
}

typedef struct check_dml_context
{
	PlannerInfo *cteroot;
	Index		m_query_level;	/* absolute query level */
}			check_dml_context;

/*
 * Returns true if any subquery of given Query has any non-SELECT commandType.
 */
static bool
cte_contains_dml_walker(Node *node, check_dml_context *ctx)
{
	if (node == NULL)
		return false;

	if (IsA(node, RangeTblEntry))
	{
		RangeTblEntry *rte = (RangeTblEntry *) node;

		/*
		 * Check if the rte is CTE, which has been defined at a higher query
		 * level than entry level of last subquery we called the walker with.
		 * In this case we would be able to iterate through cteList of higher
		 * level and analyze corresponding CTE.
		 *
		 * rte->ctelevelsup is equal to number of levels up from the level
		 * where rte is referenced to the level where its CTE is defined.
		 * Difference ctx->m_query_level - rte->ctelevelsup stands for
		 * absolute query level, where the CTE is defined. In case if this
		 * level is higher than absolute level of last subquery with
		 * initialized PlannerInfo (last CTE and its root, which the walker
		 * was last called with), we are able to derive the root. Based on its
		 * cteList it is possible to investigate the CTE. Otherwise, this CTE
		 * should have already been processed by query_tree_walker.
		 *
		 * For e.x. WITH cte1 AS (INSERT into...) SELECT * FROM (WITH cte2 as
		 * (SELECT * from cte1) SELECT * FROM (WITH cte3 as (SELECT * FROM
		 * cte2) SELECT * FROM cte3 a join cte3 b using (i)) foo) bar;
		 *
		 * Here cte3's subquery is an entry point for the walker with
		 * cteroot->query_level = 3. cte3 references the cte2, whose
		 * ctelevelsup is 2. It means that cte2 is defined at 2 levels up from
		 * the m_query_level = 4. This level is higher than level where cte3
		 * is defined, because cte3 is defined at level 3 and cte2 is at level
		 * 2. In this case we can derive parent root, whose cteList contains
		 * query of cte2.
		 */
		if (rte->rtekind == RTE_CTE &&
			rte->ctelevelsup < ctx->m_query_level &&
			(ctx->m_query_level - rte->ctelevelsup) <= ctx->cteroot->query_level)
		{
			ListCell	*lcn;
			PlannerInfo *cteroot = ctx->cteroot;
			Index		query_level = ctx->m_query_level;
			Index		levelsup = cteroot->query_level -
								   (query_level - rte->ctelevelsup);

			while (levelsup-- > 0)
			{
				ctx->cteroot = ctx->cteroot->parent_root;

				if (ctx->cteroot == NULL)
					return false;
			}

			ctx->m_query_level = ctx->cteroot->query_level;

			foreach(lcn, ctx->cteroot->parse->cteList)
			{
				CommonTableExpr *cte = (CommonTableExpr *) lfirst(lcn);

				/*
				 * Find the CTE corresponding to current rte. When CTE is
				 * recursive or is going to be shared, there is no need to
				 * continue the processing. If such rtes contain non-SELECT
				 * DML operations, which are possibly can be inlined, they
				 * will be processed separately when make_one_rel will reach
				 * them.
				 */
				if (strcmp(cte->ctename, rte->ctename) == 0 &&
					!cte->cterecursive &&
					cte_contains_dml_walker(cte->ctequery, ctx))
				{
					return true;
				}
			}

			ctx->cteroot = cteroot;
			ctx->m_query_level = query_level;
		}

		return false;			/* allow range_table_walker to continue */
	}

	if (IsA(node, Query))
	{
		Query	   *query = (Query *) node;
		bool		result;

		if (query->commandType != CMD_SELECT)
			return true;

		ctx->m_query_level++;
		result = query_tree_walker(query, cte_contains_dml_walker,
								   (void *) ctx, QTW_EXAMINE_RTES);
		ctx->m_query_level--;

		return result;
	}

	/*
	 * The only reason why we consider this node is that CTE might be defined
	 * but not referenced.
	 */
	if (IsA(node, CommonTableExpr))
	{
		CommonTableExpr *cte = (CommonTableExpr *) node;

		if (cte->cterefcount > 0 && !cte->cterecursive)
			return cte_contains_dml_walker(cte->ctequery, ctx);

		return false;
	}

	return expression_tree_walker(node, cte_contains_dml_walker,
								  (void *) ctx);
}

/*
 * Checks whether given CTE carries a non-SELECT operation inside.
 */
bool
cte_contains_dml(Node *ctequery, PlannerInfo *root)
{
	check_dml_context ctx;

	/*
	 * The root is related to the query level, where given CTE in defined,
	 * and, m_query_level in initialized with root->query_level - this level.
	 */
	ctx.cteroot = root;
	ctx.m_query_level = root->query_level;
	return cte_contains_dml_walker(ctequery, &ctx);
}
