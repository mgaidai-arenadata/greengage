/*-------------------------------------------------------------------------
 *
 * allpaths.c
 *	  Routines to find possible search paths for processing a query
 *
 * Portions Copyright (c) 2005-2008, Greenplum inc
 * Portions Copyright (c) 2012-Present Pivotal Software, Inc.
 * Portions Copyright (c) 1996-2014, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/path/allpaths.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include <math.h>

#include "catalog/catalog.h"
#include "catalog/pg_class.h"
#include "catalog/pg_operator.h"
#include "foreign/fdwapi.h"
#include "nodes/nodeFuncs.h"
#ifdef OPTIMIZER_DEBUG
#include "nodes/print.h"
#endif
#include "optimizer/clauses.h"
#include "optimizer/cost.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/plancat.h"
#include "optimizer/planmain.h"
#include "optimizer/planner.h"
#include "optimizer/prep.h"
#include "optimizer/restrictinfo.h"
#include "optimizer/var.h"
#include "optimizer/planshare.h"
#include "optimizer/subselect.h"
#include "parser/parse_clause.h"
#include "parser/parsetree.h"
#include "rewrite/rewriteManip.h"
#include "utils/guc.h"
#include "utils/lsyscache.h"
#include "utils/syscache.h"

#include "cdb/cdbmutate.h"		/* cdbmutate_warn_ctid_without_segid */
#include "cdb/cdbpath.h"		/* cdbpath_rows() */
#include "cdb/cdbsetop.h"

// TODO: these planner gucs need to be refactored into PlannerConfig.
bool		gp_enable_sort_limit = FALSE;
bool		gp_enable_sort_distinct = FALSE;

/* results of subquery_is_pushdown_safe */
typedef struct pushdown_safety_info
{
	bool	   *unsafeColumns;	/* which output columns are unsafe to use */
	bool		unsafeVolatile; /* don't push down volatile quals */
	bool		unsafeLeaky;	/* don't push down leaky quals */
} pushdown_safety_info;

/* Hook for plugins to replace standard_join_search() */
join_search_hook_type join_search_hook = NULL;


static void set_base_rel_consider_startup(PlannerInfo *root);
static void set_base_rel_sizes(PlannerInfo *root);
static void set_base_rel_pathlists(PlannerInfo *root);
static void set_rel_size(PlannerInfo *root, RelOptInfo *rel,
			 Index rti, RangeTblEntry *rte);
static void set_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
				 Index rti, RangeTblEntry *rte);
static void set_plain_rel_size(PlannerInfo *root, RelOptInfo *rel,
				   RangeTblEntry *rte);
static void set_plain_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
					   RangeTblEntry *rte);
static void set_foreign_size(PlannerInfo *root, RelOptInfo *rel,
				 RangeTblEntry *rte);
static void set_foreign_pathlist(PlannerInfo *root, RelOptInfo *rel,
					 RangeTblEntry *rte);
static void set_append_rel_size(PlannerInfo *root, RelOptInfo *rel,
					Index rti, RangeTblEntry *rte);
static void set_append_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
						Index rti, RangeTblEntry *rte);
static bool has_multiple_baserels(PlannerInfo *root);
static void generate_mergeappend_paths(PlannerInfo *root, RelOptInfo *rel,
						   List *live_childrels,
						   List *all_child_pathkeys);
static Path *get_cheapest_parameterized_child_path(PlannerInfo *root,
									  RelOptInfo *rel,
									  Relids required_outer);
static List *accumulate_append_subpath(List *subpaths, Path *path);
static void set_dummy_rel_pathlist(PlannerInfo *root, RelOptInfo *rel);
static void set_subquery_pathlist(PlannerInfo *root, RelOptInfo *rel,
					  Index rti, RangeTblEntry *rte);
static void set_function_pathlist(PlannerInfo *root, RelOptInfo *rel,
					  RangeTblEntry *rte);
static void set_tablefunction_pathlist(PlannerInfo *root, RelOptInfo *rel,
						   RangeTblEntry *rte);
static void set_values_pathlist(PlannerInfo *root, RelOptInfo *rel,
					RangeTblEntry *rte);
static void set_cte_pathlist(PlannerInfo *root, RelOptInfo *rel,
				 RangeTblEntry *rte);
static void set_worktable_pathlist(PlannerInfo *root, RelOptInfo *rel,
					   RangeTblEntry *rte);
static RelOptInfo *make_rel_from_joinlist(PlannerInfo *root, List *joinlist);
static Query *push_down_restrict(PlannerInfo *root, RelOptInfo *rel,
				   RangeTblEntry *rte, Index rti, Query *subquery);
static bool subquery_is_pushdown_safe(Query *subquery, Query *topquery,
						  pushdown_safety_info *safetyInfo);
static bool recurse_pushdown_safe(Node *setOp, Query *topquery,
					  pushdown_safety_info *safetyInfo);
static void check_output_expressions(Query *subquery,
						 pushdown_safety_info *safetyInfo);
static void compare_tlist_datatypes(List *tlist, List *colTypes,
						pushdown_safety_info *safetyInfo);
static bool targetIsInAllPartitionLists(TargetEntry *tle, Query *query);
static bool qual_is_pushdown_safe(Query *subquery, Index rti, Node *qual,
					  pushdown_safety_info *safetyInfo);
static void subquery_push_qual(Query *subquery,
				   RangeTblEntry *rte, Index rti, Node *qual);
static void recurse_push_qual(Node *setOp, Query *topquery,
				  RangeTblEntry *rte, Index rti, Node *qual);
static void bring_to_singleQE(PlannerInfo *root, RelOptInfo *rel,  List *outer_quals);
static bool check_query_for_possible_motion(Query *parse);
static void handle_gen_seggen_volatile_path(PlannerInfo *root, RelOptInfo *rel);

/*
 * make_one_rel
 *	  Finds all possible access paths for executing a query, returning a
 *	  single rel that represents the join of all base rels in the query.
 */
RelOptInfo *
make_one_rel(PlannerInfo *root, List *joinlist)
{
	RelOptInfo *rel;
	RelOptInfo *resultRel;
	Index		rti;

	/*
	 * Construct the all_baserels Relids set.
	 */
	root->all_baserels = NULL;
	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *brel = root->simple_rel_array[rti];

		/* there may be empty slots corresponding to non-baserel RTEs */
		if (brel == NULL)
			continue;

		Assert(brel->relid == rti);		/* sanity check on array */

		/* ignore RTEs that are "other rels" */
		if (brel->reloptkind != RELOPT_BASEREL)
			continue;

		root->all_baserels = bms_add_member(root->all_baserels, brel->relid);
	}

	/* Mark base rels as to whether we care about fast-start plans */
	set_base_rel_consider_startup(root);

	/*
	 * Generate access paths for the base rels.
	 */
	set_base_rel_sizes(root);

	/*
	 * If result relation is excluded by constraint exclusion we shouldn't
	 * plan this sub-query
	 */
	resultRel = root->simple_rel_array[root->parse->resultRelation];
	if (PointerIsValid(resultRel) && IS_DUMMY_REL(resultRel))
	{
		return resultRel;
	}

	set_base_rel_pathlists(root);

	/*
	 * Generate access paths for the entire join tree.
	 */
	rel = make_rel_from_joinlist(root, joinlist);

	/*
	 * The result should join all and only the query's base rels.
	 */
	Assert(bms_equal(rel->relids, root->all_baserels));

	return rel;
}

/*
 * set_base_rel_consider_startup
 *	  Set the consider_[param_]startup flags for each base-relation entry.
 *
 * For the moment, we only deal with consider_param_startup here; because the
 * logic for consider_startup is pretty trivial and is the same for every base
 * relation, we just let build_simple_rel() initialize that flag correctly to
 * start with.  If that logic ever gets more complicated it would probably
 * be better to move it here.
 */
static void
set_base_rel_consider_startup(PlannerInfo *root)
{
	/*
	 * Since parameterized paths can only be used on the inside of a nestloop
	 * join plan, there is usually little value in considering fast-start
	 * plans for them.  However, for relations that are on the RHS of a SEMI
	 * or ANTI join, a fast-start plan can be useful because we're only going
	 * to care about fetching one tuple anyway.
	 *
	 * To minimize growth of planning time, we currently restrict this to
	 * cases where the RHS is a single base relation, not a join; there is no
	 * provision for consider_param_startup to get set at all on joinrels.
	 * Also we don't worry about appendrels.  costsize.c's costing rules for
	 * nestloop semi/antijoins don't consider such cases either.
	 */
	ListCell   *lc;

	foreach(lc, root->join_info_list)
	{
		SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) lfirst(lc);

		if ((sjinfo->jointype == JOIN_SEMI || sjinfo->jointype == JOIN_ANTI) &&
			bms_membership(sjinfo->syn_righthand) == BMS_SINGLETON)
		{
			int			varno = bms_singleton_member(sjinfo->syn_righthand);
			RelOptInfo *rel = find_base_rel(root, varno);

			rel->consider_param_startup = true;
		}
	}
}

/*
 * set_base_rel_sizes
 *	  Set the size estimates (rows and widths) for each base-relation entry.
 *
 * We do this in a separate pass over the base rels so that rowcount
 * estimates are available for parameterized path generation.
 */
static void
set_base_rel_sizes(PlannerInfo *root)
{
	Index		rti;
	int			resultRelIndex = root->parse->resultRelation;
	RelOptInfo *resultRel;

	/*
	 * If result relation is excluded by constraint exclusion we shouldn't
	 * plan this sub-query. Result relation is set to zero for SELECT
	 * queries. simple_rel_array and simple_rte_array are filled by
	 * zeroes during allocation and never use zero-indexed item.
	 * So, SELECT queries bypass this logic safely.
	 */
	resultRel = root->simple_rel_array[resultRelIndex];
	if (resultRel != NULL && resultRel->reloptkind == RELOPT_BASEREL)
	{
		set_rel_size(root,
					 resultRel,
					 resultRelIndex,
					 root->simple_rte_array[resultRelIndex]);
		if (IS_DUMMY_REL(resultRel))
			return;
	}

	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *rel = root->simple_rel_array[rti];

		/* there may be empty slots corresponding to non-baserel RTEs */
		if (rel == NULL)
			continue;

		Assert(rel->relid == rti);		/* sanity check on array */

		/* ignore RTEs that are "other rels" */
		if (rel->reloptkind != RELOPT_BASEREL)
			continue;

		/* already analyzed before the loop */
		if (rti == resultRelIndex)
			continue;

		set_rel_size(root, rel, rti, root->simple_rte_array[rti]);
	}
}

/*
 * set_base_rel_pathlists
 *	  Finds all paths available for scanning each base-relation entry.
 *	  Sequential scan and any available indices are considered.
 *	  Each useful path is attached to its relation's 'pathlist' field.
 */
static void
set_base_rel_pathlists(PlannerInfo *root)
{
	Index		rti;

	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *rel = root->simple_rel_array[rti];

		/* there may be empty slots corresponding to non-baserel RTEs */
		if (rel == NULL)
			continue;

		Assert(rel->relid == rti);		/* sanity check on array */

		/* ignore RTEs that are "other rels" */
		if (rel->reloptkind != RELOPT_BASEREL)
			continue;

		/* CDB: Warn if ctid column is referenced but gp_segment_id is not. */
		cdbmutate_warn_ctid_without_segid(root, rel);

		set_rel_pathlist(root, rel, rti, root->simple_rte_array[rti]);
	}
}

/*
 * set_rel_size
 *	  Set size estimates for a base relation
 */
static void
set_rel_size(PlannerInfo *root, RelOptInfo *rel,
			 Index rti, RangeTblEntry *rte)
{
	if (rel->reloptkind == RELOPT_BASEREL &&
		relation_excluded_by_constraints(root, rel, rte))
	{
		/*
		 * We proved we don't need to scan the rel via constraint exclusion,
		 * so set up a single dummy path for it.  Here we only check this for
		 * regular baserels; if it's an otherrel, CE was already checked in
		 * set_append_rel_size().
		 *
		 * In this case, we go ahead and set up the relation's path right away
		 * instead of leaving it for set_rel_pathlist to do.  This is because
		 * we don't have a convention for marking a rel as dummy except by
		 * assigning a dummy path to it.
		 */
		set_dummy_rel_pathlist(root, rel);
	}
	else if (rte->inh)
	{
		/* It's an "append relation", process accordingly */
		set_append_rel_size(root, rel, rti, rte);
	}
	else
	{
		switch (rel->rtekind)
		{
			case RTE_RELATION:
				if (rte->relkind == RELKIND_FOREIGN_TABLE)
				{
					/* Foreign table */
					set_foreign_size(root, rel, rte);
				}
				else
				{
					/* Plain relation */
					set_plain_rel_size(root, rel, rte);
				}
				break;
			case RTE_SUBQUERY:

				/*
				 * Subqueries don't support making a choice between
				 * parameterized and unparameterized paths, so just go ahead
				 * and build their paths immediately.
				 */
				set_subquery_pathlist(root, rel, rti, rte);
				break;
			case RTE_FUNCTION:
				set_function_size_estimates(root, rel);
				break;
			case RTE_TABLEFUNCTION:
				set_tablefunction_pathlist(root, rel, rte);
				break;
			case RTE_VALUES:
				set_values_size_estimates(root, rel);
				break;
			case RTE_CTE:

				/*
				 * CTEs don't support making a choice between parameterized
				 * and unparameterized paths, so just go ahead and build their
				 * paths immediately.
				 */
				if (rte->self_reference)
					set_worktable_pathlist(root, rel, rte);
				else
					set_cte_pathlist(root, rel, rte);
				break;
			default:
				elog(ERROR, "unexpected rtekind: %d", (int) rel->rtekind);
				break;
		}
	}

	/*
	 * We insist that all non-dummy rels have a nonzero rowcount estimate.
	 */
	Assert(rel->rows > 0 || IS_DUMMY_REL(rel));
}

/*
 * Decorate the Paths of 'rel' with Motions to bring the relation's
 * result to SingleQE locus. The final plan will look something like
 * this:
 *
 *   Result (with quals from 'outer_quals')
 *           \
 *            \_Material
 *                   \
 *                    \_ Gather
 *                           \
 *                            \_SeqScan (with quals from 'baserestrictinfo')
 */
static void
bring_to_singleQE(PlannerInfo *root, RelOptInfo *rel, List *outer_quals)
{
	List	   *origpathlist;
	ListCell   *lc;

	origpathlist = rel->pathlist;
	rel->cheapest_startup_path = NULL;
	rel->cheapest_total_path = NULL;
	rel->cheapest_unique_path = NULL;
	rel->cheapest_parameterized_paths = NIL;
	rel->pathlist = NIL;

	foreach(lc, origpathlist)
	{
		Path	     *origpath = (Path *) lfirst(lc);
		Path	     *path;
		CdbPathLocus  target_locus;

		if (CdbPathLocus_IsGeneral(origpath->locus) ||
			CdbPathLocus_IsSingleQE(origpath->locus))
			path = origpath;
		else
		{
			/*
			 * Cannot pass a param through motion, so if this is a parameterized
			 * path, we can't use it.
			 */
			if (origpath->param_info)
				continue;

			/*
			 * param_info cannot cover the case that an index path's orderbyclauses
			 * See github issue: https://github.com/GreengageDB/greengage/issues/9733
			 */
			if (IsA(origpath, IndexPath))
			{
				IndexPath *ipath = (IndexPath *) origpath;
				if (contains_outer_params((Node *) ipath->indexorderbys,
										  (void *) root))
					continue;
			}

			CdbPathLocus_MakeSingleQE(&target_locus,
									  origpath->locus.numsegments);

			path = cdbpath_create_motion_path(root,
											  origpath,
											  NIL, // DESTROY pathkeys
											  false,
											  target_locus);
			if (!path)
				elog(ERROR, "Can't create valid motion for relation's path.");

			path = (Path *) create_material_path(root, rel, path);

			if (outer_quals)
				path = (Path *) create_projection_path_with_quals(root,
																  rel,
																  path,
																  outer_quals);
		}

		add_path(rel, path);
	}
	set_cheapest(rel);
}

/*
 * handle_gen_seggen_volatile_path
 *
 * Only use for base replicated rel.
 * Change the path in its pathlist if match the pattern
 * (segmentgeneral or general path contains volatile restrictions).
 */
static void
handle_gen_seggen_volatile_path(PlannerInfo *root, RelOptInfo *rel)
{
	List	   *origpathlist;
	ListCell   *lc;

	origpathlist = rel->pathlist;
	rel->cheapest_startup_path = NULL;
	rel->cheapest_total_path = NULL;
	rel->cheapest_unique_path = NULL;
	rel->cheapest_parameterized_paths = NIL;
	rel->pathlist = NIL;

	foreach(lc, origpathlist)
	{
		Path	     *origpath = (Path *) lfirst(lc);
		Path	     *path;

		path = turn_volatile_seggen_to_singleqe(root,
												origpath,
												(Node *) (rel->baserestrictinfo));
		add_path(rel, path);
	}

	set_cheapest(rel);
}

/*
 * set_rel_pathlist
 *	  Build access paths for a base relation
 */
static void
set_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
				 Index rti, RangeTblEntry *rte)
{
	if (IS_DUMMY_REL(rel))
	{
		/* We already proved the relation empty, so nothing more to do */
	}
	else if (rte->inh)
	{
		/* It's an "append relation", process accordingly */
		set_append_rel_pathlist(root, rel, rti, rte);
	}
	else
	{
		switch (rel->rtekind)
		{
			case RTE_RELATION:
				if (rte->relkind == RELKIND_FOREIGN_TABLE)
				{
					/* Foreign table */
					set_foreign_pathlist(root, rel, rte);
				}
				else
				{
					/* Plain relation */
					set_plain_rel_pathlist(root, rel, rte);
				}
				break;
			case RTE_SUBQUERY:
				/* Subquery --- fully handled during set_rel_size */
				break;
			case RTE_FUNCTION:
				/* RangeFunction */
				set_function_pathlist(root, rel, rte);
				break;
			case RTE_TABLEFUNCTION:
				/* RangeFunction --- generate a suitable path for it */
				break;
			case RTE_VALUES:
				/* Values list */
				set_values_pathlist(root, rel, rte);
				break;
			case RTE_CTE:
				/* CTE reference --- fully handled during set_rel_size */
				break;
			default:
				elog(ERROR, "unexpected rtekind: %d", (int) rel->rtekind);
				break;
		}
	}

	if (root->config->force_singleQE)
	{
		/*
		 * CDB: we cannot pass parameters across motion,
		 * if this is the inner plan of a lateral join and
		 * it contains limit clause, we will reach here.
		 * Planner will gather all the data into singleQE
		 * and materialize it.
		 */
		bring_to_singleQE(root, rel, rel->upperrestrictinfo);
	}

	/*
	 * Greengage specific behavior:
	 * Change the path in pathlist if it is a general or segmentgeneral
	 * path that contains volatile restrictions.
	 */
	if (rel->reloptkind == RELOPT_BASEREL)
		handle_gen_seggen_volatile_path(root, rel);

#ifdef OPTIMIZER_DEBUG
	debug_print_rel(root, rel);
#endif
}

/*
 * set_plain_rel_size
 *	  Set size estimates for a plain relation (no subquery, no inheritance)
 */
static void
set_plain_rel_size(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	/*
	 * Test any partial indexes of rel for applicability.  We must do this
	 * first since partial unique indexes can affect size estimates.
	 */
	check_partial_indexes(root, rel);

	/* Mark rel with estimated output rows, width, etc */
	set_baserel_size_estimates(root, rel);
}

/*
 * is_table_distributed
 *	  Is the table distributed?
 */
static bool
is_table_distributed(Oid relid)
{
	HeapTuple	gp_policy_tuple;

	gp_policy_tuple = SearchSysCache1(GPPOLICYID, ObjectIdGetDatum(relid));
	if (HeapTupleIsValid(gp_policy_tuple))
	{
		ReleaseSysCache(gp_policy_tuple);
		return true;
	}

	return false;
}

/*
 * maybe_rte_non_distributed
 *	  Is a range table entry non-distributed possibly?
 */
static bool
maybe_rte_non_distributed(List *rtable, Index rtindex)
{
	RangeTblEntry *rte;

	rte = rt_fetch(rtindex, rtable);

	if (rte->rtekind == RTE_RELATION)
		return !is_table_distributed(rte->relid);

	/*
	 * For other rte kind e.g. RTE_SUBQUERY or RTE_FUNCTION, we may
	 * not be able to know the locus of its path at this moment so
	 * set it as true.
	 */
	return true;
}

/*
 * maybe_param_non_distributed
 *	  Is a Param related to a non-distributed table possibly?
 */
static bool
maybe_param_non_distributed(PlannerInfo *root, Param *param)
{
	Index rtindex;

	for (root = root->parent_root; root != NULL; root = root->parent_root)
	{
		ListCell *ppl;

		foreach(ppl, root->plan_params)
		{
			PlannerParamItem *pitem = (PlannerParamItem *) lfirst(ppl);

			if (pitem->paramId == param->paramid)
			{
				if (IsA(pitem->item, Var))
				{
					Var *v = (Var *) pitem->item;
					rtindex = v->varno;

					return maybe_rte_non_distributed(root->parse->rtable, rtindex);
				}
				else if (IsA(pitem->item, PlaceHolderVar))
				{
					PlaceHolderVar *phv = (PlaceHolderVar *) pitem->item;
					rtindex = bms_singleton_member(phv->phrels);

					return maybe_rte_non_distributed(root->parse->rtable, rtindex);
				}
			}
		}
	}

	return false;
}

/*
 * maybe_contain_non_distributed_param_walker
 *	  Does a Param contain a non-distributed table possibly?
 */
static bool
maybe_contain_non_distributed_param_walker(Node *node, void *context)
{
	PlannerInfo *root =  (PlannerInfo *) context;

	if (node == NULL)
		return false;

	if (IsA(node, Param) && maybe_param_non_distributed(root, (Param *) node))
		return true;

	return expression_tree_walker(node, maybe_contain_non_distributed_param_walker, context);
}

/*
 * maybe_restrictclauses_include_non_distributed_param
 *	  Does a RestrictInfo list contain param with non distributed table possibly?
 */
static bool
maybe_restrictclauses_include_non_distributed_param(PlannerInfo *root, List *clauses)
{
	ListCell   *l;

	foreach(l, clauses)
	{
		RestrictInfo *c = (RestrictInfo *) lfirst(l);
		Node *expr;

		expr = (Node *) c->clause;

		if (maybe_contain_non_distributed_param_walker(expr, root))
			return true;
	}

	return false;
}

/*
 * plain_allow_indexpath_under_subplan
 *	  Determine whether create an index path for the RelOptInfo.
 *    TODO: below might have been too ambitious.
 */
static bool
plain_allow_indexpath_under_subplan(PlannerInfo *root, RelOptInfo *rel)
{

	if (!root->is_correlated_subplan)
		return true;

	if (GpPolicyIsPartitioned(rel->cdbpolicy))
		return false;

	if (GpPolicyIsReplicated(rel->cdbpolicy))
	{
		if (maybe_restrictclauses_include_non_distributed_param(root, rel->baserestrictinfo))
			return false;
		if (maybe_restrictclauses_include_non_distributed_param(root, rel->joininfo))
			return false;
	}

	return true;
}

/*
 * set_plain_rel_pathlist
 *	  Build access paths for a plain relation (no subquery, no inheritance)
 */
static void
set_plain_rel_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	Relids		required_outer;
	Path       *seqpath = NULL;

	/*
	 * We don't support pushing join clauses into the quals of a seqscan, but
	 * it could still have required parameterization due to LATERAL refs in
	 * its tlist.
	 */
	required_outer = rel->lateral_relids;

	/* Consider sequential scan */

	/*
	 * Generate paths and add them to the rel's pathlist.
	 *
	 * Note: add_path() will discard any paths that are dominated by another
	 * available path, keeping only those paths that are superior along at
	 * least one dimension of cost or sortedness.
	 */

	/* Consider sequential scan */
	switch (rel->relstorage)
	{
		case RELSTORAGE_EXTERNAL:

			/*
			 * If the relation is external, create an external path for it and
			 * select it (only external path is considered for an external
			 * base rel).
			 */
			add_path(rel, (Path *) create_external_path(root, rel, required_outer));
			set_cheapest(rel);
			return;

		case RELSTORAGE_AOROWS:
		case RELSTORAGE_AOCOLS:
		case RELSTORAGE_HEAP:
			seqpath = create_seqscan_path(root, rel, required_outer);
			break;

		default:

			/*
			 * Should not be feasible, usually indicates a failure to
			 * correctly apply rewrite rules.
			 */
			elog(ERROR, "plan contains range table with relstorage='%c'",
				 rel->relstorage);
			return;
	}

	if (plain_allow_indexpath_under_subplan(root, rel))
	{
		/* Consider index and bitmap scans */
		create_index_paths(root, rel);

		if (rel->relstorage == RELSTORAGE_HEAP)
			create_tidscan_paths(root, rel);
	}
	/* we can add the seqscan path now */
	add_path(rel, seqpath);

	/* Now find the cheapest of the paths for this rel */
	set_cheapest(rel);
}

/*
 * set_foreign_size
 *		Set size estimates for a foreign table RTE
 */
static void
set_foreign_size(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	/* Mark rel with estimated output rows, width, etc */
	set_foreign_size_estimates(root, rel);

	/* Let FDW adjust the size estimates, if it can */
	rel->fdwroutine->GetForeignRelSize(root, rel, rte->relid);

	/* ... but do not let it set the rows estimate to zero */
	rel->rows = clamp_row_est(rel->rows);
}

/*
 * set_foreign_pathlist
 *		Build access paths for a foreign table RTE
 */
static void
set_foreign_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	/* Call the FDW's GetForeignPaths function to generate path(s) */
	rel->fdwroutine->GetForeignPaths(root, rel, rte->relid);

	/* Select cheapest path */
	set_cheapest(rel);
}

/*
 * set_append_rel_size
 *	  Set size estimates for an "append relation"
 *
 * The passed-in rel and RTE represent the entire append relation.  The
 * relation's contents are computed by appending together the output of
 * the individual member relations.  Note that in the inheritance case,
 * the first member relation is actually the same table as is mentioned in
 * the parent RTE ... but it has a different RTE and RelOptInfo.  This is
 * a good thing because their outputs are not the same size.
 */
static void
set_append_rel_size(PlannerInfo *root, RelOptInfo *rel,
					Index rti, RangeTblEntry *rte)
{
	int			parentRTindex = rti;
	bool		has_live_children;
	double		parent_rows;
	double		parent_size;
	double	   *parent_attrsizes;
	int			nattrs;
	ListCell   *l;

	/* Mark rel with estimated output rows, width, etc */
	set_baserel_size_estimates(root, rel);

	/*
	 * Initialize to compute size estimates for whole append relation.
	 *
	 * We handle width estimates by weighting the widths of different child
	 * rels proportionally to their number of rows.  This is sensible because
	 * the use of width estimates is mainly to compute the total relation
	 * "footprint" if we have to sort or hash it.  To do this, we sum the
	 * total equivalent size (in "double" arithmetic) and then divide by the
	 * total rowcount estimate.  This is done separately for the total rel
	 * width and each attribute.
	 *
	 * Note: if you consider changing this logic, beware that child rels could
	 * have zero rows and/or width, if they were excluded by constraints.
	 */
	has_live_children = false;
	parent_rows = 0;
	parent_size = 0;
	nattrs = rel->max_attr - rel->min_attr + 1;
	parent_attrsizes = (double *) palloc0(nattrs * sizeof(double));

	foreach(l, root->append_rel_list)
	{
		AppendRelInfo *appinfo = (AppendRelInfo *) lfirst(l);
		int			childRTindex;
		RangeTblEntry *childRTE;
		RelOptInfo *childrel;
		List	   *childquals;
		Node	   *childqual;
		ListCell   *parentvars;
		ListCell   *childvars;
		ListCell   *targetListVars;

		/* append_rel_list contains all append rels; ignore others */
		if (appinfo->parent_relid != parentRTindex)
			continue;

		childRTindex = appinfo->child_relid;
		childRTE = root->simple_rte_array[childRTindex];

		/*
		 * The child rel's RelOptInfo was already created during
		 * add_base_rels_to_query.
		 */
		childrel = find_base_rel(root, childRTindex);
		Assert(childrel->reloptkind == RELOPT_OTHER_MEMBER_REL);

		/*
		 * We have to copy the parent's targetlist and quals to the child,
		 * with appropriate substitution of variables.  However, only the
		 * baserestrictinfo quals are needed before we can check for
		 * constraint exclusion; so do that first and then check to see if we
		 * can disregard this child.
		 *
		 * As of 8.4, the child rel's targetlist might contain non-Var
		 * expressions, which means that substitution into the quals could
		 * produce opportunities for const-simplification, and perhaps even
		 * pseudoconstant quals.  To deal with this, we strip the RestrictInfo
		 * nodes, do the substitution, do const-simplification, and then
		 * reconstitute the RestrictInfo layer.
		 */
		childquals = get_all_actual_clauses(rel->baserestrictinfo);
		childquals = (List *) adjust_appendrel_attrs(root,
													 (Node *) childquals,
													 appinfo);
		childqual = eval_const_expressions(root, (Node *)
										   make_ands_explicit(childquals));
		if (childqual && IsA(childqual, Const) &&
			(((Const *) childqual)->constisnull ||
			 !DatumGetBool(((Const *) childqual)->constvalue)))
		{
			/*
			 * Restriction reduces to constant FALSE or constant NULL after
			 * substitution, so this child need not be scanned.
			 */
			set_dummy_rel_pathlist(root, childrel);
			continue;
		}
		childquals = make_ands_implicit((Expr *) childqual);
		childquals = make_restrictinfos_from_actual_clauses(root,
															childquals);
		childrel->baserestrictinfo = childquals;

		if (relation_excluded_by_constraints(root, childrel, childRTE))
		{
			/*
			 * This child need not be scanned, so we can omit it from the
			 * appendrel.
			 */
			set_dummy_rel_pathlist(root, childrel);
			continue;
		}

		/*
		 * CE failed, so finish copying/modifying targetlist and join quals.
		 *
		 * Note: the resulting childrel->reltargetlist may contain arbitrary
		 * expressions, which otherwise would not occur in a reltargetlist.
		 * Code that might be looking at an appendrel child must cope with
		 * such.  (Normally, a reltargetlist would only include Vars and
		 * PlaceHolderVars.)
		 */
		childrel->joininfo = (List *)
			adjust_appendrel_attrs(root,
								   (Node *) rel->joininfo,
								   appinfo);
		childrel->reltargetlist = (List *)
			adjust_appendrel_attrs(root,
								   (Node *) rel->reltargetlist,
								   appinfo);

		/*
		 * Set a not-null value in childrel's attr_needed.
		 * cdbpath_dedup_fixup_append() checkes the length of reltargetlist
		 * and expects the length of append rel equal to the sub rel.
		 *
		 * GPDB_92_MERGE_FIXME: is childrel->attr_needed accurate?
		 */
		foreach (targetListVars, childrel->reltargetlist)
		{
			int attno;
			Var *v = (Var*)lfirst(targetListVars);

			if (!IsA(v, Var))
				continue;

			attno = v->varattno;
			if (attno <= FirstLowInvalidHeapAttributeNumber)
				continue;

			attno -= childrel->min_attr;
			if (childrel->attr_needed[attno] == NULL)
				childrel->attr_needed[attno] = bms_make_singleton(childrel->relid);
		}

		/*
		 * We have to make child entries in the EquivalenceClass data
		 * structures as well.  This is needed either if the parent
		 * participates in some eclass joins (because we will want to consider
		 * inner-indexscan joins on the individual children) or if the parent
		 * has useful pathkeys (because we should try to build MergeAppend
		 * paths that produce those sort orderings).
		 */
		if (rel->has_eclass_joins || has_useful_pathkeys(root, rel))
			add_child_rel_equivalences(root, appinfo, rel, childrel);
		childrel->has_eclass_joins = rel->has_eclass_joins;

		/*
		 * Note: we could compute appropriate attr_needed data for the child's
		 * variables, by transforming the parent's attr_needed through the
		 * translated_vars mapping.  However, currently there's no need
		 * because attr_needed is only examined for base relations not
		 * otherrels.  So we just leave the child's attr_needed empty.
		 */

		/*
		 * Compute the child's size.
		 */
		set_rel_size(root, childrel, childRTindex, childRTE);

		/*
		 * It is possible that constraint exclusion detected a contradiction
		 * within a child subquery, even though we didn't prove one above. If
		 * so, we can skip this child.
		 */
		if (IS_DUMMY_REL(childrel))
			continue;

		/* We have at least one live child. */
		has_live_children = true;

		/*
		 * Accumulate size information from each live child.
		 */
		Assert(childrel->rows > 0);

		parent_rows += childrel->rows;
		parent_size += childrel->width * childrel->rows;

		/*
		 * Accumulate per-column estimates too.  We need not do anything for
		 * PlaceHolderVars in the parent list.  If child expression isn't a
		 * Var, or we didn't record a width estimate for it, we have to fall
		 * back on a datatype-based estimate.
		 *
		 * By construction, child's reltargetlist is 1-to-1 with parent's.
		 */
		forboth(parentvars, rel->reltargetlist,
				childvars, childrel->reltargetlist)
		{
			Var		   *parentvar = (Var *) lfirst(parentvars);
			Node	   *childvar = (Node *) lfirst(childvars);

			if (IsA(parentvar, Var))
			{
				int			pndx = parentvar->varattno - rel->min_attr;
				int32		child_width = 0;

				if (IsA(childvar, Var) &&
					((Var *) childvar)->varno == childrel->relid)
				{
					int			cndx = ((Var *) childvar)->varattno - childrel->min_attr;

					child_width = childrel->attr_widths[cndx];
				}
				if (child_width <= 0)
					child_width = get_typavgwidth(exprType(childvar),
												  exprTypmod(childvar));
				Assert(child_width > 0);
				parent_attrsizes[pndx] += child_width * childrel->rows;
			}
		}
	}

	if (has_live_children)
	{
		/*
		 * Save the finished size estimates.
		 */
		int			i;

		Assert(parent_rows > 0);
		rel->rows = parent_rows;
		rel->width = rint(parent_size / parent_rows);
		for (i = 0; i < nattrs; i++)
			rel->attr_widths[i] = rint(parent_attrsizes[i] / parent_rows);

		/*
		 * Set "raw tuples" count equal to "rows" for the appendrel; needed
		 * because some places assume rel->tuples is valid for any baserel.
		 */
		rel->tuples = parent_rows;
	}
	else
	{
		/*
		 * All children were excluded by constraints, so mark the whole
		 * appendrel dummy.  We must do this in this phase so that the rel's
		 * dummy-ness is visible when we generate paths for other rels.
		 */
		set_dummy_rel_pathlist(root, rel);
	}

	pfree(parent_attrsizes);
}

/*
 * set_append_rel_pathlist
 *	  Build access paths for an "append relation"
 */
static void
set_append_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
						Index rti, RangeTblEntry *rte)
{
	int			parentRTindex = rti;
	List	   *live_childrels = NIL;
	List	   *subpaths = NIL;
	bool		subpaths_valid = true;
	List	   *all_child_pathkeys = NIL;
	List	   *all_child_outers = NIL;
	ListCell   *l;

	/*
	 * Generate access paths for each member relation, and remember the
	 * cheapest path for each one.  Also, identify all pathkeys (orderings)
	 * and parameterizations (required_outer sets) available for the member
	 * relations.
	 */
	foreach(l, root->append_rel_list)
	{
		AppendRelInfo *appinfo = (AppendRelInfo *) lfirst(l);
		int			childRTindex;
		RangeTblEntry *childRTE;
		RelOptInfo *childrel;
		ListCell   *lcp;

		/* append_rel_list contains all append rels; ignore others */
		if (appinfo->parent_relid != parentRTindex)
			continue;

		/* Re-locate the child RTE and RelOptInfo */
		childRTindex = appinfo->child_relid;
		childRTE = root->simple_rte_array[childRTindex];
		childrel = root->simple_rel_array[childRTindex];

		/*
		 * Compute the child's access paths.
		 */
		set_rel_pathlist(root, childrel, childRTindex, childRTE);

		/*
		 * If child is dummy, ignore it.
		 */
		if (IS_DUMMY_REL(childrel))
			continue;

		/*
		 * Child is live, so add it to the live_childrels list for use below.
		 */
		live_childrels = lappend(live_childrels, childrel);

		/*
		 * If child has an unparameterized cheapest-total path, add that to
		 * the unparameterized Append path we are constructing for the parent.
		 * If not, there's no workable unparameterized path.
		 */
		if (childrel->cheapest_total_path->param_info == NULL)
			subpaths = accumulate_append_subpath(subpaths,
											  childrel->cheapest_total_path);
		else
			subpaths_valid = false;

		/*
		 * Collect lists of all the available path orderings and
		 * parameterizations for all the children.  We use these as a
		 * heuristic to indicate which sort orderings and parameterizations we
		 * should build Append and MergeAppend paths for.
		 */
		foreach(lcp, childrel->pathlist)
		{
			Path	   *childpath = (Path *) lfirst(lcp);
			List	   *childkeys = childpath->pathkeys;
			Relids		childouter = PATH_REQ_OUTER(childpath);

			/* Unsorted paths don't contribute to pathkey list */
			if (childkeys != NIL)
			{
				ListCell   *lpk;
				bool		found = false;

				/* Have we already seen this ordering? */
				foreach(lpk, all_child_pathkeys)
				{
					List	   *existing_pathkeys = (List *) lfirst(lpk);

					if (compare_pathkeys(existing_pathkeys,
										 childkeys) == PATHKEYS_EQUAL)
					{
						found = true;
						break;
					}
				}
				if (!found)
				{
					/* No, so add it to all_child_pathkeys */
					all_child_pathkeys = lappend(all_child_pathkeys,
												 childkeys);
				}
			}

			/* Unparameterized paths don't contribute to param-set list */
			if (childouter)
			{
				ListCell   *lco;
				bool		found = false;

				/* Have we already seen this param set? */
				foreach(lco, all_child_outers)
				{
					Relids		existing_outers = (Relids) lfirst(lco);

					if (bms_equal(existing_outers, childouter))
					{
						found = true;
						break;
					}
				}
				if (!found)
				{
					/* No, so add it to all_child_outers */
					all_child_outers = lappend(all_child_outers,
											   childouter);
				}
			}
		}
	}

	/* CDB: Just one child (or none)?  Set flag if result is at most 1 row. */
	if (!subpaths)
		rel->onerow = true;
	else if (list_length(subpaths) == 1)
		rel->onerow = ((Path *) linitial(subpaths))->parent->onerow;

	/*
	 * If we found unparameterized paths for all children, build an unordered,
	 * unparameterized Append path for the rel.  (Note: this is correct even
	 * if we have zero or one live subpath due to constraint exclusion.)
	 */
	if (subpaths_valid)
		add_path(rel, (Path *) create_append_path(root, rel, subpaths, NULL));

	/*
	 * Also build unparameterized MergeAppend paths based on the collected
	 * list of child pathkeys.
	 */
	if (subpaths_valid)
		generate_mergeappend_paths(root, rel, live_childrels,
								   all_child_pathkeys);

	/*
	 * Build Append paths for each parameterization seen among the child rels.
	 * (This may look pretty expensive, but in most cases of practical
	 * interest, the child rels will expose mostly the same parameterizations,
	 * so that not that many cases actually get considered here.)
	 *
	 * The Append node itself cannot enforce quals, so all qual checking must
	 * be done in the child paths.  This means that to have a parameterized
	 * Append path, we must have the exact same parameterization for each
	 * child path; otherwise some children might be failing to check the
	 * moved-down quals.  To make them match up, we can try to increase the
	 * parameterization of lesser-parameterized paths.
	 */
	foreach(l, all_child_outers)
	{
		Relids		required_outer = (Relids) lfirst(l);
		ListCell   *lcr;

		/* Select the child paths for an Append with this parameterization */
		subpaths = NIL;
		subpaths_valid = true;
		foreach(lcr, live_childrels)
		{
			RelOptInfo *childrel = (RelOptInfo *) lfirst(lcr);
			Path	   *subpath;

			subpath = get_cheapest_parameterized_child_path(root,
															childrel,
															required_outer);
			if (subpath == NULL)
			{
				/* failed to make a suitable path for this child */
				subpaths_valid = false;
				break;
			}
			subpaths = accumulate_append_subpath(subpaths, subpath);
		}

		if (subpaths_valid)
			add_path(rel, (Path *)
					 create_append_path(root, rel, subpaths, required_outer));
	}

	/* Select cheapest paths */
	set_cheapest(rel);
}

/*
 * generate_mergeappend_paths
 *		Generate MergeAppend paths for an append relation
 *
 * Generate a path for each ordering (pathkey list) appearing in
 * all_child_pathkeys.
 *
 * We consider both cheapest-startup and cheapest-total cases, ie, for each
 * interesting ordering, collect all the cheapest startup subpaths and all the
 * cheapest total paths, and build a MergeAppend path for each case.
 *
 * We don't currently generate any parameterized MergeAppend paths.  While
 * it would not take much more code here to do so, it's very unclear that it
 * is worth the planning cycles to investigate such paths: there's little
 * use for an ordered path on the inside of a nestloop.  In fact, it's likely
 * that the current coding of add_path would reject such paths out of hand,
 * because add_path gives no credit for sort ordering of parameterized paths,
 * and a parameterized MergeAppend is going to be more expensive than the
 * corresponding parameterized Append path.  If we ever try harder to support
 * parameterized mergejoin plans, it might be worth adding support for
 * parameterized MergeAppends to feed such joins.  (See notes in
 * optimizer/README for why that might not ever happen, though.)
 */
static void
generate_mergeappend_paths(PlannerInfo *root, RelOptInfo *rel,
						   List *live_childrels,
						   List *all_child_pathkeys)
{
	ListCell   *lcp;

	foreach(lcp, all_child_pathkeys)
	{
		List	   *pathkeys = (List *) lfirst(lcp);
		List	   *startup_subpaths = NIL;
		List	   *total_subpaths = NIL;
		bool		startup_neq_total = false;
		ListCell   *lcr;

		/* Select the child paths for this ordering... */
		foreach(lcr, live_childrels)
		{
			RelOptInfo *childrel = (RelOptInfo *) lfirst(lcr);
			Path	   *cheapest_startup,
					   *cheapest_total;

			/* Locate the right paths, if they are available. */
			cheapest_startup =
				get_cheapest_path_for_pathkeys(childrel->pathlist,
											   pathkeys,
											   NULL,
											   STARTUP_COST);
			cheapest_total =
				get_cheapest_path_for_pathkeys(childrel->pathlist,
											   pathkeys,
											   NULL,
											   TOTAL_COST);

			/*
			 * If we can't find any paths with the right order just use the
			 * cheapest-total path; we'll have to sort it later.
			 */
			if (cheapest_startup == NULL || cheapest_total == NULL)
			{
				cheapest_startup = cheapest_total =
					childrel->cheapest_total_path;
				/* Assert we do have an unparameterized path for this child */
				Assert(cheapest_total->param_info == NULL);
			}

			/*
			 * Notice whether we actually have different paths for the
			 * "cheapest" and "total" cases; frequently there will be no point
			 * in two create_merge_append_path() calls.
			 */
			if (cheapest_startup != cheapest_total)
				startup_neq_total = true;

			startup_subpaths =
				accumulate_append_subpath(startup_subpaths, cheapest_startup);
			total_subpaths =
				accumulate_append_subpath(total_subpaths, cheapest_total);
		}

		/* ... and build the MergeAppend paths */
		add_path(rel, (Path *) create_merge_append_path(root,
														rel,
														startup_subpaths,
														pathkeys,
														NULL));
		if (startup_neq_total)
			add_path(rel, (Path *) create_merge_append_path(root,
															rel,
															total_subpaths,
															pathkeys,
															NULL));
	}
}

/*
 * get_cheapest_parameterized_child_path
 *		Get cheapest path for this relation that has exactly the requested
 *		parameterization.
 *
 * Returns NULL if unable to create such a path.
 */
static Path *
get_cheapest_parameterized_child_path(PlannerInfo *root, RelOptInfo *rel,
									  Relids required_outer)
{
	Path	   *cheapest;
	ListCell   *lc;

	/*
	 * Look up the cheapest existing path with no more than the needed
	 * parameterization.  If it has exactly the needed parameterization, we're
	 * done.
	 */
	cheapest = get_cheapest_path_for_pathkeys(rel->pathlist,
											  NIL,
											  required_outer,
											  TOTAL_COST);
	Assert(cheapest != NULL);
	if (bms_equal(PATH_REQ_OUTER(cheapest), required_outer))
		return cheapest;

	/*
	 * Otherwise, we can "reparameterize" an existing path to match the given
	 * parameterization, which effectively means pushing down additional
	 * joinquals to be checked within the path's scan.  However, some existing
	 * paths might check the available joinquals already while others don't;
	 * therefore, it's not clear which existing path will be cheapest after
	 * reparameterization.  We have to go through them all and find out.
	 */
	cheapest = NULL;
	foreach(lc, rel->pathlist)
	{
		Path	   *path = (Path *) lfirst(lc);

		/* Can't use it if it needs more than requested parameterization */
		if (!bms_is_subset(PATH_REQ_OUTER(path), required_outer))
			continue;

		/*
		 * Reparameterization can only increase the path's cost, so if it's
		 * already more expensive than the current cheapest, forget it.
		 */
		if (cheapest != NULL &&
			compare_path_costs(cheapest, path, TOTAL_COST) <= 0)
			continue;

		/* Reparameterize if needed, then recheck cost */
		if (!bms_equal(PATH_REQ_OUTER(path), required_outer))
		{
			path = reparameterize_path(root, path, required_outer, 1.0);
			if (path == NULL)
				continue;		/* failed to reparameterize this one */
			Assert(bms_equal(PATH_REQ_OUTER(path), required_outer));

			if (cheapest != NULL &&
				compare_path_costs(cheapest, path, TOTAL_COST) <= 0)
				continue;
		}

		/* We have a new best path */
		cheapest = path;
	}

	/* Return the best path, or NULL if we found no suitable candidate */
	return cheapest;
}

/*
 * accumulate_append_subpath
 *		Add a subpath to the list being built for an Append or MergeAppend
 *
 * It's possible that the child is itself an Append or MergeAppend path, in
 * which case we can "cut out the middleman" and just add its child paths to
 * our own list.  (We don't try to do this earlier because we need to apply
 * both levels of transformation to the quals.)
 *
 * Note that if we omit a child MergeAppend in this way, we are effectively
 * omitting a sort step, which seems fine: if the parent is to be an Append,
 * its result would be unsorted anyway, while if the parent is to be a
 * MergeAppend, there's no point in a separate sort on a child.
 */
static List *
accumulate_append_subpath(List *subpaths, Path *path)
{
	if (IsA(path, AppendPath))
	{
		AppendPath *apath = (AppendPath *) path;

		/* list_copy is important here to avoid sharing list substructure */
		return list_concat(subpaths, list_copy(apath->subpaths));
	}
	else if (IsA(path, MergeAppendPath))
	{
		MergeAppendPath *mpath = (MergeAppendPath *) path;

		/* list_copy is important here to avoid sharing list substructure */
		return list_concat(subpaths, list_copy(mpath->subpaths));
	}
	else
		return lappend(subpaths, path);
}

/*
 * set_dummy_rel_pathlist
 *	  Build a dummy path for a relation that's been excluded by constraints
 *
 * Rather than inventing a special "dummy" path type, we represent this as an
 * AppendPath with no members (see also IS_DUMMY_PATH/IS_DUMMY_REL macros).
 */
static void
set_dummy_rel_pathlist(PlannerInfo *root, RelOptInfo *rel)
{
	/* Set dummy size estimates --- we leave attr_widths[] as zeroes */
	rel->rows = 0;
	rel->width = 0;

	/* Discard any pre-existing paths; no further need for them */
	rel->pathlist = NIL;

	add_path(rel, (Path *) create_append_path(root, rel, NIL,
											  rel->lateral_relids));

	/* Select cheapest path (pretty easy in this case...) */
	set_cheapest(rel);
}

/* quick-and-dirty test to see if any joining is needed */
static bool
has_multiple_baserels(PlannerInfo *root)
{
	int			num_base_rels = 0;
	Index		rti;

	for (rti = 1; rti < root->simple_rel_array_size; rti++)
	{
		RelOptInfo *brel = root->simple_rel_array[rti];

		if (brel == NULL)
			continue;

		/* ignore RTEs that are "other rels" */
		if (brel->reloptkind == RELOPT_BASEREL)
			if (++num_base_rels > 1)
				return true;
	}
	return false;
}

/*
 * set_subquery_pathlist
 *		Build the (single) access path for a subquery RTE
 *
 * We don't currently support generating parameterized paths for subqueries
 * by pushing join clauses down into them; it seems too expensive to re-plan
 * the subquery multiple times to consider different alternatives.  So the
 * subquery will have exactly one path.  (The path will be parameterized
 * if the subquery contains LATERAL references, otherwise not.)  Since there's
 * no freedom of action here, there's no need for a separate set_subquery_size
 * phase: we just make the path right away.
 */
static void
set_subquery_pathlist(PlannerInfo *root, RelOptInfo *rel,
					  Index rti, RangeTblEntry *rte)
{
	Query	   *subquery = rte->subquery;
	Relids		required_outer;
	double		tuple_fraction;
	PlannerInfo *subroot;
	List	   *pathkeys;
	bool		forceDistRand;
	Path	   *subquery_path;
	PlannerConfig *config;

	/*
	 * Must copy the Query so that planning doesn't mess up the RTE contents
	 * (really really need to fix the planner to not scribble on its input,
	 * someday).
	 */
	subquery = copyObject(subquery);

	/*
	 * If it's a LATERAL subquery, it might contain some Vars of the current
	 * query level, requiring it to be treated as parameterized, even though
	 * we don't support pushing down join quals into subqueries.
	 */
	required_outer = rel->lateral_relids;


	forceDistRand = rte->forceDistRandom;

	/* CDB: Could be a preplanned subquery from window_planner. */
	if (rte->subquery_plan == NULL)
	{
		/*
		 * push down quals if possible. Note subquery might be
		 * different pointer from original one.
		 */
		subquery = push_down_restrict(root, rel, rte, rti, subquery);

		/*
		 * CDB: Does the subquery return at most one row?
		 */
		rel->onerow = false;

		/* Set-returning function in tlist could give any number of rows. */
		if (expression_returns_set((Node *)subquery->targetList))
		{}

		/* Always one row if aggregate function without GROUP BY. */
		else if (!subquery->groupClause &&
				 (subquery->hasAggs || subquery->havingQual))
			rel->onerow = true;

		/* LIMIT 1 or less? */
		else if (subquery->limitCount &&
				 IsA(subquery->limitCount, Const) &&
				 !((Const *) subquery->limitCount)->constisnull)
		{
			Const	   *cnst = (Const *) subquery->limitCount;

			if (cnst->consttype == INT8OID &&
				DatumGetInt64(cnst->constvalue) <= 1)
				rel->onerow = true;
		}

		/*
		 * We can safely pass the outer tuple_fraction down to the subquery if the
		 * outer level has no joining, aggregation, or sorting to do. Otherwise
		 * we'd better tell the subquery to plan for full retrieval. (XXX This
		 * could probably be made more intelligent ...)
		 */
		if (subquery->hasAggs ||
			subquery->groupClause ||
			subquery->havingQual ||
			subquery->distinctClause ||
			subquery->sortClause ||
			has_multiple_baserels(root))
			tuple_fraction = 0.0;	/* default case */
		else
			tuple_fraction = root->tuple_fraction;

		/* Generate the plan for the subquery */
		config = CopyPlannerConfig(root->config);
		config->honor_order_by = false;		/* partial order is enough */
		/*
		 * CDB: if this subquery is the inner plan of a lateral
		 * join and if it contains a limit or group by or some other clause
		 * from a bunch of conditions that can cause motion in the plan,
		 * we can only gather it to singleQE and materialize the data because we
		 * cannot pass params across motion.
		 * We also set is_under_subplan to disable other related optimizations.
		 */
		if ((!bms_is_empty(required_outer)) &&
			check_query_for_possible_motion(subquery))
		{
			config->force_singleQE = true;
			config->is_under_subplan = true;
		}

		rel->subplan = subquery_planner(root->glob, subquery,
									root,
									false, tuple_fraction,
									&subroot,
									config);
	}
	else
	{
		/* This is a preplanned sub-query RTE. */
		rel->subplan = rte->subquery_plan;
		subroot = root;
		/* XXX rel->onerow = ??? */
	}

	rel->subroot = subroot;

	/* Isolate the params needed by this specific subplan */
	rel->subplan_params = root->plan_params;
	root->plan_params = NIL;

	/*
	 * It's possible that constraint exclusion proved the subquery empty. If
	 * so, it's convenient to turn it back into a dummy path so that we will
	 * recognize appropriate optimizations at this query level.
	 */
	if (is_dummy_plan(rel->subplan))
	{
		set_dummy_rel_pathlist(root, rel);
		return;
	}

	/* Mark rel with estimated output rows, width, etc */
	set_subquery_size_estimates(root, rel);

	/* Convert subquery pathkeys to outer representation */
	pathkeys = convert_subquery_pathkeys(root, rel, subroot->query_pathkeys);

	/* Generate appropriate path */
	subquery_path = create_subqueryscan_path(root, rel, pathkeys, required_outer);

	if (forceDistRand)
		CdbPathLocus_MakeStrewn(&subquery_path->locus,
								CdbPathLocus_NumSegments(subquery_path->locus));

	add_path(rel, subquery_path);

	/* Select cheapest path (pretty easy in this case...) */
	set_cheapest(rel);
}

/*
 * set_function_pathlist
 *		Build the (single) access path for a function RTE
 */
static void
set_function_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	Relids		required_outer;
	List	   *pathkeys = NIL;

	/*
	 * We don't support pushing join clauses into the quals of a function
	 * scan, but it could still have required parameterization due to LATERAL
	 * refs in the function expression.
	 */
	required_outer = rel->lateral_relids;

	/*
	 * The result is considered unordered unless ORDINALITY was used, in which
	 * case it is ordered by the ordinal column (the last one).  See if we
	 * care, by checking for uses of that Var in equivalence classes.
	 */
	if (rte->funcordinality)
	{
		AttrNumber	ordattno = rel->max_attr;
		Var		   *var = NULL;
		ListCell   *lc;

		/*
		 * Is there a Var for it in reltargetlist?	If not, the query did not
		 * reference the ordinality column, or at least not in any way that
		 * would be interesting for sorting.
		 */
		foreach(lc, rel->reltargetlist)
		{
			Var		   *node = (Var *) lfirst(lc);

			/* checking varno/varlevelsup is just paranoia */
			if (IsA(node, Var) &&
				node->varattno == ordattno &&
				node->varno == rel->relid &&
				node->varlevelsup == 0)
			{
				var = node;
				break;
			}
		}

		/*
		 * Try to build pathkeys for this Var with int8 sorting.  We tell
		 * build_expression_pathkey not to build any new equivalence class; if
		 * the Var isn't already mentioned in some EC, it means that nothing
		 * cares about the ordering.
		 */
		if (var)
			pathkeys = build_expression_pathkey(root,
												(Expr *) var,
												NULL,	/* below outer joins */
												Int8LessOperator,
												rel->relids,
												false);
	}

	/* Generate appropriate path */
	add_path(rel, create_functionscan_path(root, rel, rte,
										   pathkeys, required_outer));

	/* Select cheapest path (pretty easy in this case...) */
	set_cheapest(rel);
}

/*
 * set_tablefunction_pathlist
 *		Build the (single) access path for a table function RTE
 */
static void
set_tablefunction_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	PlannerConfig *config;
	PlannerInfo *subroot = NULL;
	RangeTblFunction *rtfunc;
	FuncExpr   *fexpr;
	ListCell   *arg;
	Relids		required_outer;

	/* Cannot be a preplanned subquery from window_planner. */
	Assert(!rte->subquery_plan);

	Assert(list_length(rte->functions) == 1);
	rtfunc = (RangeTblFunction *) linitial(rte->functions);
	Assert(rtfunc->funcexpr && IsA(rtfunc->funcexpr, FuncExpr));
	fexpr= (FuncExpr *) rtfunc->funcexpr;

	/*
	 * We don't support pushing join clauses into the quals of a function
	 * scan, but it could still have required parameterization due to LATERAL
	 * refs in the function expression.
	 */
	required_outer = rel->lateral_relids;

	config = CopyPlannerConfig(root->config);
	config->honor_order_by = false;		/* partial order is enough */

	/* Plan input subquery */
	rel->subplan = subquery_planner(root->glob, rte->subquery, root,
									false,
									0.0, //tuple_fraction
									& subroot,
									config);
	rel->subroot = subroot;

	/*
	 * With the subquery planned we now need to clear the subquery from the
	 * TableValueExpr nodes, otherwise preprocess_expression will trip over
	 * it.
	 */
	foreach(arg, fexpr->args)
	{
		if (IsA(arg, TableValueExpr))
		{
			TableValueExpr *tve = (TableValueExpr *) arg;

			tve->subquery = NULL;
		}
	}

	/* Could the function return more than one row? */
	rel->onerow = !expression_returns_set((Node *) fexpr);

	/* Mark rel with estimated output rows, width, etc */
	set_table_function_size_estimates(root, rel);

	/* Generate appropriate path */
	add_path(rel, create_tablefunction_path(root, rel, rte,
											required_outer));

	/* Select cheapest path (pretty easy in this case...) */
	set_cheapest(rel);
}

/*
 * set_values_pathlist
 *		Build the (single) access path for a VALUES RTE
 */
static void
set_values_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	Relids		required_outer;

	/*
	 * We don't support pushing join clauses into the quals of a values scan,
	 * but it could still have required parameterization due to LATERAL refs
	 * in the values expressions.
	 */
	required_outer = rel->lateral_relids;

	/* CDB: Just one row? */
	rel->onerow = (rel->tuples <= 1 &&
				   !expression_returns_set((Node *) rte->values_lists));

	/* Generate appropriate path */
	add_path(rel, create_valuesscan_path(root, rel, rte, required_outer));

	/* Select cheapest path (pretty easy in this case...) */
	set_cheapest(rel);
}

/*
 * set_cte_pathlist
 *		Build the (single) access path for a non-self-reference CTE RTE
 *
 * There's no need for a separate set_cte_size phase, since we don't
 * support join-qual-parameterized paths for CTEs.
 */
static void
set_cte_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	PlannerInfo *cteroot;
	Index		levelsup;
	int			ndx;
	ListCell   *lc;
	int			planinfo_id;
	CommonTableExpr *cte = NULL;
	double		tuple_fraction = 0.0;
	CtePlanInfo *cteplaninfo;
	Plan	   *subplan = NULL;
	List	   *pathkeys = NULL;
	PlannerInfo *subroot = NULL;
	Relids		required_outer;

	/*
	 * Find the referenced CTE based on the given range table entry
	 */
	levelsup = rte->ctelevelsup;
	cteroot = root;
	while (levelsup-- > 0)
	{
		cteroot = cteroot->parent_root;
		if (!cteroot)			/* shouldn't happen */
			elog(ERROR, "bad levelsup for CTE \"%s\"", rte->ctename);
	}

	ndx = 0;
	foreach(lc, cteroot->parse->cteList)
	{
		cte = (CommonTableExpr *) lfirst(lc);

		if (strcmp(cte->ctename, rte->ctename) == 0)
			break;
		ndx++;
	}
	if (lc == NULL)				/* shouldn't happen */
		elog(ERROR, "could not find CTE \"%s\"", rte->ctename);

	Assert(IsA(cte->ctequery, Query));

	/*
	 * In PostgreSQL, we use the index to look up the plan ID in the
	 * cteroot->cte_plan_ids list. In GPDB, CTE plans work differently, and
	 * we look up the CtePlanInfo struct in the list_cteplaninfo instead.
	 */
	planinfo_id = ndx;

	/*
	 * Determine whether we need to generate a new subplan for this CTE.
	 *
	 * There are the following cases:
	 *   (1) If this subquery can be pulled up as an InitPlan, we will
	 *       generate a new subplan. In InitPlan case, the subplan can
	 *       not be shared with the main query or other InitPlans. We
	 *       do not store this subplan in cteplaninfo.
	 *   (2) If we never generate a subplan for this CTE, then we generate
	 *       one. If the reference count for this CTE is greater than 1
	 *       (excluding ones used in InitPlans), we create multiple subplans,
	 *       each of which has a SharedNode on top. We store these subplans
	 *       in cteplaninfo so that they can be used later.
	 */
	Assert(list_length(cteroot->list_cteplaninfo) > planinfo_id);
	cteplaninfo = list_nth(cteroot->list_cteplaninfo, planinfo_id);

	/*
	 * If there is exactly one reference to this CTE in the query, or plan
	 * sharing is disabled, create a new subplan for this CTE. It will
	 * become simple subquery scan.
	 *
	 * NOTE: The check for "exactly one reference" is a bit fuzzy. The
	 * references are counted in parse analysis phase, and it's possible
	 * that we duplicate a reference during query planning. So the check
	 * for number of references must be treated merely as a hint. If it
	 * turns out that there are in fact multiple references to the same
	 * CTE, even though we thought that there is only one, we might choose
	 * a sub-optimal plan because we missed the opportunity to share the
	 * subplan. That's acceptable for now.
	 *
	 * subquery tree will be modified if any qual is pushed down.
	 * There's risk that it'd be confusing if the tree is used
	 * later. At the moment InitPlan case uses the tree, but it
	 * is called earlier than this pass always, so we don't avoid it.
	 *
	 * Also, we might want to think extracting "common"
	 * qual expressions between multiple references, but
	 * so far we don't support it.
	 */
	if (!root->config->gp_cte_sharing || cte->cterefcount == 1)
	{
		/*
		 * If plan sharing is disabled, we avoid performing DML inside CTE for
		 * multi reference and recursive cases. Otherwise, it'll cause
		 * duplicated DML operations.
		 */
		if ((cte->cterefcount > 1 || cte->cterecursive) &&
			(((Query *) cte->ctequery)->commandType != CMD_SELECT ||
			cte_contains_dml(cte->ctequery, cteroot)))
		{
			elog(ERROR, "Too much references to non-SELECT CTE");
		}

		PlannerConfig *config = CopyPlannerConfig(root->config);

		/*
		 * Copy query node since subquery_planner may trash it, and we need it
		 * intact in case we need to create another plan for the CTE
		 */
		Query	   *subquery = (Query *) copyObject(cte->ctequery);

		/*
		 * Having multiple SharedScans can lead to deadlocks. For now,
		 * disallow sharing of ctes at lower levels.
		 */
		config->gp_cte_sharing = false;

		config->honor_order_by = false;

		/*
		 * Additionally to recursive CTE queries, don't try to push down quals
		 * to non-SELECT queries. There can be DML operation with RETURNING
		 * clause, and it's incorrect to push down upper quals to it.
		*/
		if (!cte->cterecursive && subquery->commandType == CMD_SELECT)
		{
			/*
			 * Adjust the subquery so that 'root', i.e. this subquery, is the
			 * parent of the CTE subquery, even though the CTE might've been
			 * higher up syntactically. This is because some of the quals that
			 * we push down might refer to relations between the current level
			 * and the CTE's syntactical level. Such relations are not visible
			 * at the CTE's syntactical level, and SS_finalize_plan() would
			 * throw an error on them.
			 */
			IncrementVarSublevelsUp((Node *) subquery, rte->ctelevelsup, 1);

			/*
			 * Push down quals, like we do in set_subquery_pathlist()
			 */
			subquery = push_down_restrict(root, rel, rte, rel->relid, subquery);

			subplan = subquery_planner(cteroot->glob, subquery, root,
									   cte->cterecursive,
									   tuple_fraction, &subroot, config);
		}
		else
		{
			subplan = subquery_planner(cteroot->glob, subquery, cteroot,
									   cte->cterecursive,
									   tuple_fraction, &subroot, config);
		}

		/*
		 * Do not store the subplan in cteplaninfo, since we will not share
		 * this plan.
		 */
	}
	else
	{
		/*
		 * If we haven't created a subplan for this CTE yet, do it now. This
		 * subplan will not be used by InitPlans, so that they can be shared
		 * if this CTE is referenced multiple times (excluding in InitPlans).
		 */
		if (cteplaninfo->subplan == NULL)
		{
			PlannerConfig *config = CopyPlannerConfig(root->config);

			/*
			 * Copy query node since subquery_planner may trash it and we need
			 * it intact in case we need to create another plan for the CTE
			 */
			Query	   *subquery = (Query *) copyObject(cte->ctequery);

			/*
			 * Having multiple SharedScans can lead to deadlocks. For now,
			 * disallow sharing of ctes at lower levels.
			 */
			config->gp_cte_sharing = false;

			config->honor_order_by = false;

			subplan = subquery_planner(cteroot->glob, subquery, cteroot, cte->cterecursive,
									   tuple_fraction, &subroot, config);

			/*
			 * Sharing General and SegmentGeneral subplan may lead to deadlock
			 * when executed with 1-gang and joined with N-gang.
			 */
			if (CdbPathLocus_IsGeneral(*subplan->flow) ||
				CdbPathLocus_IsSegmentGeneral(*subplan->flow))
			{
				cteplaninfo->subplan = subplan;
			}
			else
			{
				cteplaninfo->subplan = prepare_plan_for_sharing(cteroot, subplan);
			}

			cteplaninfo->subroot = subroot;
		}

		/*
		 * Create another ShareInputScan to reference the already-created
		 * subplan if not avoiding sharing for General and SegmentGeneral
		 * subplans.
		 */
		if (CdbPathLocus_IsGeneral(*cteplaninfo->subplan->flow) ||
			CdbPathLocus_IsSegmentGeneral(*cteplaninfo->subplan->flow))
		{
			/*
			 * If we are not sharing and subplan was created just now, use it.
			 * Otherwise, make a copy of it to avoid construction of DAG
			 * instead of a tree.
			 */
			if (subplan == NULL)
				subplan = (Plan *) copyObject(cteplaninfo->subplan);
		}
		else
		{
			subplan = share_prepared_plan(cteroot, cteplaninfo->subplan);
		}

		subroot = cteplaninfo->subroot;
	}

	pathkeys = subroot->query_pathkeys;

	rel->subplan = subplan;
	rel->subroot = subroot;

	/* Mark rel with estimated output rows, width, etc */
	set_cte_size_estimates(root, rel, rel->subplan);

	/* Convert subquery pathkeys to outer representation */
	pathkeys = convert_subquery_pathkeys(root, rel, pathkeys);

	/*
	 * We don't support pushing join clauses into the quals of a CTE scan, but
	 * it could still have required parameterization due to LATERAL refs in
	 * its tlist.
	 */
	required_outer = rel->lateral_relids;

	/* Generate appropriate path */
	add_path(rel, create_ctescan_path(root, rel, pathkeys,required_outer));

	/* Select cheapest path (pretty easy in this case...) */
	set_cheapest(rel);
}

/*
 * set_worktable_pathlist
 *		Build the (single) access path for a self-reference CTE RTE
 *
 * There's no need for a separate set_worktable_size phase, since we don't
 * support join-qual-parameterized paths for CTEs.
 */
static void
set_worktable_pathlist(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	Plan	   *cteplan;
	PlannerInfo *cteroot;
	Index		levelsup;
	Relids		required_outer;
	CdbLocusType ctelocus;

	/*
	 * We need to find the non-recursive term's plan, which is in the plan
	 * level that's processing the recursive UNION, which is one level *below*
	 * where the CTE comes from.
	 */
	levelsup = rte->ctelevelsup;
	if (levelsup == 0)			/* shouldn't happen */
		elog(ERROR, "bad levelsup for CTE \"%s\"", rte->ctename);
	levelsup--;
	cteroot = root;
	while (levelsup-- > 0)
	{
		cteroot = cteroot->parent_root;
		if (!cteroot)			/* shouldn't happen */
			elog(ERROR, "bad levelsup for CTE \"%s\"", rte->ctename);
	}
	cteplan = cteroot->non_recursive_plan;
	if (!cteplan)				/* shouldn't happen */
		elog(ERROR, "could not find plan for CTE \"%s\"", rte->ctename);

	/* Mark rel with estimated output rows, width, etc */
	set_cte_size_estimates(root, rel, cteplan);

	/*
	 * We don't support pushing join clauses into the quals of a worktable
	 * scan, but it could still have required parameterization due to LATERAL
	 * refs in its tlist.  (I'm not sure this is actually possible given the
	 * restrictions on recursive references, but it's easy enough to support.)
	 */
	required_outer = rel->lateral_relids;

	/*
	 * Between Recursive union plannode node and WorkTableScan plannode
	 * there must be no Motion nodes because the execution of WorkTableScan
	 * depends on the Recursive union's data structure.
	 *
	 * And the logic here is always use cteplan's locus as WTS's locus.
	 * Remember WTS path cannot be turned to replicated(means broadcast)
	 * when dealing with join. Most of the cases, it is OK. But for
	 * replicated table whose locus is CdbLocusType_SegmentGeneral,
	 * it can not be taken as everywhere, we will gather it to singleQE
	 * or redistribute it when joining.
	 *
	 * To avoid such case, if cteplan's locus is CdbLocusType_SegmentGeneral,
	 * we build WTS path using singlQE, and later in the function
	 * `set_recursive_union_flow` to add a gather on the top of cteplan.
	 */
	if (cteplan->flow->locustype == CdbLocusType_SegmentGeneral)
		ctelocus = CdbLocusType_SingleQE;
	else
		ctelocus = cteplan->flow->locustype;

	/* Generate appropriate path */
	add_path(rel, create_worktablescan_path(root, rel, ctelocus, required_outer));

	/* Select cheapest path (pretty easy in this case...) */
	set_cheapest(rel);
}

/*
 * make_rel_from_joinlist
 *	  Build access paths using a "joinlist" to guide the join path search.
 *
 * See comments for deconstruct_jointree() for definition of the joinlist
 * data structure.
 */
static RelOptInfo *
make_rel_from_joinlist(PlannerInfo *root, List *joinlist)
{
	int			levels_needed;
	List	   *initial_rels;
	ListCell   *jl;

	/*
	 * Count the number of child joinlist nodes.  This is the depth of the
	 * dynamic-programming algorithm we must employ to consider all ways of
	 * joining the child nodes.
	 */
	levels_needed = list_length(joinlist);

	if (levels_needed <= 0)
		return NULL;			/* nothing to do? */

	/*
	 * Construct a list of rels corresponding to the child joinlist nodes.
	 * This may contain both base rels and rels constructed according to
	 * sub-joinlists.
	 */
	initial_rels = NIL;
	foreach(jl, joinlist)
	{
		Node	   *jlnode = (Node *) lfirst(jl);
		RelOptInfo *thisrel;

		if (IsA(jlnode, RangeTblRef))
		{
			int			varno = ((RangeTblRef *) jlnode)->rtindex;

			thisrel = find_base_rel(root, varno);
		}
		else if (IsA(jlnode, List))
		{
			/* Recurse to handle subproblem */
			thisrel = make_rel_from_joinlist(root, (List *) jlnode);
		}
		else
		{
			elog(ERROR, "unrecognized joinlist node type: %d",
				 (int) nodeTag(jlnode));
			thisrel = NULL;		/* keep compiler quiet */
		}

		initial_rels = lappend(initial_rels, thisrel);
	}

	if (levels_needed == 1)
	{
		/*
		 * Single joinlist node, so we're done.
		 */
		return (RelOptInfo *) linitial(initial_rels);
	}
	else
	{
		/*
		 * Consider the different orders in which we could join the rels,
		 * using a plugin, GEQO, or the regular join search code.
		 *
		 * We put the initial_rels list into a PlannerInfo field because
		 * has_legal_joinclause() needs to look at it (ugly :-().
		 */
		root->initial_rels = initial_rels;

		if (join_search_hook)
			return (*join_search_hook) (root, levels_needed, initial_rels);
		else
			return standard_join_search(root, levels_needed, initial_rels);
	}
}

/*
 * standard_join_search
 *	  Find possible joinpaths for a query by successively finding ways
 *	  to join component relations into join relations.
 *
 * 'levels_needed' is the number of iterations needed, ie, the number of
 *		independent jointree items in the query.  This is > 1.
 *
 * 'initial_rels' is a list of RelOptInfo nodes for each independent
 *		jointree item.  These are the components to be joined together.
 *		Note that levels_needed == list_length(initial_rels).
 *
 * Returns the final level of join relations, i.e., the relation that is
 * the result of joining all the original relations together.
 * At least one implementation path must be provided for this relation and
 * all required sub-relations.
 *
 * To support loadable plugins that modify planner behavior by changing the
 * join searching algorithm, we provide a hook variable that lets a plugin
 * replace or supplement this function.  Any such hook must return the same
 * final join relation as the standard code would, but it might have a
 * different set of implementation paths attached, and only the sub-joinrels
 * needed for these paths need have been instantiated.
 *
 * Note to plugin authors: the functions invoked during standard_join_search()
 * modify root->join_rel_list and root->join_rel_hash.  If you want to do more
 * than one join-order search, you'll probably need to save and restore the
 * original states of those data structures.  See geqo_eval() for an example.
 */
RelOptInfo *
standard_join_search(PlannerInfo *root, int levels_needed, List *initial_rels)
{
	int			lev;
	RelOptInfo *rel;

	/*
	 * This function cannot be invoked recursively within any one planning
	 * problem, so join_rel_level[] can't be in use already.
	 */
	Assert(root->join_rel_level == NULL);

	/*
	 * We employ a simple "dynamic programming" algorithm: we first find all
	 * ways to build joins of two jointree items, then all ways to build joins
	 * of three items (from two-item joins and single items), then four-item
	 * joins, and so on until we have considered all ways to join all the
	 * items into one rel.
	 *
	 * root->join_rel_level[j] is a list of all the j-item rels.  Initially we
	 * set root->join_rel_level[1] to represent all the single-jointree-item
	 * relations.
	 */
	root->join_rel_level = (List **) palloc0((levels_needed + 1) * sizeof(List *));

	root->join_rel_level[1] = initial_rels;

	for (lev = 2; lev <= levels_needed; lev++)
	{
		ListCell   *lc;

		/*
		 * Determine all possible pairs of relations to be joined at this
		 * level, and build paths for making each one from every available
		 * pair of lower-level relations.
		 */
		join_search_one_level(root, lev);

		/*
		 * Do cleanup work on each just-processed rel.
		 */
		foreach(lc, root->join_rel_level[lev])
		{
			rel = (RelOptInfo *) lfirst(lc);

			/* Find and save the cheapest paths for this rel */
			set_cheapest(rel);

#ifdef OPTIMIZER_DEBUG
			debug_print_rel(root, rel);
#endif
		}
	}

	/*
	 * We should have a single rel at the final level.
	 */
	if (root->join_rel_level[levels_needed] == NIL)
		elog(ERROR, "failed to build any %d-way joins", levels_needed);
	Assert(list_length(root->join_rel_level[levels_needed]) == 1);

	rel = (RelOptInfo *) linitial(root->join_rel_level[levels_needed]);

	root->join_rel_level = NULL;

	return rel;
}

/*****************************************************************************
 *			PUSHING QUALS DOWN INTO SUBQUERIES
 *****************************************************************************/

/*
 * push_down_restrict
 *   push down restrictinfo to subquery if any.
 *
 * If there are any restriction clauses that have been attached to the
 * subquery relation, consider pushing them down to become WHERE or HAVING
 * quals of the subquery itself.  This transformation is useful because it
 * may allow us to generate a better plan for the subquery than evaluating
 * all the subquery output rows and then filtering them.
 *
 * There are several cases where we cannot push down clauses. Restrictions
 * involving the subquery are checked by subquery_is_pushdown_safe().
 * Restrictions on individual clauses are checked by
 * qual_is_pushdown_safe().  Also, we don't want to push down
 * pseudoconstant clauses; better to have the gating node above the
 * subquery.
 *
 * Non-pushed-down clauses will get evaluated as qpquals of the
 * SubqueryScan node.
 *
 * XXX Are there any cases where we want to make a policy decision not to
 * push down a pushable qual, because it'd result in a worse plan?
 */
static Query *
push_down_restrict(PlannerInfo *root, RelOptInfo *rel,
				   RangeTblEntry *rte, Index rti, Query *subquery)
{
	pushdown_safety_info safetyInfo;

	/* Nothing to do here if it doesn't have qual at all */
	if (rel->baserestrictinfo == NIL)
		return subquery;

	/*
	 * Zero out result area for subquery_is_pushdown_safe, so that it can set
	 * flags as needed while recursing.  In particular, we need a workspace
	 * for keeping track of unsafe-to-reference columns.  unsafeColumns[i]
	 * will be set TRUE if we find that output column i of the subquery is
	 * unsafe to use in a pushed-down qual.
	 */
	memset(&safetyInfo, 0, sizeof(safetyInfo));
	safetyInfo.unsafeColumns = (bool *)
		palloc0((list_length(subquery->targetList) + 1) * sizeof(bool));

	/*
	 * If the subquery has the "security_barrier" flag, it means the subquery
	 * originated from a view that must enforce row-level security.  Then we
	 * must not push down quals that contain leaky functions.  (Ideally this
	 * would be checked inside subquery_is_pushdown_safe, but since we don't
	 * currently pass the RTE to that function, we must do it here.)
	 */
	safetyInfo.unsafeLeaky = rte->security_barrier;

	if (subquery_is_pushdown_safe(subquery, subquery, &safetyInfo))
	{
		/* OK to consider pushing down individual quals */
		List	   *upperrestrictlist = NIL;
		ListCell   *l;

		foreach(l, rel->baserestrictinfo)
		{
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(l);
			Node	   *clause = (Node *) rinfo->clause;

			if (!rinfo->pseudoconstant &&
				qual_is_pushdown_safe(subquery, rti, clause, &safetyInfo))
			{
				/* Push it down */
				subquery_push_qual(subquery, rte, rti, clause);
			}
			else
			{
				/* Keep it in the upper query */
				upperrestrictlist = lappend(upperrestrictlist, rinfo);
			}
		}
		rel->baserestrictinfo = upperrestrictlist;
	}

	pfree(safetyInfo.unsafeColumns);

	return subquery;
}

/*
 * subquery_is_pushdown_safe - is a subquery safe for pushing down quals?
 *
 * subquery is the particular component query being checked.  topquery
 * is the top component of a set-operations tree (the same Query if no
 * set-op is involved).
 *
 * Conditions checked here:
 *
 * 1. If the subquery has a LIMIT clause, we must not push down any quals,
 * since that could change the set of rows returned.
 *
 * 2. If the subquery contains EXCEPT or EXCEPT ALL set ops we cannot push
 * quals into it, because that could change the results.
 *
 * 3. If the subquery uses DISTINCT, we cannot push volatile quals into it.
 * This is because upper-level quals should semantically be evaluated only
 * once per distinct row, not once per original row, and if the qual is
 * volatile then extra evaluations could change the results.  (This issue
 * does not apply to other forms of aggregation such as GROUP BY, because
 * when those are present we push into HAVING not WHERE, so that the quals
 * are still applied after aggregation.)
 *
 * 4. If the subquery contains window functions, we cannot push volatile quals
 * into it.  The issue here is a bit different from DISTINCT: a volatile qual
 * might succeed for some rows of a window partition and fail for others,
 * thereby changing the partition contents and thus the window functions'
 * results for rows that remain.
 *
 * 5. Do not push down quals if the subquery is a grouping extension
 * query, since this may change the meaning of the query.
 *
 * In addition, we make several checks on the subquery's output columns to see
 * if it is safe to reference them in pushed-down quals.  If output column k
 * is found to be unsafe to reference, we set safetyInfo->unsafeColumns[k]
 * to TRUE, but we don't reject the subquery overall since column k might not
 * be referenced by some/all quals.  The unsafeColumns[] array will be
 * consulted later by qual_is_pushdown_safe().  It's better to do it this way
 * than to make the checks directly in qual_is_pushdown_safe(), because when
 * the subquery involves set operations we have to check the output
 * expressions in each arm of the set op.
 *
 * Note: pushing quals into a DISTINCT subquery is theoretically dubious:
 * we're effectively assuming that the quals cannot distinguish values that
 * the DISTINCT's equality operator sees as equal, yet there are many
 * counterexamples to that assumption.  However use of such a qual with a
 * DISTINCT subquery would be unsafe anyway, since there's no guarantee which
 * "equal" value will be chosen as the output value by the DISTINCT operation.
 * So we don't worry too much about that.  Another objection is that if the
 * qual is expensive to evaluate, running it for each original row might cost
 * more than we save by eliminating rows before the DISTINCT step.  But it
 * would be very hard to estimate that at this stage, and in practice pushdown
 * seldom seems to make things worse, so we ignore that problem too.
 *
 * Note: likewise, pushing quals into a subquery with window functions is a
 * bit dubious: the quals might remove some rows of a window partition while
 * leaving others, causing changes in the window functions' results for the
 * surviving rows.  We insist that such a qual reference only partitioning
 * columns, but again that only protects us if the qual does not distinguish
 * values that the partitioning equality operator sees as equal.  The risks
 * here are perhaps larger than for DISTINCT, since no de-duplication of rows
 * occurs and thus there is no theoretical problem with such a qual.  But
 * we'll do this anyway because the potential performance benefits are very
 * large, and we've seen no field complaints about the longstanding comparable
 * behavior with DISTINCT.
 */
static bool
subquery_is_pushdown_safe(Query *subquery, Query *topquery,
						  pushdown_safety_info *safetyInfo)
{
	SetOperationStmt *topop;

	/* Check point 1 */
	if (subquery->limitOffset != NULL || subquery->limitCount != NULL)
		return false;

	/* Check points 3 and 4 */
	if (subquery->distinctClause || subquery->hasWindowFuncs)
		safetyInfo->unsafeVolatile = true;

	/* Check point 5 */
	if (subquery->groupClause != NULL &&
		contain_extended_grouping(subquery->groupClause))
		return false;

	/*
	 * If we're at a leaf query, check for unsafe expressions in its target
	 * list, and mark any unsafe ones in unsafeColumns[].  (Non-leaf nodes in
	 * setop trees have only simple Vars in their tlists, so no need to check
	 * them.)
	 */
	if (subquery->setOperations == NULL)
		check_output_expressions(subquery, safetyInfo);

	/* Are we at top level, or looking at a setop component? */
	if (subquery == topquery)
	{
		/* Top level, so check any component queries */
		if (subquery->setOperations != NULL)
			if (!recurse_pushdown_safe(subquery->setOperations, topquery,
									   safetyInfo))
				return false;
	}
	else
	{
		/* Setop component must not have more components (too weird) */
		if (subquery->setOperations != NULL)
			return false;
		/* Check whether setop component output types match top level */
		topop = (SetOperationStmt *) topquery->setOperations;
		Assert(topop && IsA(topop, SetOperationStmt));
		compare_tlist_datatypes(subquery->targetList,
								topop->colTypes,
								safetyInfo);
	}
	return true;
}

/*
 * Helper routine to recurse through setOperations tree
 */
static bool
recurse_pushdown_safe(Node *setOp, Query *topquery,
					  pushdown_safety_info *safetyInfo)
{
	if (IsA(setOp, RangeTblRef))
	{
		RangeTblRef *rtr = (RangeTblRef *) setOp;
		RangeTblEntry *rte = rt_fetch(rtr->rtindex, topquery->rtable);
		Query	   *subquery = rte->subquery;

		Assert(subquery != NULL);
		return subquery_is_pushdown_safe(subquery, topquery, safetyInfo);
	}
	else if (IsA(setOp, SetOperationStmt))
	{
		SetOperationStmt *op = (SetOperationStmt *) setOp;

		/* EXCEPT is no good (point 2 for subquery_is_pushdown_safe) */
		if (op->op == SETOP_EXCEPT)
			return false;
		/* Else recurse */
		if (!recurse_pushdown_safe(op->larg, topquery, safetyInfo))
			return false;
		if (!recurse_pushdown_safe(op->rarg, topquery, safetyInfo))
			return false;
	}
	else
	{
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(setOp));
	}
	return true;
}

/*
 * check_output_expressions - check subquery's output expressions for safety
 *
 * There are several cases in which it's unsafe to push down an upper-level
 * qual if it references a particular output column of a subquery.  We check
 * each output column of the subquery and set unsafeColumns[k] to TRUE if
 * that column is unsafe for a pushed-down qual to reference.  The conditions
 * checked here are:
 *
 * 1. We must not push down any quals that refer to subselect outputs that
 * return sets, else we'd introduce functions-returning-sets into the
 * subquery's WHERE/HAVING quals.
 *
 * 2. We must not push down any quals that refer to subselect outputs that
 * contain volatile functions, for fear of introducing strange results due
 * to multiple evaluation of a volatile function.
 *
 * 3. If the subquery uses DISTINCT ON, we must not push down any quals that
 * refer to non-DISTINCT output columns, because that could change the set
 * of rows returned.  (This condition is vacuous for DISTINCT, because then
 * there are no non-DISTINCT output columns, so we needn't check.  Note that
 * subquery_is_pushdown_safe already reported that we can't use volatile
 * quals if there's DISTINCT or DISTINCT ON.)
 *
 * 4. If the subquery has any window functions, we must not push down quals
 * that reference any output columns that are not listed in all the subquery's
 * window PARTITION BY clauses.  We can push down quals that use only
 * partitioning columns because they should succeed or fail identically for
 * every row of any one window partition, and totally excluding some
 * partitions will not change a window function's results for remaining
 * partitions.  (Again, this also requires nonvolatile quals, but
 * subquery_is_pushdown_safe handles that.)
 */
static void
check_output_expressions(Query *subquery, pushdown_safety_info *safetyInfo)
{
	ListCell   *lc;

	foreach(lc, subquery->targetList)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(lc);

		if (tle->resjunk)
			continue;			/* ignore resjunk columns */

		/* We need not check further if output col is already known unsafe */
		if (safetyInfo->unsafeColumns[tle->resno])
			continue;

		/* Functions returning sets are unsafe (point 1) */
		if (expression_returns_set((Node *) tle->expr))
		{
			safetyInfo->unsafeColumns[tle->resno] = true;
			continue;
		}

		/* Volatile functions are unsafe (point 2) */
		if (contain_volatile_functions((Node *) tle->expr))
		{
			safetyInfo->unsafeColumns[tle->resno] = true;
			continue;
		}

		/* If subquery uses DISTINCT ON, check point 3 */
		if (subquery->hasDistinctOn &&
			!targetIsInSortList(tle, InvalidOid, subquery->distinctClause))
		{
			/* non-DISTINCT column, so mark it unsafe */
			safetyInfo->unsafeColumns[tle->resno] = true;
			continue;
		}

		/* If subquery uses window functions, check point 4 */
		if (subquery->hasWindowFuncs &&
			!targetIsInAllPartitionLists(tle, subquery))
		{
			/* not present in all PARTITION BY clauses, so mark it unsafe */
			safetyInfo->unsafeColumns[tle->resno] = true;
			continue;
		}

		/* Refuse subplans */
		if (contain_subplans((Node *) tle->expr))
		{
			safetyInfo->unsafeColumns[tle->resno] = true;
			continue;
		}
	}
}

/*
 * For subqueries using UNION/UNION ALL/INTERSECT/INTERSECT ALL, we can
 * push quals into each component query, but the quals can only reference
 * subquery columns that suffer no type coercions in the set operation.
 * Otherwise there are possible semantic gotchas.  So, we check the
 * component queries to see if any of them have output types different from
 * the top-level setop outputs.  unsafeColumns[k] is set true if column k
 * has different type in any component.
 *
 * We don't have to care about typmods here: the only allowed difference
 * between set-op input and output typmods is input is a specific typmod
 * and output is -1, and that does not require a coercion.
 *
 * tlist is a subquery tlist.
 * colTypes is an OID list of the top-level setop's output column types.
 * safetyInfo->unsafeColumns[] is the result array.
 */
static void
compare_tlist_datatypes(List *tlist, List *colTypes,
						pushdown_safety_info *safetyInfo)
{
	ListCell   *l;
	ListCell   *colType = list_head(colTypes);

	foreach(l, tlist)
	{
		TargetEntry *tle = (TargetEntry *) lfirst(l);

		if (tle->resjunk)
			continue;			/* ignore resjunk columns */
		if (colType == NULL)
			elog(ERROR, "wrong number of tlist entries");
		if (exprType((Node *) tle->expr) != lfirst_oid(colType))
			safetyInfo->unsafeColumns[tle->resno] = true;
		colType = lnext(colType);
	}
	if (colType != NULL)
		elog(ERROR, "wrong number of tlist entries");
}

/*
 * targetIsInAllPartitionLists
 *		True if the TargetEntry is listed in the PARTITION BY clause
 *		of every window defined in the query.
 *
 * It would be safe to ignore windows not actually used by any window
 * function, but it's not easy to get that info at this stage; and it's
 * unlikely to be useful to spend any extra cycles getting it, since
 * unreferenced window definitions are probably infrequent in practice.
 */
static bool
targetIsInAllPartitionLists(TargetEntry *tle, Query *query)
{
	ListCell   *lc;

	foreach(lc, query->windowClause)
	{
		WindowClause *wc = (WindowClause *) lfirst(lc);

		if (!targetIsInSortList(tle, InvalidOid, wc->partitionClause))
			return false;
	}
	return true;
}

/*
 * qual_is_pushdown_safe - is a particular qual safe to push down?
 *
 * qual is a restriction clause applying to the given subquery (whose RTE
 * has index rti in the parent query).
 *
 * Conditions checked here:
 *
 * 1. The qual must not contain any subselects (mainly because I'm not sure
 * it will work correctly: sublinks will already have been transformed into
 * subplans in the qual, but not in the subquery).
 *
 * 2. If unsafeVolatile is set, the qual must not contain any volatile
 * functions.
 *
 * 3. If unsafeLeaky is set, the qual must not contain any leaky functions.
 *
 * 4. The qual must not refer to the whole-row output of the subquery
 * (since there is no easy way to name that within the subquery itself).
 *
 * 5. The qual must not refer to any subquery output columns that were
 * found to be unsafe to reference by subquery_is_pushdown_safe().
 */
static bool
qual_is_pushdown_safe(Query *subquery, Index rti, Node *qual,
					  pushdown_safety_info *safetyInfo)
{
	bool		safe = true;
	List	   *vars;
	ListCell   *vl;

	/* Refuse subselects (point 1) */
	if (contain_subplans(qual))
		return false;

	/* Refuse volatile quals if we found they'd be unsafe (point 2) */
	if (safetyInfo->unsafeVolatile &&
		contain_volatile_functions(qual))
		return false;

	/* Refuse leaky quals if told to (point 3) */
	if (safetyInfo->unsafeLeaky &&
		contain_leaky_functions(qual))
		return false;

	/*
	 * It would be unsafe to push down window function calls, but at least for
	 * the moment we could never see any in a qual anyhow.  (The same applies
	 * to aggregates, which we check for in pull_var_clause below.)
	 */
	Assert(!contain_window_function(qual));

	/*
	 * Examine all Vars used in clause; since it's a restriction clause, all
	 * such Vars must refer to subselect output columns.
	 */
	vars = pull_var_clause(qual,
						   PVC_REJECT_AGGREGATES,
						   PVC_INCLUDE_PLACEHOLDERS);
	foreach(vl, vars)
	{
		Var		   *var = (Var *) lfirst(vl);

		/*
		 * XXX Punt if we find any PlaceHolderVars in the restriction clause.
		 * It's not clear whether a PHV could safely be pushed down, and even
		 * less clear whether such a situation could arise in any cases of
		 * practical interest anyway.  So for the moment, just refuse to push
		 * down.
		 */
		if (!IsA(var, Var))
		{
			safe = false;
			break;
		}

		Assert(var->varno == rti);
		Assert(var->varattno >= 0);

		/* Check point 4 */
		if (var->varattno == 0)
		{
			safe = false;
			break;
		}

		/* Check point 5 */
		if (safetyInfo->unsafeColumns[var->varattno])
		{
			safe = false;
			break;
		}
	}

	list_free(vars);

	return safe;
}

/*
 * subquery_push_qual - push down a qual that we have determined is safe
 */
static void
subquery_push_qual(Query *subquery, RangeTblEntry *rte, Index rti, Node *qual)
{
	if (subquery->setOperations != NULL)
	{
		/* Recurse to push it separately to each component query */
		recurse_push_qual(subquery->setOperations, subquery,
						  rte, rti, qual);
	}
	else
	{
		/*
		 * We need to replace Vars in the qual (which must refer to outputs of
		 * the subquery) with copies of the subquery's targetlist expressions.
		 * Note that at this point, any uplevel Vars in the qual should have
		 * been replaced with Params, so they need no work.
		 *
		 * This step also ensures that when we are pushing into a setop tree,
		 * each component query gets its own copy of the qual.
		 */
		qual = ReplaceVarsFromTargetList(qual, rti, 0, rte,
										 subquery->targetList,
										 REPLACEVARS_REPORT_ERROR, 0,
										 &subquery->hasSubLinks);

		/*
		 * Now attach the qual to the proper place: normally WHERE, but if the
		 * subquery uses grouping or aggregation, put it in HAVING (since the
		 * qual really refers to the group-result rows).
		 */
		if (subquery->hasAggs || subquery->groupClause || subquery->havingQual)
			subquery->havingQual = make_and_qual(subquery->havingQual, qual);
		else
			subquery->jointree->quals =
				make_and_qual(subquery->jointree->quals, qual);

		/*
		 * We need not change the subquery's hasAggs or hasSublinks flags,
		 * since we can't be pushing down any aggregates that weren't there
		 * before, and we don't push down subselects at all.
		 */
	}
}

/*
 * Helper routine to recurse through setOperations tree
 */
static void
recurse_push_qual(Node *setOp, Query *topquery,
				  RangeTblEntry *rte, Index rti, Node *qual)
{
	if (IsA(setOp, RangeTblRef))
	{
		RangeTblRef *rtr = (RangeTblRef *) setOp;
		RangeTblEntry *subrte = rt_fetch(rtr->rtindex, topquery->rtable);
		Query	   *subquery = subrte->subquery;

		Assert(subquery != NULL);
		subquery_push_qual(subquery, rte, rti, qual);
	}
	else if (IsA(setOp, SetOperationStmt))
	{
		SetOperationStmt *op = (SetOperationStmt *) setOp;

		recurse_push_qual(op->larg, topquery, rte, rti, qual);
		recurse_push_qual(op->rarg, topquery, rte, rti, qual);
	}
	else
	{
		elog(ERROR, "unrecognized node type: %d",
			 (int) nodeTag(setOp));
	}
}

static bool
check_query_for_possible_motion(Query *parse)
{
	ListCell   *lc;

	// LIMIT, DISTINCT, GROUP BY, aggregate functions or recursive CTEs
	// can cause motions in a plan, so return true if they are presented
	if (parse->limitCount || parse->limitOffset ||
		parse->groupClause || parse->distinctClause ||
		parse->hasAggs || parse->hasRecursive)
		return true;

	// INTERSECT, EXCEPT or UNION without ALL set operations also can
	// cause motions in a plan, so return true for them as well
	if (parse->setOperations)
	{
		SetOperationStmt *stmt = (SetOperationStmt *) parse->setOperations;

		if (!stmt->all ||
			stmt->op == SETOP_INTERSECT ||
			stmt->op == SETOP_EXCEPT)
			return true;
	}

	foreach(lc, parse->cteList)
	{
		CommonTableExpr *cte = (CommonTableExpr *) lfirst(lc);

		if (check_query_for_possible_motion((Query *) cte->ctequery))
			return true;
	}

	foreach(lc, parse->rtable)
	{
		RangeTblEntry *rte = (RangeTblEntry *) lfirst(lc);

		if (rte->rtekind == RTE_SUBQUERY &&
			check_query_for_possible_motion(rte->subquery))
			return true;
	}

	return false;
}

/*****************************************************************************
 *			DEBUG SUPPORT
 *****************************************************************************/

#ifdef OPTIMIZER_DEBUG

static void
print_relids(Relids relids)
{
	Relids		tmprelids;
	int			x;
	bool		first = true;

	tmprelids = bms_copy(relids);
	while ((x = bms_first_member(tmprelids)) >= 0)
	{
		if (!first)
			printf(" ");
		printf("%d", x);
		first = false;
	}
	bms_free(tmprelids);
}

static void
print_restrictclauses(PlannerInfo *root, List *clauses)
{
	ListCell   *l;

	foreach(l, clauses)
	{
		RestrictInfo *c = lfirst(l);

		print_expr((Node *) c->clause, root->parse->rtable);
		if (lnext(l))
			printf(", ");
	}
}

static void
print_path(PlannerInfo *root, Path *path, int indent)
{
	const char *ptype;
	const char *ltype;
	bool		join = false;
	Path	   *subpath = NULL;
	int			i;

	switch (nodeTag(path))
	{
		case T_Path:
			ptype = "SeqScan";
			break;
		case T_IndexPath:
			ptype = "IdxScan";
			break;
		case T_BitmapHeapPath:
			ptype = "BitmapHeapScan";
			break;
		case T_BitmapAndPath:
			ptype = "BitmapAndPath";
			break;
		case T_BitmapOrPath:
			ptype = "BitmapOrPath";
			break;
		case T_TidPath:
			ptype = "TidScan";
			break;
		case T_ForeignPath:
			ptype = "ForeignScan";
			break;
		case T_AppendPath:
			ptype = "Append";
			break;
		case T_MergeAppendPath:
			ptype = "MergeAppend";
			break;
		case T_ResultPath:
			ptype = "Result";
			break;
		case T_MaterialPath:
			ptype = "Material";
			subpath = ((MaterialPath *) path)->subpath;
			break;
		case T_UniquePath:
			ptype = "Unique";
			subpath = ((UniquePath *) path)->subpath;
			break;
		case T_NestPath:
			ptype = "NestLoop";
			join = true;
			break;
		case T_MergePath:
			ptype = "MergeJoin";
			join = true;
			break;
		case T_HashPath:
			ptype = "HashJoin";
			join = true;
			break;
		case T_CdbMotionPath:
			ptype = "Motion";
			subpath = ((CdbMotionPath *) path)->subpath;
			break;
		default:
			ptype = "???Path";
			break;
	}

	for (i = 0; i < indent; i++)
		printf("\t");
	printf("%s", ptype);

	if (path->parent)
	{
		printf("(");
		print_relids(path->parent->relids);
		printf(") rows=%.0f", path->parent->rows);
	}

	switch (path->locus.locustype)
	{
		case CdbLocusType_Entry:
			ltype = "Entry";
			break;
		case CdbLocusType_SingleQE:
			ltype = "SingleQE";
			break;
		case CdbLocusType_General:
			ltype = "General";
			break;
		case CdbLocusType_SegmentGeneral:
			ltype = "SegmentGeneral";
			break;
		case CdbLocusType_Replicated:
			ltype = "Replicated";
			break;
		case CdbLocusType_Hashed:
			ltype = "Hashed";
			break;
		case CdbLocusType_HashedOJ:
			ltype = "HashedOJ";
			break;
		case CdbLocusType_Strewn:
			ltype = "Strewn";
			break;
		default:
			ltype = "???CdbLocus";
			break;
	}
	printf(" locus=%s", ltype);
	printf(" cost=%.2f..%.2f\n", path->startup_cost, path->total_cost);

	if (path->pathkeys)
	{
		for (i = 0; i < indent; i++)
			printf("\t");
		printf("  pathkeys: ");
		print_pathkeys(path->pathkeys, root->parse->rtable);
	}

	if (join)
	{
		JoinPath   *jp = (JoinPath *) path;

		for (i = 0; i < indent; i++)
			printf("\t");
		printf("  clauses: ");
		print_restrictclauses(root, jp->joinrestrictinfo);
		printf("\n");

		if (IsA(path, MergePath))
		{
			MergePath  *mp = (MergePath *) path;

			for (i = 0; i < indent; i++)
				printf("\t");
			printf("  sortouter=%d sortinner=%d materializeinner=%d\n",
				   ((mp->outersortkeys) ? 1 : 0),
				   ((mp->innersortkeys) ? 1 : 0),
				   ((mp->materialize_inner) ? 1 : 0));
		}

		print_path(root, jp->outerjoinpath, indent + 1);
		print_path(root, jp->innerjoinpath, indent + 1);
	}

	if (subpath)
		print_path(root, subpath, indent + 1);
}

void
debug_print_rel(PlannerInfo *root, RelOptInfo *rel)
{
	ListCell   *l;

	printf("RELOPTINFO (");
	print_relids(rel->relids);
	printf("): rows=%.0f width=%d\n", rel->rows, rel->width);

	if (rel->baserestrictinfo)
	{
		printf("\tbaserestrictinfo: ");
		print_restrictclauses(root, rel->baserestrictinfo);
		printf("\n");
	}

	if (rel->joininfo)
	{
		printf("\tjoininfo: ");
		print_restrictclauses(root, rel->joininfo);
		printf("\n");
	}

	printf("\tpath list:\n");
	foreach(l, rel->pathlist)
		print_path(root, lfirst(l), 1);
	if (rel->cheapest_startup_path)
	{
		printf("\n\tcheapest startup path:\n");
		print_path(root, rel->cheapest_startup_path, 1);
	}
	if (rel->cheapest_total_path)
	{
		printf("\n\tcheapest total path:\n");
		print_path(root, rel->cheapest_total_path, 1);
	}
	printf("\n");
	fflush(stdout);
}

#endif   /* OPTIMIZER_DEBUG */
