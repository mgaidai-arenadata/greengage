/*-------------------------------------------------------------------------
 *
 * parsenodes.h
 *	  definitions for parse tree nodes
 *
 * Many of the node types used in parsetrees include a "location" field.
 * This is a byte (not character) offset in the original source text, to be
 * used for positioning an error cursor when there is an error related to
 * the node.  Access to the original source text is needed to make use of
 * the location.
 *
 *
 * Portions Copyright (c) 2006-2009, Greenplum inc
 * Portions Copyright (c) 2012-Present Pivotal Software, Inc.
 * Portions Copyright (c) 1996-2014, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/include/nodes/parsenodes.h
 *
 *-------------------------------------------------------------------------
 */
#ifndef PARSENODES_H
#define PARSENODES_H

#include "nodes/bitmapset.h"
#include "nodes/primnodes.h"
#include "nodes/value.h"
#include "catalog/gp_policy.h"

typedef struct PartitionNode PartitionNode; /* see relation.h */

/* Possible sources of a Query */
typedef enum QuerySource
{
	QSRC_ORIGINAL,				/* original parsetree (explicit query) */
	QSRC_PARSER,				/* added by parse analysis (now unused) */
	QSRC_INSTEAD_RULE,			/* added by unconditional INSTEAD rule */
	QSRC_QUAL_INSTEAD_RULE,		/* added by conditional INSTEAD rule */
	QSRC_NON_INSTEAD_RULE,		/* added by non-INSTEAD rule */
	QSRC_PLANNER				/* added in planner by splicing parse tree */
} QuerySource;

/* Sort ordering options for ORDER BY and CREATE INDEX */
typedef enum SortByDir
{
	SORTBY_DEFAULT,
	SORTBY_ASC,
	SORTBY_DESC,
	SORTBY_USING				/* not allowed in CREATE INDEX ... */
} SortByDir;

typedef enum SortByNulls
{
	SORTBY_NULLS_DEFAULT,
	SORTBY_NULLS_FIRST,
	SORTBY_NULLS_LAST
} SortByNulls;

/*
 * Grantable rights are encoded so that we can OR them together in a bitmask.
 * The present representation of AclItem limits us to 16 distinct rights,
 * even though AclMode is defined as uint32.  See utils/acl.h.
 *
 * Caution: changing these codes breaks stored ACLs, hence forces initdb.
 */
typedef uint32 AclMode;			/* a bitmask of privilege bits */

#define ACL_INSERT		(1<<0)	/* for relations */
#define ACL_SELECT		(1<<1)
#define ACL_UPDATE		(1<<2)
#define ACL_DELETE		(1<<3)
#define ACL_TRUNCATE	(1<<4)
#define ACL_REFERENCES	(1<<5)
#define ACL_TRIGGER		(1<<6)
#define ACL_EXECUTE		(1<<7)	/* for functions */
#define ACL_USAGE		(1<<8)	/* for languages, namespaces, FDWs, and
								 * servers */
#define ACL_CREATE		(1<<9)	/* for namespaces and databases */
#define ACL_CREATE_TEMP (1<<10) /* for databases */
#define ACL_CONNECT		(1<<11) /* for databases */
#define N_ACL_RIGHTS	12		/* 1 plus the last 1<<x */
#define ACL_NO_RIGHTS	0
/* Currently, SELECT ... FOR [KEY] UPDATE/SHARE requires UPDATE privileges */
#define ACL_SELECT_FOR_UPDATE	ACL_UPDATE


/*****************************************************************************
 *	Query Tree
 *****************************************************************************/

/*
 * ParentStmtType represents whether the query is included in
 * a utility stmt. And it indicates the type of this utility stmt.
 * PARENTSTMTTYPE_NONE		query is not included in a utility stmt.
 * PARENTSTMTTYPE_CTAS		query is included in a CreateTableAsStmt.
 * PARENTSTMTTYPE_COPY		query is included in a CopyStmt.
 * PARENTSTMTTYPE_REFRESH_MATVIEW		query is included in a RefreshMatviewStmt.
 *
 * Previously we added the isCtas field to Query to indicate that
 * the query is included in CreateTableAsStmt. For this type of
 * query, you need to make a different MPP plan. The copy statement
 * also contains the query, which also requires a different query
 * plan.
 * In postgres, we don't need to make a different query plan for the
 * query in the utility stament. But in greengage, we need to. So we
 * use a field to indicate whether the query is contained in utitily
 * statemnt, and the type of utitily statemnt.
 */

typedef uint8 ParentStmtType;

#define PARENTSTMTTYPE_NONE	0
#define PARENTSTMTTYPE_CTAS	1
#define PARENTSTMTTYPE_COPY	2
#define PARENTSTMTTYPE_REFRESH_MATVIEW	3

/*
 * Query -
 *	  Parse analysis turns all statements into a Query tree
 *	  for further processing by the rewriter and planner.
 *
 *	  Utility statements (i.e. non-optimizable statements) have the
 *	  utilityStmt field set, and the Query itself is mostly dummy.
 *	  DECLARE CURSOR is a special case: it is represented like a SELECT,
 *	  but the original DeclareCursorStmt is stored in utilityStmt.
 *
 *	  Planning converts a Query tree into a Plan tree headed by a PlannedStmt
 *	  node --- the Query structure is not used by the executor.
 */
typedef struct Query
{
	NodeTag		type;

	CmdType		commandType;	/* select|insert|update|delete|utility */

	QuerySource querySource;	/* where did I come from? */

	uint32		queryId;		/* query identifier (can be set by plugins) */

	bool		canSetTag;		/* do I set the command result tag? */

	Node	   *utilityStmt;	/* non-null if this is DECLARE CURSOR or a
								 * non-optimizable statement */

	int			resultRelation; /* rtable index of target relation for
								 * INSERT/UPDATE/DELETE; 0 for SELECT */

	bool		hasAggs;		/* has aggregates in tlist or havingQual */
	bool		hasWindowFuncs; /* has window functions in tlist */
	bool		hasSubLinks;	/* has subquery SubLink */
	bool        hasDynamicFunctions; /* has functions with unstable return types */
	bool		hasFuncsWithExecRestrictions; /* has functions with EXECUTE ON MASTER or ALL SEGMENTS */
	bool		hasDistinctOn;	/* distinctClause is from DISTINCT ON */
	bool		hasRecursive;	/* WITH RECURSIVE was specified */
	bool		hasModifyingCTE;	/* has INSERT/UPDATE/DELETE in WITH */
	bool		hasForUpdate;	/* FOR [KEY] UPDATE/SHARE was specified */

	List	   *cteList;		/* WITH list (of CommonTableExpr's) */

	List	   *rtable;			/* list of range table entries */
	FromExpr   *jointree;		/* table join tree (FROM and WHERE clauses) */

	List	   *targetList;		/* target list (of TargetEntry) */

	List	   *withCheckOptions;		/* a list of WithCheckOption's */

	List	   *returningList;	/* return-values list (of TargetEntry) */

	/*
	 * A list of GroupClauses or GroupingClauses.  The order of GroupClauses
	 * or GroupingClauses are based on input queries. However, in each
	 * grouping set, all GroupClauses will appear in front of GroupingClauses.
	 * See the following GROUP BY clause:
	 *
	 * GROUP BY ROLLUP(b,c),a, CUBE(e,d)
	 *
	 * the result list can be roughly represented as follows.
	 *
	 * GroupClause(a) --> GroupingClause( ROLLUP, groupsets (GroupClause(b)
	 * --> GroupClause(c) ) ) --> GroupingClause( CUBE, groupsets
	 * (GroupClause(e) --> GroupClause(d) ) )
	 */
	List	   *groupClause;	/* a list of SortGroupClause's */

	Node	   *havingQual;		/* qualifications applied to groups */

	List	   *windowClause;	/* defined window specifications */

	List	   *distinctClause; /* a list of SortGroupClause's */

	List	   *sortClause;		/* a list of SortGroupClause's */

	List	   *scatterClause;	/* a list of tle's */
	bool		isTableValueSelect; /* GPDB: Is this a TABLE (...) subquery argument? */

	Node	   *limitOffset;	/* # of result tuples to skip (int8 expr) */
	Node	   *limitCount;		/* # of result tuples to return (int8 expr) */

	List	   *rowMarks;		/* a list of RowMarkClause's */

	Node	   *setOperations;	/* set-operation tree if this is top level of
								 * a UNION/INTERSECT/EXCEPT query */
	List	   *constraintDeps; /* a list of pg_constraint OIDs that the query
								 * depends on to be semantically valid */

	/*
	 * MPP: Used only on QD. Don't serialize. Holds the result distribution
	 * policy for SELECT ... INTO, CTAS, CTAE and set operations.
	 */
	struct GpPolicy *intoPolicy;

	/*
	 * GPDB: Used to indicate this query is part of CTAS or COPY so that its plan
	 * would always be dispatched in parallel.
	 */
	ParentStmtType	parentStmtType;
	bool		expandMatViews; /* force expansion of materialized views during rewrite to treat as views */
} Query;

/****************************************************************************
 *	Supporting data structures for Parse Trees
 *
 *	Most of these node types appear in raw parsetrees output by the grammar,
 *	and get transformed to something else by the analyzer.  A few of them
 *	are used as-is in transformed querytrees.
 ****************************************************************************/

/*
 * TypeName - specifies a type in definitions
 *
 * For TypeName structures generated internally, it is often easier to
 * specify the type by OID than by name.  If "names" is NIL then the
 * actual type OID is given by typeOid, otherwise typeOid is unused.
 * Similarly, if "typmods" is NIL then the actual typmod is expected to
 * be prespecified in typemod, otherwise typemod is unused.
 *
 * If pct_type is TRUE, then names is actually a field name and we look up
 * the type of that field.  Otherwise (the normal case), names is a type
 * name possibly qualified with schema and database name.
 */
typedef struct TypeName
{
	NodeTag		type;
	List	   *names;			/* qualified name (list of Value strings) */
	Oid			typeOid;		/* type identified by OID */
	bool		timezone;		/* timezone specified? */
	bool		setof;			/* is a set? */
	bool		pct_type;		/* %TYPE specified? */
	List	   *typmods;		/* type modifier expression(s) */
	int32		typemod;		/* prespecified type modifier */
	List	   *arrayBounds;	/* array bounds */
	int			location;		/* token location, or -1 if unknown */
} TypeName;

/*
 * ColumnRef - specifies a reference to a column, or possibly a whole tuple
 *
 * The "fields" list must be nonempty.  It can contain string Value nodes
 * (representing names) and A_Star nodes (representing occurrence of a '*').
 * Currently, A_Star must appear only as the last list element --- the grammar
 * is responsible for enforcing this!
 *
 * Note: any array subscripting or selection of fields from composite columns
 * is represented by an A_Indirection node above the ColumnRef.  However,
 * for simplicity in the normal case, initial field selection from a table
 * name is represented within ColumnRef and not by adding A_Indirection.
 */
typedef struct ColumnRef
{
	NodeTag		type;
	List	   *fields;			/* field names (Value strings) or A_Star */
	int			location;		/* token location, or -1 if unknown */
} ColumnRef;

/*
 * ParamRef - specifies a $n parameter reference
 */
typedef struct ParamRef
{
	NodeTag		type;
	int			number;			/* the number of the parameter */
	int			location;		/* token location, or -1 if unknown */
} ParamRef;

/*
 * A_Expr - infix, prefix, and postfix expressions
 */
typedef enum A_Expr_Kind
{
	AEXPR_OP,					/* normal operator */
	AEXPR_AND,					/* booleans - name field is unused */
	AEXPR_OR,
	AEXPR_NOT,
	AEXPR_OP_ANY,				/* scalar op ANY (array) */
	AEXPR_OP_ALL,				/* scalar op ALL (array) */
	AEXPR_DISTINCT,				/* IS DISTINCT FROM - name must be "=" */
	AEXPR_NULLIF,				/* NULLIF - name must be "=" */
	AEXPR_OF,					/* IS [NOT] OF - name must be "=" or "<>" */
	AEXPR_IN					/* [NOT] IN - name must be "=" or "<>" */
} A_Expr_Kind;

typedef struct A_Expr
{
	NodeTag		type;
	A_Expr_Kind kind;			/* see above */
	List	   *name;			/* possibly-qualified name of operator */
	Node	   *lexpr;			/* left argument, or NULL if none */
	Node	   *rexpr;			/* right argument, or NULL if none */
	int			location;		/* token location, or -1 if unknown */
} A_Expr;

/*
 * A_Const - a literal constant
 */
typedef struct A_Const
{
	NodeTag		type;
	Value		val;			/* value (includes type info, see value.h) */
	int			location;		/* token location, or -1 if unknown */
} A_Const;

/*
 * TypeCast - a CAST expression
 */
typedef struct TypeCast
{
	NodeTag		type;
	Node	   *arg;			/* the expression being casted */
	TypeName   *typeName;		/* the target type */
	int			location;		/* token location, or -1 if unknown */
} TypeCast;

/*
 * CollateClause - a COLLATE expression
 */
typedef struct CollateClause
{
	NodeTag		type;
	Node	   *arg;			/* input expression */
	List	   *collname;		/* possibly-qualified collation name */
	int			location;		/* token location, or -1 if unknown */
} CollateClause;

/*
 * FuncCall - a function or aggregate invocation
 *
 * agg_order (if not NIL) indicates we saw 'foo(... ORDER BY ...)', or if
 * agg_within_group is true, it was 'foo(...) WITHIN GROUP (ORDER BY ...)'.
 * agg_star indicates we saw a 'foo(*)' construct, while agg_distinct
 * indicates we saw 'foo(DISTINCT ...)'.  In any of these cases, the
 * construct *must* be an aggregate call.  Otherwise, it might be either an
 * aggregate or some other kind of function.  However, if FILTER or OVER is
 * present it had better be an aggregate or window function.
 *
 * Normally, you'd initialize this via makeFuncCall() and then only change the
 * parts of the struct its defaults don't match afterwards, as needed.
 */
typedef struct FuncCall
{
	NodeTag		type;
	List	   *funcname;		/* qualified name of function */
	List	   *args;			/* the arguments (list of exprs) */
	List	   *agg_order;		/* ORDER BY (list of SortBy) */
	Node	   *agg_filter;		/* FILTER clause, if any */
	bool		agg_within_group;		/* ORDER BY appeared in WITHIN GROUP */
	bool		agg_star;		/* argument was really '*' */
	bool		agg_distinct;	/* arguments were labeled DISTINCT */
	bool		func_variadic;	/* last argument was labeled VARIADIC */
	struct WindowDef *over;		/* OVER clause, if any */
	int			location;		/* token location, or -1 if unknown */
} FuncCall;

/*
 * A_Star - '*' representing all columns of a table or compound field
 *
 * This can appear within ColumnRef.fields, A_Indirection.indirection, and
 * ResTarget.indirection lists.
 */
typedef struct A_Star
{
	NodeTag		type;
} A_Star;

/*
 * A_Indices - array subscript or slice bounds ([lidx:uidx] or [uidx])
 */
typedef struct A_Indices
{
	NodeTag		type;
	Node	   *lidx;			/* NULL if it's a single subscript */
	Node	   *uidx;
} A_Indices;

/*
 * A_Indirection - select a field and/or array element from an expression
 *
 * The indirection list can contain A_Indices nodes (representing
 * subscripting), string Value nodes (representing field selection --- the
 * string value is the name of the field to select), and A_Star nodes
 * (representing selection of all fields of a composite type).
 * For example, a complex selection operation like
 *				(foo).field1[42][7].field2
 * would be represented with a single A_Indirection node having a 4-element
 * indirection list.
 *
 * Currently, A_Star must appear only as the last list element --- the grammar
 * is responsible for enforcing this!
 */
typedef struct A_Indirection
{
	NodeTag		type;
	Node	   *arg;			/* the thing being selected from */
	List	   *indirection;	/* subscripts and/or field names and/or * */
} A_Indirection;

/*
 * A_ArrayExpr - an ARRAY[] construct
 */
typedef struct A_ArrayExpr
{
	NodeTag		type;
	List	   *elements;		/* array element expressions */
	int			location;		/* token location, or -1 if unknown */
} A_ArrayExpr;

/*
 * ResTarget -
 *	  result target (used in target list of pre-transformed parse trees)
 *
 * In a SELECT target list, 'name' is the column label from an
 * 'AS ColumnLabel' clause, or NULL if there was none, and 'val' is the
 * value expression itself.  The 'indirection' field is not used.
 *
 * INSERT uses ResTarget in its target-column-names list.  Here, 'name' is
 * the name of the destination column, 'indirection' stores any subscripts
 * attached to the destination, and 'val' is not used.
 *
 * In an UPDATE target list, 'name' is the name of the destination column,
 * 'indirection' stores any subscripts attached to the destination, and
 * 'val' is the expression to assign.
 *
 * See A_Indirection for more info about what can appear in 'indirection'.
 */
typedef struct ResTarget
{
	NodeTag		type;
	char	   *name;			/* column name or NULL */
	List	   *indirection;	/* subscripts, field names, and '*', or NIL */
	Node	   *val;			/* the value expression to compute or assign */
	int			location;		/* token location, or -1 if unknown */
} ResTarget;

/*
 * SortBy - for ORDER BY clause
 */
typedef struct SortBy
{
	NodeTag		type;
	Node	   *node;			/* expression to sort on */
	SortByDir	sortby_dir;		/* ASC/DESC/USING/default */
	SortByNulls sortby_nulls;	/* NULLS FIRST/LAST */
	List	   *useOp;			/* name of op to use, if SORTBY_USING */
	int			location;		/* operator location, or -1 if none/unknown */
} SortBy;

/*
 * WindowDef - raw representation of WINDOW and OVER clauses
 *
 * For entries in a WINDOW list, "name" is the window name being defined.
 * For OVER clauses, we use "name" for the "OVER window" syntax, or "refname"
 * for the "OVER (window)" syntax, which is subtly different --- the latter
 * implies overriding the window frame clause.
 */
typedef struct WindowDef
{
	NodeTag		type;
	char	   *name;			/* window's own name */
	char	   *refname;		/* referenced window name, if any */
	List	   *partitionClause;	/* PARTITION BY expression list */
	List	   *orderClause;	/* ORDER BY (list of SortBy) */
	int			frameOptions;	/* frame_clause options, see below */
	Node	   *startOffset;	/* expression for starting bound, if any */
	Node	   *endOffset;		/* expression for ending bound, if any */
	int			location;		/* parse location, or -1 if none/unknown */
} WindowDef;

/*
 * frameOptions is an OR of these bits.  The NONDEFAULT and BETWEEN bits are
 * used so that ruleutils.c can tell which properties were specified and
 * which were defaulted; the correct behavioral bits must be set either way.
 * The START_foo and END_foo options must come in pairs of adjacent bits for
 * the convenience of gram.y, even though some of them are useless/invalid.
 * We will need more bits (and fields) to cover the full SQL:2008 option set.
 */
#define FRAMEOPTION_NONDEFAULT					0x00001 /* any specified? */
#define FRAMEOPTION_RANGE						0x00002 /* RANGE behavior */
#define FRAMEOPTION_ROWS						0x00004 /* ROWS behavior */
#define FRAMEOPTION_BETWEEN						0x00008 /* BETWEEN given? */
#define FRAMEOPTION_START_UNBOUNDED_PRECEDING	0x00010 /* start is U. P. */
#define FRAMEOPTION_END_UNBOUNDED_PRECEDING		0x00020 /* (disallowed) */
#define FRAMEOPTION_START_UNBOUNDED_FOLLOWING	0x00040 /* (disallowed) */
#define FRAMEOPTION_END_UNBOUNDED_FOLLOWING		0x00080 /* end is U. F. */
#define FRAMEOPTION_START_CURRENT_ROW			0x00100 /* start is C. R. */
#define FRAMEOPTION_END_CURRENT_ROW				0x00200 /* end is C. R. */
#define FRAMEOPTION_START_VALUE_PRECEDING		0x00400 /* start is V. P. */
#define FRAMEOPTION_END_VALUE_PRECEDING			0x00800 /* end is V. P. */
#define FRAMEOPTION_START_VALUE_FOLLOWING		0x01000 /* start is V. F. */
#define FRAMEOPTION_END_VALUE_FOLLOWING			0x02000 /* end is V. F. */

#define FRAMEOPTION_START_VALUE \
	(FRAMEOPTION_START_VALUE_PRECEDING | FRAMEOPTION_START_VALUE_FOLLOWING)
#define FRAMEOPTION_END_VALUE \
	(FRAMEOPTION_END_VALUE_PRECEDING | FRAMEOPTION_END_VALUE_FOLLOWING)

#define FRAMEOPTION_DEFAULTS \
	(FRAMEOPTION_RANGE | FRAMEOPTION_START_UNBOUNDED_PRECEDING | \
	 FRAMEOPTION_END_CURRENT_ROW)

/*
 * RangeSubselect - subquery appearing in a FROM clause
 */
typedef struct RangeSubselect
{
	NodeTag		type;
	bool		lateral;		/* does it have LATERAL prefix? */
	Node	   *subquery;		/* the untransformed sub-select clause */
	Alias	   *alias;			/* table alias & optional column aliases */
} RangeSubselect;

/*
 * RangeFunction - function call appearing in a FROM clause
 *
 * functions is a List because we use this to represent the construct
 * ROWS FROM(func1(...), func2(...), ...).  Each element of this list is a
 * two-element sublist, the first element being the untransformed function
 * call tree, and the second element being a possibly-empty list of ColumnDef
 * nodes representing any columndef list attached to that function within the
 * ROWS FROM() syntax.
 *
 * alias and coldeflist represent any alias and/or columndef list attached
 * at the top level.  (We disallow coldeflist appearing both here and
 * per-function, but that's checked in parse analysis, not by the grammar.)
 */
typedef struct RangeFunction
{
	NodeTag		type;
	bool		lateral;		/* does it have LATERAL prefix? */
	bool		ordinality;		/* does it have WITH ORDINALITY suffix? */
	bool		is_rowsfrom;	/* is result of ROWS FROM() syntax? */
	List	   *functions;		/* per-function information, see above */
	Alias	   *alias;			/* table alias & optional column aliases */
	List	   *coldeflist;		/* list of ColumnDef nodes to describe result
								 * of function returning RECORD */
} RangeFunction;

/*
 * ColumnDef - column definition (used in various creates)
 *
 * If the column has a default value, we may have the value expression
 * in either "raw" form (an untransformed parse tree) or "cooked" form
 * (a post-parse-analysis, executable expression tree), depending on
 * how this ColumnDef node was created (by parsing, or by inheritance
 * from an existing relation).  We should never have both in the same node!
 *
 * Similarly, we may have a COLLATE specification in either raw form
 * (represented as a CollateClause with arg==NULL) or cooked form
 * (the collation's OID).
 *
 * The constraints list may contain a CONSTR_DEFAULT item in a raw
 * parsetree produced by gram.y, but transformCreateStmt will remove
 * the item and set raw_default instead.  CONSTR_DEFAULT items
 * should not appear in any subsequent processing.
 */
typedef struct ColumnDef
{
	NodeTag		type;
	char	   *colname;		/* name of column */
	TypeName   *typeName;		/* type of column */
	int			inhcount;		/* number of times column is inherited */
	bool		is_local;		/* column has local (non-inherited) def'n */
	bool		is_not_null;	/* NOT NULL constraint specified? */
	bool		is_from_type;	/* column definition came from table type */
	AttrNumber	attnum;			/* attribute number */
	char		storage;		/* attstorage setting, or 0 for default */
	Node	   *raw_default;	/* default value (untransformed parse tree) */
	Node	   *cooked_default; /* default value (transformed expr tree) */
	CollateClause *collClause;	/* untransformed COLLATE spec, if any */
	Oid			collOid;		/* collation OID (InvalidOid if not set) */
	List	   *constraints;	/* other constraints on column */
	List	   *encoding;		/* ENCODING clause */
	List	   *fdwoptions;		/* per-column FDW options */
	int			location;		/* parse location, or -1 if none/unknown */
} ColumnDef;

/*
 * TableLikeClause - CREATE TABLE ( ... LIKE ... ) clause
 */
typedef struct TableLikeClause
{
	NodeTag		type;
	RangeVar   *relation;
	bits32		options;		/* OR of TableLikeOption flags */
} TableLikeClause;

typedef enum TableLikeOption
{
	CREATE_TABLE_LIKE_DEFAULTS = 1 << 0,
	CREATE_TABLE_LIKE_CONSTRAINTS = 1 << 1,
	CREATE_TABLE_LIKE_INDEXES = 1 << 2,
	CREATE_TABLE_LIKE_STORAGE = 1 << 3,
	CREATE_TABLE_LIKE_COMMENTS = 1 << 4,
	CREATE_TABLE_LIKE_ALL = 0x7FFFFFFF
} TableLikeOption;

/*
 * IndexElem - index parameters (used in CREATE INDEX)
 *
 * For a plain index attribute, 'name' is the name of the table column to
 * index, and 'expr' is NULL.  For an index expression, 'name' is NULL and
 * 'expr' is the expression tree.
 */
typedef struct IndexElem
{
	NodeTag		type;
	char	   *name;			/* name of attribute to index, or NULL */
	Node	   *expr;			/* expression to index, or NULL */
	char	   *indexcolname;	/* name for index column; NULL = default */
	List	   *collation;		/* name of collation; NIL = default */
	List	   *opclass;		/* name of desired opclass; NIL = default */
	SortByDir	ordering;		/* ASC/DESC/default */
	SortByNulls nulls_ordering; /* FIRST/LAST/default */
} IndexElem;

/*
 * column reference encoding clause for storage
 */
typedef struct ColumnReferenceStorageDirective
{
	NodeTag		type;
	char	   *column;	  /* column name, or NULL for DEFAULTs (deflt==true) */
	bool		deflt;
	List	   *encoding;
} ColumnReferenceStorageDirective;

/*
 * DefElem - a generic "name = value" option definition
 *
 * In some contexts the name can be qualified.  Also, certain SQL commands
 * allow a SET/ADD/DROP action to be attached to option settings, so it's
 * convenient to carry a field for that too.  (Note: currently, it is our
 * practice that the grammar allows namespace and action only in statements
 * where they are relevant; C code can just ignore those fields in other
 * statements.)
 */
typedef enum DefElemAction
{
	DEFELEM_UNSPEC,				/* no action given */
	DEFELEM_SET,
	DEFELEM_ADD,
	DEFELEM_DROP
} DefElemAction;

typedef struct DefElem
{
	NodeTag		type;
	char	   *defnamespace;	/* NULL if unqualified name */
	char	   *defname;
	Node	   *arg;			/* a (Value *) or a (TypeName *) */
	DefElemAction defaction;	/* unspecified action, or SET/ADD/DROP */
} DefElem;

/*
 * LockingClause - raw representation of FOR [NO KEY] UPDATE/[KEY] SHARE
 *		options
 *
 * Note: lockedRels == NIL means "all relations in query".  Otherwise it
 * is a list of RangeVar nodes.  (We use RangeVar mainly because it carries
 * a location field --- currently, parse analysis insists on unqualified
 * names in LockingClause.)
 */
typedef enum LockClauseStrength
{
	/* order is important -- see applyLockingClause */
	LCS_FORKEYSHARE,
	LCS_FORSHARE,
	LCS_FORNOKEYUPDATE,
	LCS_FORUPDATE
} LockClauseStrength;

typedef struct LockingClause
{
	NodeTag		type;
	List	   *lockedRels;		/* FOR [KEY] UPDATE/SHARE relations */
	LockClauseStrength strength;
	bool		noWait;			/* NOWAIT option */
} LockingClause;

/*
 * XMLSERIALIZE (in raw parse tree only)
 */
typedef struct XmlSerialize
{
	NodeTag		type;
	XmlOptionType xmloption;	/* DOCUMENT or CONTENT */
	Node	   *expr;
	TypeName   *typeName;
	int			location;		/* token location, or -1 if unknown */
} XmlSerialize;


/****************************************************************************
 *	Nodes for a Query tree
 ****************************************************************************/

/*--------------------
 * RangeTblEntry -
 *	  A range table is a List of RangeTblEntry nodes.
 *
 *	  A range table entry may represent a plain relation, a sub-select in
 *	  FROM, or the result of a JOIN clause.  (Only explicit JOIN syntax
 *	  produces an RTE, not the implicit join resulting from multiple FROM
 *	  items.  This is because we only need the RTE to deal with SQL features
 *	  like outer joins and join-output-column aliasing.)  Other special
 *	  RTE types also exist, as indicated by RTEKind.
 *
 *	  Note that we consider RTE_RELATION to cover anything that has a pg_class
 *	  entry.  relkind distinguishes the sub-cases.
 *
 *	  alias is an Alias node representing the AS alias-clause attached to the
 *	  FROM expression, or NULL if no clause.
 *
 *	  eref is the table reference name and column reference names (either
 *	  real or aliases).  Note that system columns (OID etc) are not included
 *	  in the column list.
 *	  eref->aliasname is required to be present, and should generally be used
 *	  to identify the RTE for error messages etc.
 *
 *	  In RELATION RTEs, the colnames in both alias and eref are indexed by
 *	  physical attribute number; this means there must be colname entries for
 *	  dropped columns.  When building an RTE we insert empty strings ("") for
 *	  dropped columns.  Note however that a stored rule may have nonempty
 *	  colnames for columns dropped since the rule was created (and for that
 *	  matter the colnames might be out of date due to column renamings).
 *	  The same comments apply to FUNCTION RTEs when a function's return type
 *	  is a named composite type.
 *
 *	  In JOIN RTEs, the colnames in both alias and eref are one-to-one with
 *	  joinaliasvars entries.  A JOIN RTE will omit columns of its inputs when
 *	  those columns are known to be dropped at parse time.  Again, however,
 *	  a stored rule might contain entries for columns dropped since the rule
 *	  was created.  (This is only possible for columns not actually referenced
 *	  in the rule.)  When loading a stored rule, we replace the joinaliasvars
 *	  items for any such columns with null pointers.  (We can't simply delete
 *	  them from the joinaliasvars list, because that would affect the attnums
 *	  of Vars referencing the rest of the list.)
 *
 *	  inh is TRUE for relation references that should be expanded to include
 *	  inheritance children, if the rel has any.  This *must* be FALSE for
 *	  RTEs other than RTE_RELATION entries.
 *
 *	  inFromCl marks those range variables that are listed in the FROM clause.
 *	  It's false for RTEs that are added to a query behind the scenes, such
 *	  as the NEW and OLD variables for a rule, or the subqueries of a UNION.
 *	  This flag is not used anymore during parsing, since the parser now uses
 *	  a separate "namespace" data structure to control visibility, but it is
 *	  needed by ruleutils.c to determine whether RTEs should be shown in
 *	  decompiled queries.
 *
 *	  requiredPerms and checkAsUser specify run-time access permissions
 *	  checks to be performed at query startup.  The user must have *all*
 *	  of the permissions that are OR'd together in requiredPerms (zero
 *	  indicates no permissions checking).  If checkAsUser is not zero,
 *	  then do the permissions checks using the access rights of that user,
 *	  not the current effective user ID.  (This allows rules to act as
 *	  setuid gateways.)  Permissions checks only apply to RELATION RTEs.
 *
 *	  For SELECT/INSERT/UPDATE permissions, if the user doesn't have
 *	  table-wide permissions then it is sufficient to have the permissions
 *	  on all columns identified in selectedCols (for SELECT) and/or
 *	  modifiedCols (for INSERT/UPDATE; we can tell which from the query type).
 *	  selectedCols and modifiedCols are bitmapsets, which cannot have negative
 *	  integer members, so we subtract FirstLowInvalidHeapAttributeNumber from
 *	  column numbers before storing them in these fields.  A whole-row Var
 *	  reference is represented by setting the bit for InvalidAttrNumber.
 *--------------------
 */
typedef enum RTEKind
{
	RTE_RELATION,				/* ordinary relation reference */
	RTE_SUBQUERY,				/* subquery in FROM */
	RTE_JOIN,					/* join */
	RTE_FUNCTION,				/* function in FROM */
	RTE_VALUES,					/* VALUES (<exprlist>), (<exprlist>), ... */
	RTE_VOID,                   /* CDB: deleted RTE */
	RTE_CTE,					/* common table expr (WITH list element) */
	RTE_TABLEFUNCTION,          /* CDB: Functions over multiset input */
} RTEKind;

typedef struct RangeTblEntry
{
	NodeTag		type;

	RTEKind		rtekind;		/* see above */

	/*
	 * XXX the fields applicable to only some rte kinds should be merged into
	 * a union.  I didn't do this yet because the diffs would impact a lot of
	 * code that is being actively worked on.  FIXME someday.
	 */

	/*
	 * Fields valid for a plain relation RTE (else zero):
	 */
	Oid			relid;			/* OID of the relation */
	char		relkind;		/* relation kind (see pg_class.relkind) */

	/*
	 * Fields valid for a subquery RTE (else NULL):
	 */
	Query	   *subquery;		/* the sub-query */
	bool		security_barrier;		/* is from security_barrier view? */

	/* These are for pre-planned sub-queries only.  They are internal to
	 * window planning.
	 */
	struct Plan *subquery_plan;
	List		*subquery_rtable;
	List		*subquery_pathkeys;

	/*
	 * Fields valid for a join RTE (else NULL/zero):
	 *
	 * joinaliasvars is a list of (usually) Vars corresponding to the columns
	 * of the join result.  An alias Var referencing column K of the join
	 * result can be replaced by the K'th element of joinaliasvars --- but to
	 * simplify the task of reverse-listing aliases correctly, we do not do
	 * that until planning time.  In detail: an element of joinaliasvars can
	 * be a Var of one of the join's input relations, or such a Var with an
	 * implicit coercion to the join's output column type, or a COALESCE
	 * expression containing the two input column Vars (possibly coerced).
	 * Within a Query loaded from a stored rule, it is also possible for
	 * joinaliasvars items to be null pointers, which are placeholders for
	 * (necessarily unreferenced) columns dropped since the rule was made.
	 * Also, once planning begins, joinaliasvars items can be almost anything,
	 * as a result of subquery-flattening substitutions.
	 */
	JoinType	jointype;		/* type of join */
	List	   *joinaliasvars;	/* list of alias-var expansions */

	/*
	 * Fields valid for a function RTE (else NIL/zero):
	 *
	 * When funcordinality is true, the eref->colnames list includes an alias
	 * for the ordinality column.  The ordinality column is otherwise
	 * implicit, and must be accounted for "by hand" in places such as
	 * expandRTE().
	 */
	List	   *functions;		/* list of RangeTblFunction nodes */
	bool		funcordinality; /* is this called WITH ORDINALITY? */

	/*
	 * Fields valid for a values RTE (else NIL):
	 */
	List	   *values_lists;	/* list of expression lists */
	List	   *values_collations;		/* OID list of column collation OIDs */

	/*
	 * Fields valid for a CTE RTE (else NULL/zero):
	 */
	char	   *ctename;		/* name of the WITH list item */
	Index		ctelevelsup;	/* number of query levels up */
	bool		self_reference; /* is this a recursive self-reference? */
	List	   *ctecoltypes;	/* OID list of column type OIDs */
	List	   *ctecoltypmods;	/* integer list of column typmods */
	List	   *ctecolcollations;		/* OID list of column collation OIDs */

	/* GPDB: Valid for base-relations, true if GP_DIST_RANDOM
	 * pseudo-function was specified as modifier in FROM-clause
	 */
	bool		forceDistRandom;

	/*
	 * Fields valid in all RTEs:
	 */
	Alias	   *alias;			/* user-written alias clause, if any */
	Alias	   *eref;			/* expanded reference names */
	bool		lateral;		/* subquery, function, or values is LATERAL? */
	bool		inh;			/* inheritance requested? */
	bool		inFromCl;		/* present in FROM clause? */
	AclMode		requiredPerms;	/* bitmask of required access permissions */
	Oid			checkAsUser;	/* if valid, check access as this role */
	Bitmapset  *selectedCols;	/* columns needing SELECT permission */
	Bitmapset  *modifiedCols;	/* columns needing INSERT/UPDATE permission */

	List	   *securityQuals;	/* any security barrier quals to apply */

    List       *pseudocols;     /* CDB: List of CdbRelColumnInfo nodes defining
                                 *  pseudo columns for targetlist of scan node.
                                 *  Referenced by Var nodes with varattno =
                                 *  FirstLowInvalidHeapAttributeNumber minus
                                 *  the 0-based position in the list.  Used
                                 *  only in planner & EXPLAIN, not in executor.
                                 */
} RangeTblEntry;

/*
 * RangeTblFunction -
 *	  RangeTblEntry subsidiary data for one function in a FUNCTION RTE.
 *
 * If the function had a column definition list (required for an
 * otherwise-unspecified RECORD result), funccolnames lists the names given
 * in the definition list, funccoltypes lists their declared column types,
 * funccoltypmods lists their typmods, funccolcollations their collations.
 * Otherwise, those fields are NIL.
 *
 * Notice we don't attempt to store info about the results of functions
 * returning named composite types, because those can change from time to
 * time.  We do however remember how many columns we thought the type had
 * (including dropped columns!), so that we can successfully ignore any
 * columns added after the query was parsed.
 */
typedef struct RangeTblFunction
{
	NodeTag		type;

	Node	   *funcexpr;		/* expression tree for func call */
	int			funccolcount;	/* number of columns it contributes to RTE */
	/* These fields record the contents of a column definition list, if any: */
	List	   *funccolnames;	/* column names (list of String) */
	List	   *funccoltypes;	/* OID list of column type OIDs */
	List	   *funccoltypmods; /* integer list of column typmods */
	List	   *funccolcollations;		/* OID list of column collation OIDs */

	bytea	   *funcuserdata;	/* describe function user data. assume bytea */

/* This is set during planning for use by the executor: */
	Bitmapset  *funcparams;		/* PARAM_EXEC Param IDs affecting this func */
} RangeTblFunction;

/*
 * WithCheckOption -
 *		representation of WITH CHECK OPTION checks to be applied to new tuples
 *		when inserting/updating an auto-updatable view.
 */
typedef struct WithCheckOption
{
	NodeTag		type;
	char	   *viewname;		/* name of view that specified the WCO */
	Node	   *qual;			/* constraint qual to check */
	bool		cascaded;		/* true = WITH CASCADED CHECK OPTION */
} WithCheckOption;

/*
 * SortGroupClause -
 *	   representation of ORDER BY, GROUP BY, DISTINCT, DISTINCT ON items
 *
 * You might think that ORDER BY is only interested in defining ordering,
 * and GROUP/DISTINCT are only interested in defining equality.  However,
 * one way to implement grouping is to sort and then apply a "uniq"-like
 * filter.  So it's also interesting to keep track of possible sort operators
 * for GROUP/DISTINCT, and in particular to try to sort for the grouping
 * in a way that will also yield a requested ORDER BY ordering.  So we need
 * to be able to compare ORDER BY and GROUP/DISTINCT lists, which motivates
 * the decision to give them the same representation.
 *
 * tleSortGroupRef must match ressortgroupref of exactly one entry of the
 *		query's targetlist; that is the expression to be sorted or grouped by.
 * eqop is the OID of the equality operator.
 * sortop is the OID of the ordering operator (a "<" or ">" operator),
 *		or InvalidOid if not available.
 * nulls_first means about what you'd expect.  If sortop is InvalidOid
 *		then nulls_first is meaningless and should be set to false.
 * hashable is TRUE if eqop is hashable (note this condition also depends
 *		on the datatype of the input expression).
 *
 * In an ORDER BY item, all fields must be valid.  (The eqop isn't essential
 * here, but it's cheap to get it along with the sortop, and requiring it
 * to be valid eases comparisons to grouping items.)  Note that this isn't
 * actually enough information to determine an ordering: if the sortop is
 * collation-sensitive, a collation OID is needed too.  We don't store the
 * collation in SortGroupClause because it's not available at the time the
 * parser builds the SortGroupClause; instead, consult the exposed collation
 * of the referenced targetlist expression to find out what it is.
 *
 * In a grouping item, eqop must be valid.  If the eqop is a btree equality
 * operator, then sortop should be set to a compatible ordering operator.
 * We prefer to set eqop/sortop/nulls_first to match any ORDER BY item that
 * the query presents for the same tlist item.  If there is none, we just
 * use the default ordering op for the datatype.
 *
 * If the tlist item's type has a hash opclass but no btree opclass, then
 * we will set eqop to the hash equality operator, sortop to InvalidOid,
 * and nulls_first to false.  A grouping item of this kind can only be
 * implemented by hashing, and of course it'll never match an ORDER BY item.
 *
 * The hashable flag is provided since we generally have the requisite
 * information readily available when the SortGroupClause is constructed,
 * and it's relatively expensive to get it again later.  Note there is no
 * need for a "sortable" flag since OidIsValid(sortop) serves the purpose.
 *
 * A query might have both ORDER BY and DISTINCT (or DISTINCT ON) clauses.
 * In SELECT DISTINCT, the distinctClause list is as long or longer than the
 * sortClause list, while in SELECT DISTINCT ON it's typically shorter.
 * The two lists must match up to the end of the shorter one --- the parser
 * rearranges the distinctClause if necessary to make this true.  (This
 * restriction ensures that only one sort step is needed to both satisfy the
 * ORDER BY and set up for the Unique step.  This is semantically necessary
 * for DISTINCT ON, and presents no real drawback for DISTINCT.)
 */
typedef struct SortGroupClause
{
	NodeTag		type;
	Index		tleSortGroupRef;	/* reference into targetlist */
	Oid			eqop;			/* the equality operator ('=' op) */
	Oid			sortop;			/* the ordering operator ('<' op), or 0 */
	bool		nulls_first;	/* do NULLs come before normal values? */
	bool		hashable;		/* can eqop be implemented by hashing? */
} SortGroupClause;

/*
 * GroupingClause -
 *     representation of grouping extension clauses,
 *     such as ROLLUP, CUBE, and GROUPING SETS.
 */
typedef struct GroupingClause
{
	NodeTag      type;
	GroupingType groupType;
	List         *groupsets;
	int			 location;
} GroupingClause;

/*
 * GroupingFunc -
 *     representation of a grouping function for grouping extension
 *     clauses.
 *
 * This is used to determine whether a null value for a column in
 * the output tuple is the result of grouping. For example, a table
 *
 *    test (a integer, b integer)
 *
 * has two rows:
 *
 *    (1,1), (null,1)
 *
 * The query "select a,sum(b),grouping(a) from test group by rollup(a)"
 * returns
 *
 *    1   ,    1,    0
 *    null,    1,    0
 *    null,    2,    1
 *
 * The output row "null,1,0" indicates that the 'null' value for 'a' is not
 * from grouping, while the row "null,2,1" indicates that the 'null' value for
 * 'a' is from grouping.
 */
typedef struct GroupingFunc
{
	NodeTag   type;
	List     *args;  /* arguments provided in the query. */
	int       ngrpcols; /* the number of grouping attributes */
} GroupingFunc;


/*
 * WindowClause -
 *		transformed representation of WINDOW and OVER clauses
 *
 * A parsed Query's windowClause list contains these structs.  "name" is set
 * if the clause originally came from WINDOW, and is NULL if it originally
 * was an OVER clause (but note that we collapse out duplicate OVERs).
 * partitionClause and orderClause are lists of SortGroupClause structs.
 * winref is an ID number referenced by WindowFunc nodes; it must be unique
 * among the members of a Query's windowClause list.
 * When refname isn't null, the partitionClause is always copied from there;
 * the orderClause might or might not be copied (see copiedOrder); the framing
 * options are never copied, per spec.
 */
typedef struct WindowClause
{
	NodeTag		type;
	char	   *name;			/* window name (NULL in an OVER clause) */
	char	   *refname;		/* referenced window name, if any */
	List	   *partitionClause;	/* PARTITION BY list */
	List	   *orderClause;	/* ORDER BY list */
	int			frameOptions;	/* frame_clause options, see WindowDef */
	Node	   *startOffset;	/* expression for starting bound, if any */
	Node	   *endOffset;		/* expression for ending bound, if any */
	Index		winref;			/* ID referenced by window functions */
	bool		copiedOrder;	/* did we copy orderClause from refname? */
} WindowClause;

/*
 * RowMarkClause -
 *	   parser output representation of FOR [KEY] UPDATE/SHARE clauses
 *
 * Query.rowMarks contains a separate RowMarkClause node for each relation
 * identified as a FOR [KEY] UPDATE/SHARE target.  If one of these clauses
 * is applied to a subquery, we generate RowMarkClauses for all normal and
 * subquery rels in the subquery, but they are marked pushedDown = true to
 * distinguish them from clauses that were explicitly written at this query
 * level.  Also, Query.hasForUpdate tells whether there were explicit FOR
 * UPDATE/SHARE/KEY SHARE clauses in the current query level.
 */
typedef struct RowMarkClause
{
	NodeTag		type;
	Index		rti;			/* range table index of target relation */
	LockClauseStrength strength;
	bool		noWait;			/* NOWAIT option */
	bool		pushedDown;		/* pushed down from higher query level? */
} RowMarkClause;

/*
 * WithClause -
 *	   representation of WITH clause
 *
 * Note: WithClause does not propagate into the Query representation;
 * but CommonTableExpr does.
 */
typedef struct WithClause
{
	NodeTag		type;
	List	   *ctes;			/* list of CommonTableExprs */
	bool		recursive;		/* true = WITH RECURSIVE */
	int			location;		/* token location, or -1 if unknown */
} WithClause;

/*
 * CommonTableExpr -
 *	   representation of WITH list element
 *
 * We don't currently support the SEARCH or CYCLE clause.
 */
typedef struct CommonTableExpr
{
	NodeTag		type;
	char	   *ctename;		/* query name (never qualified) */
	List	   *aliascolnames;	/* optional list of column names */
	/* SelectStmt/InsertStmt/etc before parse analysis, Query afterwards: */
	Node	   *ctequery;		/* the CTE's subquery */
	int			location;		/* token location, or -1 if unknown */
	/* These fields are set during parse analysis: */
	bool		cterecursive;	/* is this CTE actually recursive? */
	int			cterefcount;	/* number of RTEs referencing this CTE
								 * (excluding internal self-references) */
	List	   *ctecolnames;	/* list of output column names */
	List	   *ctecoltypes;	/* OID list of output column type OIDs */
	List	   *ctecoltypmods;	/* integer list of output column typmods */
	List	   *ctecolcollations;		/* OID list of column collation OIDs */
} CommonTableExpr;

/* Convenience macro to get the output tlist of a CTE's query */
#define GetCTETargetList(cte) \
	(AssertMacro(IsA((cte)->ctequery, Query)), \
	 ((Query *) (cte)->ctequery)->commandType == CMD_SELECT ? \
	 ((Query *) (cte)->ctequery)->targetList : \
	 ((Query *) (cte)->ctequery)->returningList)


/*****************************************************************************
 *		Optimizable Statements
 *****************************************************************************/

/* ----------------------
 *		Insert Statement
 *
 * The source expression is represented by SelectStmt for both the
 * SELECT and VALUES cases.  If selectStmt is NULL, then the query
 * is INSERT ... DEFAULT VALUES.
 * ----------------------
 */
typedef struct InsertStmt
{
	NodeTag		type;
	RangeVar   *relation;		/* relation to insert into */
	List	   *cols;			/* optional: names of the target columns */
	Node	   *selectStmt;		/* the source SELECT/VALUES, or NULL */
	List	   *returningList;	/* list of expressions to return */
	WithClause *withClause;		/* WITH clause */
} InsertStmt;

/* ----------------------
 *		Delete Statement
 * ----------------------
 */
typedef struct DeleteStmt
{
	NodeTag		type;
	RangeVar   *relation;		/* relation to delete from */
	List	   *usingClause;	/* optional using clause for more tables */
	Node	   *whereClause;	/* qualifications */
	List	   *returningList;	/* list of expressions to return */
	WithClause *withClause;		/* WITH clause */
} DeleteStmt;

/* ----------------------
 *		Update Statement
 * ----------------------
 */
typedef struct UpdateStmt
{
	NodeTag		type;
	RangeVar   *relation;		/* relation to update */
	List	   *targetList;		/* the target list (of ResTarget) */
	Node	   *whereClause;	/* qualifications */
	List	   *fromClause;		/* optional from clause for more tables */
	List	   *returningList;	/* list of expressions to return */
	WithClause *withClause;		/* WITH clause */
} UpdateStmt;

/* ----------------------
 *		Select Statement
 *
 * A "simple" SELECT is represented in the output of gram.y by a single
 * SelectStmt node; so is a VALUES construct.  A query containing set
 * operators (UNION, INTERSECT, EXCEPT) is represented by a tree of SelectStmt
 * nodes, in which the leaf nodes are component SELECTs and the internal nodes
 * represent UNION, INTERSECT, or EXCEPT operators.  Using the same node
 * type for both leaf and internal nodes allows gram.y to stick ORDER BY,
 * LIMIT, etc, clause values into a SELECT statement without worrying
 * whether it is a simple or compound SELECT.
 * ----------------------
 */
typedef enum SetOperation
{
	SETOP_NONE = 0,
	SETOP_UNION,
	SETOP_INTERSECT,
	SETOP_EXCEPT
} SetOperation;

/*
 * In raw parser output, this represents what the user wrote in the
 * DISTRIBUTED BY clause. In parse analysis, if no distributed by
 * was given, we add implicit columns.
 *
 * 'keyCols' is a List of IndexElems. It is used as a handy container
 * for column name + operator class pair. Only the 'indexcolname' and
 * 'opclass' fields are used.
 */
typedef struct DistributedBy
{
	NodeTag		type;
	GpPolicyType ptype;
	int			numsegments;
	List	   *keyCols;	/* valid when ptype is POLICYTYPE_PARTITIONED */
} DistributedBy;

typedef struct SelectStmt
{
	NodeTag		type;

	/*
	 * These fields are used only in "leaf" SelectStmts.
	 */
	List	   *distinctClause; /* NULL, list of DISTINCT ON exprs, or
								 * lcons(NIL,NIL) for all (SELECT DISTINCT) */
	IntoClause *intoClause;		/* target for SELECT INTO */
	List	   *targetList;		/* the target list (of ResTarget) */
	List	   *fromClause;		/* the FROM clause */
	Node	   *whereClause;	/* WHERE qualification */
	List	   *groupClause;	/* GROUP BY clauses */
	Node	   *havingClause;	/* HAVING conditional-expression */
	List	   *windowClause;	/* window specification clauses */
	List       *scatterClause;	/* GPDB: TableValueExpr data distribution */

	/*
	 * In a "leaf" node representing a VALUES list, the above fields are all
	 * null, and instead this field is set.  Note that the elements of the
	 * sublists are just expressions, without ResTarget decoration. Also note
	 * that a list element can be DEFAULT (represented as a SetToDefault
	 * node), regardless of the context of the VALUES list. It's up to parse
	 * analysis to reject that where not valid.
	 */
	List	   *valuesLists;	/* untransformed list of expression lists */

	/*
	 * These fields are used in both "leaf" SelectStmts and upper-level
	 * SelectStmts.
	 */
	List	   *sortClause;		/* sort clause (a list of SortBy's) */
	Node	   *limitOffset;	/* # of result tuples to skip */
	Node	   *limitCount;		/* # of result tuples to return */
	List	   *lockingClause;	/* FOR UPDATE (list of LockingClause's) */
	WithClause *withClause;		/* WITH clause */

	/*
	 * These fields are used only in upper-level SelectStmts.
	 */
	SetOperation op;			/* type of set op */
	bool		all;			/* ALL specified? */
	struct SelectStmt *larg;	/* left child */
	struct SelectStmt *rarg;	/* right child */
	/* Eventually add fields for CORRESPONDING spec here */
} SelectStmt;


/* ----------------------
 *		Set Operation node for post-analysis query trees
 *
 * After parse analysis, a SELECT with set operations is represented by a
 * top-level Query node containing the leaf SELECTs as subqueries in its
 * range table.  Its setOperations field shows the tree of set operations,
 * with leaf SelectStmt nodes replaced by RangeTblRef nodes, and internal
 * nodes replaced by SetOperationStmt nodes.  Information about the output
 * column types is added, too.  (Note that the child nodes do not necessarily
 * produce these types directly, but we've checked that their output types
 * can be coerced to the output column type.)  Also, if it's not UNION ALL,
 * information about the types' sort/group semantics is provided in the form
 * of a SortGroupClause list (same representation as, eg, DISTINCT).
 * The resolved common column collations are provided too; but note that if
 * it's not UNION ALL, it's okay for a column to not have a common collation,
 * so a member of the colCollations list could be InvalidOid even though the
 * column has a collatable type.
 * ----------------------
 */
typedef struct SetOperationStmt
{
	NodeTag		type;
	SetOperation op;			/* type of set op */
	bool		all;			/* ALL specified? */
	Node	   *larg;			/* left child */
	Node	   *rarg;			/* right child */
	/* Eventually add fields for CORRESPONDING spec here */

	/* Fields derived during parse analysis: */
	List	   *colTypes;		/* OID list of output column type OIDs */
	List	   *colTypmods;		/* integer list of output column typmods */
	List	   *colCollations;	/* OID list of output column collation OIDs */
	List	   *groupClauses;	/* a list of SortGroupClause's */
	/* groupClauses is NIL if UNION ALL, but must be set otherwise */
} SetOperationStmt;


/*****************************************************************************
 *		Other Statements (no optimizations required)
 *
 *		These are not touched by parser/analyze.c except to put them into
 *		the utilityStmt field of a Query.  This is eventually passed to
 *		ProcessUtility (by-passing rewriting and planning).  Some of the
 *		statements do need attention from parse analysis, and this is
 *		done by routines in parser/parse_utilcmd.c after ProcessUtility
 *		receives the command for execution.
 *****************************************************************************/

/*
 * When a command can act on several kinds of objects with only one
 * parse structure required, use these constants to designate the
 * object type.  Note that commands typically don't support all the types.
 */

typedef enum ObjectType
{
	OBJECT_AGGREGATE,
	OBJECT_ATTRIBUTE,			/* type's attribute, when distinct from column */
	OBJECT_CAST,
	OBJECT_COLUMN,
	OBJECT_CONSTRAINT,
	OBJECT_COLLATION,
	OBJECT_CONVERSION,
	OBJECT_DATABASE,
	OBJECT_DOMAIN,
	OBJECT_EVENT_TRIGGER,
	OBJECT_EXTENSION,
	OBJECT_FDW,
	OBJECT_FOREIGN_SERVER,
	OBJECT_FOREIGN_TABLE,
	OBJECT_FUNCTION,
	OBJECT_INDEX,
	OBJECT_LANGUAGE,
	OBJECT_LARGEOBJECT,
	OBJECT_MATVIEW,
	OBJECT_OPCLASS,
	OBJECT_OPERATOR,
	OBJECT_OPFAMILY,
	OBJECT_ROLE,
	OBJECT_RULE,
	OBJECT_SCHEMA,
	OBJECT_SEQUENCE,
	OBJECT_TABLE,
	OBJECT_EXTTABLE,
	OBJECT_EXTPROTOCOL,
	OBJECT_TABLESPACE,
	OBJECT_TRIGGER,
	OBJECT_TSCONFIGURATION,
	OBJECT_TSDICTIONARY,
	OBJECT_TSPARSER,
	OBJECT_TSTEMPLATE,
	OBJECT_TYPE,
	OBJECT_VIEW,
	OBJECT_RESQUEUE,
	OBJECT_RESGROUP
} ObjectType;

/* ----------------------
 *		Create Schema Statement
 *
 * NOTE: the schemaElts list contains raw parsetrees for component statements
 * of the schema, such as CREATE TABLE, GRANT, etc.  These are analyzed and
 * executed after the schema itself is created.
 * ----------------------
 */
typedef struct CreateSchemaStmt
{
	NodeTag		type;
	char	   *schemaname;		/* the name of the schema to create */
	char	   *authid;			/* the owner of the created schema */
	List	   *schemaElts;		/* schema components (list of parsenodes) */
	bool		if_not_exists;	/* just do nothing if schema already exists? */

	/*
	 * In GPDB, when a CreateSchemaStmt is dispatched to executor nodes, the
	 * following field is set.
	 *
	 * There's a special case for when the temporary namespace is created,
	 * on the first use in the session. There are actually two temporary
	 * namespaces, the regular one, and a temporary toast namespace. They are
	 * both created in the same command, with istemp='true'.
	 */
	bool        istemp;         /* true for temp schemas (internal only) */
} CreateSchemaStmt;

typedef enum DropBehavior
{
	DROP_RESTRICT,				/* drop fails if any dependent objects */
	DROP_CASCADE				/* remove dependent objects too */
} DropBehavior;

/* ----------------------
 *	Alter Table
 * ----------------------
 */
typedef struct AlterTableStmt
{
	NodeTag		type;
	RangeVar   *relation;		/* table to work on */
	List	   *cmds;			/* list of subcommands */
	ObjectType	relkind;		/* type of object */
	bool		missing_ok;		/* skip error if table missing */
} AlterTableStmt;

typedef enum AlterTableType
{
	AT_AddColumn,				/* add column */
	AT_AddColumnRecurse,		/* internal to commands/tablecmds.c */
	AT_AddColumnToView,			/* implicitly via CREATE OR REPLACE VIEW */
	AT_ColumnDefault,			/* alter column default */
	AT_ColumnDefaultRecurse,	/* internal to commands/tablecmds.c */
	AT_DropNotNull,				/* alter column drop not null */
	AT_SetNotNull,				/* alter column set not null */
	AT_SetStatistics,			/* alter column set statistics */
	AT_SetOptions,				/* alter column set ( options ) */
	AT_ResetOptions,			/* alter column reset ( options ) */
	AT_SetStorage,				/* alter column set storage */
	AT_DropColumn,				/* drop column */
	AT_DropColumnRecurse,		/* internal to commands/tablecmds.c */
	AT_AddIndex,				/* add index */
	AT_ReAddIndex,				/* internal to commands/tablecmds.c */
	AT_AddConstraint,			/* add constraint */
	AT_AddConstraintRecurse,	/* internal to commands/tablecmds.c */
	AT_ReAddConstraint,			/* internal to commands/tablecmds.c */
	AT_AlterConstraint,			/* alter constraint */
	AT_ValidateConstraint,		/* validate constraint */
	AT_ValidateConstraintRecurse,		/* internal to commands/tablecmds.c */
	AT_ProcessedConstraint,		/* pre-processed add constraint (local in
								 * parser/parse_utilcmd.c) */
	AT_AddIndexConstraint,		/* add constraint using existing index */
	AT_DropConstraint,			/* drop constraint */
	AT_DropConstraintRecurse,	/* internal to commands/tablecmds.c */
	AT_AlterColumnType,			/* alter column type */
	AT_AlterColumnGenericOptions,		/* alter column OPTIONS (...) */
	AT_ChangeOwner,				/* change owner */
	AT_ClusterOn,				/* CLUSTER ON */
	AT_DropCluster,				/* SET WITHOUT CLUSTER */
	AT_AddOids,					/* SET WITH OIDS */
	AT_AddOidsRecurse,			/* internal to commands/tablecmds.c */
	AT_DropOids,				/* SET WITHOUT OIDS */
	AT_SetTableSpace,			/* SET TABLESPACE */
	AT_SetRelOptions,			/* SET (...) -- AM specific parameters */
	AT_ResetRelOptions,			/* RESET (...) -- AM specific parameters */
	AT_ReplaceRelOptions,		/* replace reloption list in its entirety */
	AT_EnableTrig,				/* ENABLE TRIGGER name */
	AT_EnableAlwaysTrig,		/* ENABLE ALWAYS TRIGGER name */
	AT_EnableReplicaTrig,		/* ENABLE REPLICA TRIGGER name */
	AT_DisableTrig,				/* DISABLE TRIGGER name */
	AT_EnableTrigAll,			/* ENABLE TRIGGER ALL */
	AT_DisableTrigAll,			/* DISABLE TRIGGER ALL */
	AT_EnableTrigUser,			/* ENABLE TRIGGER USER */
	AT_DisableTrigUser,			/* DISABLE TRIGGER USER */
	AT_EnableRule,				/* ENABLE RULE name */
	AT_EnableAlwaysRule,		/* ENABLE ALWAYS RULE name */
	AT_EnableReplicaRule,		/* ENABLE REPLICA RULE name */
	AT_DisableRule,				/* DISABLE RULE name */
	AT_AddInherit,				/* INHERIT parent */
	AT_DropInherit,				/* NO INHERIT parent */
	AT_AddOf,					/* OF <type_name> */
	AT_DropOf,					/* NOT OF */
	AT_ReplicaIdentity,			/* REPLICA IDENTITY */
	AT_GenericOptions,			/* OPTIONS (...) */
	AT_SetDistributedBy,		/* SET DISTRIBUTED BY */
	AT_ExpandTable,          /* EXPAND DISTRIBUTED */
	AT_ExpandPartitionTablePrepare,	/* EXPAND PARTITION PREPARE */

	/* CDB: Partitioned Tables */
	AT_PartAdd,					/* Add */
	AT_PartAddForSplit,			/* Add, as subcommand of a split */
	AT_PartAlter,				/* Alter */
	AT_PartDrop,				/* Drop */
	AT_PartExchange,			/* Exchange */
	AT_PartRename,				/* Rename */
	AT_PartSetTemplate,			/* Set Subpartition Template */
	AT_PartSplit,				/* Split */
	AT_PartTruncate,			/* Truncate */
	AT_PartAddInternal,			/* CREATE TABLE time partition addition */
	AT_PartAttachIndex			/* ALTER INDEX ATTACH PARTITION (not exposed to user) */
} AlterTableType;

typedef struct ReplicaIdentityStmt
{
	NodeTag		type;
	char		identity_type;
	char	   *name;
} ReplicaIdentityStmt;

typedef struct AlterTableCmd	/* one subcommand of an ALTER TABLE */
{
	NodeTag		type;
	AlterTableType subtype;		/* Type of table alteration to apply */
	char	   *name;			/* column, constraint, or trigger to act on,
								 * or new owner or tablespace */
	Node	   *def;			/* definition of new column, column type,
								 * index, constraint, or parent table */
	Node	   *transform;		/* transformation expr for ALTER TYPE */
	DropBehavior behavior;		/* RESTRICT or CASCADE for DROP cases */
	bool		part_expanded;	/* expands from another command, for partitioning */
	List	   *partoids;		/* If applicable, OIDs of partition part tables */
	bool		missing_ok;		/* skip error if missing? */
	/* addition info for partition table */
	Bitmapset	*ps_none;
	Bitmapset	*ps_root;
	Bitmapset	*ps_interior;
	Bitmapset	*ps_leaf;
} AlterTableCmd;


typedef struct SetDistributionCmd
{
	NodeTag		type;
	int	        backendId;     /* backend ID on QD */
	List	   *relids;            /* oid of relations(partitions) which have related temporary table */
} SetDistributionCmd;


typedef enum AlterPartitionIdType
{
	AT_AP_IDNone,				/* no ID */
	AT_AP_IDName,				/* IDentify by Name */
	AT_AP_IDValue,				/* IDentifier FOR Value */
	AT_AP_IDRank,				/* IDentifier FOR Rank */
	AT_AP_ID_oid,				/* IDentifier by oid (for internal use only) */
	AT_AP_IDList,				/* List of IDentifier(for internal use only) */
	AT_AP_IDRule,				/* partition rule (for internal use only) */
	AT_AP_IDDefault,			/* IDentify DEFAULT partition */
	AT_AP_IDRangeVar			/* IDentify Partition by RangeVar */
} AlterPartitionIdType;

typedef struct AlterPartitionId /* Identify a partition by name, val, pos */
{
	NodeTag		type;
	AlterPartitionIdType idtype;/* Type of table alteration to apply */
	Node	   *partiddef;		/* partition id definition */
	int					location;	/* token location, or -1 if unknown */
} AlterPartitionId;

typedef struct AlterPartitionCmd/* one subcmd of an ALTER TABLE...PARTITION */
{
	NodeTag		type;
	Node	   *partid;			/* partition id */
	Node	   *arg1;			/* argument 1 */
	Node	   *arg2;			/* argument 2 */
	int					location;	/* token location, or -1 if unknown */
} AlterPartitionCmd;

typedef struct InheritPartitionCmd
{
	NodeTag		type;
	RangeVar   *parent;
} InheritPartitionCmd;

/* ----------------------
 *	Alter Domain
 *
 * The fields are used in different ways by the different variants of
 * this command.
 * ----------------------
 */
typedef struct AlterDomainStmt
{
	NodeTag		type;
	char		subtype;		/*------------
								 *	T = alter column default
								 *	N = alter column drop not null
								 *	O = alter column set not null
								 *	C = add constraint
								 *	X = drop constraint
								 *------------
								 */
	List	   *typeName;		/* domain to work on */
	char	   *name;			/* column or constraint name to act on */
	Node	   *def;			/* definition of default or constraint */
	DropBehavior behavior;		/* RESTRICT or CASCADE for DROP cases */
	bool		missing_ok;		/* skip error if missing? */
} AlterDomainStmt;


/* ----------------------
 *		Grant|Revoke Statement
 * ----------------------
 */
typedef enum GrantTargetType
{
	ACL_TARGET_OBJECT,			/* grant on specific named object(s) */
	ACL_TARGET_ALL_IN_SCHEMA,	/* grant on all objects in given schema(s) */
	ACL_TARGET_DEFAULTS			/* ALTER DEFAULT PRIVILEGES */
} GrantTargetType;

typedef enum GrantObjectType
{
	ACL_OBJECT_COLUMN,			/* column */
	ACL_OBJECT_RELATION,		/* table, view */
	ACL_OBJECT_SEQUENCE,		/* sequence */
	ACL_OBJECT_DATABASE,		/* database */
	ACL_OBJECT_EXTPROTOCOL,		/* external table protocol */
	ACL_OBJECT_DOMAIN,			/* domain */
	ACL_OBJECT_FDW,				/* foreign-data wrapper */
	ACL_OBJECT_FOREIGN_SERVER,	/* foreign server */
	ACL_OBJECT_FUNCTION,		/* function */
	ACL_OBJECT_LANGUAGE,		/* procedural language */
	ACL_OBJECT_LARGEOBJECT,		/* largeobject */
	ACL_OBJECT_NAMESPACE,		/* namespace */
	ACL_OBJECT_TABLESPACE,		/* tablespace */
	ACL_OBJECT_TYPE				/* type */
} GrantObjectType;

typedef struct GrantStmt
{
	NodeTag		type;
	bool		is_grant;		/* true = GRANT, false = REVOKE */
	GrantTargetType targtype;	/* type of the grant target */
	GrantObjectType objtype;	/* kind of object being operated on */
	List	   *objects;		/* list of RangeVar nodes, FuncWithArgs nodes,
								 * or plain names (as Value strings) */
	List	   *privileges;		/* list of AccessPriv nodes */
	/* privileges == NIL denotes ALL PRIVILEGES */
	List	   *grantees;		/* list of PrivGrantee nodes */
	bool		grant_option;	/* grant or revoke grant option */
	DropBehavior behavior;		/* drop behavior (for REVOKE) */
} GrantStmt;

typedef struct PrivGrantee
{
	NodeTag		type;
	char	   *rolname;		/* if NULL then PUBLIC */
} PrivGrantee;

/*
 * Note: FuncWithArgs carries only the types of the input parameters of the
 * function.  So it is sufficient to identify an existing function, but it
 * is not enough info to define a function nor to call it.
 */
typedef struct FuncWithArgs
{
	NodeTag		type;
	List	   *funcname;		/* qualified name of function */
	List	   *funcargs;		/* list of Typename nodes */
} FuncWithArgs;

/*
 * An access privilege, with optional list of column names
 * priv_name == NULL denotes ALL PRIVILEGES (only used with a column list)
 * cols == NIL denotes "all columns"
 * Note that simple "ALL PRIVILEGES" is represented as a NIL list, not
 * an AccessPriv with both fields null.
 */
typedef struct AccessPriv
{
	NodeTag		type;
	char	   *priv_name;		/* string name of privilege */
	List	   *cols;			/* list of Value strings */
} AccessPriv;

/* ----------------------
 *		Grant/Revoke Role Statement
 *
 * Note: because of the parsing ambiguity with the GRANT <privileges>
 * statement, granted_roles is a list of AccessPriv; the execution code
 * should complain if any column lists appear.  grantee_roles is a list
 * of role names, as Value strings.
 * ----------------------
 */
typedef struct GrantRoleStmt
{
	NodeTag		type;
	List	   *granted_roles;	/* list of roles to be granted/revoked */
	List	   *grantee_roles;	/* list of member roles to add/delete */
	bool		is_grant;		/* true = GRANT, false = REVOKE */
	bool		admin_opt;		/* with admin option */
	char	   *grantor;		/* set grantor to other than current role */
	DropBehavior behavior;		/* drop behavior (for REVOKE) */
} GrantRoleStmt;


typedef enum LogErrorsType
{
	LOG_ERRORS_DISABLE,			/* disable log errors */
	LOG_ERRORS_ENABLE,			/* drop the error log when relation drops */
	LOG_ERRORS_PERSISTENTLY		/* keep the error log when relation drops */
} LogErrorsType;

/*
 * Node that represents the single row error handling (SREH) clause.
 * used in COPY and External Tables.
 */
typedef struct SingleRowErrorDesc
{
	NodeTag		type;
	int			rejectlimit;		/* per segment error reject limit */
	bool		is_limit_in_rows;	/* true for ROWS false for PERCENT */
	bool		into_file;			/* log into file not table */
	LogErrorsType log_errors_type;	/* log errors type */
} SingleRowErrorDesc;

/* ----------------------
 *	Alter Default Privileges Statement
 * ----------------------
 */
typedef struct AlterDefaultPrivilegesStmt
{
	NodeTag		type;
	List	   *options;		/* list of DefElem */
	GrantStmt  *action;			/* GRANT/REVOKE action (with objects=NIL) */
} AlterDefaultPrivilegesStmt;

/* ----------------------
 *		Copy Statement
 *
 * We support "COPY relation FROM file", "COPY relation TO file", and
 * "COPY (query) TO file".  In any given CopyStmt, exactly one of "relation"
 * and "query" must be non-NULL.
 * ----------------------
 */
typedef struct CopyStmt
{
	NodeTag		type;
	RangeVar   *relation;		/* the relation to copy */
	Node	   *query;			/* the SELECT query to copy */
	List	   *attlist;		/* List of column names (as Strings), or NIL
								 * for all columns */
	bool		is_from;		/* TO or FROM */
	bool		is_program;		/* is 'filename' a program to popen? */
	bool		skip_ext_partition;		/* skip external partitions */
	char	   *filename;		/* filename, or NULL for STDIN/STDOUT */
	List	   *options;		/* List of DefElem nodes */
	Node	   *sreh;			/* Single row error handling info */
	/* Convenient location for dispatch of misc meta data */
	PartitionNode *partitions;
	List		*ao_segnos;		/* AO segno map */
} CopyStmt;

/* ----------------------
 * SET Statement (includes RESET)
 *
 * "SET var TO DEFAULT" and "RESET var" are semantically equivalent, but we
 * preserve the distinction in VariableSetKind for CreateCommandTag().
 * ----------------------
 */
typedef enum
{
	VAR_SET_VALUE,				/* SET var = value */
	VAR_SET_DEFAULT,			/* SET var TO DEFAULT */
	VAR_SET_CURRENT,			/* SET var FROM CURRENT */
	VAR_SET_MULTI,				/* special case for SET TRANSACTION ... */
	VAR_RESET,					/* RESET var */
	VAR_RESET_ALL				/* RESET ALL */
} VariableSetKind;

typedef struct VariableSetStmt
{
	NodeTag		type;
	VariableSetKind kind;
	char	   *name;			/* variable to be set */
	List	   *args;			/* List of A_Const nodes */
	bool		is_local;		/* SET LOCAL? */
} VariableSetStmt;

/* ----------------------
 * Show Statement
 * ----------------------
 */
typedef struct VariableShowStmt
{
	NodeTag		type;
	char	   *name;
} VariableShowStmt;

/* ----------------------
 *		Create Table Statement
 *
 * NOTE: in the raw gram.y output, ColumnDef and Constraint nodes are
 * intermixed in tableElts, and constraints is NIL.  After parse analysis,
 * tableElts contains just ColumnDefs, and constraints contains just
 * Constraint nodes (in fact, only CONSTR_CHECK nodes, in the present
 * implementation).
 * ----------------------
 */

typedef struct CreateStmt
{
	NodeTag		type;
	RangeVar   *relation;		/* relation to create */
	List	   *tableElts;		/* column definitions (list of ColumnDef) */
	List	   *inhRelations;	/* relations to inherit from (list of
								 * inhRelation) */
	List	   *inhOids;		/* list relations Oids to inherit from */
	int			parentOidCount; /* count of parent with OIDs */
	TypeName   *ofTypename;		/* OF typename */
	List	   *constraints;	/* constraints (list of Constraint nodes) */
	List	   *options;		/* options from WITH clause */
	OnCommitAction oncommit;	/* what do we do at COMMIT? */
	char	   *tablespacename; /* table space to use, or NULL */
	bool		if_not_exists;	/* just do nothing if it already exists? */

	DistributedBy *distributedBy;   /* what columns we distribute the data by */
	Node       *partitionBy;     /* what columns we partition the data by */
	char	    relKind;         /* CDB: force relkind to this */
	char		relStorage;
	List	   *deferredStmts;	/* CDB: Statements, e.g., partial indexes, that can't be
								 * analyzed until after CREATE (until the target table
								 * is created and visible). */
	bool		is_part_child;	/* CDB: child table in a partition? Marked during analysis for
								 * interior or leaf parts of the new table.  Not marked for a
								 * a partition root or ordinary table.
								 */
	bool        is_part_parent; /* CDB: Marked during analysis for top and interior
								 * parent of partition tables which don't contain
								 * any data */
	bool		is_add_part;	/* CDB: is create adding a part to a partition? */
	bool		is_split_part;	/* CDB: is create spliting a part? */
	Oid			ownerid;		/* OID of the role to own this. if InvalidOid, GetUserId() */
	bool		buildAoBlkdir; /* whether to build the block directory for an AO table */
	List	   *attr_encodings; /* attribute storage directives */
	bool		isCtas;			/* CDB: is create table as */

	Node       *intoQuery;      /* CDB: only set for matview with no data */
	GpPolicy   *intoPolicy;     /* CDB: only set for matview with no data */
} CreateStmt;

/* ----------------------
 *	Definitions for external tables
 * ----------------------
 */
typedef enum ExtTableType
{
	EXTTBL_TYPE_LOCATION,		/* table defined with LOCATION clause */
	EXTTBL_TYPE_EXECUTE			/* table defined with EXECUTE clause */
} ExtTableType;

typedef struct
{
	NodeTag			type;
	ExtTableType	exttabletype;
	List			*location_list;
	List			*on_clause;
	char			*command_string;
} ExtTableTypeDesc;

typedef struct CreateExternalStmt
{
	NodeTag		type;
	RangeVar   *relation;		/* external relation to create */
	List	   *tableElts;		/* column definitions (list of ColumnDef) */
	ExtTableTypeDesc *exttypedesc;    /* LOCATION or EXECUTE information */
	char	   *format;			/* data format name */
	List	   *formatOpts;		/* List of DefElem nodes for data format */
	bool		isweb;
	bool		iswritable;
	Node	   *sreh;			/* Single row error handling info */
	List       *extOptions;		/* generic options to external table */
	List	   *encoding;		/* List (size 1 max) of DefElem nodes for
								   data encoding */
	DistributedBy *distributedBy;   /* what columns we distribute the data by */

} CreateExternalStmt;

/* ----------------------
 *	Definitions for foreign tables
 * ----------------------
 */
typedef struct CreateForeignStmt
{
	NodeTag		type;
	RangeVar   *relation;		/* foreign relation to create */
	List	   *tableElts;		/* column definitions (list of ColumnDef) */
	char	   *srvname;		/* server name */
	List	   *options;		/* generic options to foreign table */

} CreateForeignStmt;

/* ----------
 * Definitions for constraints in CreateStmt
 *
 * Note that column defaults are treated as a type of constraint,
 * even though that's a bit odd semantically.
 *
 * For constraints that use expressions (CONSTR_CHECK, CONSTR_DEFAULT)
 * we may have the expression in either "raw" form (an untransformed
 * parse tree) or "cooked" form (the nodeToString representation of
 * an executable expression tree), depending on how this Constraint
 * node was created (by parsing, or by inheritance from an existing
 * relation).  We should never have both in the same node!
 *
 * FKCONSTR_ACTION_xxx values are stored into pg_constraint.confupdtype
 * and pg_constraint.confdeltype columns; FKCONSTR_MATCH_xxx values are
 * stored into pg_constraint.confmatchtype.  Changing the code values may
 * require an initdb!
 *
 * If skip_validation is true then we skip checking that the existing rows
 * in the table satisfy the constraint, and just install the catalog entries
 * for the constraint.  A new FK constraint is marked as valid iff
 * initially_valid is true.  (Usually skip_validation and initially_valid
 * are inverses, but we can set both true if the table is known empty.)
 *
 * Constraint attributes (DEFERRABLE etc) are initially represented as
 * separate Constraint nodes for simplicity of parsing.  parse_utilcmd.c makes
 * a pass through the constraints list to insert the info into the appropriate
 * Constraint node.
 * ----------
 */

typedef enum ConstrType			/* types of constraints */
{
	CONSTR_NULL,				/* not standard SQL, but a lot of people
								 * expect it */
	CONSTR_NOTNULL,
	CONSTR_DEFAULT,
	CONSTR_CHECK,
	CONSTR_PRIMARY,
	CONSTR_UNIQUE,
	CONSTR_EXCLUSION,
	CONSTR_FOREIGN,
	CONSTR_ATTR_DEFERRABLE,		/* attributes for previous constraint node */
	CONSTR_ATTR_NOT_DEFERRABLE,
	CONSTR_ATTR_DEFERRED,
	CONSTR_ATTR_IMMEDIATE
} ConstrType;

/* Foreign key action codes */
#define FKCONSTR_ACTION_NOACTION	'a'
#define FKCONSTR_ACTION_RESTRICT	'r'
#define FKCONSTR_ACTION_CASCADE		'c'
#define FKCONSTR_ACTION_SETNULL		'n'
#define FKCONSTR_ACTION_SETDEFAULT	'd'

/* Foreign key matchtype codes */
#define FKCONSTR_MATCH_FULL			'f'
#define FKCONSTR_MATCH_PARTIAL		'p'
#define FKCONSTR_MATCH_SIMPLE		's'

typedef struct Constraint
{
	NodeTag		type;
	ConstrType	contype;		/* see above */

	/* Fields used for most/all constraint types: */
	char	   *conname;		/* Constraint name, or NULL if unnamed */
	bool		deferrable;		/* DEFERRABLE? */
	bool		initdeferred;	/* INITIALLY DEFERRED? */
	int			location;		/* token location, or -1 if unknown */

	/* Fields used for constraints with expressions (CHECK and DEFAULT): */
	bool		is_no_inherit;	/* is constraint non-inheritable? */
	Node	   *raw_expr;		/* expr, as untransformed parse tree */
	char	   *cooked_expr;	/* expr, as nodeToString representation */

	/* Fields used for unique constraints (UNIQUE and PRIMARY KEY): */
	List	   *keys;			/* String nodes naming referenced column(s) */

	/* Fields used for EXCLUSION constraints: */
	List	   *exclusions;		/* list of (IndexElem, operator name) pairs */

	/* Fields used for index constraints (UNIQUE, PRIMARY KEY, EXCLUSION): */
	List	   *options;		/* options from WITH clause */
	char	   *indexname;		/* existing index to use; otherwise NULL */
	char	   *indexspace;		/* index tablespace; NULL for default */
	/* These could be, but currently are not, used for UNIQUE/PKEY: */
	char	   *access_method;	/* index access method; NULL for default */
	Node	   *where_clause;	/* partial index predicate */

	/* Fields used for FOREIGN KEY constraints: */
	RangeVar   *pktable;		/* Primary key table */
	List	   *fk_attrs;		/* Attributes of foreign key */
	List	   *pk_attrs;		/* Corresponding attrs in PK table */
	char		fk_matchtype;	/* FULL, PARTIAL, SIMPLE */
	char		fk_upd_action;	/* ON UPDATE action */
	char		fk_del_action;	/* ON DELETE action */
	List	   *old_conpfeqop;	/* pg_constraint.conpfeqop of my former self */
	Oid			old_pktable_oid;	/* pg_constraint.confrelid of my former self */

	/* Fields used for constraints that allow a NOT VALID specification */
	bool		skip_validation;	/* skip validation of existing rows? */
	bool		initially_valid;	/* start the new constraint as valid */
	Oid			trig1Oid;
	Oid			trig2Oid;
	Oid			trig3Oid;
	Oid			trig4Oid;
} Constraint;

/* ----------
 * Definitions for Table Partition clauses in CreateStmt
 *
 * ----------
 */
typedef enum PartitionByType			/* types of Partitions */
{
	PARTTYP_RANGE,
	PARTTYP_LIST
} PartitionByType;

typedef enum PartitionByVerbosity		/* control Partition messaging */
{
	PART_VERBO_NORMAL, 		/* normal (all messages) */
	PART_VERBO_NODISTRO, 	/* NO DISTRIBution policy messages */
	PART_VERBO_NOPARTNAME   /* NO distro or partition name messages
							   (for SET SUBPARTITION TEMPLATE) */
} PartitionByVerbosity;

typedef struct PartitionBy			/* the Partition By clause */
{
	NodeTag				type;
	PartitionByType		partType;
	List			   *keys;		/* key columns (Partition By ...) */
	List			   *keyopclass;	/* opclass for each key */
	Node			   *subPart;	/* optional subpartn (PartitionBy ptr) */
	Node			   *partSpec;	/* specification or template */
	Node			   *partDefault;/* DEFAULT partition (if exists) */
	int				    partDepth;	/* depth (starting at zero) */
	RangeVar		   *parentRel;	/* parent relation */
	bool				bKeepMe;    /* keep the top-level pby [nefarious] */
	int				    partQuiet;	/* PartitionByVerbosity */
	int					location;	/* token location, or -1 if unknown */
} PartitionBy;

/*
 * An element in a partition configuration. This represents a single clause --
 * or perhaps an expansion of a single clause.
 */
typedef struct PartitionElem
{
	NodeTag				type;
	char			   *partName;	/* partition name (optional) */
	Node			   *boundSpec;	/* boundary specification */
	Node			   *subSpec;	/* subpartition spec */
	bool                isDefault;	/* TRUE if default partition declaration */
	Node			   *storeAttr;	/* storage clause attributes */
	char			   *AddPartDesc;/* set by tablecmds.c:atpxAddPart */
	int					partno;		/* number of the partition element */
	long				rrand;		/* if not zero, "random" id for relname */
	List			   *colencs;	/* column encoding clauses */
	int					location;	/* token location, or -1 if unknown */
} PartitionElem;

typedef enum PartitionEdgeBounding
{
	PART_EDGE_UNSPECIFIED,
	PART_EDGE_INCLUSIVE,
	PART_EDGE_EXCLUSIVE
} PartitionEdgeBounding;

/* a "Range Item" is the "values" portition of a LIST partition, or
 * the "values" of a START, END, or EVERY spec in a RANGE partition */
typedef struct PartitionRangeItem
{
	NodeTag				type;
	List			   *partRangeVal;	/*  value */
	PartitionEdgeBounding partedge;		/* inclusive/exclusive ? */
	int					everycount;		/* if EVERY, how many in the set */
	int					location;		/* token location, or -1 if unknown */
} PartitionRangeItem;

/* partition boundary specification */
typedef struct PartitionBoundSpec
{
	NodeTag				type;
	Node			   *partStart;		/* start of range */
	Node			   *partEnd;		/* end */
	Node 			   *partEvery;		/* every specification */
	List 			   *everyGenList;	/* generated EVERY partitions */
	/* MPP-6297: check for WITH (tablename=name) clause */
	char			   *pWithTnameStr;	/* and disable EVERY if tname set */
	int					location;		/* token location, or -1 if unknown */
} PartitionBoundSpec;

/* VALUES clause specification */
typedef struct PartitionValuesSpec
{
	NodeTag				type;
	List			   *partValues;		/* VALUES clause for LIST partition */
	int					location;
} PartitionValuesSpec;

typedef struct PartitionSpec			/* a Partition Specification */
{
	NodeTag				type;
	List			   *partElem;		/* partition element list */
	List			   *enc_clauses;	/* ENCODING () clauses */
	Node			   *subSpec;		/* subpartition spec */
	bool				istemplate;
	int					location;		/* token location, or -1 if unknown */
} PartitionSpec;

typedef struct ExpandStmtSpec
{
	NodeTag				type;
	/* for ctas method */
	Oid					backendId;
} ExpandStmtSpec;

/* ----------------------
 *		Create/Drop TableSpace Statements
 * ----------------------
 */

typedef struct CreateTableSpaceStmt
{
	NodeTag		type;
	char	   *tablespacename;
	char	   *owner;
	char	   *location;
	List	   *options;
} CreateTableSpaceStmt;

typedef struct DropTableSpaceStmt
{
	NodeTag		type;
	char	   *tablespacename;
	bool		missing_ok;		/* skip error if missing? */
} DropTableSpaceStmt;

typedef struct AlterTableSpaceOptionsStmt
{
	NodeTag		type;
	char	   *tablespacename;
	List	   *options;
	bool		isReset;
} AlterTableSpaceOptionsStmt;

typedef struct AlterTableMoveAllStmt
{
	NodeTag		type;
	char	   *orig_tablespacename;
	ObjectType	objtype;		/* Object type to move */
	List	   *roles;			/* List of roles to move objects of */
	char	   *new_tablespacename;
	bool		nowait;
} AlterTableMoveAllStmt;

/* ----------------------
 *		Create/Alter Extension Statements
 * ----------------------
 */

typedef enum CreateExtensionState
{
	CREATE_EXTENSION_INIT,		/* not start to create extension */
	CREATE_EXTENSION_BEGIN,     /* start to create extension */
	CREATE_EXTENSION_END		/* finish to create extension */
} CreateExtensionState;

typedef enum UpdateExtensionState
{
	UPDATE_EXTENSION_INIT,		/* not start to update extension */
	UPDATE_EXTENSION_BEGIN,     /* start to update extension */
	UPDATE_EXTENSION_END		/* finish to update extension */
} UpdateExtensionState;

typedef struct CreateExtensionStmt
{
	NodeTag		type;
	char	   *extname;
	bool		if_not_exists;	/* just do nothing if it already exists? */
	List	   *options;		/* List of DefElem nodes */
	CreateExtensionState create_ext_state;		/* create extension state */
} CreateExtensionStmt;

/* Only used for ALTER EXTENSION UPDATE; later might need an action field */
typedef struct AlterExtensionStmt
{
	NodeTag		type;
	char	   *extname;
	List	   *options;		/* List of DefElem nodes */
	UpdateExtensionState update_ext_state;	/* update extension state, only used for ALTER EXTENSION UPDATE */
} AlterExtensionStmt;

typedef struct AlterExtensionContentsStmt
{
	NodeTag		type;
	char	   *extname;		/* Extension's name */
	int			action;			/* +1 = add object, -1 = drop object */
	ObjectType	objtype;		/* Object's type */
	List	   *objname;		/* Qualified name of the object */
	List	   *objargs;		/* Arguments if needed (eg, for functions) */
} AlterExtensionContentsStmt;

/* ----------------------
 *		Create/Alter FOREIGN DATA WRAPPER Statements
 * ----------------------
 */

typedef struct CreateFdwStmt
{
	NodeTag		type;
	char	   *fdwname;		/* foreign-data wrapper name */
	List	   *func_options;	/* HANDLER/VALIDATOR options */
	List	   *options;		/* generic options to FDW */
} CreateFdwStmt;

typedef struct AlterFdwStmt
{
	NodeTag		type;
	char	   *fdwname;		/* foreign-data wrapper name */
	List	   *func_options;	/* HANDLER/VALIDATOR options */
	List	   *options;		/* generic options to FDW */
} AlterFdwStmt;

/* ----------------------
 *		Create/Alter FOREIGN SERVER Statements
 * ----------------------
 */

typedef struct CreateForeignServerStmt
{
	NodeTag		type;
	char	   *servername;		/* server name */
	char	   *servertype;		/* optional server type */
	char	   *version;		/* optional server version */
	char	   *fdwname;		/* FDW name */
	List	   *options;		/* generic options to server */
} CreateForeignServerStmt;

typedef struct AlterForeignServerStmt
{
	NodeTag		type;
	char	   *servername;		/* server name */
	char	   *version;		/* optional server version */
	List	   *options;		/* generic options to server */
	bool		has_version;	/* version specified */
} AlterForeignServerStmt;

/* ----------------------
 *		Create FOREIGN TABLE Statements
 * ----------------------
 */

typedef struct CreateForeignTableStmt
{
	CreateStmt	base;
	char	   *servername;
	List	   *options;
} CreateForeignTableStmt;

/* ----------------------
 *		Create/Drop USER MAPPING Statements
 * ----------------------
 */

typedef struct CreateUserMappingStmt
{
	NodeTag		type;
	char	   *username;		/* username or PUBLIC/CURRENT_USER */
	char	   *servername;		/* server name */
	List	   *options;		/* generic options to server */
} CreateUserMappingStmt;

typedef struct AlterUserMappingStmt
{
	NodeTag		type;
	char	   *username;		/* username or PUBLIC/CURRENT_USER */
	char	   *servername;		/* server name */
	List	   *options;		/* generic options to server */
} AlterUserMappingStmt;

typedef struct DropUserMappingStmt
{
	NodeTag		type;
	char	   *username;		/* username or PUBLIC/CURRENT_USER */
	char	   *servername;		/* server name */
	bool		missing_ok;		/* ignore missing mappings */
} DropUserMappingStmt;

/* ----------------------
 *		Create TRIGGER Statement
 * ----------------------
 */
typedef struct CreateTrigStmt
{
	NodeTag		type;
	char	   *trigname;		/* TRIGGER's name */
	RangeVar   *relation;		/* relation trigger is on */
	List	   *funcname;		/* qual. name of function to call */
	List	   *args;			/* list of (T_String) Values or NIL */
	bool		row;			/* ROW/STATEMENT */
	/* timing uses the TRIGGER_TYPE bits defined in catalog/pg_trigger.h */
	int16		timing;			/* BEFORE, AFTER, or INSTEAD */
	/* events uses the TRIGGER_TYPE bits defined in catalog/pg_trigger.h */
	int16		events;			/* "OR" of INSERT/UPDATE/DELETE/TRUNCATE */
	List	   *columns;		/* column names, or NIL for all columns */
	Node	   *whenClause;		/* qual expression, or NULL if none */
	bool		isconstraint;	/* This is a constraint trigger */
	/* The remaining fields are only used for constraint triggers */
	bool		deferrable;		/* [NOT] DEFERRABLE */
	bool		initdeferred;	/* INITIALLY {DEFERRED|IMMEDIATE} */
	RangeVar   *constrrel;		/* opposite relation, if RI trigger */
	Oid			trigOid;
} CreateTrigStmt;

/* ----------------------
 *		Create EVENT TRIGGER Statement
 * ----------------------
 */
typedef struct CreateEventTrigStmt
{
	NodeTag		type;
	char	   *trigname;		/* TRIGGER's name */
	char	   *eventname;		/* event's identifier */
	List	   *whenclause;		/* list of DefElems indicating filtering */
	List	   *funcname;		/* qual. name of function to call */
} CreateEventTrigStmt;

/* ----------------------
 *		Alter EVENT TRIGGER Statement
 * ----------------------
 */
typedef struct AlterEventTrigStmt
{
	NodeTag		type;
	char	   *trigname;		/* TRIGGER's name */
	char		tgenabled;		/* trigger's firing configuration WRT
								 * session_replication_role */
} AlterEventTrigStmt;

/* ----------------------
 *		Create/Drop PROCEDURAL LANGUAGE Statements
 *		Create PROCEDURAL LANGUAGE Statements
 * ----------------------
 */
typedef struct CreatePLangStmt
{
	NodeTag		type;
	bool		replace;		/* T => replace if already exists */
	char	   *plname;			/* PL name */
	List	   *plhandler;		/* PL call handler function (qual. name) */
	List	   *plinline;		/* optional inline function (qual. name) */
	List	   *plvalidator;	/* optional validator function (qual. name) */
	bool		pltrusted;		/* PL is trusted */
} CreatePLangStmt;

/* ----------------------
 *	Create/Alter/Drop Resource Queue Statements
 * ----------------------
 */
typedef struct CreateQueueStmt
{
	NodeTag		type;
	char	   *queue;			/* resource queue name */
	List	   *options;		/* List of DefElem nodes */
} CreateQueueStmt;

typedef struct AlterQueueStmt
{
	NodeTag		type;
	char	   *queue;			/* resource queue  name */
	List	   *options;		/* List of DefElem nodes */
} AlterQueueStmt;

typedef struct DropQueueStmt
{
	NodeTag		type;
	char	   *queue;			/* resource queue to remove */
} DropQueueStmt;

/* ----------------------
 *	Create/Alter/Drop Resource Group Statements
 * ----------------------
 */
typedef struct CreateResourceGroupStmt
{
	NodeTag		type;
	char	   *name;			/* resource group name */
	List	   *options;		/* List of DefElem nodes */
} CreateResourceGroupStmt;

typedef struct DropResourceGroupStmt
{
	NodeTag		type;
	char	   *name;			/* resource group to remove */
} DropResourceGroupStmt;

typedef struct AlterResourceGroupStmt
{
	NodeTag		type;
	char	   *name;			/* resource group to alter */
	List	   *options;		/* List of DefElem nodes */
} AlterResourceGroupStmt;

/* ----------------------
 *	Create/Alter/Drop Role Statements
 *
 * Note: these node types are also used for the backwards-compatible
 * Create/Alter/Drop User/Group statements.  In the ALTER and DROP cases
 * there's really no need to distinguish what the original spelling was,
 * but for CREATE we mark the type because the defaults vary.
 * ----------------------
 */
typedef enum RoleStmtType
{
	ROLESTMT_ROLE,
	ROLESTMT_USER,
	ROLESTMT_GROUP
} RoleStmtType;

typedef struct CreateRoleStmt
{
	NodeTag		type;
	RoleStmtType stmt_type;		/* ROLE/USER/GROUP */
	char	   *role;			/* role name */
	List	   *options;		/* List of DefElem nodes */
} CreateRoleStmt;

typedef struct AlterRoleStmt
{
	NodeTag		type;
	char	   *role;			/* role name */
	List	   *options;		/* List of DefElem nodes */
	int			action;			/* +1 = add members, -1 = drop members */
} AlterRoleStmt;

typedef struct AlterRoleSetStmt
{
	NodeTag		type;
	char	   *role;			/* role name */
	char	   *database;		/* database name, or NULL */
	VariableSetStmt *setstmt;	/* SET or RESET subcommand */
} AlterRoleSetStmt;

typedef struct DropRoleStmt
{
	NodeTag		type;
	List	   *roles;			/* List of roles to remove */
	bool		missing_ok;		/* skip error if a role is missing? */
} DropRoleStmt;

typedef struct DenyLoginPoint
{
	NodeTag			type;
	Value 		   *day;
	Value		   *time;
} DenyLoginPoint;

typedef struct DenyLoginInterval
{
	NodeTag			type;
	DenyLoginPoint *start;
	DenyLoginPoint *end;
} DenyLoginInterval;


/* ----------------------
 *		{Create|Alter} SEQUENCE Statement
 * ----------------------
 */

typedef struct CreateSeqStmt
{
	NodeTag		type;
	RangeVar   *sequence;		/* the sequence to create */
	List	   *options;
	Oid			ownerId;		/* ID of owner, or InvalidOid for default */
} CreateSeqStmt;

typedef struct AlterSeqStmt
{
	NodeTag		type;
	RangeVar   *sequence;		/* the sequence to alter */
	List	   *options;
	bool		missing_ok;		/* skip error if a role is missing? */
} AlterSeqStmt;

/* ----------------------
 *		Create {Aggregate|Operator|Type|Protocol} Statement
 * ----------------------
 */
typedef struct DefineStmt
{
	NodeTag		type;
	ObjectType	kind;			/* aggregate, operator, type, protocol */
	bool		oldstyle;		/* hack to signal old CREATE AGG syntax */
	List	   *defnames;		/* qualified name (list of Value strings) */
	List	   *args;			/* a list of TypeName (if needed) */
	List	   *definition;		/* a list of DefElem */
	bool		trusted;		/* used only for PROTOCOL as this point */
} DefineStmt;

/* ----------------------
 *		Create Domain Statement
 * ----------------------
 */
typedef struct CreateDomainStmt
{
	NodeTag		type;
	List	   *domainname;		/* qualified name (list of Value strings) */
	TypeName   *typeName;		/* the base type */
	CollateClause *collClause;	/* untransformed COLLATE spec, if any */
	List	   *constraints;	/* constraints (list of Constraint nodes) */
} CreateDomainStmt;

/* ----------------------
 *		Create Operator Class Statement
 * ----------------------
 */
typedef struct CreateOpClassStmt
{
	NodeTag		type;
	List	   *opclassname;	/* qualified name (list of Value strings) */
	List	   *opfamilyname;	/* qualified name (ditto); NIL if omitted */
	char	   *amname;			/* name of index AM opclass is for */
	TypeName   *datatype;		/* datatype of indexed column */
	List	   *items;			/* List of CreateOpClassItem nodes */
	bool		isDefault;		/* Should be marked as default for type? */
} CreateOpClassStmt;

#define OPCLASS_ITEM_OPERATOR		1
#define OPCLASS_ITEM_FUNCTION		2
#define OPCLASS_ITEM_STORAGETYPE	3

typedef struct CreateOpClassItem
{
	NodeTag		type;
	int			itemtype;		/* see codes above */
	/* fields used for an operator or function item: */
	List	   *name;			/* operator or function name */
	List	   *args;			/* argument types */
	int			number;			/* strategy num or support proc num */
	List	   *order_family;	/* only used for ordering operators */
	List	   *class_args;		/* only used for functions */
	/* fields used for a storagetype item: */
	TypeName   *storedtype;		/* datatype stored in index */
} CreateOpClassItem;

/* ----------------------
 *		Create Operator Family Statement
 * ----------------------
 */
typedef struct CreateOpFamilyStmt
{
	NodeTag		type;
	List	   *opfamilyname;	/* qualified name (list of Value strings) */
	char	   *amname;			/* name of index AM opfamily is for */
} CreateOpFamilyStmt;

/* ----------------------
 *		Alter Operator Family Statement
 * ----------------------
 */
typedef struct AlterOpFamilyStmt
{
	NodeTag		type;
	List	   *opfamilyname;	/* qualified name (list of Value strings) */
	char	   *amname;			/* name of index AM opfamily is for */
	bool		isDrop;			/* ADD or DROP the items? */
	List	   *items;			/* List of CreateOpClassItem nodes */
} AlterOpFamilyStmt;

/* ----------------------
 *		DROP Statement, applies to:
 *        Table, External Table, Sequence, View, Index, Type, Domain,
 *        Conversion, Schema
 * ----------------------
 */

typedef struct DropStmt
{
	NodeTag		type;
	List	   *objects;		/* list of sublists of names (as Values) */
	List	   *arguments;		/* list of sublists of arguments (as Values) */
	ObjectType	removeType;		/* object type */
	DropBehavior behavior;		/* RESTRICT or CASCADE behavior */
	bool		missing_ok;		/* skip error if object is missing? */
	bool		bAllowPartn;	/* allow action on a partition */
	bool		concurrent;		/* drop index concurrently? */
} DropStmt;

/* ----------------------
 *				Truncate Table Statement
 * ----------------------
 */
typedef struct TruncateStmt
{
	NodeTag		type;
	List	   *relations;		/* relations (RangeVars) to be truncated */
	bool		restart_seqs;	/* restart owned sequences? */
	DropBehavior behavior;		/* RESTRICT or CASCADE behavior */
} TruncateStmt;

/* ----------------------
 *				Comment On Statement
 * ----------------------
 */
typedef struct CommentStmt
{
	NodeTag		type;
	ObjectType	objtype;		/* Object's type */
	List	   *objname;		/* Qualified name of the object */
	List	   *objargs;		/* Arguments if needed (eg, for functions) */
	char	   *comment;		/* Comment to insert, or NULL to remove */
} CommentStmt;

/* ----------------------
 *				SECURITY LABEL Statement
 * ----------------------
 */
typedef struct SecLabelStmt
{
	NodeTag		type;
	ObjectType	objtype;		/* Object's type */
	List	   *objname;		/* Qualified name of the object */
	List	   *objargs;		/* Arguments if needed (eg, for functions) */
	char	   *provider;		/* Label provider (or NULL) */
	char	   *label;			/* New security label to be assigned */
} SecLabelStmt;

/* ----------------------
 *		Declare Cursor Statement
 *
 * Note: the "query" field of DeclareCursorStmt is only used in the raw grammar
 * output.  After parse analysis it's set to null, and the Query points to the
 * DeclareCursorStmt, not vice versa.
 * ----------------------
 */
#define CURSOR_OPT_BINARY		0x0001	/* BINARY */
#define CURSOR_OPT_SCROLL		0x0002	/* SCROLL explicitly given */
#define CURSOR_OPT_NO_SCROLL	0x0004	/* NO SCROLL explicitly given */
#define CURSOR_OPT_INSENSITIVE	0x0008	/* INSENSITIVE */
#define CURSOR_OPT_HOLD			0x0010	/* WITH HOLD */
/* these planner-control flags do not correspond to any SQL grammar: */
#define CURSOR_OPT_FAST_PLAN	0x0020	/* prefer fast-start plan */
#define CURSOR_OPT_GENERIC_PLAN 0x0040	/* force use of generic plan */
#define CURSOR_OPT_CUSTOM_PLAN	0x0080	/* force use of custom plan */

/*
 * This is used to request the planner to create a plan that's updatable with
 * CURRENT OF. It can be passed to SPI_prepare_cursor.
 */
#define CURSOR_OPT_UPDATABLE	0x0200	/* updateable with CURRENT OF, if possible */
#define CURSOR_OPT_PARALLEL_RETRIEVE 0x0400	/* Cursor for parallel retrieving */

typedef struct DeclareCursorStmt
{
	NodeTag		type;
	char	   *portalname;		/* name of the portal (cursor) */
	int			options;		/* bitmask of options (see above) */
	Node	   *query;			/* the raw SELECT query */
} DeclareCursorStmt;

/* ----------------------
 *		Close Portal Statement
 * ----------------------
 */
typedef struct ClosePortalStmt
{
	NodeTag		type;
	char	   *portalname;		/* name of the portal (cursor) */
	/* NULL means CLOSE ALL */
} ClosePortalStmt;

/* ----------------------
 *		Fetch Statement (also Move)
 * ----------------------
 */
typedef enum FetchDirection
{
	/* for these, howMany is how many rows to fetch; FETCH_ALL means ALL */
	FETCH_FORWARD,
	FETCH_BACKWARD,
	/* for these, howMany indicates a position; only one row is fetched */
	FETCH_ABSOLUTE,
	FETCH_RELATIVE
} FetchDirection;

#define FETCH_ALL	INT64CONST(0x7FFFFFFFFFFFFFFF)

typedef struct FetchStmt
{
	NodeTag		type;
	FetchDirection direction;	/* see above */
	int64		howMany;		/* number of rows, or position argument */
	char	   *portalname;		/* name of portal (cursor) */
	bool		ismove;			/* TRUE if MOVE */
} FetchStmt;

/* ----------------------
 *		Create Index Statement
 *
 * This represents creation of an index and/or an associated constraint.
 * If isconstraint is true, we should create a pg_constraint entry along
 * with the index.  But if indexOid isn't InvalidOid, we are not creating an
 * index, just a UNIQUE/PKEY constraint using an existing index.  isconstraint
 * must always be true in this case, and the fields describing the index
 * properties are empty.
 * ----------------------
 */
typedef struct IndexStmt
{
	NodeTag		type;
	char	   *idxname;		/* name of new index, or NULL for default */
	RangeVar   *relation;		/* relation to build index on */
	Oid			relationOid;
	char	   *accessMethod;	/* name of access method (eg. btree) */
	char	   *tableSpace;		/* tablespace, or NULL for default */
	List	   *indexParams;	/* columns to index: a list of IndexElem */
	List	   *options;		/* WITH clause options: a list of DefElem */
	Node	   *whereClause;	/* qualification (partial-index predicate) */
	List	   *excludeOpNames; /* exclusion operator names, or NIL if none */
	char	   *idxcomment;		/* comment to apply to index, or NULL */
	Oid			indexOid;		/* OID of an existing index, if any */
	bool		is_part_child;	/* in service of a part of a partition? */
	Oid			oldNode;		/* relfilenode of existing storage, if any */
	bool		unique;			/* is index unique? */
	bool		primary;		/* is index a primary key? */
	bool		isconstraint;	/* is it for a pkey/unique constraint? */
	bool		deferrable;		/* is the constraint DEFERRABLE? */
	bool		initdeferred;	/* is the constraint INITIALLY DEFERRED? */
	bool		concurrent;		/* should this be a concurrent index build? */
	bool		is_split_part;	/* Is this for SPLIT PARTITION command? */
	Oid			parentIndexId;	/* attach to a parent index if set */
	Oid			parentConstraintId;		/* attach to a parent constraint if set */
} IndexStmt;

/* ----------------------
 *		Create Function Statement
 * ----------------------
 */
typedef struct CreateFunctionStmt
{
	NodeTag		type;
	bool		replace;		/* T => replace if already exists */
	List	   *funcname;		/* qualified name of function to create */
	List	   *parameters;		/* a list of FunctionParameter */
	TypeName   *returnType;		/* the return type */
	List	   *options;		/* a list of DefElem */
	List	   *withClause;		/* a list of DefElem */
} CreateFunctionStmt;

typedef enum FunctionParameterMode
{
	/* the assigned enum values appear in pg_proc, don't change 'em! */
	FUNC_PARAM_IN = 'i',		/* input only */
	FUNC_PARAM_OUT = 'o',		/* output only */
	FUNC_PARAM_INOUT = 'b',		/* both */
	FUNC_PARAM_VARIADIC = 'v',	/* variadic (always input) */
	FUNC_PARAM_TABLE = 't'		/* table function output column */
} FunctionParameterMode;

typedef struct FunctionParameter
{
	NodeTag		type;
	char	   *name;			/* parameter name, or NULL if not given */
	TypeName   *argType;		/* TypeName for parameter type */
	FunctionParameterMode mode; /* IN/OUT/etc */
	Node	   *defexpr;		/* raw default expr, or NULL if not given */
} FunctionParameter;

typedef struct AlterFunctionStmt
{
	NodeTag		type;
	FuncWithArgs *func;			/* name and args of function */
	List	   *actions;		/* list of DefElem */
} AlterFunctionStmt;

/* ----------------------
 *		DO Statement
 *
 * DoStmt is the raw parser output, InlineCodeBlock is the execution-time API
 * ----------------------
 */
typedef struct DoStmt
{
	NodeTag		type;
	List	   *args;			/* List of DefElem nodes */
} DoStmt;

typedef struct InlineCodeBlock
{
	NodeTag		type;
	char	   *source_text;	/* source text of anonymous code block */
	Oid			langOid;		/* OID of selected language */
	bool		langIsTrusted;	/* trusted property of the language */
} InlineCodeBlock;

/* ----------------------
 *		Alter Object Rename Statement
 * ----------------------
 */
typedef struct RenameStmt
{
	NodeTag		type;
	ObjectType	renameType;		/* OBJECT_TABLE, OBJECT_COLUMN, etc */
	ObjectType	relationType;	/* if column name, associated relation type */
	RangeVar   *relation;		/* in case it's a table */
	Oid			objid;			/* in case it's a table */
	List	   *object;			/* in case it's some other object */
	List	   *objarg;			/* argument types, if applicable */
	char	   *subname;		/* name of contained object (column, rule,
								 * trigger, etc) */
	char	   *newname;		/* the new name */
	DropBehavior behavior;		/* RESTRICT or CASCADE behavior */

	bool		bAllowPartn;	/* allow action on a partition */
	bool		missing_ok;		/* skip error if missing? */
} RenameStmt;

/* ----------------------
 *		ALTER object SET SCHEMA Statement
 * ----------------------
 */
typedef struct AlterObjectSchemaStmt
{
	NodeTag		type;
	ObjectType objectType;		/* OBJECT_TABLE, OBJECT_TYPE, etc */
	RangeVar   *relation;		/* in case it's a table */
	List	   *object;			/* in case it's some other object */
	List	   *objarg;			/* argument types, if applicable */
	char	   *newschema;		/* the new schema */
	bool		missing_ok;		/* skip error if missing? */
} AlterObjectSchemaStmt;

/* ----------------------
 *		Alter Object Owner Statement
 * ----------------------
 */
typedef struct AlterOwnerStmt
{
	NodeTag		type;
	ObjectType objectType;		/* OBJECT_TABLE, OBJECT_TYPE, etc */
	RangeVar   *relation;		/* in case it's a table */
	List	   *object;			/* in case it's some other object */
	List	   *objarg;			/* argument types, if applicable */
	char	   *newowner;		/* the new owner */
} AlterOwnerStmt;

/* ----------------------
 * ALTER TYPE ... SET DEFAULT ENCODING ()
 * ----------------------
 */
typedef struct AlterTypeStmt
{
	NodeTag		type;
	List	   *typeName;
	List	   *encoding;
} AlterTypeStmt;

/* ----------------------
 *		Create Rule Statement
 * ----------------------
 */
typedef struct RuleStmt
{
	NodeTag		type;
	RangeVar   *relation;		/* relation the rule is for */
	char	   *rulename;		/* name of the rule */
	Node	   *whereClause;	/* qualifications */
	CmdType		event;			/* SELECT, INSERT, etc */
	bool		instead;		/* is a 'do instead'? */
	List	   *actions;		/* the action statements */
	bool		replace;		/* OR REPLACE */
} RuleStmt;

/* ----------------------
 *		Notify Statement
 * ----------------------
 */
typedef struct NotifyStmt
{
	NodeTag		type;
	char	   *conditionname;	/* condition name to notify */
	char	   *payload;		/* the payload string, or NULL if none */
} NotifyStmt;

/* ----------------------
 *		Listen Statement
 * ----------------------
 */
typedef struct ListenStmt
{
	NodeTag		type;
	char	   *conditionname;	/* condition name to listen on */
} ListenStmt;

/* ----------------------
 *		Unlisten Statement
 * ----------------------
 */
typedef struct UnlistenStmt
{
	NodeTag		type;
	char	   *conditionname;	/* name to unlisten on, or NULL for all */
} UnlistenStmt;

/* ----------------------
 *		{Begin|Commit|Rollback} Transaction Statement
 * ----------------------
 */
typedef enum TransactionStmtKind
{
	TRANS_STMT_BEGIN,
	TRANS_STMT_START,			/* semantically identical to BEGIN */
	TRANS_STMT_COMMIT,
	TRANS_STMT_ROLLBACK,
	TRANS_STMT_SAVEPOINT,
	TRANS_STMT_RELEASE,
	TRANS_STMT_ROLLBACK_TO,
	TRANS_STMT_PREPARE,
	TRANS_STMT_COMMIT_PREPARED,
	TRANS_STMT_ROLLBACK_PREPARED
} TransactionStmtKind;

typedef struct TransactionStmt
{
	NodeTag		type;
	TransactionStmtKind kind;	/* see above */
	List	   *options;		/* for BEGIN/START and savepoint commands */
	char	   *gid;			/* for two-phase-commit related commands */
} TransactionStmt;

/* ----------------------
 *		Create Type Statement, composite types
 * ----------------------
 */
typedef struct CompositeTypeStmt
{
	NodeTag		type;
	RangeVar   *typevar;		/* the composite type to be created */
	List	   *coldeflist;		/* list of ColumnDef nodes */
} CompositeTypeStmt;

/* ----------------------
 *		Create Type Statement, enum types
 * ----------------------
 */
typedef struct CreateEnumStmt
{
	NodeTag		type;
	List	   *typeName;		/* qualified name (list of Value strings) */
	List	   *vals;			/* enum values (list of Value strings) */
} CreateEnumStmt;

/* ----------------------
 *		Create Type Statement, range types
 * ----------------------
 */
typedef struct CreateRangeStmt
{
	NodeTag		type;
	List	   *typeName;		/* qualified name (list of Value strings) */
	List	   *params;			/* range parameters (list of DefElem) */
} CreateRangeStmt;

/* ----------------------
 *		Alter Type Statement, enum types
 * ----------------------
 */
typedef struct AlterEnumStmt
{
	NodeTag		type;
	List	   *typeName;		/* qualified name (list of Value strings) */
	char	   *newVal;			/* new enum value's name */
	char	   *newValNeighbor; /* neighboring enum value, if specified */
	bool		newValIsAfter;	/* place new enum value after neighbor? */
	bool		skipIfExists;	/* no error if label already exists */
} AlterEnumStmt;

/* ----------------------
 *		Create View Statement
 * ----------------------
 */
typedef enum ViewCheckOption
{
	NO_CHECK_OPTION,
	LOCAL_CHECK_OPTION,
	CASCADED_CHECK_OPTION
} ViewCheckOption;

typedef struct ViewStmt
{
	NodeTag		type;
	RangeVar   *view;			/* the view to be created */
	List	   *aliases;		/* target column names */
	Node	   *query;			/* the SELECT query */
	bool		replace;		/* replace an existing view? */
	List	   *options;		/* options from WITH clause */
	ViewCheckOption withCheckOption;	/* WITH CHECK OPTION */
} ViewStmt;

/* ----------------------
 *		Load Statement
 * ----------------------
 */
typedef struct LoadStmt
{
	NodeTag		type;
	char	   *filename;		/* file to load */
} LoadStmt;

/* ----------------------
 *		Createdb Statement
 * ----------------------
 */
typedef struct CreatedbStmt
{
	NodeTag		type;
	char	   *dbname;			/* name of database to create */
	List	   *options;		/* List of DefElem nodes */
} CreatedbStmt;

/* ----------------------
 *	Alter Database
 * ----------------------
 */
typedef struct AlterDatabaseStmt
{
	NodeTag		type;
	char	   *dbname;			/* name of database to alter */
	List	   *options;		/* List of DefElem nodes */
} AlterDatabaseStmt;

typedef struct AlterDatabaseSetStmt
{
	NodeTag		type;
	char	   *dbname;			/* database name */
	VariableSetStmt *setstmt;	/* SET or RESET subcommand */
} AlterDatabaseSetStmt;

/* ----------------------
 *		Dropdb Statement
 * ----------------------
 */
typedef struct DropdbStmt
{
	NodeTag		type;
	char	   *dbname;			/* database to drop */
	bool		missing_ok;		/* skip error if db is missing? */
} DropdbStmt;

/* ----------------------
 *		Alter System Statement
 * ----------------------
 */
typedef struct AlterSystemStmt
{
	NodeTag		type;
	VariableSetStmt *setstmt;	/* SET subcommand */
} AlterSystemStmt;

/* ----------------------
 *		Cluster Statement (support pbrown's cluster index implementation)
 * ----------------------
 */
typedef struct ClusterStmt
{
	NodeTag		type;
	RangeVar   *relation;		/* relation being indexed, or NULL if all */
	char	   *indexname;		/* original index defined */
	bool		verbose;		/* print progress info */
} ClusterStmt;

/* ----------------------
 *		Vacuum and Analyze Statements
 *
 * Even though these are nominally two statements, it's convenient to use
 * just one node type for both.  Note that at least one of VACOPT_VACUUM
 * and VACOPT_ANALYZE must be set in options.  VACOPT_FREEZE is an internal
 * convenience for the grammar and is not examined at runtime --- the
 * freeze_min_age and freeze_table_age fields are what matter.
 * ----------------------
 */
typedef enum VacuumOption
{
	VACOPT_VACUUM = 1 << 0,		/* do VACUUM */
	VACOPT_ANALYZE = 1 << 1,	/* do ANALYZE */
	VACOPT_VERBOSE = 1 << 2,	/* print progress info */
	VACOPT_FREEZE = 1 << 3,		/* FREEZE option */
	VACOPT_FULL = 1 << 4,		/* FULL (non-concurrent) vacuum */
	VACOPT_NOWAIT = 1 << 5,		/* don't wait to get lock (autovacuum only) */
	VACOPT_ROOTONLY = 1 << 6,	/* only ANALYZE root partition tables */
	VACOPT_FULLSCAN = 1 << 7	/* ANALYZE using full table scan */
} VacuumOption;

typedef enum AOVacuumPhase
{
	AOVAC_NONE = 0,
	AOVAC_PREPARE,
	AOVAC_COMPACT,
	AOVAC_DROP,
	AOVAC_CLEANUP
} AOVacuumPhase;

typedef struct VacuumStmt
{
	NodeTag		type;
	int			options;		/* OR of VacuumOption flags */
	int			freeze_min_age; /* min freeze age, or -1 to use default */
	int			freeze_table_age;		/* age at which to scan whole table */
	int			multixact_freeze_min_age;		/* min multixact freeze age,
												 * or -1 to use default */
	int			multixact_freeze_table_age;		/* multixact age at which to
												 * scan whole table */
	RangeVar   *relation;		/* single table to process, or NULL */
	List	   *va_cols;		/* list of column names, or NIL for all */

	/* Object IDs for relations which expand from partition definitions */
	List	   *expanded_relids;

	bool skip_twophase;
	/*
	 * AO segment file num to compact (integer).
	 */
	List *appendonly_compaction_segno;

	/*
	 * AO table meta data from the dispatcher.
	 * Used during compaction.
	 *
	 * Unless appendonly_compaction_vacuum_cleanup is specified, it should
	 * only contain a single entry. If the entry is
	 * APPENDONLY_COMPACTION_SEGNO_INVALID, it is a pseudo compaction
	 * transaction. If the list has no entries, it is a drop transaction.
	 */
	List *appendonly_compaction_insert_segno;

	/*
	 * MPP-24168: If the appendonly table is empty, we should vacuum
	 * auxiliary tables in prepare phase itself.  Othewise, age of
	 * auxiliary heap relations never gets updated.
	 */
	bool appendonly_relation_empty;

	AOVacuumPhase appendonly_phase;

	/* invoked via automatic statistic collection */
	bool auto_stats;
} VacuumStmt;

/* ----------------------
 *		Explain Statement
 *
 * The "query" field is either a raw parse tree (SelectStmt, InsertStmt, etc)
 * or a Query node if parse analysis has been done.  Note that rewriting and
 * planning of the query are always postponed until execution of EXPLAIN.
 * ----------------------
 */
typedef struct ExplainStmt
{
	NodeTag		type;
	Node	   *query;			/* the query (see comments above) */
	List	   *options;		/* list of DefElem nodes */
} ExplainStmt;

/* ----------------------
 *		CREATE TABLE AS Statement (a/k/a SELECT INTO)
 *
 * A query written as CREATE TABLE AS will produce this node type natively.
 * A query written as SELECT ... INTO will be transformed to this form during
 * parse analysis.
 * A query written as CREATE MATERIALIZED view will produce this node type,
 * during parse analysis, since it needs all the same data.
 *
 * The "query" field is handled similarly to EXPLAIN, though note that it
 * can be a SELECT or an EXECUTE, but not other DML statements.
 * ----------------------
 */
typedef struct CreateTableAsStmt
{
	NodeTag		type;
	Node	   *query;			/* the query (see comments above) */
	IntoClause *into;			/* destination table */
	ObjectType	relkind;		/* OBJECT_TABLE or OBJECT_MATVIEW */
	bool		is_select_into; /* it was written as SELECT INTO */
} CreateTableAsStmt;

/* ----------------------
 *		REFRESH MATERIALIZED VIEW Statement
 * ----------------------
 */
typedef struct RefreshMatViewStmt
{
	NodeTag		type;
	bool		concurrent;		/* allow concurrent access? */
	bool		skipData;		/* true for WITH NO DATA */
	RangeVar   *relation;		/* relation to insert into */
} RefreshMatViewStmt;

/* ----------------------
 * Checkpoint Statement
 * ----------------------
 */
typedef struct CheckPointStmt
{
	NodeTag		type;
} CheckPointStmt;

/* ----------------------
 * Discard Statement
 * ----------------------
 */

typedef enum DiscardMode
{
	DISCARD_ALL,
	DISCARD_PLANS,
	DISCARD_SEQUENCES,
	DISCARD_TEMP
} DiscardMode;

typedef struct DiscardStmt
{
	NodeTag		type;
	DiscardMode target;
} DiscardStmt;

/* ----------------------
 *		LOCK Statement
 * ----------------------
 */
typedef struct LockStmt
{
	NodeTag		type;
	List	   *relations;		/* relations to lock */
	int			mode;			/* lock mode */
	bool		nowait;			/* no wait mode */
	bool		masteronly;		/* GPDB: lock only on master */
} LockStmt;

/* ----------------------
 *		SET CONSTRAINTS Statement
 * ----------------------
 */
typedef struct ConstraintsSetStmt
{
	NodeTag		type;
	List	   *constraints;	/* List of names as RangeVars */
	bool		deferred;
} ConstraintsSetStmt;

/* ----------------------
 *		REINDEX Statement
 * ----------------------
 */
typedef struct ReindexStmt
{
	NodeTag		type;
	ObjectType	kind;			/* OBJECT_INDEX, OBJECT_TABLE, etc. */
	RangeVar   *relation;		/* Table or index to reindex */
	const char *name;			/* name of database to reindex */
	bool		do_system;		/* include system tables in database case */
	bool		do_user;		/* include user tables in database case */
	Oid			relid;			/* oid of TABLE, used by QE */
} ReindexStmt;

/* ----------------------
 *		CREATE CONVERSION Statement
 * ----------------------
 */
typedef struct CreateConversionStmt
{
	NodeTag		type;
	List	   *conversion_name;	/* Name of the conversion */
	char	   *for_encoding_name;		/* source encoding name */
	char	   *to_encoding_name;		/* destination encoding name */
	List	   *func_name;		/* qualified conversion function name */
	bool		def;			/* is this a default conversion? */
} CreateConversionStmt;

/* ----------------------
 *	CREATE CAST Statement
 * ----------------------
 */
typedef struct CreateCastStmt
{
	NodeTag		type;
	TypeName   *sourcetype;
	TypeName   *targettype;
	FuncWithArgs *func;
	CoercionContext context;
	bool		inout;
} CreateCastStmt;

/* ----------------------
 *		PREPARE Statement
 * ----------------------
 */
typedef struct PrepareStmt
{
	NodeTag		type;
	char	   *name;			/* Name of plan, arbitrary */
	List	   *argtypes;		/* Types of parameters (List of TypeName) */
	Node	   *query;			/* The query itself (as a raw parsetree) */
} PrepareStmt;


/* ----------------------
 *		EXECUTE Statement
 * ----------------------
 */

typedef struct ExecuteStmt
{
	NodeTag		type;
	char	   *name;			/* The name of the plan to execute */
	List	   *params;			/* Values to assign to parameters */
} ExecuteStmt;


/* ----------------------
 *		DEALLOCATE Statement
 * ----------------------
 */
typedef struct DeallocateStmt
{
	NodeTag		type;
	char	   *name;			/* The name of the plan to remove */
	/* NULL means DEALLOCATE ALL */
} DeallocateStmt;

/*
 *		DROP OWNED statement
 */
typedef struct DropOwnedStmt
{
	NodeTag		type;
	List	   *roles;
	DropBehavior behavior;
} DropOwnedStmt;

/*
 *		REASSIGN OWNED statement
 */
typedef struct ReassignOwnedStmt
{
	NodeTag		type;
	List	   *roles;
	char	   *newrole;
} ReassignOwnedStmt;

/*
 * TS Dictionary stmts: DefineStmt, RenameStmt and DropStmt are default
 */
typedef struct AlterTSDictionaryStmt
{
	NodeTag		type;
	List	   *dictname;		/* qualified name (list of Value strings) */
	List	   *options;		/* List of DefElem nodes */
} AlterTSDictionaryStmt;

/*
 * TS Configuration stmts: DefineStmt, RenameStmt and DropStmt are default
 */
typedef struct AlterTSConfigurationStmt
{
	NodeTag		type;
	List	   *cfgname;		/* qualified name (list of Value strings) */

	/*
	 * dicts will be non-NIL if ADD/ALTER MAPPING was specified. If dicts is
	 * NIL, but tokentype isn't, DROP MAPPING was specified.
	 */
	List	   *tokentype;		/* list of Value strings */
	List	   *dicts;			/* list of list of Value strings */
	bool		override;		/* if true - remove old variant */
	bool		replace;		/* if true - replace dictionary by another */
	bool		missing_ok;		/* for DROP - skip error if missing? */
} AlterTSConfigurationStmt;

typedef struct RetrieveStmt
{
	NodeTag		type;
	char		*endpoint_name;
	int64		count;
	bool		is_all;
} RetrieveStmt;

#endif   /* PARSENODES_H */
