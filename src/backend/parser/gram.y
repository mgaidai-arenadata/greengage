%{

/*#define YYDEBUG 1*/
/*-------------------------------------------------------------------------
 *
 * gram.y
 *	  POSTGRESQL BISON rules/actions
 *
 * Portions Copyright (c) 2006-2010, Greenplum inc
 * Portions Copyright (c) 2012-Present Pivotal Software, Inc.
 * Portions Copyright (c) 1996-2014, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/parser/gram.y
 *
 * HISTORY
 *	  AUTHOR			DATE			MAJOR EVENT
 *	  Andrew Yu			Sept, 1994		POSTQUEL to SQL conversion
 *	  Andrew Yu			Oct, 1994		lispy code conversion
 *
 * NOTES
 *	  CAPITALS are used to represent terminal symbols.
 *	  non-capitals are used to represent non-terminals.
 *
 *	  In general, nothing in this file should initiate database accesses
 *	  nor depend on changeable state (such as SET variables).  If you do
 *	  database accesses, your code will fail when we have aborted the
 *	  current transaction and are just parsing commands to find the next
 *	  ROLLBACK or COMMIT.  If you make use of SET variables, then you
 *	  will do the wrong thing in multi-query strings like this:
 *			SET SQL_inheritance TO off; SELECT * FROM foo;
 *	  because the entire string is parsed by gram.y before the SET gets
 *	  executed.  Anything that depends on the database or changeable state
 *	  should be handled during parse analysis so that it happens at the
 *	  right time not the wrong time.  The handling of SQL_inheritance is
 *	  a good example.
 *
 * WARNINGS
 *	  If you use a list, make sure the datum is a node so that the printing
 *	  routines work.
 *
 *	  Sometimes we assign constants to makeStrings. Make sure we don't free
 *	  those.
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <ctype.h>
#include <limits.h>

#include "catalog/index.h"
#include "catalog/namespace.h"
#include "catalog/pg_trigger.h"
#include "commands/defrem.h"
#include "commands/trigger.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "parser/gramparse.h"
#include "parser/parser.h"
#include "storage/lmgr.h"
#include "utils/date.h"
#include "utils/datetime.h"
#include "utils/numeric.h"
#include "utils/xml.h"
#include "cdb/cdbutil.h"
#include "cdb/cdbvars.h"
#include "cdb/cdbpartition.h"

#include "utils/guc.h"


/*
 * Location tracking support --- simpler than bison's default, since we only
 * want to track the start position not the end position of each nonterminal.
 */
#define YYLLOC_DEFAULT(Current, Rhs, N) \
	do { \
		if ((N) > 0) \
			(Current) = (Rhs)[1]; \
		else \
			(Current) = (-1); \
	} while (0)

/*
 * The above macro assigns -1 (unknown) as the parse location of any
 * nonterminal that was reduced from an empty rule.  This is problematic
 * for nonterminals defined like
 *		OptFooList: / * EMPTY * / { ... } | OptFooList Foo { ... } ;
 * because we'll set -1 as the location during the first reduction and then
 * copy it during each subsequent reduction, leaving us with -1 for the
 * location even when the list is not empty.  To fix that, do this in the
 * action for the nonempty rule(s):
 *		if (@$ < 0) @$ = @2;
 * (Although we have many nonterminals that follow this pattern, we only
 * bother with fixing @$ like this when the nonterminal's parse location
 * is actually referenced in some rule.)
 */

/*
 * Bison doesn't allocate anything that needs to live across parser calls,
 * so we can easily have it use palloc instead of malloc.  This prevents
 * memory leaks if we error out during parsing.  Note this only works with
 * bison >= 2.0.  However, in bison 1.875 the default is to use alloca()
 * if possible, so there's not really much problem anyhow, at least if
 * you're building with gcc.
 */
#define YYMALLOC palloc
#define YYFREE   pfree

/* Private struct for the result of privilege_target production */
typedef struct PrivTarget
{
	GrantTargetType targtype;
	GrantObjectType objtype;
	List	   *objs;
} PrivTarget;

/* ConstraintAttributeSpec yields an integer bitmask of these flags: */
#define CAS_NOT_DEFERRABLE			0x01
#define CAS_DEFERRABLE				0x02
#define CAS_INITIALLY_IMMEDIATE		0x04
#define CAS_INITIALLY_DEFERRED		0x08
#define CAS_NOT_VALID				0x10
#define CAS_NO_INHERIT				0x20


#define parser_yyerror(msg)  scanner_yyerror(msg, yyscanner)
#define parser_errposition(pos)  scanner_errposition(pos, yyscanner)

static void base_yyerror(YYLTYPE *yylloc, core_yyscan_t yyscanner,
						 const char *msg);
static Node *makeColumnRef(char *colname, List *indirection,
						   int location, core_yyscan_t yyscanner);
static Node *makeTypeCast(Node *arg, TypeName *typename, int location);
static Node *makeStringConst(char *str, int location);
static Node *makeStringConstCast(char *str, int location, TypeName *typename);
static Node *makeIntConst(int val, int location);
static Node *makeFloatConst(char *str, int location);
static Node *makeBitStringConst(char *str, int location);
static Node *makeNullAConst(int location);
static Node *makeAConst(Value *v, int location);
static Node *makeBoolAConst(bool state, int location);
static void check_qualified_name(List *names, core_yyscan_t yyscanner);
static List *check_func_name(List *names, core_yyscan_t yyscanner);
static List *check_indirection(List *indirection, core_yyscan_t yyscanner);
static List *extractArgTypes(List *parameters);
static List *extractAggrArgTypes(List *aggrargs);
static List *makeOrderedSetArgs(List *directargs, List *orderedargs,
								core_yyscan_t yyscanner);
static void insertSelectOptions(SelectStmt *stmt,
								List *sortClause, List *lockingClause,
								Node *limitOffset, Node *limitCount,
								WithClause *withClause,
								core_yyscan_t yyscanner);
static Node *makeSetOp(SetOperation op, bool all, Node *larg, Node *rarg);
static Node *doNegate(Node *n, int location);
static void doNegateFloat(Value *v);
static Node *makeAArrayExpr(List *elements, int location);
static Node *makeXmlExpr(XmlExprOp op, char *name, List *named_args,
						 List *args, int location);
static List *mergeTableFuncParameters(List *func_args, List *columns);
static TypeName *TableFuncTypeName(List *columns);
static RangeVar *makeRangeVarFromAnyName(List *names, int position, core_yyscan_t yyscanner);
static void SplitColQualList(List *qualList,
							 List **constraintList, CollateClause **collClause,
							 core_yyscan_t yyscanner);
static void processCASbits(int cas_bits, int location, const char *constrType,
			   bool *deferrable, bool *initdeferred, bool *not_valid,
			   bool *no_inherit, core_yyscan_t yyscanner);
static Node *makeRecursiveViewSelect(char *relname, List *aliases, Node *query);

static void checkWindowExclude(void);
static Node *makeIsNotDistinctFromNode(Node *expr, int position);

%}

%pure-parser
%expect 0
%name-prefix="base_yy"
%locations

%parse-param {core_yyscan_t yyscanner}
%lex-param   {core_yyscan_t yyscanner}

%union
{
	core_YYSTYPE		core_yystype;
	/* these fields must match core_YYSTYPE: */
	int					ival;
	char				*str;
	const char			*keyword;

	char				chr;
	bool				boolean;
	JoinType			jtype;
	DropBehavior		dbehavior;
	OnCommitAction		oncommit;
	List				*list;
	Node				*node;
	Value				*value;
	ObjectType			objtype;
	TypeName			*typnam;
	FunctionParameter   *fun_param;
	FunctionParameterMode fun_param_mode;
	FuncWithArgs		*funwithargs;
	DefElem				*defelt;
	SortBy				*sortby;
	WindowDef			*windef;
	JoinExpr			*jexpr;
	IndexElem			*ielem;
	Alias				*alias;
	RangeVar			*range;
	IntoClause			*into;
	WithClause			*with;
	A_Indices			*aind;
	ResTarget			*target;
	struct PrivTarget	*privtarget;
	AccessPriv			*accesspriv;
	InsertStmt			*istmt;
	VariableSetStmt		*vsetstmt;
}

%type <node>	stmt schema_stmt
		AlterEventTrigStmt
		AlterDatabaseStmt AlterDatabaseSetStmt AlterDomainStmt AlterEnumStmt
		AlterFdwStmt AlterForeignServerStmt AlterGroupStmt
		AlterObjectSchemaStmt AlterOwnerStmt AlterSeqStmt AlterSystemStmt AlterTableStmt
		AlterTblSpcStmt AlterExtensionStmt AlterExtensionContentsStmt AlterForeignTableStmt
		AlterCompositeTypeStmt AlterUserStmt AlterUserMappingStmt AlterUserSetStmt
		AlterRoleStmt AlterRoleSetStmt
		AlterDefaultPrivilegesStmt DefACLAction
		AnalyzeStmt ClosePortalStmt ClusterStmt CommentStmt
		ConstraintsSetStmt CopyStmt CreateAsStmt CreateCastStmt
		CreateDomainStmt CreateExtensionStmt CreateGroupStmt CreateOpClassStmt
		CreateOpFamilyStmt AlterOpFamilyStmt CreatePLangStmt
		CreateSchemaStmt CreateSeqStmt CreateStmt CreateTableSpaceStmt
		CreateFdwStmt CreateForeignServerStmt CreateForeignTableStmt
		CreateAssertStmt CreateTrigStmt CreateEventTrigStmt
		CreateUserStmt CreateUserMappingStmt CreateRoleStmt
		CreatedbStmt DeclareCursorStmt DefineStmt DeleteStmt DiscardStmt DoStmt
		DropGroupStmt DropOpClassStmt DropOpFamilyStmt DropPLangStmt DropStmt
		DropAssertStmt DropTrigStmt DropRuleStmt DropCastStmt DropRoleStmt
		DropUserStmt DropdbStmt DropTableSpaceStmt DropFdwStmt
		DropForeignServerStmt DropUserMappingStmt ExplainStmt FetchStmt
		GrantStmt GrantRoleStmt IndexStmt InsertStmt ListenStmt LoadStmt
		LockStmt NotifyStmt ExplainableStmt PreparableStmt
		CreateFunctionStmt AlterFunctionStmt ReindexStmt RemoveAggrStmt
		RemoveFuncStmt RemoveOperStmt RenameStmt RevokeStmt RevokeRoleStmt
		RuleActionStmt RuleActionStmtOrEmpty RuleStmt
		SecLabelStmt SelectStmt TransactionStmt TruncateStmt
		UnlistenStmt UpdateStmt VacuumStmt
		VariableResetStmt VariableSetStmt VariableShowStmt
		ViewStmt CheckPointStmt CreateConversionStmt
		DeallocateStmt PrepareStmt ExecuteStmt
		DropOwnedStmt ReassignOwnedStmt
		AlterTSConfigurationStmt AlterTSDictionaryStmt
		CreateMatViewStmt RefreshMatViewStmt
		RetrieveStmt

/* GPDB-specific commands */
%type <node>	AlterTypeStmt AlterQueueStmt AlterResourceGroupStmt
		CreateExternalStmt
		CreateQueueStmt CreateResourceGroupStmt
		DropQueueStmt DropResourceGroupStmt
		ExtTypedesc OptSingleRowErrorHandling ExtSingleRowErrorHandling

%type <node>    deny_login_role deny_interval deny_point deny_day_specifier

%type <node>	select_no_parens select_with_parens select_clause
				simple_select values_clause

%type <node>	alter_column_default opclass_item opclass_drop alter_using
%type <ival>	add_drop opt_asc_desc opt_nulls_order

%type <node>	alter_table_cmd alter_type_cmd opt_collate_clause
	   replica_identity
%type <list>	alter_table_cmds alter_type_cmds

%type <node>	alter_table_partition_cmd alter_table_partition_id_spec
				alter_table_partition_id_spec_with_opt_default
%type <list>	part_values_clause multi_spec_value_list part_values_single
%type <ival>	opt_table_partition_exchange_validate

%type <dbehavior>	opt_drop_behavior

%type <list>	createdb_opt_list alterdb_opt_list copy_opt_list
				transaction_mode_list
				create_extension_opt_list alter_extension_opt_list
%type <defelt>	createdb_opt_item alterdb_opt_item copy_opt_item
				transaction_mode_item
				create_extension_opt_item alter_extension_opt_item

%type <list>	ext_on_clause_list format_opt format_opt_list format_def_list
				ext_options ext_options_opt ext_options_list
				ext_opt_encoding_list
%type <defelt>	ext_on_clause_item format_opt_item format_def_item
				ext_options_item
				ext_opt_encoding_item

%type <ival>	opt_lock lock_type cast_context
%type <ival>	vacuum_option_list vacuum_option_elem
%type <boolean>	opt_force opt_or_replace
				opt_grant_grant_option opt_grant_admin_option
				opt_nowait opt_if_exists opt_with_data opt_masteronly

%type <list>	OptRoleList AlterOptRoleList
%type <defelt>	CreateOptRoleElem AlterOptRoleElem
%type <defelt>	AlterOnlyOptRoleElem

%type <str>		opt_type
%type <str>		foreign_server_version opt_foreign_server_version
%type <str>		auth_ident
%type <str>		opt_in_database

%type <list>	OptQueueList
%type <defelt>	OptQueueElem

%type <list>	OptResourceGroupList
%type <defelt>	OptResourceGroupElem

%type <str>		OptSchemaName
%type <list>	OptSchemaEltList

%type <boolean> TriggerForSpec TriggerForType
%type <ival>	TriggerActionTime
%type <list>	TriggerEvents TriggerOneEvent
%type <value>	TriggerFuncArg
%type <node>	TriggerWhen

%type <list>	event_trigger_when_list event_trigger_value_list
%type <defelt>	event_trigger_when_item
%type <chr>		enable_trigger

%type <str>		copy_file_name
				database_name access_method_clause access_method attr_name
				name cursor_name file_name
				index_name opt_index_name cluster_index_specification

%type <list>	func_name handler_name qual_Op qual_all_Op subquery_Op
				opt_class opt_inline_handler opt_validator validator_clause
				opt_collate

%type <range>	qualified_name OptConstrFromTable

%type <str>		all_Op MathOp

%type <str>		iso_level opt_encoding
%type <node>	grantee
%type <list>	grantee_list
%type <accesspriv> privilege
%type <list>	privileges privilege_list
%type <privtarget> privilege_target
%type <funwithargs> function_with_argtypes
%type <list>	function_with_argtypes_list
%type <ival>	defacl_privilege_target
%type <defelt>	DefACLOption
%type <list>	DefACLOptionList

%type <list>	stmtblock stmtmulti
				OptTableElementList TableElementList OptInherit definition
				OptExtTableElementList ExtTableElementList
				OptTypedTableElementList TypedTableElementList
				reloptions opt_reloptions
				OptWith opt_distinct opt_definition func_args func_args_list
				func_args_with_defaults func_args_with_defaults_list
				aggr_args aggr_args_list
				func_as createfunc_opt_list alterfunc_opt_list
				old_aggr_definition old_aggr_list
				oper_argtypes RuleActionList RuleActionMulti
				cdb_string_list
				opt_column_list columnList opt_name_list
				exttab_auth_list keyvalue_list
				sort_clause opt_sort_clause sortby_list index_params
				name_list role_list from_clause from_list opt_array_bounds
				qualified_name_list any_name any_name_list
				any_operator expr_list attrs
				target_list opt_target_list insert_column_list set_target_list
				set_clause_list set_clause multiple_set_clause
				ctext_expr_list ctext_row def_list indirection opt_indirection
				reloption_list group_clause group_elem_list group_elem TriggerFuncArgs select_limit
				opt_select_limit opclass_item_list opclass_drop_list
				opclass_purpose opt_opfamily transaction_mode_list_or_empty
				OptTableFuncElementList TableFuncElementList opt_type_modifiers
				prep_type_clause
				execute_param_clause using_clause returning_clause
				opt_enum_val_list enum_val_list table_func_column_list
				scatter_clause
				create_generic_options alter_generic_options
				relation_expr_list dostmt_opt_list

%type <node>    table_value_select_clause

%type <list>	opt_fdw_options fdw_options
%type <defelt>	fdw_option

%type <range>	OptTempTableName
%type <into>	into_clause create_as_target create_mv_target

%type <defelt>	createfunc_opt_item common_func_opt_item dostmt_opt_item
%type <fun_param> func_arg func_arg_with_default table_func_column aggr_arg
%type <fun_param_mode> arg_class
%type <typnam>	func_return func_type

%type <boolean>  OptWeb OptWritable OptSrehLimitType OptLogErrorTable ExtLogErrorTable

%type <boolean>  opt_trusted opt_restart_seqs
%type <ival>	 OptTemp
%type <ival>	 OptNoLog
%type <oncommit> OnCommitOption

%type <ival>	for_locking_strength
%type <node>	for_locking_item
%type <list>	for_locking_clause opt_for_locking_clause for_locking_items
%type <list>	locked_rels_list
%type <boolean>	opt_all

%type <node>	join_outer join_qual
%type <jtype>	join_type

%type <list>	extract_list overlay_list position_list
%type <list>	substr_list trim_list
%type <list>	opt_interval interval_second
%type <node>	overlay_placing substr_from substr_for

%type <boolean> opt_instead
%type <boolean> opt_unique opt_concurrently opt_verbose opt_full
%type <boolean> opt_freeze opt_default opt_ordered opt_recheck
%type <boolean> opt_rootonly_all
%type <boolean> opt_dxl
%type <defelt>	opt_binary opt_oids copy_delimiter

%type <boolean> copy_from opt_program skip_external_partition

%type <ival>	opt_column event cursor_options opt_hold opt_set_data
%type <objtype>	reindex_type drop_type comment_type security_label_type

%type <node>	fetch_args limit_clause select_limit_value
				offset_clause select_offset_value
				select_fetch_first_value I_or_F_const
%type <ival>	row_or_rows first_or_next

%type <list>	OptSeqOptList SeqOptList
%type <defelt>	SeqOptElem

%type <istmt>	insert_rest

%type <vsetstmt> generic_set set_rest set_rest_more generic_reset reset_rest
				 SetResetClause FunctionSetResetClause

%type <node>	TableElement TypedTableElement ConstraintElem TableFuncElement
%type <node>	columnDef columnOptions
%type <defelt>	def_elem reloption_elem old_aggr_elem keyvalue_pair
%type <node>	ExtTableElement
%type <node>	ExtcolumnDef
%type <node>	cdb_string
%type <node>	def_arg columnElem where_clause where_or_current_clause
				a_expr b_expr c_expr AexprConst indirection_el
				columnref in_expr having_clause func_table array_expr
				ExclusionWhereClause
%type <list>	rowsfrom_item rowsfrom_list opt_col_def_list
%type <boolean> opt_ordinality
%type <list>	ExclusionConstraintList ExclusionConstraintElem
%type <list>	func_arg_list
%type <node>	func_arg_expr
%type <list>	row type_list array_expr_list
%type <node>	case_expr case_arg when_clause when_operand case_default
%type <list>	when_clause_list
%type <node>	decode_expr search_result decode_default
%type <list>	search_result_list
%type <ival>	sub_type
%type <node>	ctext_expr
%type <value>	NumericOnly
%type <list>	NumericOnly_list
%type <alias>	alias_clause opt_alias_clause
%type <list>	func_alias_clause
%type <sortby>	sortby
%type <ielem>	index_elem
%type <node>	table_ref
%type <jexpr>	joined_table
%type <range>	relation_expr
%type <range>	relation_expr_opt_alias
%type <target>	target_el single_set_clause set_target insert_column_item

%type <str>		generic_option_name
%type <node>	generic_option_arg
%type <defelt>	generic_option_elem alter_generic_option_elem
%type <list>	generic_option_list alter_generic_option_list
%type <str>		explain_option_name
%type <node>	explain_option_arg
%type <defelt>	explain_option_elem
%type <list>	explain_option_list
%type <node>	copy_generic_opt_arg copy_generic_opt_arg_list_item
%type <defelt>	copy_generic_opt_elem
%type <list>	copy_generic_opt_list copy_generic_opt_arg_list
%type <list>	copy_options

%type <typnam>	Typename SimpleTypename ConstTypename
				GenericType Numeric opt_float
				Character ConstCharacter
				CharacterWithLength CharacterWithoutLength
				ConstDatetime ConstInterval
				Bit ConstBit BitWithLength BitWithoutLength
%type <str>		character
%type <str>		extract_arg
%type <str>		opt_charset
%type <boolean> opt_varying opt_timezone opt_no_inherit

%type <ival>	Iconst SignedIconst
%type <str>		Sconst comment_text notify_payload
%type <str>		RoleId opt_granted_by opt_boolean_or_string
%type <str>		QueueId
%type <list>	var_list
%type <str>		ColId ColLabel ColLabelNoAs var_name type_function_name param_name
%type <keyword> PartitionIdentKeyword	
%type <str>		PartitionColId
%type <str>		NonReservedWord NonReservedWord_or_Sconst
%type <node>	var_value zone_value

%type <keyword> unreserved_keyword type_func_name_keyword
%type <keyword> col_name_keyword reserved_keyword
%type <keyword> keywords_ok_in_alias_no_as

%type <node>	TableConstraint TableLikeClause
%type <ival>	TableLikeOptionList TableLikeOption
%type <list>	ColQualList
%type <node>	NullColConstraintElem DefaultColConstraintElem
%type <node>	ExtColConstraintElem
%type <list>	ExtColQualList
%type <node>	ColConstraint ColConstraintElem ConstraintAttr
%type <ival>	key_actions key_delete key_match key_update key_action
%type <ival>	ConstraintAttributeSpec ConstraintAttributeElem
%type <str>		ExistingIndex

%type <list>	constraints_set_list
%type <boolean> constraints_set_mode
%type <str>		OptTableSpace OptConsTableSpace OptTableSpaceOwner
%type <node>    DistributedBy OptDistributedBy 
%type <ival>	TabPartitionByType OptTabPartitionRangeInclusive
%type <node>	OptTabPartitionBy TabSubPartitionBy TabSubPartition
				tab_part_val tab_part_val_no_paran
%type <node>	opt_list_subparts
%type <ival>	opt_check_option
%type <node>	OptTabPartitionSpec OptTabSubPartitionSpec TabSubPartitionTemplate      /* PartitionSpec */
%type <list>	TabPartitionElemList TabSubPartitionElemList /* list of PartitionElem */

%type <node> 	TabPartitionElem TabSubPartitionElem  /* PartitionElem */

%type <node> 	TabPartitionBoundarySpec OptTabPartitionBoundarySpec  /* PartitionBoundSpec */
%type <list> 	TabPartitionBoundarySpecValList
				part_values_or_spec_list
%type <node> 	TabPartitionBoundarySpecStart TabPartitionBoundarySpecEnd
				OptTabPartitionBoundarySpecEnd        /* PartitionRangeItem */
%type <node> 	OptTabPartitionBoundarySpecEvery      /* PartitionRangeItem */
%type <str> 	TabPartitionNameDecl TabSubPartitionNameDecl
				TabPartitionDefaultNameDecl TabSubPartitionDefaultNameDecl 
%type <node>	opt_table_partition_split_into
%type <node> 	OptTabPartitionStorageAttr
%type <node>	opt_time

%type <node>	column_reference_storage_directive
%type <list>	opt_storage_encoding OptTabPartitionColumnEncList
				TabPartitionColumnEncList

%type <str>		opt_provider security_label

%type <target>	xml_attribute_el
%type <list>	xml_attribute_list xml_attributes
%type <node>	xml_root_version opt_xml_root_standalone
%type <node>	xmlexists_argument
%type <ival>	document_or_content
%type <boolean> xml_whitespace_option

%type <node>	func_application func_expr_common_subexpr
%type <node>	func_expr func_expr_windowless
%type <node>	common_table_expr
%type <with>	with_clause opt_with_clause
%type <list>	cte_list

%type <list>	within_group_clause
%type <node>	filter_clause
%type <list>	window_clause window_definition_list opt_partition_clause
%type <windef>	window_definition over_clause window_specification
				opt_frame_clause frame_extent frame_bound
%type <str>		opt_existing_window_name
%type <ival>	window_frame_exclusion

%type <list>	distributed_by_list
%type <ielem>	distributed_by_elem

%type <boolean> opt_if_not_exists

/*
 * Non-keyword token types.  These are hard-wired into the "flex" lexer.
 * They must be listed first so that their numeric codes do not depend on
 * the set of keywords.  PL/pgsql depends on this so that it can share the
 * same lexer.  If you add/change tokens here, fix PL/pgsql to match!
 *
 * DOT_DOT is unused in the core SQL grammar, and so will always provoke
 * parse errors.  It is needed by PL/pgsql.
 */
%token <str>	IDENT FCONST SCONST BCONST XCONST Op
%token <ival>	ICONST PARAM
%token			TYPECAST DOT_DOT COLON_EQUALS

/*
 * If you want to make any keyword changes, update the keyword table in
 * src/include/parser/kwlist.h and add new keywords to the appropriate one
 * of the reserved-or-not-so-reserved keyword lists, below; search
 * this file for "Keyword category lists".
 */

/* ordinary key words in alphabetical order */
%token <keyword> ABORT_P ABSOLUTE_P ACCESS ACTION ADD_P ADMIN AFTER
	AGGREGATE ALL ALSO ALTER ALWAYS ANALYSE ANALYZE AND ANY ARRAY AS ASC
	ASSERTION ASSIGNMENT ASYMMETRIC AT ATTRIBUTE AUTHORIZATION

	BACKWARD BEFORE BEGIN_P BETWEEN BIGINT BINARY BIT
	BOOLEAN_P BOTH BY

	CACHE CALLED CASCADE CASCADED CASE CAST CATALOG_P CHAIN CHAR_P
	CHARACTER CHARACTERISTICS CHECK CHECKPOINT CLASS CLOSE
	CLUSTER COALESCE COLLATE COLLATION COLUMN COMMENT COMMENTS COMMIT
	COMMITTED CONCURRENCY CONCURRENTLY CONFIGURATION CONNECTION CONSTRAINT CONSTRAINTS
	CONTENT_P CONTINUE_P CONVERSION_P COPY COST CREATE
	CROSS CSV CURRENT_P
	CURRENT_CATALOG CURRENT_DATE CURRENT_ROLE CURRENT_SCHEMA
	CURRENT_TIME CURRENT_TIMESTAMP CURRENT_USER CURSOR CYCLE

	DATA_P DATABASE DAY_P DEALLOCATE DEC DECIMAL_P DECLARE DEFAULT DEFAULTS
	DEFERRABLE DEFERRED DEFINER DELETE_P DELIMITER DELIMITERS DESC
	DICTIONARY DISABLE_P DISCARD DISTINCT DO DOCUMENT_P DOMAIN_P DOUBLE_P DROP

	EACH ELSE ENABLE_P ENCODING ENCRYPTED END_P ENDPOINT ENUM_P ESCAPE EVENT EXCEPT
	EXCLUDE EXCLUDING EXCLUSIVE EXECUTE EXISTS EXPLAIN
	EXTENSION EXTERNAL EXTRACT

	FALSE_P FAMILY FETCH FILTER FIRST_P FLOAT_P FOLLOWING FOR
	FORCE FOREIGN FORWARD FREEZE FROM FULL FUNCTION FUNCTIONS

	GLOBAL GRANT GRANTED GREATEST GROUP_P

	HANDLER HAVING HEADER_P HOLD HOUR_P

	IDENTITY_P IF_P ILIKE IMMEDIATE IMMUTABLE IMPLICIT_P IN_P
	INCLUDING INCREMENT INDEX INDEXES INHERIT INHERITS INITIALLY INLINE_P
	INNER_P INOUT INPUT_P INSENSITIVE INSERT INSTEAD INT_P INTEGER
	INTERSECT INTERVAL INTO INVOKER IS ISNULL ISOLATION

	JOIN

	KEY

	LABEL LANGUAGE LARGE_P LAST_P LATERAL_P LC_COLLATE_P LC_CTYPE_P
	LEADING LEAKPROOF LEAST LEFT LEVEL LIKE LIMIT LISTEN LOAD LOCAL
	LOCALTIME LOCALTIMESTAMP LOCATION LOCK_P

	MAPPING MATCH MATERIALIZED MAXVALUE MEMORY_LIMIT MEMORY_SHARED_QUOTA MEMORY_SPILL_RATIO
	MINUTE_P MINVALUE MODE MONTH_P MOVE

	NAME_P NAMES NATIONAL NATURAL NCHAR NEXT NO NONE
	NOT NOTHING NOTIFY NOTNULL NOWAIT NULL_P NULLIF
	NULLS_P NUMERIC

	OBJECT_P OF OFF OFFSET OIDS ON ONLY OPERATOR OPTION OPTIONS OR
	ORDER ORDINALITY OUT_P OUTER_P OVER OVERLAPS OVERLAY OWNED OWNER

	PARSER PARTIAL PARTITION PASSING PASSWORD PLACING PLANS POSITION
	PRECEDING PRECISION PRESERVE PREPARE PREPARED PRIMARY
	PRIOR PRIVILEGES PROCEDURAL PROCEDURE PROGRAM

	QUOTE

	RANGE READ REAL REASSIGN RECHECK RECURSIVE REF REFERENCES REFRESH REINDEX
	RELATIVE_P RELEASE RENAME REPEATABLE REPLACE REPLICA
	RESET RESTART RESTRICT RETURNING RETURNS REVOKE RIGHT ROLE ROLLBACK
	ROW ROWS RULE

	SAVEPOINT SCHEMA SCROLL SEARCH SECOND_P SECURITY SELECT SEQUENCE SEQUENCES
	SERIALIZABLE SERVER SESSION SESSION_USER SET SETOF SHARE
	SHOW SIMILAR SIMPLE SMALLINT SNAPSHOT SOME STABLE STANDALONE_P START
	STATEMENT STATISTICS STDIN STDOUT STORAGE STRICT_P STRIP_P SUBSTRING
	SYMMETRIC SYSID SYSTEM_P

	TABLE TABLES TABLESPACE TEMP TEMPLATE TEMPORARY TEXT_P THEN TIME TIMESTAMP
	TO TRAILING TRANSACTION TREAT TRIGGER TRIM TRUE_P
	TRUNCATE TRUSTED TYPE_P TYPES_P

	UNBOUNDED UNCOMMITTED UNENCRYPTED UNION UNIQUE UNKNOWN UNLISTEN UNLOGGED
	UNTIL UPDATE USER USING

	VACUUM VALID VALIDATE VALIDATOR VALUE_P VALUES VARCHAR VARIADIC VARYING
	VERBOSE VERSION_P VIEW VIEWS VOLATILE

	WHEN WHERE WHITESPACE_P WINDOW WITH WITHIN WITHOUT WORK WRAPPER WRITE

	XML_P XMLATTRIBUTES XMLCONCAT XMLELEMENT XMLEXISTS XMLFOREST XMLPARSE
	XMLPI XMLROOT XMLSERIALIZE

	YEAR_P YES_P

	ZONE


/* GPDB-added keywords, in alphabetical order */
%token <keyword>
	ACTIVE

	CONTAINS CPUSET CPU_RATE_LIMIT

	CREATEEXTTABLE CUBE

	DECODE DENY DISTRIBUTED DXL

	ERRORS EVERY EXCHANGE EXPAND

	FIELDS FILL FORMAT

	FULLSCAN

	GROUP_ID GROUPING

	HASH HOST

	IGNORE_P INCLUSIVE INITPLAN

	LIST LOG_P

	MASTER MEDIAN MISSING MODIFIES

	NEWLINE NOCREATEEXTTABLE NOOVERCOMMIT

	ORDERED OTHERS OVERCOMMIT

	PARALLEL RETRIEVE

	PARTITIONS PERCENT PERSISTENTLY PROTOCOL

	QUEUE

	RANDOMLY READABLE READS REJECT_P REPLICATED RESOURCE
	ROLLUP ROOTPARTITION

	SCATTER SEGMENT SEGMENTS SETS SPLIT SQL SUBPARTITION

	THRESHOLD TIES

	VALIDATION

	WEB WRITABLE

/*
 * The grammar thinks these are keywords, but they are not in the kwlist.h
 * list and so can never be entered directly.  The filter in parser.c
 * creates these tokens when required.
 */
%token			NULLS_FIRST NULLS_LAST WITH_ORDINALITY WITH_TIME


/* Precedence: lowest to highest */
%nonassoc	SET				/* see relation_expr_opt_alias */
%left		UNION EXCEPT
%left		INTERSECT
%left		OR
%left		AND
%right		NOT
%right		'='
%nonassoc	'<' '>'
%nonassoc	LIKE ILIKE SIMILAR
%nonassoc	ESCAPE
%nonassoc	OVERLAPS
%nonassoc	BETWEEN
%nonassoc	IN_P
%left		POSTFIXOP		/* dummy for postfix Op rules */
/*
 * To support target_el without AS, we must give IDENT an explicit priority
 * between POSTFIXOP and Op.  We can safely assign the same priority to
 * various unreserved keywords as needed to resolve ambiguities (this can't
 * have any bad effects since obviously the keywords will still behave the
 * same as if they weren't keywords).  We need to do this for PARTITION,
 * RANGE, ROWS to support opt_existing_window_name; and for RANGE, ROWS
 * so that they can follow a_expr without creating postfix-operator problems;
 * and for NULL so that it can follow b_expr in ColQualList without creating
 * postfix-operator problems.
 *
 * The frame_bound productions UNBOUNDED PRECEDING and UNBOUNDED FOLLOWING
 * are even messier: since UNBOUNDED is an unreserved keyword (per spec!),
 * there is no principled way to distinguish these from the productions
 * a_expr PRECEDING/FOLLOWING.  We hack this up by giving UNBOUNDED slightly
 * lower precedence than PRECEDING and FOLLOWING.  At present this doesn't
 * appear to cause UNBOUNDED to be treated differently from other unreserved
 * keywords anywhere else in the grammar, but it's definitely risky.  We can
 * blame any funny behavior of UNBOUNDED on the SQL standard, though.
 */
%nonassoc	UNBOUNDED		/* ideally should have same precedence as IDENT */
%nonassoc	IDENT NULL_P PARTITION RANGE ROWS PRECEDING FOLLOWING

/*
 * This is a bit ugly... To allow these to be column aliases without
 * the "AS" keyword, and not conflict with PostgreSQL's non-standard
 * suffix operators, we need to give these a precidence.
 */

%nonassoc   ABORT_P
			%nonassoc ABSOLUTE_P
			%nonassoc ACCESS
			%nonassoc ACTION
			%nonassoc ACTIVE
			%nonassoc ADD_P
			%nonassoc ADMIN
			%nonassoc AFTER
			%nonassoc AGGREGATE
			%nonassoc ALSO
			%nonassoc ALTER
			%nonassoc ASSERTION
			%nonassoc ASSIGNMENT
			%nonassoc BACKWARD
			%nonassoc BEFORE
			%nonassoc BEGIN_P
			%nonassoc BY
			%nonassoc CACHE
			%nonassoc CALLED
			%nonassoc CASCADE
			%nonassoc CASCADED
			%nonassoc CHAIN
			%nonassoc CHARACTERISTICS
			%nonassoc CHECKPOINT
			%nonassoc CLASS
			%nonassoc CLOSE
			%nonassoc CLUSTER
			%nonassoc COMMENT
			%nonassoc COMMIT
			%nonassoc COMMITTED
			%nonassoc CONCURRENCY
			%nonassoc CONCURRENTLY
			%nonassoc CONNECTION
			%nonassoc CONSTRAINTS
			%nonassoc CONTAINS
			%nonassoc CONTENT_P
			%nonassoc CONTINUE_P
			%nonassoc CONVERSION_P
			%nonassoc COPY
			%nonassoc COST
			%nonassoc CPUSET
			%nonassoc CPU_RATE_LIMIT
			%nonassoc CREATEEXTTABLE
			%nonassoc CSV
			%nonassoc CURRENT_P
			%nonassoc CURSOR
			%nonassoc CYCLE
			%nonassoc DATA_P
			%nonassoc DATABASE
			%nonassoc DAY_P
			%nonassoc DEALLOCATE
			%nonassoc DECLARE
			%nonassoc DEFAULTS
			%nonassoc DEFERRED
			%nonassoc DEFINER
			%nonassoc DELETE_P
			%nonassoc DELIMITER
			%nonassoc DELIMITERS
			%nonassoc DISABLE_P
			%nonassoc DOMAIN_P
			%nonassoc DOUBLE_P
			%nonassoc DROP
			%nonassoc EACH
			%nonassoc ENABLE_P
			%nonassoc ENCODING
			%nonassoc ENCRYPTED
			%nonassoc END_P
			%nonassoc ENDPOINT
			%nonassoc ENUM_P
			%nonassoc ERRORS
			%nonassoc EVERY
			%nonassoc EXCHANGE
			%nonassoc EXCLUDING
			%nonassoc EXCLUSIVE
			%nonassoc EXECUTE
			%nonassoc EXPLAIN
			%nonassoc EXTERNAL
			%nonassoc FETCH
			%nonassoc FIELDS
			%nonassoc FILL
			%nonassoc FIRST_P
			%nonassoc FORCE
			%nonassoc FORMAT
			%nonassoc FORWARD
			%nonassoc FUNCTION
			%nonassoc GLOBAL
			%nonassoc GRANTED
			%nonassoc HANDLER
			%nonassoc HASH
			%nonassoc HEADER_P
			%nonassoc HOLD
			%nonassoc HOST
			%nonassoc HOUR_P
			%nonassoc IF_P
			%nonassoc IMMEDIATE
			%nonassoc IMMUTABLE
			%nonassoc IMPLICIT_P
			%nonassoc INCLUDING
			%nonassoc INCLUSIVE
			%nonassoc INCREMENT
			%nonassoc INDEX
			%nonassoc INDEXES
			%nonassoc INHERIT
			%nonassoc INHERITS
			%nonassoc INPUT_P
			%nonassoc INSENSITIVE
			%nonassoc INSERT
			%nonassoc INSTEAD
			%nonassoc INVOKER
			%nonassoc ISOLATION
			%nonassoc KEY
			%nonassoc LANGUAGE
			%nonassoc LARGE_P
			%nonassoc LAST_P
			%nonassoc LEVEL
			%nonassoc LIST
			%nonassoc LISTEN
			%nonassoc LOAD
			%nonassoc LOCAL
			%nonassoc LOCATION
			%nonassoc LOCK_P
			%nonassoc MASTER
			%nonassoc MATCH
			%nonassoc MAXVALUE
			%nonassoc MEMORY_LIMIT
			%nonassoc MEMORY_SHARED_QUOTA
			%nonassoc MEMORY_SPILL_RATIO
			%nonassoc MINUTE_P
			%nonassoc MINVALUE
			%nonassoc MISSING
			%nonassoc MODE
			%nonassoc MODIFIES
			%nonassoc MONTH_P
			%nonassoc MOVE
			%nonassoc NAME_P
			%nonassoc NAMES
			%nonassoc NEWLINE
			%nonassoc NEXT
			%nonassoc NO
			%nonassoc NOCREATEEXTTABLE
			%nonassoc NOOVERCOMMIT
			%nonassoc NOTHING
			%nonassoc NOTIFY
			%nonassoc NOWAIT
			%nonassoc NULLS_P
			%nonassoc OBJECT_P
			%nonassoc OF
			%nonassoc OIDS
			%nonassoc OPTION
			%nonassoc OPTIONS
			%nonassoc OTHERS
			%nonassoc OVER
			%nonassoc OVERCOMMIT
			%nonassoc OWNED
			%nonassoc OWNER
			%nonassoc PARALLEL
			%nonassoc PARTIAL
			%nonassoc PARTITIONS
			%nonassoc PASSWORD
			%nonassoc PERCENT
			%nonassoc PERSISTENTLY
			%nonassoc PREPARE
			%nonassoc PREPARED
			%nonassoc PRIOR
			%nonassoc PRIVILEGES
			%nonassoc PROCEDURAL
			%nonassoc PROCEDURE
			%nonassoc PROTOCOL
			%nonassoc QUEUE
			%nonassoc QUOTE
			%nonassoc RANDOMLY
			%nonassoc READ
			%nonassoc READABLE
			%nonassoc READS
			%nonassoc REASSIGN
			%nonassoc RECHECK
			%nonassoc RECURSIVE
			%nonassoc REINDEX
			%nonassoc REJECT_P
			%nonassoc RELATIVE_P
			%nonassoc RELEASE
			%nonassoc RENAME
			%nonassoc REPEATABLE
			%nonassoc REPLACE
			%nonassoc RESET
			%nonassoc RESOURCE
			%nonassoc RESTART
			%nonassoc RESTRICT
			%nonassoc RETRIEVE
			%nonassoc RETURNS
			%nonassoc REVOKE
			%nonassoc ROLE
			%nonassoc ROLLBACK
			%nonassoc RULE
			%nonassoc SAVEPOINT
			%nonassoc SCHEMA
			%nonassoc SCROLL
			%nonassoc SEARCH
			%nonassoc SECOND_P
			%nonassoc SECURITY
			%nonassoc SEGMENT
			%nonassoc SEGMENTS
			%nonassoc SEQUENCE
			%nonassoc SERIALIZABLE
			%nonassoc SESSION
			%nonassoc SHARE
			%nonassoc SHOW
			%nonassoc SIMPLE
			%nonassoc SPLIT
			%nonassoc SQL
			%nonassoc STABLE
			%nonassoc START
			%nonassoc STATEMENT
			%nonassoc STATISTICS
			%nonassoc STDIN
			%nonassoc STDOUT
			%nonassoc STORAGE
			%nonassoc SUBPARTITION
			%nonassoc SYSID
			%nonassoc SYSTEM_P
			%nonassoc STRICT_P
			%nonassoc TABLESPACE
			%nonassoc TEMP
			%nonassoc TEMPLATE
			%nonassoc TEMPORARY
			%nonassoc THRESHOLD
			%nonassoc TIES
			%nonassoc TRANSACTION
			%nonassoc TRIGGER
			%nonassoc TRUNCATE
			%nonassoc TRUSTED
			%nonassoc TYPE_P
			%nonassoc UNCOMMITTED
			%nonassoc UNENCRYPTED
			%nonassoc UNLISTEN
			%nonassoc UNTIL
			%nonassoc UPDATE
			%nonassoc VACUUM
			%nonassoc VALID
			%nonassoc VALIDATION
			%nonassoc VALIDATOR
			%nonassoc VALUE_P
			%nonassoc VARYING
			%nonassoc VERSION_P
			%nonassoc VIEW
			%nonassoc VOLATILE
			%nonassoc WEB
			%nonassoc WITH
			%nonassoc WITHIN
			%nonassoc WITHOUT
			%nonassoc WORK
			%nonassoc WRITABLE
			%nonassoc WRITE
			%nonassoc YEAR_P
			%nonassoc BIGINT
			%nonassoc BIT
			%nonassoc BOOLEAN_P
			%nonassoc CHAR_P
			%nonassoc CHARACTER
			%nonassoc COALESCE
			%nonassoc CUBE
			%nonassoc DEC
			%nonassoc DECIMAL_P
			%nonassoc EXISTS
			%nonassoc EXTRACT
			%nonassoc FLOAT_P
			%nonassoc GREATEST
			%nonassoc GROUP_ID
			%nonassoc GROUPING
			%nonassoc INOUT
			%nonassoc INT_P
			%nonassoc INTEGER
			%nonassoc INTERVAL
			%nonassoc LEAST
			%nonassoc MEDIAN
			%nonassoc NATIONAL
			%nonassoc NCHAR
			%nonassoc NONE
			%nonassoc NULLIF
			%nonassoc NUMERIC
			%nonassoc OUT_P
			%nonassoc OVERLAY
			%nonassoc POSITION
			%nonassoc PRECISION
			%nonassoc REAL
			%nonassoc ROLLUP
			%nonassoc ROW
			%nonassoc SETOF
			%nonassoc SETS
			%nonassoc SMALLINT
			%nonassoc SUBSTRING
			%nonassoc TIME
			%nonassoc TIMESTAMP
			%nonassoc TREAT
			%nonassoc TRIM
			%nonassoc VALUES
			%nonassoc VARCHAR
			%nonassoc AUTHORIZATION
			%nonassoc BINARY
			%nonassoc FREEZE
			%nonassoc LOG_P
			%nonassoc OUTER_P
			%nonassoc VERBOSE
			%nonassoc UNKNOWN
			%nonassoc ZONE
			


%left		Op OPERATOR		/* multi-character ops and user-defined operators */
%nonassoc	NOTNULL
%nonassoc	ISNULL
%nonassoc	IS				/* sets precedence for IS NULL, etc */
%left		'+' '-'
%left		'*' '/' '%'
%left		'^'
/* Unary Operators */
%left		AT				/* sets precedence for AT TIME ZONE */
%left		COLLATE
%right		UMINUS
%left		'[' ']'
%left		'(' ')'
%left		TYPECAST
%left		'.'
/*
 * These might seem to be low-precedence, but actually they are not part
 * of the arithmetic hierarchy at all in their use as JOIN operators.
 * We make them high-precedence to support their use as function names.
 * They wouldn't be given a precedence at all, were it not that we need
 * left-associativity among the JOIN rules themselves.
 */
%left		JOIN CROSS LEFT FULL RIGHT INNER_P NATURAL
/* kluge to keep xml_whitespace_option from causing shift/reduce conflicts */
%right		PRESERVE STRIP_P

%%

/*
 *	The target production for the whole parse.
 */
stmtblock:	stmtmulti
			{
				pg_yyget_extra(yyscanner)->parsetree = $1;
			}
		;

/* the thrashing around here is to discard "empty" statements... */
stmtmulti:	stmtmulti ';' stmt
				{
					if ($3 != NULL)
						$$ = lappend($1, $3);
					else
						$$ = $1;
				}
			| stmt
				{
					if ($1 != NULL)
						$$ = list_make1($1);
					else
						$$ = NIL;
				}
		;

stmt :
			AlterEventTrigStmt
			| AlterDatabaseStmt
			| AlterDatabaseSetStmt
			| AlterDefaultPrivilegesStmt
			| AlterDomainStmt
			| AlterEnumStmt
			| AlterExtensionStmt
			| AlterExtensionContentsStmt
			| AlterFdwStmt
			| AlterForeignServerStmt
			| AlterForeignTableStmt
			| AlterFunctionStmt
			| AlterGroupStmt
			| AlterObjectSchemaStmt
			| AlterOwnerStmt
			| AlterQueueStmt
			| AlterResourceGroupStmt
			| AlterRoleSetStmt
			| AlterRoleStmt
			| AlterSeqStmt
			| AlterSystemStmt
			| AlterTblSpcStmt
			| AlterTSConfigurationStmt
			| AlterTSDictionaryStmt
			| AlterTableStmt
			| AlterCompositeTypeStmt
			| AlterTypeStmt
			| AlterUserMappingStmt
			| AlterUserSetStmt
			| AlterUserStmt
			| AnalyzeStmt
			| CheckPointStmt
			| ClosePortalStmt
			| ClusterStmt
			| CommentStmt
			| ConstraintsSetStmt
			| CopyStmt
			| CreateAsStmt
			| CreateAssertStmt
			| CreateCastStmt
			| CreateConversionStmt
			| CreateDomainStmt
			| CreateExtensionStmt
			| CreateExternalStmt
			| CreateFdwStmt
			| CreateForeignServerStmt
			| CreateForeignTableStmt
			| CreateFunctionStmt
			| CreateGroupStmt
			| CreateMatViewStmt
			| CreateOpClassStmt
			| CreateOpFamilyStmt
			| AlterOpFamilyStmt
			| CreatePLangStmt
			| CreateQueueStmt
			| CreateResourceGroupStmt
			| CreateSchemaStmt
			| CreateSeqStmt
			| CreateStmt
			| CreateTableSpaceStmt
			| CreateTrigStmt
			| CreateEventTrigStmt
			| CreateRoleStmt
			| CreateUserStmt
			| CreateUserMappingStmt
			| CreatedbStmt
			| DeallocateStmt
			| DeclareCursorStmt
			| DefineStmt
			| DeleteStmt
			| DiscardStmt
			| DoStmt
			| DropAssertStmt
			| DropCastStmt
			| DropFdwStmt
			| DropForeignServerStmt
			| DropGroupStmt
			| DropOpClassStmt
			| DropOpFamilyStmt
			| DropOwnedStmt
			| DropPLangStmt
			| DropQueueStmt
			| DropResourceGroupStmt
			| DropRuleStmt
			| DropStmt
			| DropTableSpaceStmt
			| DropTrigStmt
			| DropRoleStmt
			| DropUserStmt
			| DropUserMappingStmt
			| DropdbStmt
			| ExecuteStmt
			| ExplainStmt
			| FetchStmt
			| GrantStmt
			| GrantRoleStmt
			| IndexStmt
			| InsertStmt
			| ListenStmt
			| RefreshMatViewStmt
			| LoadStmt
			| LockStmt
			| NotifyStmt
			| PrepareStmt
			| ReassignOwnedStmt
			| ReindexStmt
			| RemoveAggrStmt
			| RemoveFuncStmt
			| RemoveOperStmt
			| RenameStmt
			| RevokeStmt
			| RevokeRoleStmt
			| RuleStmt
			| SecLabelStmt
			| SelectStmt
			| TransactionStmt
			| TruncateStmt
			| UnlistenStmt
			| UpdateStmt
			| VacuumStmt
			| VariableResetStmt
			| VariableSetStmt
			| VariableShowStmt
			| ViewStmt
			| RetrieveStmt
			| /*EMPTY*/
				{ $$ = NULL; }
		;

/*****************************************************************************
 *
 * Create a new Postgres Resource Queue
 *
 *****************************************************************************/

CreateQueueStmt:
			CREATE RESOURCE QUEUE QueueId OptQueueList
				{
					CreateQueueStmt *n = makeNode(CreateQueueStmt);
					DefElem         *def1 = /* mark start of WITH items */
						makeDefElem("withliststart", 
									(Node *)makeInteger(TRUE));
					n->queue = $4;
					n->options = list_concat(lappend($5, def1), NULL); 
					$$ = (Node *)n;
				}
			| CREATE RESOURCE QUEUE QueueId OptQueueList WITH definition
				{
					CreateQueueStmt *n    = makeNode(CreateQueueStmt);
					DefElem         *def1 = /* mark start of WITH items */
						makeDefElem("withliststart", 
									(Node *)makeInteger(TRUE));
					n->queue = $4;
					n->options = list_concat(lappend($5, def1), $7); 
					$$ = (Node *)n;
				}
		;

/*
 * Options for CREATE and ALTER RESOURCE QUEUE 
 */
OptQueueList:
			OptQueueList OptQueueElem				{ $$ = lappend($1, $2); }
			| /*EMPTY*/								{ $$ = NIL; }
		;

OptQueueElem:
			ACTIVE THRESHOLD NumericOnly
				{
					/* was "activelimit" */
					$$ = makeDefElem("active_statements", (Node *)$3);
				}
			| COST THRESHOLD NumericOnly /* enforce float type in queue.c */
				{
					/* was "costlimit" */
					$$ = makeDefElem("max_cost", (Node *)$3);
				}
			| IGNORE_P THRESHOLD NumericOnly /* enforce float type in queue.c */
				{
					/* was "ignorecostlimit" */
					$$ = makeDefElem("min_cost", (Node *)$3);
				}
			| OVERCOMMIT
				{
					/* was "overcommit" */
					$$ = makeDefElem("cost_overcommit", (Node *)makeInteger(TRUE));
				}
			| NOOVERCOMMIT
				{
					/* was "overcommit" */
					$$ = makeDefElem("cost_overcommit", (Node *)makeInteger(FALSE));
				}
		;

/*****************************************************************************
 *
 * Alter a postgres Resource Queue
 *
 *****************************************************************************/

AlterQueueStmt:
			ALTER RESOURCE QUEUE QueueId OptQueueList
				 {
					AlterQueueStmt *n = makeNode(AlterQueueStmt);
					n->queue = $4;
					n->options = $5;
					$$ = (Node *)n;
				 }
			| ALTER RESOURCE QUEUE QueueId OptQueueList WITH definition
				 {
					AlterQueueStmt *n    = makeNode(AlterQueueStmt);
					DefElem        *def1 = /* mark start of WITH items */
						makeDefElem("withliststart", 
									(Node *)makeInteger(TRUE));
					DefElem        *def2 = /* mark start of WITHOUT items */
						makeDefElem("withoutliststart", 
									(Node *)makeInteger(TRUE));
					n->queue = $4;
					n->options = list_concat(lappend($5, def1), $7); 
					n->options = lappend(n->options, def2); 
					$$ = (Node *)n;
				 }
			| ALTER RESOURCE QUEUE QueueId OptQueueList WITHOUT definition
				 {
					AlterQueueStmt *n    = makeNode(AlterQueueStmt);
					DefElem        *def1 = /* mark start of WITH items */
						makeDefElem("withliststart", 
									(Node *)makeInteger(TRUE));
					DefElem        *def2 = /* mark start of WITHOUT items */
						makeDefElem("withoutliststart", 
									(Node *)makeInteger(TRUE));
					n->queue = $4;
					n->options = lappend($5, def1); 
					n->options = list_concat(lappend(n->options, def2), $7); 
					$$ = (Node *)n;
				 }
			| ALTER RESOURCE QUEUE QueueId OptQueueList WITH definition 
			  WITHOUT definition
				 {
					AlterQueueStmt *n    = makeNode(AlterQueueStmt);
					DefElem        *def1 = /* mark start of WITH items */
						makeDefElem("withliststart", 
									(Node *)makeInteger(TRUE));
					DefElem        *def2 = /* mark start of WITHOUT items */
						makeDefElem("withoutliststart", 
									(Node *)makeInteger(TRUE));
					n->queue = $4;
					n->options = list_concat(lappend($5, def1), $7); 
					n->options = list_concat(lappend(n->options, def2), $9);
					$$ = (Node *)n;
				 }
		;

/*****************************************************************************
 *
 * Drop a postgres Resource Queue
 *
 *****************************************************************************/

DropQueueStmt:
			DROP RESOURCE QUEUE QueueId
				 {
					DropQueueStmt *n = makeNode(DropQueueStmt);
					n->queue = $4;
					$$ = (Node *)n;
				 }
		;

/*****************************************************************************
 *
 * Create a new GPDB Resource Group
 *
 *****************************************************************************/

CreateResourceGroupStmt:
			CREATE RESOURCE GROUP_P name WITH definition
				{
					CreateResourceGroupStmt *n = makeNode(CreateResourceGroupStmt);
					n->name = $4;
					n->options = $6;
					$$ = (Node *)n;
				}
		;

/*****************************************************************************
 *
 * Drop a GPDB Resource Group
 *
 *****************************************************************************/

DropResourceGroupStmt:
			DROP RESOURCE GROUP_P name
				 {
					DropResourceGroupStmt *n = makeNode(DropResourceGroupStmt);
					n->name = $4;
					$$ = (Node *)n;
				 }
		;

/*****************************************************************************
 *
 * Alter a GPDB Resource Group
 *
 *****************************************************************************/
AlterResourceGroupStmt:
			ALTER RESOURCE GROUP_P name SET OptResourceGroupList
				 {
					AlterResourceGroupStmt *n = makeNode(AlterResourceGroupStmt);
					n->name = $4;
					n->options = $6;
					$$ = (Node *)n;
				 }
		;

/*
 * Option for ALTER RESOURCE GROUP
 */
OptResourceGroupList: OptResourceGroupElem			{ $$ = list_make1($1); }
		;

OptResourceGroupElem:
			CONCURRENCY SignedIconst
				{
					/* was "concurrency" */
					$$ = makeDefElem("concurrency", (Node *) makeInteger($2));
				}
			| CPU_RATE_LIMIT SignedIconst
				{
					$$ = makeDefElem("cpu_rate_limit", (Node *) makeInteger($2));
				}
			| CPUSET Sconst
				{
					$$ = makeDefElem("cpuset", (Node *) makeString($2));
				}
			| MEMORY_SHARED_QUOTA SignedIconst
				{
					$$ = makeDefElem("memory_shared_quota", (Node *) makeInteger($2));
				}
			| MEMORY_LIMIT SignedIconst
				{
					$$ = makeDefElem("memory_limit", (Node *) makeInteger($2));
				}
			| MEMORY_SPILL_RATIO SignedIconst
				{
					$$ = makeDefElem("memory_spill_ratio", (Node *) makeInteger($2));
				}
		;

/*****************************************************************************
 *
 * Create a new Postgres DBMS role
 *
 *****************************************************************************/

CreateRoleStmt:
			CREATE ROLE RoleId opt_with OptRoleList
				{
					CreateRoleStmt *n = makeNode(CreateRoleStmt);
					n->stmt_type = ROLESTMT_ROLE;
					n->role = $3;
					n->options = $5;
					$$ = (Node *)n;
				}
		;


opt_with:	WITH									{}
			| /*EMPTY*/								{}
		;

/*
 * Options for CREATE ROLE and ALTER ROLE (also used by CREATE/ALTER USER
 * for backwards compatibility).  Note: the only option required by SQL99
 * is "WITH ADMIN name".
 */
OptRoleList:
			OptRoleList CreateOptRoleElem			{ $$ = lappend($1, $2); }
			| /* EMPTY */							{ $$ = NIL; }
		;

AlterOptRoleList:
			AlterOptRoleList AlterOnlyOptRoleElem	{ $$ = lappend($1, $2); }
			| /* EMPTY */							{ $$ = NIL; }
		;

/*
 * GPDB: Options that are allowed in ALTER ROLE, but *not* CREATE ROLE.
 * AlterOptRoleElem is for elements that are allowed in either.
 *
 * At the moment this applies only to ALTER ROLE ... DROP DENY.
 */
AlterOnlyOptRoleElem:
			AlterOptRoleElem			{ $$ = $1; }
			| DROP DENY FOR deny_point	{ $$ = makeDefElem("drop_deny", $4); }
		;

AlterOptRoleElem:
			PASSWORD Sconst
				{
					$$ = makeDefElem("password",
									 (Node *)makeString($2));
				}
			| PASSWORD NULL_P
				{
					$$ = makeDefElem("password", NULL);
				}
			| ENCRYPTED PASSWORD Sconst
				{
					$$ = makeDefElem("encryptedPassword",
									 (Node *)makeString($3));
				}
			| UNENCRYPTED PASSWORD Sconst
				{
					$$ = makeDefElem("unencryptedPassword",
									 (Node *)makeString($3));
				}
			| INHERIT
				{
					$$ = makeDefElem("inherit", (Node *)makeInteger(TRUE));
				}
			| CONNECTION LIMIT SignedIconst
				{
					$$ = makeDefElem("connectionlimit", (Node *)makeInteger($3));
				}
			| VALID UNTIL Sconst
				{
					$$ = makeDefElem("validUntil", (Node *)makeString($3));
				}
			| RESOURCE QUEUE any_name
				{
					$$ = makeDefElem("resourceQueue", (Node *)$3);
				}
			| RESOURCE GROUP_P any_name
				{
					$$ = makeDefElem("resourceGroup", (Node *)$3);
				}
			| CREATEEXTTABLE exttab_auth_list
				{
					$$ = makeDefElem("exttabauth", (Node *)$2);
				}
			| NOCREATEEXTTABLE exttab_auth_list
				{
					$$ = makeDefElem("exttabnoauth", (Node *)$2);
				}
		/*	Supported but not documented for roles, for use by ALTER GROUP. */
			| USER role_list
				{
					$$ = makeDefElem("rolemembers", (Node *)$2);
				}
			| deny_login_role
				{
					$$ = makeDefElem("deny", (Node *)$1);
				}
			| IDENT
				{
					/*
					 * We handle identifiers that aren't parser keywords with
					 * the following special-case codes, to avoid bloating the
					 * size of the main parser.
					 */
					if (strcmp($1, "superuser") == 0)
						$$ = makeDefElem("superuser", (Node *)makeInteger(TRUE));
					else if (strcmp($1, "nosuperuser") == 0)
						$$ = makeDefElem("superuser", (Node *)makeInteger(FALSE));
					else if (strcmp($1, "createuser") == 0)
					{
						/* For backwards compatibility, synonym for SUPERUSER */
						$$ = makeDefElem("superuser", (Node *)makeInteger(TRUE));
					}
					else if (strcmp($1, "nocreateuser") == 0)
					{
						/* For backwards compatibility, synonym for SUPERUSER */
						$$ = makeDefElem("superuser", (Node *)makeInteger(FALSE));
					}
					else if (strcmp($1, "createrole") == 0)
						$$ = makeDefElem("createrole", (Node *)makeInteger(TRUE));
					else if (strcmp($1, "nocreaterole") == 0)
						$$ = makeDefElem("createrole", (Node *)makeInteger(FALSE));
					else if (strcmp($1, "replication") == 0)
						$$ = makeDefElem("isreplication", (Node *)makeInteger(TRUE));
					else if (strcmp($1, "noreplication") == 0)
						$$ = makeDefElem("isreplication", (Node *)makeInteger(FALSE));
					else if (strcmp($1, "createdb") == 0)
						$$ = makeDefElem("createdb", (Node *)makeInteger(TRUE));
					else if (strcmp($1, "nocreatedb") == 0)
						$$ = makeDefElem("createdb", (Node *)makeInteger(FALSE));
					else if (strcmp($1, "login") == 0)
						$$ = makeDefElem("canlogin", (Node *)makeInteger(TRUE));
					else if (strcmp($1, "nologin") == 0)
						$$ = makeDefElem("canlogin", (Node *)makeInteger(FALSE));
					else if (strcmp($1, "noinherit") == 0)
					{
						/*
						 * Note that INHERIT is a keyword, so it's handled by main parser, but
						 * NOINHERIT is handled here.
						 */
						$$ = makeDefElem("inherit", (Node *)makeInteger(FALSE));
					}
					else
						ereport(ERROR,
								(errcode(ERRCODE_SYNTAX_ERROR),
								 errmsg("unrecognized role option \"%s\"", $1),
									 parser_errposition(@1)));
				}
		;

CreateOptRoleElem:
			AlterOptRoleElem			{ $$ = $1; }
			/* The following are not supported by ALTER ROLE/USER/GROUP */
			| SYSID Iconst
				{
					$$ = makeDefElem("sysid", (Node *)makeInteger($2));
				}
			| ADMIN role_list
				{
					$$ = makeDefElem("adminmembers", (Node *)$2);
				}
			| ROLE role_list
				{
					$$ = makeDefElem("rolemembers", (Node *)$2);
				}
			| IN_P ROLE role_list
				{
					$$ = makeDefElem("addroleto", (Node *)$3);
				}
			| IN_P GROUP_P role_list
				{
					$$ = makeDefElem("addroleto", (Node *)$3);
				}
		;

deny_login_role: DENY deny_interval { $$ = (Node *)$2; }
			| DENY deny_point { $$ = (Node *)$2; }
		;

deny_interval: BETWEEN deny_point AND deny_point
				{
					DenyLoginInterval *n = makeNode(DenyLoginInterval);
					n->start = (DenyLoginPoint *)$2;
					n->end = (DenyLoginPoint *)$4;
					$$ = (Node *)n;
				}
		;

deny_day_specifier: Sconst { $$ = (Node *)makeString($1); }
			| Iconst { $$ = (Node *)makeInteger($1); }
		;

deny_point: DAY_P deny_day_specifier opt_time
				{
					DenyLoginPoint *n = makeNode(DenyLoginPoint);
					n->day = (Value *)$2;
					n->time = (Value *)$3;
					$$ = (Node *)n;
				}
		;

opt_time: TIME Sconst { $$ = (Node *)makeString($2); }
		| /* nothing */ { $$ = NULL; }
		;

exttab_auth_list:
		'(' keyvalue_list ')'	{ $$ = $2; }
		| /*EMPTY*/				{ $$ = NIL; }
		;

keyvalue_list:
		keyvalue_pair						{ $$ = list_make1($1); }
		| keyvalue_list ',' keyvalue_pair	{ $$ = lappend($1, $3); }
		;

keyvalue_pair:
		ColLabel '=' Sconst
		{
			$$ = makeDefElem($1, (Node *)makeString($3));
		}
		;


/*****************************************************************************
 *
 * Create a new Postgres DBMS user (role with implied login ability)
 *
 *****************************************************************************/

CreateUserStmt:
			CREATE USER RoleId opt_with OptRoleList
				{
					CreateRoleStmt *n = makeNode(CreateRoleStmt);
					n->stmt_type = ROLESTMT_USER;
					n->role = $3;
					n->options = $5;
					$$ = (Node *)n;
				}
		;


/*****************************************************************************
 *
 * Alter a postgresql DBMS role
 *
 *****************************************************************************/

AlterRoleStmt:
			ALTER ROLE RoleId opt_with AlterOptRoleList
				 {
					AlterRoleStmt *n = makeNode(AlterRoleStmt);
					n->role = $3;
					n->action = +1;	/* add, if there are members */
					n->options = $5;
					$$ = (Node *)n;
				 }
		;

opt_in_database:
			   /* EMPTY */					{ $$ = NULL; }
			| IN_P DATABASE database_name	{ $$ = $3; }
		;

AlterRoleSetStmt:
			ALTER ROLE RoleId opt_in_database SetResetClause
				{
					AlterRoleSetStmt *n = makeNode(AlterRoleSetStmt);
					n->role = $3;
					n->database = $4;
					n->setstmt = $5;
					$$ = (Node *)n;
				}
			| ALTER ROLE ALL opt_in_database SetResetClause
				{
					AlterRoleSetStmt *n = makeNode(AlterRoleSetStmt);
					n->role = NULL;
					n->database = $4;
					n->setstmt = $5;
					$$ = (Node *)n;
				}
		;


/*****************************************************************************
 *
 * Alter a postgresql DBMS user
 *
 *****************************************************************************/

AlterUserStmt:
			ALTER USER RoleId opt_with AlterOptRoleList
				 {
					AlterRoleStmt *n = makeNode(AlterRoleStmt);
					n->role = $3;
					n->action = +1;	/* add, if there are members */
					n->options = $5;
					$$ = (Node *)n;
				 }
		;


AlterUserSetStmt:
			ALTER USER RoleId opt_in_database SetResetClause
				{
					AlterRoleSetStmt *n = makeNode(AlterRoleSetStmt);
					n->role = $3;
					n->database = $4;
					n->setstmt = $5;
					$$ = (Node *)n;
				}
			| ALTER USER ALL opt_in_database SetResetClause
				{
					AlterRoleSetStmt *n = makeNode(AlterRoleSetStmt);
					n->role = NULL;
					n->database = $4;
					n->setstmt = $5;
					$$ = (Node *)n;
				}
			;


/*****************************************************************************
 *
 * Drop a postgresql DBMS role
 *
 * XXX Ideally this would have CASCADE/RESTRICT options, but since a role
 * might own objects in multiple databases, there is presently no way to
 * implement either cascading or restricting.  Caveat DBA.
 *****************************************************************************/

DropRoleStmt:
			DROP ROLE role_list
				{
					DropRoleStmt *n = makeNode(DropRoleStmt);
					n->missing_ok = FALSE;
					n->roles = $3;
					$$ = (Node *)n;
				}
			| DROP ROLE IF_P EXISTS role_list
				{
					DropRoleStmt *n = makeNode(DropRoleStmt);
					n->missing_ok = TRUE;
					n->roles = $5;
					$$ = (Node *)n;
				}
			;

/*****************************************************************************
 *
 * Drop a postgresql DBMS user
 *
 * XXX Ideally this would have CASCADE/RESTRICT options, but since a user
 * might own objects in multiple databases, there is presently no way to
 * implement either cascading or restricting.  Caveat DBA.
 *****************************************************************************/

DropUserStmt:
			DROP USER role_list
				{
					DropRoleStmt *n = makeNode(DropRoleStmt);
					n->missing_ok = FALSE;
					n->roles = $3;
					$$ = (Node *)n;
				}
			| DROP USER IF_P EXISTS role_list
				{
					DropRoleStmt *n = makeNode(DropRoleStmt);
					n->roles = $5;
					n->missing_ok = TRUE;
					$$ = (Node *)n;
				}
			;


/*****************************************************************************
 *
 * Create a postgresql group (role without login ability)
 *
 *****************************************************************************/

CreateGroupStmt:
			CREATE GROUP_P RoleId opt_with OptRoleList
				{
					CreateRoleStmt *n = makeNode(CreateRoleStmt);
					n->stmt_type = ROLESTMT_GROUP;
					n->role = $3;
					n->options = $5;
					$$ = (Node *)n;
				}
		;


/*****************************************************************************
 *
 * Alter a postgresql group
 *
 *****************************************************************************/

AlterGroupStmt:
			ALTER GROUP_P RoleId add_drop USER role_list
				{
					AlterRoleStmt *n = makeNode(AlterRoleStmt);
					n->role = $3;
					n->action = $4;
					n->options = list_make1(makeDefElem("rolemembers",
														(Node *)$6));
					$$ = (Node *)n;
				}
		;

add_drop:	ADD_P									{ $$ = +1; }
			| DROP									{ $$ = -1; }
		;


/*****************************************************************************
 *
 * Drop a postgresql group
 *
 * XXX see above notes about cascading DROP USER; groups have same problem.
 *****************************************************************************/

DropGroupStmt:
			DROP GROUP_P role_list
				{
					DropRoleStmt *n = makeNode(DropRoleStmt);
					n->missing_ok = FALSE;
					n->roles = $3;
					$$ = (Node *)n;
				}
			| DROP GROUP_P IF_P EXISTS role_list
				{
					DropRoleStmt *n = makeNode(DropRoleStmt);
					n->missing_ok = TRUE;
					n->roles = $5;
					$$ = (Node *)n;
				}
		;


/*****************************************************************************
 *
 * Manipulate a schema
 *
 *****************************************************************************/

CreateSchemaStmt:
			CREATE SCHEMA OptSchemaName AUTHORIZATION RoleId OptSchemaEltList
				{
					CreateSchemaStmt *n = makeNode(CreateSchemaStmt);
					/* One can omit the schema name or the authorization id. */
					if ($3 != NULL)
						n->schemaname = $3;
					else
						n->schemaname = $5;
					n->authid = $5;
					n->schemaElts = $6;
					n->if_not_exists = false;
					$$ = (Node *)n;
				}
			| CREATE SCHEMA ColId OptSchemaEltList
				{
					CreateSchemaStmt *n = makeNode(CreateSchemaStmt);
					/* ...but not both */
					n->schemaname = $3;
					n->authid = NULL;
					n->schemaElts = $4;
					n->if_not_exists = false;
					$$ = (Node *)n;
				}
			| CREATE SCHEMA IF_P NOT EXISTS OptSchemaName AUTHORIZATION RoleId OptSchemaEltList
				{
					CreateSchemaStmt *n = makeNode(CreateSchemaStmt);
					/* One can omit the schema name or the authorization id. */
					if ($6 != NULL)
						n->schemaname = $6;
					else
						n->schemaname = $8;
					n->authid = $8;
					if ($9 != NIL)
						ereport(ERROR,
								(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
								 errmsg("CREATE SCHEMA IF NOT EXISTS cannot include schema elements"),
								 parser_errposition(@9)));
					n->schemaElts = $9;
					n->if_not_exists = true;
					$$ = (Node *)n;
				}
			| CREATE SCHEMA IF_P NOT EXISTS ColId OptSchemaEltList
				{
					CreateSchemaStmt *n = makeNode(CreateSchemaStmt);
					/* ...but not both */
					n->schemaname = $6;
					n->authid = NULL;
					if ($7 != NIL)
						ereport(ERROR,
								(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
								 errmsg("CREATE SCHEMA IF NOT EXISTS cannot include schema elements"),
								 parser_errposition(@7)));
					n->schemaElts = $7;
					n->if_not_exists = true;
					$$ = (Node *)n;
				}
		;

OptSchemaName:
			ColId									{ $$ = $1; }
			| /* EMPTY */							{ $$ = NULL; }
		;

OptSchemaEltList:
			OptSchemaEltList schema_stmt
				{
					if (@$ < 0)			/* see comments for YYLLOC_DEFAULT */
						@$ = @2;
					$$ = lappend($1, $2);
				}
			| /* EMPTY */
				{ $$ = NIL; }
		;

/*
 *	schema_stmt are the ones that can show up inside a CREATE SCHEMA
 *	statement (in addition to by themselves).
 */
schema_stmt:
			CreateStmt
			| IndexStmt
			| CreateSeqStmt
			| CreateTrigStmt
			| GrantStmt
			| ViewStmt
		;


/*****************************************************************************
 *
 * Set PG internal variable
 *	  SET name TO 'var_value'
 * Include SQL syntax (thomas 1997-10-22):
 *	  SET TIME ZONE 'var_value'
 *
 *****************************************************************************/

VariableSetStmt:
			SET set_rest
				{
					VariableSetStmt *n = $2;
					n->is_local = false;
					$$ = (Node *) n;
				}
			| SET LOCAL set_rest
				{
					VariableSetStmt *n = $3;
					n->is_local = true;
					$$ = (Node *) n;
				}
			| SET SESSION set_rest
				{
					VariableSetStmt *n = $3;
					n->is_local = false;
					$$ = (Node *) n;
				}
		;

set_rest:
			TRANSACTION transaction_mode_list
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_SET_MULTI;
					n->name = "TRANSACTION";
					n->args = $2;
					$$ = n;
				}
			| SESSION CHARACTERISTICS AS TRANSACTION transaction_mode_list
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_SET_MULTI;
					n->name = "SESSION CHARACTERISTICS";
					n->args = $5;
					$$ = n;
				}
			| set_rest_more
			;

generic_set:
			var_name TO var_list
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_SET_VALUE;
					n->name = $1;
					n->args = $3;
					$$ = n;
				}
			| var_name '=' var_list
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_SET_VALUE;
					n->name = $1;
					n->args = $3;
					$$ = n;
				}
			| var_name TO DEFAULT
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_SET_DEFAULT;
					n->name = $1;
					$$ = n;
				}
			| var_name '=' DEFAULT
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_SET_DEFAULT;
					n->name = $1;
					$$ = n;
				}
		;

set_rest_more:	/* Generic SET syntaxes: */
			generic_set 						{$$ = $1;}
			| var_name FROM CURRENT_P
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_SET_CURRENT;
					n->name = $1;
					$$ = n;
				}
			/* Special syntaxes mandated by SQL standard: */
			| TIME ZONE zone_value
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_SET_VALUE;
					n->name = "timezone";
					if ($3 != NULL)
						n->args = list_make1($3);
					else
						n->kind = VAR_SET_DEFAULT;
					$$ = n;
				}
			| CATALOG_P Sconst
				{
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("current database cannot be changed"),
							 parser_errposition(@2)));
					$$ = NULL; /*not reached*/
				}
			| SCHEMA Sconst
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_SET_VALUE;
					n->name = "search_path";
					n->args = list_make1(makeStringConst($2, @2));
					$$ = n;
				}
			| NAMES opt_encoding
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_SET_VALUE;
					n->name = "client_encoding";
					if ($2 != NULL)
						n->args = list_make1(makeStringConst($2, @2));
					else
						n->kind = VAR_SET_DEFAULT;
					$$ = n;
				}
			| ROLE NonReservedWord_or_Sconst
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_SET_VALUE;
					n->name = "role";
					n->args = list_make1(makeStringConst($2, @2));
					$$ = n;
				}
			| SESSION AUTHORIZATION NonReservedWord_or_Sconst
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_SET_VALUE;
					n->name = "session_authorization";
					n->args = list_make1(makeStringConst($3, @3));
					$$ = n;
				}
			| SESSION AUTHORIZATION DEFAULT
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_SET_DEFAULT;
					n->name = "session_authorization";
					$$ = n;
				}
			| XML_P OPTION document_or_content
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_SET_VALUE;
					n->name = "xmloption";
					n->args = list_make1(makeStringConst($3 == XMLOPTION_DOCUMENT ? "DOCUMENT" : "CONTENT", @3));
					$$ = n;
				}
			/* Special syntaxes invented by PostgreSQL: */
			| TRANSACTION SNAPSHOT Sconst
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_SET_MULTI;
					n->name = "TRANSACTION SNAPSHOT";
					n->args = list_make1(makeStringConst($3, @3));
					$$ = n;
				}
		;

var_name:	ColId								{ $$ = $1; }
			| var_name '.' ColId
				{ $$ = psprintf("%s.%s", $1, $3); }
		;

var_list:	var_value								{ $$ = list_make1($1); }
			| var_list ',' var_value				{ $$ = lappend($1, $3); }
		;

var_value:	opt_boolean_or_string
				{ $$ = makeStringConst($1, @1); }
			| NumericOnly
				{ $$ = makeAConst($1, @1); }
		;

iso_level:	READ UNCOMMITTED						{ $$ = "read uncommitted"; }
			| READ COMMITTED						{ $$ = "read committed"; }
			| REPEATABLE READ						{ $$ = "repeatable read"; }
			| SERIALIZABLE							{ $$ = "serializable"; }
		;

opt_boolean_or_string:
			TRUE_P									{ $$ = "true"; }
			| FALSE_P								{ $$ = "false"; }
			| ON									{ $$ = "on"; }
			/*
			 * OFF is also accepted as a boolean value, but is handled by
			 * the NonReservedWord rule.  The action for booleans and strings
			 * is the same, so we don't need to distinguish them here.
			 */
			| NonReservedWord_or_Sconst				{ $$ = $1; }
		;

/* Timezone values can be:
 * - a string such as 'pst8pdt'
 * - an identifier such as "pst8pdt"
 * - an integer or floating point number
 * - a time interval per SQL99
 * ColId gives reduce/reduce errors against ConstInterval and LOCAL,
 * so use IDENT and reject anything which is a reserved word.
 */
zone_value:
			Sconst
				{
					$$ = makeStringConst($1, @1);
				}
			| IDENT
				{
					$$ = makeStringConst($1, @1);
				}
			| ConstInterval Sconst opt_interval
				{
					TypeName *t = $1;
					if ($3 != NIL)
					{
						A_Const *n = (A_Const *) linitial($3);
						if ((n->val.val.ival & ~(INTERVAL_MASK(HOUR) | INTERVAL_MASK(MINUTE))) != 0)
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("time zone interval must be HOUR or HOUR TO MINUTE"),
									 parser_errposition(@3)));
					}
					t->typmods = $3;
					$$ = makeStringConstCast($2, @2, t);
				}
			| ConstInterval '(' Iconst ')' Sconst opt_interval
				{
					TypeName *t = $1;
					if ($6 != NIL)
					{
						A_Const *n = (A_Const *) linitial($6);
						if ((n->val.val.ival & ~(INTERVAL_MASK(HOUR) | INTERVAL_MASK(MINUTE))) != 0)
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("time zone interval must be HOUR or HOUR TO MINUTE"),
									 parser_errposition(@6)));
						if (list_length($6) != 1)
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("interval precision specified twice"),
									 parser_errposition(@1)));
						t->typmods = lappend($6, makeIntConst($3, @3));
					}
					else
						t->typmods = list_make2(makeIntConst(INTERVAL_FULL_RANGE, -1),
												makeIntConst($3, @3));
					$$ = makeStringConstCast($5, @5, t);
				}
			| NumericOnly							{ $$ = makeAConst($1, @1); }
			| DEFAULT								{ $$ = NULL; }
			| LOCAL									{ $$ = NULL; }
		;

opt_encoding:
			Sconst									{ $$ = $1; }
			| DEFAULT								{ $$ = NULL; }
			| /*EMPTY*/								{ $$ = NULL; }
		;

NonReservedWord_or_Sconst:
			NonReservedWord							{ $$ = $1; }
			| Sconst								{ $$ = $1; }
		;

VariableResetStmt:
			RESET reset_rest						{ $$ = (Node *) $2; }
		;

reset_rest:
			generic_reset							{ $$ = $1; }
			| TIME ZONE
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_RESET;
					n->name = "timezone";
					$$ = n;
				}
			| TRANSACTION ISOLATION LEVEL
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_RESET;
					n->name = "transaction_isolation";
					$$ = n;
				}
			| SESSION AUTHORIZATION
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_RESET;
					n->name = "session_authorization";
					$$ = n;
				}
		;

generic_reset:
			var_name
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_RESET;
					n->name = $1;
					$$ = n;
				}
			| ALL
				{
					VariableSetStmt *n = makeNode(VariableSetStmt);
					n->kind = VAR_RESET_ALL;
					$$ = n;
				}
		;

/* SetResetClause allows SET or RESET without LOCAL */
SetResetClause:
			SET set_rest					{ $$ = $2; }
			| VariableResetStmt				{ $$ = (VariableSetStmt *) $1; }
		;

/* SetResetClause allows SET or RESET without LOCAL */
FunctionSetResetClause:
			SET set_rest_more				{ $$ = $2; }
			| VariableResetStmt				{ $$ = (VariableSetStmt *) $1; }
		;


VariableShowStmt:
			SHOW var_name
				{
					VariableShowStmt *n = makeNode(VariableShowStmt);
					n->name = $2;
					$$ = (Node *) n;
				}
			| SHOW TIME ZONE
				{
					VariableShowStmt *n = makeNode(VariableShowStmt);
					n->name = "timezone";
					$$ = (Node *) n;
				}
			| SHOW TRANSACTION ISOLATION LEVEL
				{
					VariableShowStmt *n = makeNode(VariableShowStmt);
					n->name = "transaction_isolation";
					$$ = (Node *) n;
				}
			| SHOW SESSION AUTHORIZATION
				{
					VariableShowStmt *n = makeNode(VariableShowStmt);
					n->name = "session_authorization";
					$$ = (Node *) n;
				}
			| SHOW ALL
				{
					VariableShowStmt *n = makeNode(VariableShowStmt);
					n->name = "all";
					$$ = (Node *) n;
				}
		;


ConstraintsSetStmt:
			SET CONSTRAINTS constraints_set_list constraints_set_mode
				{
					ConstraintsSetStmt *n = makeNode(ConstraintsSetStmt);
					n->constraints = $3;
					n->deferred = $4;
					$$ = (Node *) n;
				}
		;

constraints_set_list:
			ALL										{ $$ = NIL; }
			| qualified_name_list					{ $$ = $1; }
		;

constraints_set_mode:
			DEFERRED								{ $$ = TRUE; }
			| IMMEDIATE								{ $$ = FALSE; }
		;


/*
 * Checkpoint statement
 */
CheckPointStmt:
			CHECKPOINT
				{
					CheckPointStmt *n = makeNode(CheckPointStmt);
					$$ = (Node *)n;
				}
		;


/*****************************************************************************
 *
 * DISCARD { ALL | TEMP | PLANS | SEQUENCES }
 *
 *****************************************************************************/

DiscardStmt:
			DISCARD ALL
				{
					DiscardStmt *n = makeNode(DiscardStmt);
					n->target = DISCARD_ALL;
					$$ = (Node *) n;
				}
			| DISCARD TEMP
				{
					DiscardStmt *n = makeNode(DiscardStmt);
					n->target = DISCARD_TEMP;
					$$ = (Node *) n;
				}
			| DISCARD TEMPORARY
				{
					DiscardStmt *n = makeNode(DiscardStmt);
					n->target = DISCARD_TEMP;
					$$ = (Node *) n;
				}
			| DISCARD PLANS
				{
					DiscardStmt *n = makeNode(DiscardStmt);
					n->target = DISCARD_PLANS;
					$$ = (Node *) n;
				}
			| DISCARD SEQUENCES
				{
					DiscardStmt *n = makeNode(DiscardStmt);
					n->target = DISCARD_SEQUENCES;
					$$ = (Node *) n;
				}

		;


/*****************************************************************************
 *
 *	ALTER [ TABLE | INDEX | SEQUENCE | VIEW | MATERIALIZED VIEW ] variations
 *
 * Note: we accept all subcommands for each of the five variants, and sort
 * out what's really legal at execution time.
 *****************************************************************************/

AlterTableStmt:
			ALTER TABLE relation_expr alter_table_cmds
				{
					AlterTableStmt *n = makeNode(AlterTableStmt);
					n->relation = $3;
					n->cmds = $4;
					n->relkind = OBJECT_TABLE;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
		|	ALTER TABLE IF_P EXISTS relation_expr alter_table_cmds
				{
					AlterTableStmt *n = makeNode(AlterTableStmt);
					n->relation = $5;
					n->cmds = $6;
					n->relkind = OBJECT_TABLE;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
		|	ALTER EXTERNAL TABLE relation_expr alter_table_cmds
				{
					AlterTableStmt *n = makeNode(AlterTableStmt);
					n->relation = $4;
					n->cmds = $5;
					n->relkind = OBJECT_EXTTABLE;
					$$ = (Node *)n;
				}
		|	ALTER TABLE ALL IN_P TABLESPACE name SET TABLESPACE name opt_nowait
				{
					AlterTableMoveAllStmt *n =
						makeNode(AlterTableMoveAllStmt);
					n->orig_tablespacename = $6;
					n->objtype = OBJECT_TABLE;
					n->roles = NIL;
					n->new_tablespacename = $9;
					n->nowait = $10;
					$$ = (Node *)n;
				}
		|	ALTER TABLE ALL IN_P TABLESPACE name OWNED BY role_list SET TABLESPACE name opt_nowait
				{
					AlterTableMoveAllStmt *n =
						makeNode(AlterTableMoveAllStmt);
					n->orig_tablespacename = $6;
					n->objtype = OBJECT_TABLE;
					n->roles = $9;
					n->new_tablespacename = $12;
					n->nowait = $13;
					$$ = (Node *)n;
				}
		|	ALTER INDEX qualified_name alter_table_cmds
				{
					AlterTableStmt *n = makeNode(AlterTableStmt);
					n->relation = $3;
					n->cmds = $4;
					n->relkind = OBJECT_INDEX;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
		|	ALTER INDEX IF_P EXISTS qualified_name alter_table_cmds
				{
					AlterTableStmt *n = makeNode(AlterTableStmt);
					n->relation = $5;
					n->cmds = $6;
					n->relkind = OBJECT_INDEX;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
		|	ALTER INDEX ALL IN_P TABLESPACE name SET TABLESPACE name opt_nowait
				{
					AlterTableMoveAllStmt *n =
						makeNode(AlterTableMoveAllStmt);
					n->orig_tablespacename = $6;
					n->objtype = OBJECT_INDEX;
					n->roles = NIL;
					n->new_tablespacename = $9;
					n->nowait = $10;
					$$ = (Node *)n;
				}
		|	ALTER INDEX ALL IN_P TABLESPACE name OWNED BY role_list SET TABLESPACE name opt_nowait
				{
					AlterTableMoveAllStmt *n =
						makeNode(AlterTableMoveAllStmt);
					n->orig_tablespacename = $6;
					n->objtype = OBJECT_INDEX;
					n->roles = $9;
					n->new_tablespacename = $12;
					n->nowait = $13;
					$$ = (Node *)n;
				}
		|	ALTER SEQUENCE qualified_name alter_table_cmds
				{
					AlterTableStmt *n = makeNode(AlterTableStmt);
					n->relation = $3;
					n->cmds = $4;
					n->relkind = OBJECT_SEQUENCE;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
		|	ALTER SEQUENCE IF_P EXISTS qualified_name alter_table_cmds
				{
					AlterTableStmt *n = makeNode(AlterTableStmt);
					n->relation = $5;
					n->cmds = $6;
					n->relkind = OBJECT_SEQUENCE;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
		|	ALTER VIEW qualified_name alter_table_cmds
				{
					AlterTableStmt *n = makeNode(AlterTableStmt);
					n->relation = $3;
					n->cmds = $4;
					n->relkind = OBJECT_VIEW;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
		|	ALTER VIEW IF_P EXISTS qualified_name alter_table_cmds
				{
					AlterTableStmt *n = makeNode(AlterTableStmt);
					n->relation = $5;
					n->cmds = $6;
					n->relkind = OBJECT_VIEW;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
		|	ALTER MATERIALIZED VIEW qualified_name alter_table_cmds
				{
					AlterTableStmt *n = makeNode(AlterTableStmt);
					n->relation = $4;
					n->cmds = $5;
					n->relkind = OBJECT_MATVIEW;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
		|	ALTER MATERIALIZED VIEW IF_P EXISTS qualified_name alter_table_cmds
				{
					AlterTableStmt *n = makeNode(AlterTableStmt);
					n->relation = $6;
					n->cmds = $7;
					n->relkind = OBJECT_MATVIEW;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
		|	ALTER MATERIALIZED VIEW ALL IN_P TABLESPACE name SET TABLESPACE name opt_nowait
				{
					AlterTableMoveAllStmt *n =
						makeNode(AlterTableMoveAllStmt);
					n->orig_tablespacename = $7;
					n->objtype = OBJECT_MATVIEW;
					n->roles = NIL;
					n->new_tablespacename = $10;
					n->nowait = $11;
					$$ = (Node *)n;
				}
		|	ALTER MATERIALIZED VIEW ALL IN_P TABLESPACE name OWNED BY role_list SET TABLESPACE name opt_nowait
				{
					AlterTableMoveAllStmt *n =
						makeNode(AlterTableMoveAllStmt);
					n->orig_tablespacename = $7;
					n->objtype = OBJECT_MATVIEW;
					n->roles = $10;
					n->new_tablespacename = $13;
					n->nowait = $14;
					$$ = (Node *)n;
				}
		;

alter_table_cmds:
			alter_table_cmd							{ $$ = list_make1($1); }
			| alter_table_cmds ',' alter_table_cmd	{ $$ = lappend($1, $3); }
		;

alter_table_cmd:
			/* ALTER TABLE <name> ADD <coldef> */
			ADD_P columnDef
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_AddColumn;
					n->def = $2;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ADD COLUMN <coldef> */
			| ADD_P COLUMN columnDef
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_AddColumn;
					n->def = $3;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ALTER [COLUMN] <colname> {SET DEFAULT <expr>|DROP DEFAULT} */
			| ALTER opt_column ColId alter_column_default
				{
					ColumnDef *colDef = makeNode(ColumnDef);
					colDef->raw_default = $4;
					
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_ColumnDefault;
					n->name = $3;
					n->def = (Node *) colDef;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ALTER [COLUMN] <colname> DROP NOT NULL */
			| ALTER opt_column ColId DROP NOT NULL_P
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_DropNotNull;
					n->name = $3;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ALTER [COLUMN] <colname> SET NOT NULL */
			| ALTER opt_column ColId SET NOT NULL_P
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_SetNotNull;
					n->name = $3;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ALTER [COLUMN] <colname> SET STATISTICS <SignedIconst> */
			| ALTER opt_column ColId SET STATISTICS SignedIconst
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_SetStatistics;
					n->name = $3;
					n->def = (Node *) makeInteger($6);
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ALTER [COLUMN] <colname> SET ( column_parameter = value [, ... ] ) */
			| ALTER opt_column ColId SET reloptions
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_SetOptions;
					n->name = $3;
					n->def = (Node *) $5;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ALTER [COLUMN] <colname> SET ( column_parameter = value [, ... ] ) */
			| ALTER opt_column ColId RESET reloptions
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_ResetOptions;
					n->name = $3;
					n->def = (Node *) $5;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ALTER [COLUMN] <colname> SET STORAGE <storagemode> */
			| ALTER opt_column ColId SET STORAGE ColId
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_SetStorage;
					n->name = $3;
					n->def = (Node *) makeString($6);
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> DROP [COLUMN] IF EXISTS <colname> [RESTRICT|CASCADE] */
			| DROP opt_column IF_P EXISTS ColId opt_drop_behavior
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_DropColumn;
					n->name = $5;
					n->behavior = $6;
					n->missing_ok = TRUE;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> DROP [COLUMN] <colname> [RESTRICT|CASCADE] */
			| DROP opt_column ColId opt_drop_behavior
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_DropColumn;
					n->name = $3;
					n->behavior = $4;
					n->missing_ok = FALSE;
					$$ = (Node *)n;
				}
			/*
			 * ALTER TABLE <name> ALTER [COLUMN] <colname> [SET DATA] TYPE <typename>
			 *		[ USING <expression> ]
			 */
			| ALTER opt_column ColId opt_set_data TYPE_P Typename opt_collate_clause alter_using
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					ColumnDef *def = makeNode(ColumnDef);
					n->subtype = AT_AlterColumnType;
					n->name = $3;
					n->def = (Node *) def;
					/* We only use these fields of the ColumnDef node */
					def->typeName = $6;
					def->collClause = (CollateClause *) $7;
					def->raw_default = $8;
					def->location = @3;
					$$ = (Node *)n;
				}
			/* ALTER FOREIGN TABLE <name> ALTER [COLUMN] <colname> OPTIONS */
			| ALTER opt_column ColId alter_generic_options
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_AlterColumnGenericOptions;
					n->name = $3;
					n->def = (Node *) $4;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ADD CONSTRAINT ... */
			| ADD_P TableConstraint
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_AddConstraint;
					n->def = $2;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ALTER CONSTRAINT ... */
			| ALTER CONSTRAINT name ConstraintAttributeSpec
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					Constraint *c = makeNode(Constraint);
					n->subtype = AT_AlterConstraint;
					n->def = (Node *) c;
					c->contype = CONSTR_FOREIGN; /* others not supported, yet */
					c->conname = $3;
					processCASbits($4, @4, "ALTER CONSTRAINT statement",
									&c->deferrable,
									&c->initdeferred,
									NULL, NULL, yyscanner);
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> VALIDATE CONSTRAINT ... */
			| VALIDATE CONSTRAINT name
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_ValidateConstraint;
					n->name = $3;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> DROP CONSTRAINT IF EXISTS <name> [RESTRICT|CASCADE] */
			| DROP CONSTRAINT IF_P EXISTS name opt_drop_behavior
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_DropConstraint;
					n->name = $5;
					n->behavior = $6;
					n->missing_ok = TRUE;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> DROP CONSTRAINT <name> [RESTRICT|CASCADE] */
			| DROP CONSTRAINT name opt_drop_behavior
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_DropConstraint;
					n->name = $3;
					n->behavior = $4;
					n->missing_ok = FALSE;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> SET WITH OIDS  */
			| SET WITH OIDS
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_AddOids;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> SET WITHOUT OIDS  */
			| SET WITHOUT OIDS
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_DropOids;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> CLUSTER ON <indexname> */
			| CLUSTER ON name
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_ClusterOn;
					n->name = $3;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> SET WITHOUT CLUSTER */
			| SET WITHOUT CLUSTER
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_DropCluster;
					n->name = NULL;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ENABLE TRIGGER <trig> */
			| ENABLE_P TRIGGER name
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_EnableTrig;
					n->name = $3;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ENABLE ALWAYS TRIGGER <trig> */
			| ENABLE_P ALWAYS TRIGGER name
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_EnableAlwaysTrig;
					n->name = $4;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ENABLE REPLICA TRIGGER <trig> */
			| ENABLE_P REPLICA TRIGGER name
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_EnableReplicaTrig;
					n->name = $4;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ENABLE TRIGGER ALL */
			| ENABLE_P TRIGGER ALL
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_EnableTrigAll;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ENABLE TRIGGER USER */
			| ENABLE_P TRIGGER USER
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_EnableTrigUser;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> DISABLE TRIGGER <trig> */
			| DISABLE_P TRIGGER name
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_DisableTrig;
					n->name = $3;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> DISABLE TRIGGER ALL */
			| DISABLE_P TRIGGER ALL
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_DisableTrigAll;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> DISABLE TRIGGER USER */
			| DISABLE_P TRIGGER USER
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_DisableTrigUser;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ENABLE RULE <rule> */
			| ENABLE_P RULE name
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_EnableRule;
					n->name = $3;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ENABLE ALWAYS RULE <rule> */
			| ENABLE_P ALWAYS RULE name
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_EnableAlwaysRule;
					n->name = $4;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> ENABLE REPLICA RULE <rule> */
			| ENABLE_P REPLICA RULE name
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_EnableReplicaRule;
					n->name = $4;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> DISABLE RULE <rule> */
			| DISABLE_P RULE name
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_DisableRule;
					n->name = $3;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> INHERIT <parent> */
			| INHERIT qualified_name
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_AddInherit;
					n->def = (Node *) $2;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> NO INHERIT <parent> */
			| NO INHERIT qualified_name
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_DropInherit;
					n->def = (Node *) $3;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> SET [WITH] [DISTRIBUTED BY] */
			/* distro only */
			| SET DistributedBy
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_SetDistributedBy;
					n->def = (Node *) list_make2(NULL, $2);
					$$ = (Node *)n;
				}
			/* storage and distro */
			| SET WITH definition DistributedBy
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_SetDistributedBy;
					n->def = (Node *) list_make2($3, $4);
					$$ = (Node *)n;
				}
			/* storage only */
			| SET WITH definition
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_SetDistributedBy;
					n->def = (Node *) list_make2($3, NULL);
					$$ = (Node *)n;
				}
			| alter_table_partition_cmd
				{
					$$ = $1;
				}
			/* ALTER TABLE <name> EXPAND TABLE*/
			| EXPAND TABLE
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_ExpandTable;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> EXPAND PARTITION PREPARE*/
			| EXPAND PARTITION PREPARE
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_ExpandPartitionTablePrepare;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> OF <type_name> */
			| OF any_name
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					TypeName *def = makeTypeNameFromNameList($2);
					def->location = @2;
					n->subtype = AT_AddOf;
					n->def = (Node *) def;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> NOT OF */
			| NOT OF
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_DropOf;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> OWNER TO RoleId */
			| OWNER TO RoleId
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_ChangeOwner;
					n->name = $3;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> SET TABLESPACE <tablespacename> */
			| SET TABLESPACE name
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_SetTableSpace;
					n->name = $3;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> SET (...) */
			| SET reloptions
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_SetRelOptions;
					n->def = (Node *)$2;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> RESET (...) */
			| RESET reloptions
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_ResetRelOptions;
					n->def = (Node *)$2;
					$$ = (Node *)n;
				}
			/* ALTER TABLE <name> REPLICA IDENTITY  */
			| REPLICA IDENTITY_P replica_identity
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_ReplicaIdentity;
					n->def = $3;
					$$ = (Node *)n;
				}
			| alter_generic_options
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_GenericOptions;
					n->def = (Node *)$1;
					$$ = (Node *) n;
				}
		;

alter_column_default:
			SET DEFAULT a_expr			{ $$ = $3; }
			| DROP DEFAULT				{ $$ = NULL; }
		;

opt_drop_behavior:
			CASCADE						{ $$ = DROP_CASCADE; }
			| RESTRICT					{ $$ = DROP_RESTRICT; }
			| /* EMPTY */				{ $$ = DROP_RESTRICT; /* default */ }
		;

opt_collate_clause:
			COLLATE any_name
				{
					CollateClause *n = makeNode(CollateClause);
					n->arg = NULL;
					n->collname = $2;
					n->location = @1;
					$$ = (Node *) n;
				}
			| /* EMPTY */				{ $$ = NULL; }
		;

alter_using:
			USING a_expr				{ $$ = $2; }
			| /* EMPTY */				{ $$ = NULL; }
		;

replica_identity:
			NOTHING
				{
					ReplicaIdentityStmt *n = makeNode(ReplicaIdentityStmt);
					n->identity_type = REPLICA_IDENTITY_NOTHING;
					n->name = NULL;
					$$ = (Node *) n;
				}
			| FULL
				{
					ReplicaIdentityStmt *n = makeNode(ReplicaIdentityStmt);
					n->identity_type = REPLICA_IDENTITY_FULL;
					n->name = NULL;
					$$ = (Node *) n;
				}
			| DEFAULT
				{
					ReplicaIdentityStmt *n = makeNode(ReplicaIdentityStmt);
					n->identity_type = REPLICA_IDENTITY_DEFAULT;
					n->name = NULL;
					$$ = (Node *) n;
				}
			| USING INDEX name
				{
					ReplicaIdentityStmt *n = makeNode(ReplicaIdentityStmt);
					n->identity_type = REPLICA_IDENTITY_INDEX;
					n->name = $3;
					$$ = (Node *) n;
				}
;

reloptions:
			'(' reloption_list ')'					{ $$ = $2; }
		;

opt_reloptions:		WITH reloptions					{ $$ = $2; }
			 |		/* EMPTY */						{ $$ = NIL; }
		;

reloption_list:
			reloption_elem							{ $$ = list_make1($1); }
			| reloption_list ',' reloption_elem		{ $$ = lappend($1, $3); }
		;

/* This should match def_elem and also allow qualified names */
reloption_elem:
			ColLabel '=' def_arg
				{
					/*
					 * appendoptimized is an alias for appendonly in order to
					 * provide a reloption syntax which better reflects the
					 * featureset of AO tables. It is implemented as a very
					 * thin alias, the reloptions and messaging will still
					 * say appendonly.
					 */
					if (strcmp($1, "appendoptimized") == 0)
						$$ = makeDefElem("appendonly", (Node *) $3);
					else
						$$ = makeDefElem($1, (Node *) $3);
				}
			| ColLabel
				{
					/*
					 * Similarly to the above, translate 'appendoptimized' to
					 * 'appendonly'. Also, adding the implicit 'true' in case 
					 * we don't handle that properly in parse analysis.
					 * See: https://github.com/GreengageDB/greengage/issues/14510.
					 */
					if (strcmp($1, "appendonly") == 0 || strcmp($1, "appendoptimized") == 0)
						$$ = makeDefElem("appendonly", (Node *) makeString(pstrdup("true")));
					else
						$$ = makeDefElem($1, NULL);
				}
			| ColLabel '.' ColLabel '=' def_arg
				{
					$$ = makeDefElemExtended($1, $3, (Node *) $5,
											 DEFELEM_UNSPEC);
				}
			| ColLabel '.' ColLabel
				{
					$$ = makeDefElemExtended($1, $3, NULL, DEFELEM_UNSPEC);
				}
		;

opt_table_partition_split_into: 
			INTO '(' 
            alter_table_partition_id_spec_with_opt_default ','
            alter_table_partition_id_spec_with_opt_default ')'	
				{
                    /* re-use alterpartitioncmd struct here... */
					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
                    pc->partid = (Node *)$3;
                    pc->arg1 = (Node *)$5;
                    pc->arg2 = NULL;
                    pc->location = @5;
					$$ = (Node *)pc;
                }
			| /*EMPTY*/						{ $$ = NULL; /* default */ }
		;

opt_table_partition_exchange_validate: 
			WITH VALIDATION						{ $$ = +1; }
			| WITHOUT VALIDATION				{ $$ = +0; }
			| /*EMPTY*/							{ $$ = +1; /* default */ }
		;

alter_table_partition_id_spec: 
			PartitionColId
				{
					AlterPartitionId *n = makeNode(AlterPartitionId);
					n->idtype = AT_AP_IDName;
                    n->partiddef = (Node *)makeString($1);
                    n->location  = @1;
					$$ = (Node *)n;
				}
            | FOR 
            '(' TabPartitionBoundarySpecValList ')'	
				{
					AlterPartitionId *n = makeNode(AlterPartitionId);
					n->idtype = AT_AP_IDValue;
                    n->partiddef = (Node *)$3;
                    n->location  = @3;
					$$ = (Node *)n;
				}
			/*
			 * What we'd really want here is:
			 *
			 * FOR '(' RANK '(' NumericOnly ')' ')'
			 *
			 * But we don't want to make RANK a reserved keyword. Also,
			 * just replacing RANK with IDENT creates a conflict with this
			 * AexprConst rule:
			 *
			 * func_name '(' func_arg_list opt_sort_clause ')' Sconst
			 *
			 * I.e. after the parser has shifted "func_name '('", it doesn't
			 * know whether there's the Sconst at the end, which implies an
			 * AexprConst, or not.
			 *
			 * To avoid that conflict, this rule (after FOR '(') matches
			 * exactly the AexprConst rule except for the final Sconst.
			 * That way, the parser doesn't need to decide which one this is,
			 * until it has shifted the whole thing. Then we check in the
			 * code that func_name was RANK, and that the expr_list was a
			 * NumericOnly.
 			 */
           | FOR '(' func_name '(' func_arg_list opt_sort_clause ')' ')'
				{
					Node		   *arg;
					Value		   *val;
					Node		   *fname;
					AlterPartitionId *n;

                    /* allow RANK only */
					if (list_length($3) != 1)
                        parser_yyerror("syntax error");
					fname = linitial($3);
					if (!(strcmp(strVal(linitial($3)), "rank") == 0))
                        parser_yyerror("syntax error");

					/* expr_list must be a single numeric constant */
					if (list_length($5) != 1)
						parser_yyerror("syntax error");

					arg = linitial($5);
					if (!IsA(arg, A_Const))
						parser_yyerror("syntax error");
					val = &((A_Const *) arg)->val;
					if (!IsA(val, Integer) && !IsA(val, Float))
						parser_yyerror("syntax error");

					/* we don't want a sort clause */
					if ($6)
						parser_yyerror("syntax error");

					n = makeNode(AlterPartitionId);
					n->idtype = AT_AP_IDRank;
                    n->partiddef = (Node *) val;
                    n->location  = @5;

					$$ = (Node *)n;
				}
		;

alter_table_partition_id_spec_with_opt_default:
			PARTITION alter_table_partition_id_spec
				{
					AlterPartitionId *n = (AlterPartitionId*)$2;
                    $$ = (Node *)n;
				}
			| DEFAULT PARTITION alter_table_partition_id_spec
				{
					ereport(ERROR,
							(errcode(ERRCODE_SYNTAX_ERROR),
							 errmsg("cannot specify a name, rank, or value for a DEFAULT partition in this context")));
				}
			| DEFAULT PARTITION 
				{
					AlterPartitionId *n = makeNode(AlterPartitionId);
					n->idtype = AT_AP_IDDefault;
                    n->partiddef = NULL;
                    n->location  = @1;
					$$ = (Node *)n;
				}
		;

alter_table_partition_cmd:
			ADD_P PARTITION 
            OptTabPartitionBoundarySpec
 			OptTabPartitionStorageAttr
			OptTabSubPartitionSpec
           
				{
					AlterPartitionId  *pid   = makeNode(AlterPartitionId);
					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
					AlterTableCmd     *n     = makeNode(AlterTableCmd);
                    PartitionElem     *pelem = makeNode(PartitionElem); 

                    pid->idtype = AT_AP_IDNone;
                    pid->location = @3;
                    pid->partiddef = NULL;

                    pc->partid = (Node *) pid;

                    pelem->partName  = NULL;
                    pelem->boundSpec = $3;
                    pelem->subSpec   = $5;
                    pelem->location  = @3;
                    pelem->isDefault = false; /* not default */
                    pelem->storeAttr = $4;
                    pelem->AddPartDesc = NULL;
					pc->arg1 = (Node *) pelem;

                    pc->location = @3;

					n->subtype = AT_PartAdd;
					n->def = (Node *)pc;
					$$ = (Node *)n;
				}
			| ADD_P DEFAULT PARTITION 
            alter_table_partition_id_spec 
            OptTabPartitionBoundarySpec
            OptTabPartitionStorageAttr
			OptTabSubPartitionSpec 
				{
					AlterPartitionId  *pid   = (AlterPartitionId *)$4;
					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
					AlterTableCmd     *n     = makeNode(AlterTableCmd);
                    PartitionElem     *pelem = makeNode(PartitionElem); 

                    if (pid->idtype != AT_AP_IDName)
						ereport(ERROR,
								(errcode(ERRCODE_SYNTAX_ERROR),
								 errmsg("can only ADD a partition by name")));

                    pc->partid = (Node *) pid;

                    pelem->partName  = NULL;
                    pelem->boundSpec = $5;
                    pelem->subSpec   = $7;
                    pelem->location  = @5;
                    pelem->isDefault = true;
                    pelem->storeAttr = $6;
                    pelem->AddPartDesc = NULL;
					pc->arg1 = (Node *) pelem;
                    pc->location = @5;

					n->subtype = AT_PartAdd;
					n->def = (Node *)pc;
					$$ = (Node *)n;
				}
			| ADD_P PARTITION 
            alter_table_partition_id_spec 
            OptTabPartitionBoundarySpec
            OptTabPartitionStorageAttr
			OptTabSubPartitionSpec 
				{
					AlterPartitionId  *pid   = (AlterPartitionId *)$3;
					AlterPartitionCmd *pc    = makeNode(AlterPartitionCmd);
					AlterTableCmd     *n     = makeNode(AlterTableCmd);
                    PartitionElem     *pelem = makeNode(PartitionElem); 

                    if (pid->idtype != AT_AP_IDName)
						ereport(ERROR,
								(errcode(ERRCODE_SYNTAX_ERROR),
								 errmsg("can only ADD a partition by name")));

                    pc->partid = (Node *) pid;

                    pelem->partName  = NULL;
                    pelem->boundSpec = $4;
                    pelem->subSpec   = $6;
                    pelem->location  = @4;
                    pelem->isDefault = false;
                    pelem->storeAttr = $5;
                    pelem->AddPartDesc = NULL;
                    pc->arg1 = (Node *) pelem;

                    pc->location = @4;

					n->subtype = AT_PartAdd;
					n->def = (Node *)pc;
					$$ = (Node *)n;
				}
			| ALTER 
            alter_table_partition_id_spec_with_opt_default
            alter_table_cmd
				{
                    /* NOTE: only allow a subset of valid ALTER TABLE
                       cmds for partitions.
                    */

					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
					AlterTableCmd *n = makeNode(AlterTableCmd);

                    pc->partid = (Node *)$2;
                    pc->arg1 = (Node *)$3;
                    pc->arg2 = NULL;
                    pc->location = @3;

					n->subtype = AT_PartAlter;
					n->def = (Node *)pc;
					$$ = (Node *)n;
				}
			| DROP PARTITION IF_P EXISTS 
            alter_table_partition_id_spec	 
            opt_drop_behavior
				{
					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
					AlterTableCmd *n = makeNode(AlterTableCmd);
					DropStmt *ds = makeNode(DropStmt);

					ds->missing_ok = TRUE;
					ds->behavior = $6;

                    /* 
                       build an (incomplete) drop statement for arg1: 
                       fill in the rest after the partition id spec is
                       validated
                    */

                    pc->partid = (Node *)$5;
                    pc->arg1 = (Node *)ds;
                    pc->arg2 = NULL;
                    pc->location = @5;

					n->subtype = AT_PartDrop;
					n->def = (Node *)pc;
					$$ = (Node *)n;
				}
			| DROP DEFAULT PARTITION IF_P EXISTS 
            opt_drop_behavior
				{
					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
					AlterTableCmd *n = makeNode(AlterTableCmd);
					DropStmt *ds = makeNode(DropStmt);
					AlterPartitionId *pid = makeNode(AlterPartitionId);

					pid->idtype = AT_AP_IDDefault;
                    pid->partiddef = NULL;
                    pid->location  = @2;

					ds->missing_ok = TRUE;
					ds->behavior = $6;

                    /* 
                       build an (incomplete) drop statement for arg1: 
                       fill in the rest after the partition id spec is
                       validated
                    */

                    pc->partid = (Node *)pid;
                    pc->arg1 = (Node *)ds;
                    pc->arg2 = NULL;
                    pc->location = @3;

					n->subtype = AT_PartDrop;
					n->def = (Node *)pc;
					$$ = (Node *)n;
				}
			| DROP 
            alter_table_partition_id_spec_with_opt_default
            opt_drop_behavior
				{
					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
					AlterTableCmd *n = makeNode(AlterTableCmd);
					DropStmt *ds = makeNode(DropStmt);

					ds->missing_ok = FALSE;
					ds->behavior = $3;

                    /* 
                       build an (incomplete) drop statement for arg1: 
                       fill in the rest after the partition id spec is
                       validated
                    */

                    pc->partid = (Node *)$2;
                    pc->arg1 = (Node *)ds;
                    pc->arg2 = NULL;
                    pc->location = @2;

					n->subtype = AT_PartDrop;
					n->def = (Node *)pc;
					$$ = (Node *)n;
				}
			| DROP PARTITION 
				{
					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
					AlterTableCmd *n = makeNode(AlterTableCmd);
					DropStmt *ds = makeNode(DropStmt);
					AlterPartitionId *pid = makeNode(AlterPartitionId);

					ds->missing_ok = FALSE;
					ds->behavior = DROP_RESTRICT; /* default */ 

                    /* 
                       build an (incomplete) drop statement for arg1: 
                       fill in the rest after the partition id spec is
                       validated
                    */

                    /* just try to drop the first partition if not specified */
					pid->idtype = AT_AP_IDNone;
                    pid->location  = @2;

                    pc->partid = (Node *)pid;
                    pc->arg1 = (Node *)ds;
                    pc->arg2 = NULL;
                    pc->location = @2;

					n->subtype = AT_PartDrop;
					n->def = (Node *)pc;
					$$ = (Node *)n;
				}
			| EXCHANGE 
            alter_table_partition_id_spec_with_opt_default 
            WITH TABLE qualified_name
            opt_table_partition_exchange_validate	
				{
					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
					AlterPartitionCmd *pc2 = makeNode(AlterPartitionCmd);
					AlterTableCmd *n = makeNode(AlterTableCmd);

                    pc->partid = (Node *)$2;
                    pc->arg1 = (Node *)$5;
                    pc->arg2 = (Node *)pc2;
                    pc2->arg1 = (Node *)makeInteger($6);
                    pc->location = @5;

					n->subtype = AT_PartExchange;
					n->def = (Node *)pc;
					$$ = (Node *)n;
				}
			| RENAME 
            alter_table_partition_id_spec_with_opt_default TO IDENT	
				{
					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
					AlterTableCmd *n = makeNode(AlterTableCmd);

                    pc->partid = (Node *)$2;
                    pc->arg1 = (Node *)makeString($4);
                    pc->arg2 = NULL;
                    pc->location = @4;

					n->subtype = AT_PartRename;
					n->def = (Node *)pc;
					$$ = (Node *)n;
				}
			| SET SUBPARTITION TEMPLATE
            '(' TabSubPartitionElemList ')' 
				{
					AlterPartitionId  *pid   = makeNode(AlterPartitionId);
					AlterPartitionCmd *pc    = makeNode(AlterPartitionCmd);
					AlterTableCmd     *n     = makeNode(AlterTableCmd);
                    PartitionElem     *pelem = makeNode(PartitionElem); 
					PartitionSpec	  *ps    = makeNode(PartitionSpec); 

					/* treat this case as similar to ADD PARTITION */

                    pid->idtype    = AT_AP_IDName;
                    pid->location  = @3;
                    pid->partiddef = 
						(Node *)makeString("subpartition_template");

                    pc->partid = (Node *) pid;

					/* build a subpartition spec and add it to CREATE TABLE */
					ps->partElem   = $5; 
					ps->subSpec	   = NULL;
					ps->istemplate = true;
					ps->location   = @4;

                    pelem->partName  = NULL;
                    pelem->boundSpec = NULL;
                    pelem->subSpec   = (Node *)ps;
                    pelem->location  = @4;
                    pelem->isDefault = true;
                    pelem->storeAttr = NULL;
                    pelem->AddPartDesc = NULL;
					pc->arg1 = (Node *) pelem;

					/* a little (temporary?) syntax check on templates */
					if (ps->partElem)
					{
						List *elems;
						ListCell *lc;
						Assert(IsA(ps->partElem, List));

						elems = (List *)ps->partElem;
						foreach(lc, elems)
						{
							PartitionElem *e = lfirst(lc);

							if (!IsA(e, PartitionElem))
								continue;

							if (e->subSpec)
								ereport(ERROR,
										(errcode(ERRCODE_SYNTAX_ERROR),
										 errmsg("template cannot contain "
												"specification for child "
												"partition")));
						}
					}

                    pc->location = @5;

					n->subtype = AT_PartSetTemplate;
					n->def = (Node *)pc;
					$$ = (Node *)n;
				}
			| SET SUBPARTITION TEMPLATE
            '('  ')' 
				{
					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
					AlterTableCmd *n = makeNode(AlterTableCmd);

                    pc->partid = NULL; 
                    pc->arg1 = NULL;
                    pc->arg2 = NULL;
                    pc->location = @4;

					n->subtype = AT_PartSetTemplate;
					n->def = (Node *)pc;
					$$ = (Node *)n;
				}
			| SPLIT 
            DEFAULT PARTITION TabPartitionBoundarySpecStart
            TabPartitionBoundarySpecEnd
            opt_table_partition_split_into	
				{
					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
					AlterTableCmd *n = makeNode(AlterTableCmd);
					AlterPartitionId *pid = makeNode(AlterPartitionId);

					pid->idtype = AT_AP_IDDefault;
                    pid->partiddef = NULL;
                    pid->location  = @2;

                    pc->partid = (Node *)pid;
                    pc->arg1 = (Node *)list_make2($4, $5);
                    pc->arg2 = (Node *)$6;
                    pc->location = @5;

					n->subtype = AT_PartSplit;
					n->def = (Node *)pc;
					$$ = (Node *)n;
				}
			| SPLIT 
            alter_table_partition_id_spec_with_opt_default AT 
            '(' part_values_or_spec_list ')'	
            opt_table_partition_split_into	
				{
					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
					AlterTableCmd *n = makeNode(AlterTableCmd);

                    pc->partid = (Node *)$2;

					/* 
					 * The first element of the list is only defined if
					 * we're doing default splits for range partitioning.
				 	 */
                    pc->arg1 = (Node *)list_make2(NULL, $5);
                    pc->arg2 = (Node *)$7;
                    pc->location = @5;

					n->subtype = AT_PartSplit;
					n->def = (Node *)pc;
					$$ = (Node *)n;
				}
			| TRUNCATE 
            alter_table_partition_id_spec_with_opt_default
            opt_drop_behavior
				{
					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
					AlterTableCmd *n = makeNode(AlterTableCmd);
					TruncateStmt *ts = makeNode(TruncateStmt);

                    /* 
                       build an (incomplete) truncate statement for arg1: 
                       fill in the rest after the partition id spec is
                       validated
                    */
					ts->relations = NULL;
					ts->behavior = $3;

                    pc->partid = (Node *)$2;
                    pc->arg1 = (Node *)ts;
                    pc->arg2 = NULL;
                    pc->location = @2;

					n->subtype = AT_PartTruncate;
					n->def = (Node *)pc;
					$$ = (Node *)n;
				}
		;


/*****************************************************************************
 *
 *	ALTER TYPE
 *
 * really variants of the ALTER TABLE subcommands with different spellings
 *****************************************************************************/

AlterCompositeTypeStmt:
			ALTER TYPE_P any_name alter_type_cmds
				{
					AlterTableStmt *n = makeNode(AlterTableStmt);

					/* can't use qualified_name, sigh */
					n->relation = makeRangeVarFromAnyName($3, @3, yyscanner);
					n->cmds = $4;
					n->relkind = OBJECT_TYPE;
					$$ = (Node *)n;
				}
			;

alter_type_cmds:
			alter_type_cmd							{ $$ = list_make1($1); }
			| alter_type_cmds ',' alter_type_cmd	{ $$ = lappend($1, $3); }
		;

alter_type_cmd:
			/* ALTER TYPE <name> ADD ATTRIBUTE <coldef> [RESTRICT|CASCADE] */
			ADD_P ATTRIBUTE TableFuncElement opt_drop_behavior
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_AddColumn;
					n->def = $3;
					n->behavior = $4;
					$$ = (Node *)n;
				}
			/* ALTER TYPE <name> DROP ATTRIBUTE IF EXISTS <attname> [RESTRICT|CASCADE] */
			| DROP ATTRIBUTE IF_P EXISTS ColId opt_drop_behavior
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_DropColumn;
					n->name = $5;
					n->behavior = $6;
					n->missing_ok = TRUE;
					$$ = (Node *)n;
				}
			/* ALTER TYPE <name> DROP ATTRIBUTE <attname> [RESTRICT|CASCADE] */
			| DROP ATTRIBUTE ColId opt_drop_behavior
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					n->subtype = AT_DropColumn;
					n->name = $3;
					n->behavior = $4;
					n->missing_ok = FALSE;
					$$ = (Node *)n;
				}
			/* ALTER TYPE <name> ALTER ATTRIBUTE <attname> [SET DATA] TYPE <typename> [RESTRICT|CASCADE] */
			| ALTER ATTRIBUTE ColId opt_set_data TYPE_P Typename opt_collate_clause opt_drop_behavior
				{
					AlterTableCmd *n = makeNode(AlterTableCmd);
					ColumnDef *def = makeNode(ColumnDef);
					n->subtype = AT_AlterColumnType;
					n->name = $3;
					n->def = (Node *) def;
					n->behavior = $8;
					/* We only use these fields of the ColumnDef node */
					def->typeName = $6;
					def->collClause = (CollateClause *) $7;
					def->raw_default = NULL;
					def->location = @3;
					$$ = (Node *)n;
				}
		;


/*****************************************************************************
 *
 *		QUERY :
 *				close <portalname>
 *
 *****************************************************************************/

ClosePortalStmt:
			CLOSE cursor_name
				{
					ClosePortalStmt *n = makeNode(ClosePortalStmt);
					n->portalname = $2;
					$$ = (Node *)n;
				}
			| CLOSE ALL
				{
					ClosePortalStmt *n = makeNode(ClosePortalStmt);
					n->portalname = NULL;
					$$ = (Node *)n;
				}
		;


/*****************************************************************************
 *
 *		QUERY :
 *				COPY relname [(columnList)] FROM/TO file [WITH] [(options)]
 *				COPY ( SELECT ... ) TO file	[WITH] [(options)]
 *
 *				where 'file' can be one of:
 *				{ PROGRAM 'command' | STDIN | STDOUT | 'filename' }
 *
 *				In the preferred syntax the options are comma-separated
 *				and use generic identifiers instead of keywords.  The pre-9.0
 *				syntax had a hard-wired, space-separated set of options.
 *
 *				Really old syntax, from versions 7.2 and prior:
 *				COPY [ BINARY ] table [ WITH OIDS ] FROM/TO file
 *					[ [ USING ] DELIMITERS 'delimiter' ] ]
 *					[ WITH NULL AS 'null string' ]
 *				This option placement is not supported with COPY (SELECT...).
 *
 *****************************************************************************/

CopyStmt:	COPY opt_binary qualified_name opt_column_list opt_oids
			copy_from opt_program copy_file_name copy_delimiter opt_with copy_options
			OptSingleRowErrorHandling skip_external_partition
				{
					CopyStmt *n = makeNode(CopyStmt);
					n->relation = $3;
					n->query = NULL;
					n->attlist = $4;
					n->is_from = $6;
					n->is_program = $7;
					n->filename = $8;
					n->sreh = $12;
					n->partitions = NULL;
					n->ao_segnos = NIL;

					if (n->is_program && n->filename == NULL)
						ereport(ERROR,
								(errcode(ERRCODE_SYNTAX_ERROR),
								 errmsg("STDIN/STDOUT not allowed with PROGRAM"),
								 parser_errposition(@8)));

					n->options = NIL;
					n->skip_ext_partition = $13;

					/* Concatenate user-supplied flags */
					if ($2)
						n->options = lappend(n->options, $2);
					if ($5)
						n->options = lappend(n->options, $5);
					if ($9)
						n->options = lappend(n->options, $9);
					if ($11)
						n->options = list_concat(n->options, $11);
					$$ = (Node *)n;
				}
			| COPY select_with_parens TO opt_program copy_file_name opt_with copy_options
				{
					CopyStmt *n = makeNode(CopyStmt);
					n->relation = NULL;
					n->query = $2;
					n->attlist = NIL;
					n->is_from = false;
					n->is_program = $4;
					n->filename = $5;
					n->options = $7;
					n->partitions = NULL;
					n->ao_segnos = NIL;
					n->skip_ext_partition = false;

					if (n->is_program && n->filename == NULL)
						ereport(ERROR,
								(errcode(ERRCODE_SYNTAX_ERROR),
								 errmsg("STDIN/STDOUT not allowed with PROGRAM"),
								 parser_errposition(@5)));

					$$ = (Node *)n;
				}
		;

copy_from:
			FROM									{ $$ = TRUE; }
			| TO									{ $$ = FALSE; }
		;

opt_program:
			PROGRAM									{ $$ = TRUE; }
			| /* EMPTY */							{ $$ = FALSE; }
		;

skip_external_partition:
			IGNORE_P EXTERNAL PARTITIONS			{ $$ = TRUE; }
			| /*EMPTY*/								{ $$ = FALSE; }
		;

/*
 * copy_file_name NULL indicates stdio is used. Whether stdin or stdout is
 * used depends on the direction. (It really doesn't make sense to copy from
 * stdout. We silently correct the "typo".)		 - AY 9/94
 */
copy_file_name:
			Sconst									{ $$ = $1; }
			| STDIN									{ $$ = NULL; }
			| STDOUT								{ $$ = NULL; }
		;

copy_options: copy_opt_list							{ $$ = $1; }
			| '(' copy_generic_opt_list ')'			{ $$ = $2; }
		;

/* old COPY option syntax */
copy_opt_list:
			copy_opt_list copy_opt_item				{ $$ = lappend($1, $2); }
			| /* EMPTY */							{ $$ = NIL; }
		;

copy_opt_item:
			BINARY
				{
					$$ = makeDefElem("format", (Node *)makeString("binary"));
				}
			| OIDS
				{
					$$ = makeDefElem("oids", (Node *)makeInteger(TRUE));
				}
			| FREEZE
				{
					$$ = makeDefElem("freeze", (Node *)makeInteger(TRUE));
				}
			| DELIMITER opt_as Sconst
				{
					$$ = makeDefElem("delimiter", (Node *)makeString($3));
				}
			| NULL_P opt_as Sconst
				{
					$$ = makeDefElem("null", (Node *)makeString($3));
				}
			| CSV
				{
					$$ = makeDefElem("format", (Node *)makeString("csv"));
				}
			| HEADER_P
				{
					$$ = makeDefElem("header", (Node *)makeInteger(TRUE));
				}
			| QUOTE opt_as Sconst
				{
					$$ = makeDefElem("quote", (Node *)makeString($3));
				}
			| ESCAPE opt_as Sconst
				{
					$$ = makeDefElem("escape", (Node *)makeString($3));
				}
			| FORCE QUOTE columnList
				{
					$$ = makeDefElem("force_quote", (Node *)$3);
				}
			| FORCE QUOTE '*'
				{
					$$ = makeDefElem("force_quote", (Node *)makeNode(A_Star));
				}
			| FORCE NOT NULL_P columnList
				{
					$$ = makeDefElem("force_not_null", (Node *)$4);
				}
			| FORCE NULL_P columnList
				{
					$$ = makeDefElem("force_null", (Node *)$3);
				}
			| ENCODING Sconst
				{
					$$ = makeDefElem("encoding", (Node *)makeString($2));
				}
			| FILL MISSING FIELDS
				{
					$$ = makeDefElem("fill_missing_fields", (Node *)makeInteger(TRUE));
				}
			| NEWLINE opt_as Sconst
				{
					$$ = makeDefElem("newline", (Node *)makeString($3));
				}	
			| ON SEGMENT
				{
					$$ = makeDefElem("on_segment", (Node *)makeInteger(TRUE));
				}
		;

/* The following exist for backward compatibility with very old versions */

opt_binary:
			BINARY
				{
					$$ = makeDefElem("format", (Node *)makeString("binary"));
				}
			| /*EMPTY*/								{ $$ = NULL; }
		;

opt_oids:
			WITH OIDS
				{
					$$ = makeDefElem("oids", (Node *)makeInteger(TRUE));
				}
			| /*EMPTY*/								{ $$ = NULL; }
		;

copy_delimiter:
			opt_using DELIMITERS Sconst
				{
					$$ = makeDefElem("delimiter", (Node *)makeString($3));
				}
			| /*EMPTY*/								{ $$ = NULL; }
		;

opt_using:
			USING									{}
			| /*EMPTY*/								{}
		;

/* new COPY option syntax */
copy_generic_opt_list:
			copy_generic_opt_elem
				{
					$$ = list_make1($1);
				}
			| copy_generic_opt_list ',' copy_generic_opt_elem
				{
					$$ = lappend($1, $3);
				}
		;

copy_generic_opt_elem:
			ColLabel copy_generic_opt_arg
				{
					$$ = makeDefElem($1, $2);
				}
		;

copy_generic_opt_arg:
			opt_boolean_or_string			{ $$ = (Node *) makeString($1); }
			| NumericOnly					{ $$ = (Node *) $1; }
			| '*'							{ $$ = (Node *) makeNode(A_Star); }
			| '(' copy_generic_opt_arg_list ')'		{ $$ = (Node *) $2; }
			| /* EMPTY */					{ $$ = NULL; }
		;

copy_generic_opt_arg_list:
			  copy_generic_opt_arg_list_item
				{
					$$ = list_make1($1);
				}
			| copy_generic_opt_arg_list ',' copy_generic_opt_arg_list_item
				{
					$$ = lappend($1, $3);
				}
		;

/* beware of emitting non-string list elements here; see commands/define.c */
copy_generic_opt_arg_list_item:
			opt_boolean_or_string	{ $$ = (Node *) makeString($1); }
		;


/*****************************************************************************
 *
 *		QUERY :
 *				CREATE TABLE relname
 *
 *****************************************************************************/

CreateStmt:	CREATE OptTemp TABLE qualified_name '(' OptTableElementList ')'
			OptInherit OptWith OnCommitOption OptTableSpace OptDistributedBy 
			OptTabPartitionBy
				{
					CreateStmt *n = makeNode(CreateStmt);
					$4->relpersistence = $2;
					n->relation = $4;
					n->tableElts = $6;
					n->inhRelations = $8;
					n->constraints = NIL;
					n->options = $9;
					n->oncommit = $10;
					n->tablespacename = $11;
					n->if_not_exists = false;
					n->distributedBy = (DistributedBy *) $12;
					n->partitionBy = $13;
					n->relKind = RELKIND_RELATION;
					$$ = (Node *)n;
				}
		| CREATE OptTemp TABLE IF_P NOT EXISTS qualified_name '('
			OptTableElementList ')' OptInherit OptWith OnCommitOption
			OptTableSpace OptDistributedBy 
			OptTabPartitionBy
				{
					CreateStmt *n = makeNode(CreateStmt);
					$7->relpersistence = $2;
					n->relation = $7;
					n->tableElts = $9;
					n->inhRelations = $11;
					n->constraints = NIL;
					n->options = $12;
					n->oncommit = $13;
					n->tablespacename = $14;
					n->if_not_exists = true;
					n->distributedBy = (DistributedBy *) $15;
					n->partitionBy = $16;
					n->relKind = RELKIND_RELATION;
					$$ = (Node *)n;
				}
		| CREATE OptTemp TABLE qualified_name OF any_name
			OptTypedTableElementList OptWith OnCommitOption OptTableSpace
			OptDistributedBy OptTabPartitionBy
				{
					CreateStmt *n = makeNode(CreateStmt);
					$4->relpersistence = $2;
					n->relation = $4;
					n->tableElts = $7;
					n->ofTypename = makeTypeNameFromNameList($6);
					n->ofTypename->location = @6;
					n->constraints = NIL;
					n->options = $8;
					n->oncommit = $9;
					n->tablespacename = $10;
					n->if_not_exists = false;
					n->distributedBy = (DistributedBy *) $11;
					n->partitionBy = $12;
					n->relKind = RELKIND_RELATION;
					$$ = (Node *)n;
				}
		| CREATE OptTemp TABLE IF_P NOT EXISTS qualified_name OF any_name
			OptTypedTableElementList OptWith OnCommitOption OptTableSpace
			OptDistributedBy OptTabPartitionBy
				{
					CreateStmt *n = makeNode(CreateStmt);
					$7->relpersistence = $2;
					n->relation = $7;
					n->tableElts = $10;
					n->ofTypename = makeTypeNameFromNameList($9);
					n->ofTypename->location = @9;
					n->constraints = NIL;
					n->options = $11;
					n->oncommit = $12;
					n->tablespacename = $13;
					n->if_not_exists = true;
					n->distributedBy = (DistributedBy *) $14;
					n->partitionBy = $15;
					n->relKind = RELKIND_RELATION;
					$$ = (Node *)n;
				}
		;

/*
 * Redundancy here is needed to avoid shift/reduce conflicts,
 * since TEMP is not a reserved word.  See also OptTempTableName.
 *
 * NOTE: we accept both GLOBAL and LOCAL options.  They currently do nothing,
 * but future versions might consider GLOBAL to request SQL-spec-compliant
 * temp table behavior, so warn about that.  Since we have no modules the
 * LOCAL keyword is really meaningless; furthermore, some other products
 * implement LOCAL as meaning the same as our default temp table behavior,
 * so we'll probably continue to treat LOCAL as a noise word.
 */
OptTemp:	TEMPORARY					{ $$ = RELPERSISTENCE_TEMP; }
			| TEMP						{ $$ = RELPERSISTENCE_TEMP; }
			| LOCAL TEMPORARY			{ $$ = RELPERSISTENCE_TEMP; }
			| LOCAL TEMP				{ $$ = RELPERSISTENCE_TEMP; }
			| GLOBAL TEMPORARY
				{
					ereport(WARNING,
							(errmsg("GLOBAL is deprecated in temporary table creation"),
							 parser_errposition(@1)));
					$$ = RELPERSISTENCE_TEMP;
				}
			| GLOBAL TEMP
				{
					ereport(WARNING,
							(errmsg("GLOBAL is deprecated in temporary table creation"),
							 parser_errposition(@1)));
					$$ = RELPERSISTENCE_TEMP;
				}
			| UNLOGGED					{ $$ = RELPERSISTENCE_UNLOGGED; }
			| /*EMPTY*/					{ $$ = RELPERSISTENCE_PERMANENT; }
		;

OptTableElementList:
			TableElementList					{ $$ = $1; }
			| /*EMPTY*/							{ $$ = NIL; }
		;

OptTypedTableElementList:
			'(' TypedTableElementList ')'		{ $$ = $2; }
			| /*EMPTY*/							{ $$ = NIL; }
		;

TableElementList:
			TableElement
				{
					$$ = list_make1($1);
				}
			| TableElementList ',' TableElement
				{
					$$ = lappend($1, $3);
				}
		;

TypedTableElementList:
			TypedTableElement
				{
					$$ = list_make1($1);
				}
			| TypedTableElementList ',' TypedTableElement
				{
					$$ = lappend($1, $3);
				}
		;

TableElement:
			columnDef							{ $$ = $1; }
			| TableLikeClause					{ $$ = $1; }
			| TableConstraint					{ $$ = $1; }
			| column_reference_storage_directive { $$ = $1; }
		;

TypedTableElement:
			columnOptions						{ $$ = $1; }
			| TableConstraint					{ $$ = $1; }
		;

column_reference_storage_directive:
			COLUMN ColId ENCODING definition
				{
					ColumnReferenceStorageDirective *n =
						makeNode(ColumnReferenceStorageDirective);

					n->column = $2;
					n->encoding = $4;
					$$ = (Node *)n;
				}
			| DEFAULT COLUMN ENCODING definition
				{
					ColumnReferenceStorageDirective *n =
						makeNode(ColumnReferenceStorageDirective);

					n->deflt = true;
					n->encoding = $4;

					$$ = (Node *)n;
				}
		;

columnDef:	ColId Typename create_generic_options ColQualList opt_storage_encoding
				{
					ColumnDef *n = makeNode(ColumnDef);
					n->colname = $1;
					n->typeName = $2;
					n->inhcount = 0;
					n->is_local = true;
					n->encoding = $5;
					n->is_not_null = false;
					n->is_from_type = false;
					n->storage = 0;
					n->raw_default = NULL;
					n->cooked_default = NULL;
					n->collOid = InvalidOid;
					n->fdwoptions = $3;
					SplitColQualList($4, &n->constraints, &n->collClause,
									 yyscanner);
					n->location = @1;
					$$ = (Node *)n;
				}
		;

columnOptions:	ColId WITH OPTIONS ColQualList
				{
					ColumnDef *n = makeNode(ColumnDef);
					n->colname = $1;
					n->typeName = NULL;
					n->inhcount = 0;
					n->is_local = true;
					n->is_not_null = false;
					n->is_from_type = false;
					n->storage = 0;
					n->raw_default = NULL;
					n->cooked_default = NULL;
					n->collOid = InvalidOid;
					SplitColQualList($4, &n->constraints, &n->collClause,
									 yyscanner);
					n->location = @1;
					$$ = (Node *)n;
				}
		;

ColQualList:
			ColQualList ColConstraint				{ $$ = lappend($1, $2); }
			| /*EMPTY*/								{ $$ = NIL; }
		;

ColConstraint:
			CONSTRAINT name ColConstraintElem
				{
					Constraint *n = (Constraint *) $3;
					Assert(IsA(n, Constraint));
					n->conname = $2;
					n->location = @1;
					$$ = (Node *) n;
				}
			| ColConstraintElem						{ $$ = $1; }
			| ConstraintAttr						{ $$ = $1; }
			| COLLATE any_name
				{
					/*
					 * Note: the CollateClause is momentarily included in
					 * the list built by ColQualList, but we split it out
					 * again in SplitColQualList.
					 */
					CollateClause *n = makeNode(CollateClause);
					n->arg = NULL;
					n->collname = $2;
					n->location = @1;
					$$ = (Node *) n;
				}
		;

opt_storage_encoding: ENCODING definition { $$ = $2; }
			| /* nothing */ { $$ = NIL; }
		;

/* DEFAULT NULL is already the default for Postgres.
 * But define it here and carry it forward into the system
 * to make it explicit.
 * - thomas 1998-09-13
 *
 * WITH NULL and NULL are not SQL-standard syntax elements,
 * so leave them out. Use DEFAULT NULL to explicitly indicate
 * that a column may have that value. WITH NULL leads to
 * shift/reduce conflicts with WITH TIME ZONE anyway.
 * - thomas 1999-01-08
 *
 * DEFAULT expression must be b_expr not a_expr to prevent shift/reduce
 * conflict on NOT (since NOT might start a subsequent NOT NULL constraint,
 * or be part of a_expr NOT LIKE or similar constructs).
 */

NullColConstraintElem:
			NOT NULL_P
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_NOTNULL;
					n->location = @1;
					$$ = (Node *)n;
				}
			| NULL_P
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_NULL;
					n->location = @1;
					$$ = (Node *)n;
				}
		;

DefaultColConstraintElem:
			DEFAULT b_expr
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_DEFAULT;
					n->location = @1;
					n->raw_expr = $2;
					n->cooked_expr = NULL;
					$$ = (Node *)n;
				}
		;

ColConstraintElem:
			NullColConstraintElem 					{ $$ = $1; }
			| DefaultColConstraintElem				{ $$ = $1; }
			| UNIQUE opt_definition OptConsTableSpace
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_UNIQUE;
					n->location = @1;
					n->keys = NULL;
					n->options = $2;
					n->indexname = NULL;
					n->indexspace = $3;
					$$ = (Node *)n;
				}
			| PRIMARY KEY opt_definition OptConsTableSpace
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_PRIMARY;
					n->location = @1;
					n->keys = NULL;
					n->options = $3;
					n->indexname = NULL;
					n->indexspace = $4;
					$$ = (Node *)n;
				}
			| CHECK '(' a_expr ')' opt_no_inherit
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_CHECK;
					n->location = @1;
					n->is_no_inherit = $5;
					n->raw_expr = $3;
					n->cooked_expr = NULL;
					$$ = (Node *)n;
				}
			| REFERENCES qualified_name opt_column_list key_match key_actions
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_FOREIGN;
					n->location = @1;
					n->pktable			= $2;
					n->fk_attrs			= NIL;
					n->pk_attrs			= $3;
					n->fk_matchtype		= $4;
					n->fk_upd_action	= (char) ($5 >> 8);
					n->fk_del_action	= (char) ($5 & 0xFF);
					n->skip_validation  = false;
					n->initially_valid  = true;
					$$ = (Node *)n;
				}
		;

/*
 * ConstraintAttr represents constraint attributes, which we parse as if
 * they were independent constraint clauses, in order to avoid shift/reduce
 * conflicts (since NOT might start either an independent NOT NULL clause
 * or an attribute).  parse_utilcmd.c is responsible for attaching the
 * attribute information to the preceding "real" constraint node, and for
 * complaining if attribute clauses appear in the wrong place or wrong
 * combinations.
 *
 * See also ConstraintAttributeSpec, which can be used in places where
 * there is no parsing conflict.  (Note: currently, NOT VALID and NO INHERIT
 * are allowed clauses in ConstraintAttributeSpec, but not here.  Someday we
 * might need to allow them here too, but for the moment it doesn't seem
 * useful in the statements that use ConstraintAttr.)
 */
ConstraintAttr:
			DEFERRABLE
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_ATTR_DEFERRABLE;
					n->location = @1;
					$$ = (Node *)n;
				}
			| NOT DEFERRABLE
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_ATTR_NOT_DEFERRABLE;
					n->location = @1;
					$$ = (Node *)n;
				}
			| INITIALLY DEFERRED
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_ATTR_DEFERRED;
					n->location = @1;
					$$ = (Node *)n;
				}
			| INITIALLY IMMEDIATE
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_ATTR_IMMEDIATE;
					n->location = @1;
					$$ = (Node *)n;
				}
		;


TableLikeClause:
			LIKE qualified_name TableLikeOptionList
				{
					TableLikeClause *n = makeNode(TableLikeClause);
					n->relation = $2;
					n->options = $3;
					$$ = (Node *)n;
				}
		;

TableLikeOptionList:
				TableLikeOptionList INCLUDING TableLikeOption	{ $$ = $1 | $3; }
				| TableLikeOptionList EXCLUDING TableLikeOption	{ $$ = $1 & ~$3; }
				| /* EMPTY */						{ $$ = 0; }
		;

TableLikeOption:
				DEFAULTS			{ $$ = CREATE_TABLE_LIKE_DEFAULTS; }
				| CONSTRAINTS		{ $$ = CREATE_TABLE_LIKE_CONSTRAINTS; }
				| INDEXES			{ $$ = CREATE_TABLE_LIKE_INDEXES; }
				| STORAGE			{ $$ = CREATE_TABLE_LIKE_STORAGE; }
				| COMMENTS			{ $$ = CREATE_TABLE_LIKE_COMMENTS; }
				| ALL				{ $$ = CREATE_TABLE_LIKE_ALL; }
		;


/* ConstraintElem specifies constraint syntax which is not embedded into
 *	a column definition. ColConstraintElem specifies the embedded form.
 * - thomas 1997-12-03
 */
TableConstraint:
			CONSTRAINT name ConstraintElem
				{
					Constraint *n = (Constraint *) $3;
					Assert(IsA(n, Constraint));
					n->conname = $2;
					n->location = @1;
					$$ = (Node *) n;
				}
			| ConstraintElem						{ $$ = $1; }
		;

ConstraintElem:
			CHECK '(' a_expr ')' ConstraintAttributeSpec
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_CHECK;
					n->location = @1;
					n->raw_expr = $3;
					n->cooked_expr = NULL;
					processCASbits($5, @5, "CHECK",
								   NULL, NULL, &n->skip_validation,
								   &n->is_no_inherit, yyscanner);
					n->initially_valid = !n->skip_validation;
					$$ = (Node *)n;
				}
			| UNIQUE '(' columnList ')' opt_definition OptConsTableSpace
				ConstraintAttributeSpec
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_UNIQUE;
					n->location = @1;
					n->keys = $3;
					n->options = $5;
					n->indexname = NULL;
					n->indexspace = $6;
					processCASbits($7, @7, "UNIQUE",
								   &n->deferrable, &n->initdeferred, NULL,
								   NULL, yyscanner);
					$$ = (Node *)n;
				}
			| UNIQUE ExistingIndex ConstraintAttributeSpec
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_UNIQUE;
					n->location = @1;
					n->keys = NIL;
					n->options = NIL;
					n->indexname = $2;
					n->indexspace = NULL;
					processCASbits($3, @3, "UNIQUE",
								   &n->deferrable, &n->initdeferred, NULL,
								   NULL, yyscanner);
					$$ = (Node *)n;
				}
			| PRIMARY KEY '(' columnList ')' opt_definition OptConsTableSpace
				ConstraintAttributeSpec
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_PRIMARY;
					n->location = @1;
					n->keys = $4;
					n->options = $6;
					n->indexname = NULL;
					n->indexspace = $7;
					processCASbits($8, @8, "PRIMARY KEY",
								   &n->deferrable, &n->initdeferred, NULL,
								   NULL, yyscanner);
					$$ = (Node *)n;
				}
			| PRIMARY KEY ExistingIndex ConstraintAttributeSpec
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_PRIMARY;
					n->location = @1;
					n->keys = NIL;
					n->options = NIL;
					n->indexname = $3;
					n->indexspace = NULL;
					processCASbits($4, @4, "PRIMARY KEY",
								   &n->deferrable, &n->initdeferred, NULL,
								   NULL, yyscanner);
					$$ = (Node *)n;
				}
			| EXCLUDE access_method_clause '(' ExclusionConstraintList ')'
				opt_definition OptConsTableSpace ExclusionWhereClause
				ConstraintAttributeSpec
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_EXCLUSION;
					n->location = @1;
					n->access_method	= $2;
					n->exclusions		= $4;
					n->options			= $6;
					n->indexname		= NULL;
					n->indexspace		= $7;
					n->where_clause		= $8;
					processCASbits($9, @9, "EXCLUDE",
								   &n->deferrable, &n->initdeferred, NULL,
								   NULL, yyscanner);
					$$ = (Node *)n;
				}
			| FOREIGN KEY '(' columnList ')' REFERENCES qualified_name
				opt_column_list key_match key_actions ConstraintAttributeSpec
				{
					Constraint *n = makeNode(Constraint);
					n->contype = CONSTR_FOREIGN;
					n->location = @1;
					n->pktable			= $7;
					n->fk_attrs			= $4;
					n->pk_attrs			= $8;
					n->fk_matchtype		= $9;
					n->fk_upd_action	= (char) ($10 >> 8);
					n->fk_del_action	= (char) ($10 & 0xFF);
					processCASbits($11, @11, "FOREIGN KEY",
								   &n->deferrable, &n->initdeferred,
								   &n->skip_validation, NULL,
								   yyscanner);
					n->initially_valid = !n->skip_validation;
					$$ = (Node *)n;
				}
		;

opt_no_inherit:	NO INHERIT							{  $$ = TRUE; }
			| /* EMPTY */							{  $$ = FALSE; }
		;

opt_column_list:
			'(' columnList ')'						{ $$ = $2; }
			| /*EMPTY*/								{ $$ = NIL; }
		;

columnList:
			columnElem								{ $$ = list_make1($1); }
			| columnList ',' columnElem				{ $$ = lappend($1, $3); }
		;

columnElem: ColId
				{
					$$ = (Node *) makeString($1);
				}
		;

distributed_by_list:
			distributed_by_elem						{ $$ = list_make1($1); }
			| distributed_by_list ',' distributed_by_elem
				{
					IndexElem *newelem = $3;
					ListCell *lc;

					foreach(lc, $1)
					{
						IndexElem  *oldelem = (IndexElem *) lfirst(lc);

						if (strcmp(oldelem->name, newelem->name) == 0)
							ereport(ERROR,
									(errcode(ERRCODE_DUPLICATE_COLUMN),
									 errmsg("duplicate column in DISTRIBUTED BY clause"),
									 parser_errposition(@3)));
					}

					$$ = lappend($1, newelem);
				}
			;

distributed_by_elem: ColId opt_class
				{
					/*
					 * only these fields are used, leave others as 0/NULL
					 */
					$$ = makeNode(IndexElem);
					$$->name = $1;
					$$->opclass = $2;
				}
		;

key_match:  MATCH FULL
			{
				$$ = FKCONSTR_MATCH_FULL;
			}
		| MATCH PARTIAL
			{
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("MATCH PARTIAL not yet implemented"),
						 parser_errposition(@1)));
				$$ = FKCONSTR_MATCH_PARTIAL;
			}
		| MATCH SIMPLE
			{
				$$ = FKCONSTR_MATCH_SIMPLE;
			}
		| /*EMPTY*/
			{
				$$ = FKCONSTR_MATCH_SIMPLE;
			}
		;

ExclusionConstraintList:
			ExclusionConstraintElem					{ $$ = list_make1($1); }
			| ExclusionConstraintList ',' ExclusionConstraintElem
													{ $$ = lappend($1, $3); }
		;

ExclusionConstraintElem: index_elem WITH any_operator
			{
				$$ = list_make2($1, $3);
			}
			/* allow OPERATOR() decoration for the benefit of ruleutils.c */
			| index_elem WITH OPERATOR '(' any_operator ')'
			{
				$$ = list_make2($1, $5);
			}
		;

ExclusionWhereClause:
			WHERE '(' a_expr ')'					{ $$ = $3; }
			| /*EMPTY*/								{ $$ = NULL; }
		;

/*
 * We combine the update and delete actions into one value temporarily
 * for simplicity of parsing, and then break them down again in the
 * calling production.  update is in the left 8 bits, delete in the right.
 * Note that NOACTION is the default.
 */
key_actions:
			key_update
				{ $$ = ($1 << 8) | (FKCONSTR_ACTION_NOACTION & 0xFF); }
			| key_delete
				{ $$ = (FKCONSTR_ACTION_NOACTION << 8) | ($1 & 0xFF); }
			| key_update key_delete
				{ $$ = ($1 << 8) | ($2 & 0xFF); }
			| key_delete key_update
				{ $$ = ($2 << 8) | ($1 & 0xFF); }
			| /*EMPTY*/
				{ $$ = (FKCONSTR_ACTION_NOACTION << 8) | (FKCONSTR_ACTION_NOACTION & 0xFF); }
		;

key_update: ON UPDATE key_action		{ $$ = $3; }
		;

key_delete: ON DELETE_P key_action		{ $$ = $3; }
		;

key_action:
			NO ACTION					{ $$ = FKCONSTR_ACTION_NOACTION; }
			| RESTRICT					{ $$ = FKCONSTR_ACTION_RESTRICT; }
			| CASCADE					{ $$ = FKCONSTR_ACTION_CASCADE; }
			| SET NULL_P				{ $$ = FKCONSTR_ACTION_SETNULL; }
			| SET DEFAULT				{ $$ = FKCONSTR_ACTION_SETDEFAULT; }
		;

OptInherit: INHERITS '(' qualified_name_list ')'	{ $$ = $3; }
			| /*EMPTY*/								{ $$ = NIL; }
		;

/* WITH (options) is preferred, WITH OIDS and WITHOUT OIDS are legacy forms */
OptWith:
			WITH reloptions				{ $$ = $2; }
			| WITH OIDS					{ $$ = list_make1(defWithOids(true)); }
			| WITHOUT OIDS				{ $$ = list_make1(defWithOids(false)); }
			| /*EMPTY*/					{ $$ = NIL; }
		;

OnCommitOption:  ON COMMIT DROP				{ $$ = ONCOMMIT_DROP; }
			| ON COMMIT DELETE_P ROWS		{ $$ = ONCOMMIT_DELETE_ROWS; }
			| ON COMMIT PRESERVE ROWS		{ $$ = ONCOMMIT_PRESERVE_ROWS; }
			| /*EMPTY*/						{ $$ = ONCOMMIT_NOOP; }
		;

OptTableSpace:   TABLESPACE name					{ $$ = $2; }
			| /*EMPTY*/								{ $$ = NULL; }
		;

OptConsTableSpace:   USING INDEX TABLESPACE name	{ $$ = $4; }
			| /*EMPTY*/								{ $$ = NULL; }
		;

ExistingIndex:   USING INDEX index_name				{ $$ = $3; }
		;

DistributedBy:   DISTRIBUTED BY  '(' distributed_by_list ')'
			{
				DistributedBy *distributedBy = makeNode(DistributedBy);
				distributedBy->ptype = POLICYTYPE_PARTITIONED;
				distributedBy->numsegments = -1;
				distributedBy->keyCols = $4;
				$$ = (Node *)distributedBy;
			}
			| DISTRIBUTED RANDOMLY
			{
				DistributedBy *distributedBy = makeNode(DistributedBy);
				distributedBy->ptype = POLICYTYPE_PARTITIONED;
				distributedBy->numsegments = -1;
				distributedBy->keyCols = NIL;
				$$ = (Node *)distributedBy;
			}
			| DISTRIBUTED REPLICATED
			{
				DistributedBy *distributedBy = makeNode(DistributedBy);
				distributedBy->ptype = POLICYTYPE_REPLICATED;
				distributedBy->numsegments = -1;
				distributedBy->keyCols = NIL;
				$$ = (Node *)distributedBy;
			}
		;

OptDistributedBy:   DistributedBy			{ $$ = $1; }
			| /*EMPTY*/								{ $$ = NULL; }
		;

/* START PARTITION RULES */

OptTabPartitionColumnEncList: TabPartitionColumnEncList { $$ = $1; }
			| /*EMPTY*/ { $$ = NULL; }
	;

TabPartitionColumnEncList:
	column_reference_storage_directive { $$ = list_make1($1); }
	| TabPartitionColumnEncList column_reference_storage_directive
				{
					$$ = lappend($1, $2);
				}
	;

OptTabPartitionStorageAttr: WITH definition TABLESPACE name 
				{
                    /* re-use alterpartitioncmd struct here... */
					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
                    pc->partid = NULL;
                    pc->arg1 = (Node *)$2;
                    pc->arg2 = (Node *)makeString($4);
                    pc->location = @1;
					$$ = (Node *)pc;
                }
			| WITH definition
				{
                    /* re-use alterpartitioncmd struct here... */
					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
                    pc->partid = NULL;
                    pc->arg1 = (Node *)$2;
                    pc->arg2 = NULL;
                    pc->location = @1;
					$$ = (Node *)pc;
 				}
			| TABLESPACE name 
				{
                    /* re-use alterpartitioncmd struct here... */
					AlterPartitionCmd *pc = makeNode(AlterPartitionCmd);
                    pc->partid = NULL;
                    pc->arg1 = NULL;
                    pc->arg2 = (Node *)makeString($2);
                    pc->location = @1;
					$$ = (Node *)pc;
				}
			| /*EMPTY*/ { $$ = NULL; }
		;

OptTabPartitionSpec: '(' TabPartitionElemList ')'
				{
                        PartitionSpec *n = makeNode(PartitionSpec); 
                        n->partElem  = $2;
                        n->subSpec   = NULL;
                        n->location  = @2;
                        $$ = (Node *)n;
				}
			| /*EMPTY*/								{ $$ = NULL; }
		;

OptTabSubPartitionSpec: 
            '(' TabSubPartitionElemList ')' 
				{
                        PartitionSpec *n = makeNode(PartitionSpec); 
                        n->partElem  = $2;
                        n->subSpec   = NULL;
                        n->location  = @2;
                        $$ = (Node *)n;
				}
			| /*EMPTY*/								{ $$ = NULL; }
		;

TabPartitionElemList:
            TabPartitionElem						{ $$ = list_make1($1); }
			| TabPartitionElemList ',' 
              TabPartitionElem						{ $$ = lappend($1, $3); }
		;
TabSubPartitionElemList:
            TabSubPartitionElem						{ $$ = list_make1($1); }
			| TabSubPartitionElemList ',' 
              TabSubPartitionElem					{ $$ = lappend($1, $3); }
		;

tab_part_val_no_paran: AexprConst { $$ = $1; }
			| CAST '(' tab_part_val AS Typename ')'
				{ 
					$$ = makeTypeCast($3, $5, @4);
				}
			| tab_part_val_no_paran TYPECAST Typename
				{ 
					$$ = makeTypeCast($1, $3, @2); 
				}
			| '-' tab_part_val_no_paran { $$ = doNegate($2, @1); }
		;

tab_part_val: tab_part_val_no_paran { $$ = $1; }
			| '(' tab_part_val_no_paran ')' { $$ = $2; }
			| '(' tab_part_val_no_paran ')' TYPECAST Typename
				{ 
					$$ = makeTypeCast($2, $5, @4); 
				}
		; 

TabPartitionBoundarySpecValList:
              tab_part_val				{ $$ = list_make1($1); }
			| TabPartitionBoundarySpecValList ',' 
              tab_part_val				{ $$ = lappend($1, $3); }
		;

OptTabPartitionRangeInclusive:
			INCLUSIVE			{ $$ = PART_EDGE_INCLUSIVE; }
			| EXCLUSIVE			{ $$ = PART_EDGE_EXCLUSIVE; }
			| /*EMPTY*/			{ $$ = PART_EDGE_UNSPECIFIED; }
		;

TabPartitionBoundarySpecStart:
			START 
            '(' TabPartitionBoundarySpecValList ')'
			OptTabPartitionRangeInclusive
				{
                        PartitionRangeItem *n = makeNode(PartitionRangeItem); 
                        n->partRangeVal  = $3;
                        if (!($5))
                            n->partedge = PART_EDGE_INCLUSIVE;
                        else
                            n->partedge = $5;
                        n->location  = @1;
                        $$ = (Node *)n;
				}
            ;

TabPartitionBoundarySpecEnd:
			END_P 
            '(' TabPartitionBoundarySpecValList ')'
			OptTabPartitionRangeInclusive
				{
                        PartitionRangeItem *n = makeNode(PartitionRangeItem); 
                        n->partRangeVal  = $3;
                        if (!($5))
                            n->partedge = PART_EDGE_EXCLUSIVE;
                        else
                            n->partedge = $5;
                        n->location  = @1;
                        $$ = (Node *)n;
				}
            ;

OptTabPartitionBoundarySpecEvery:
            EVERY '(' TabPartitionBoundarySpecValList ')' 
				{
                        PartitionRangeItem *n = makeNode(PartitionRangeItem); 
                        n->partRangeVal  = $3;
                        n->location  = @1;

                        $$ = (Node *)n;
				}
			| /*EMPTY*/								{ $$ = NULL; }
            ;

OptTabPartitionBoundarySpecEnd:
            TabPartitionBoundarySpecEnd 			{ $$ = $1; }
			| /*EMPTY*/								{ $$ = NULL; }
		;

/* VALUES for LIST, start..end for RANGE. */
TabPartitionBoundarySpec:
			part_values_clause
				{
                        PartitionValuesSpec *n = makeNode(PartitionValuesSpec); 

                        n->partValues = $1;
                        n->location  = @1;
                        $$ = (Node *)n;
				}
			| TabPartitionBoundarySpecStart
              OptTabPartitionBoundarySpecEnd
              OptTabPartitionBoundarySpecEvery  
				{
                        PartitionBoundSpec *n = makeNode(PartitionBoundSpec); 
                        n->partStart = $1;
                        n->partEnd   = $2;
                        n->partEvery = $3;
                        n->everyGenList = NIL; 
						n->pWithTnameStr = NULL;
                        n->location  = @1;
                        $$ = (Node *)n;
				}
			| TabPartitionBoundarySpecEnd
              OptTabPartitionBoundarySpecEvery	
				{
                        PartitionBoundSpec *n = makeNode(PartitionBoundSpec); 
                        n->partStart = NULL;
                        n->partEnd   = $1;
                        n->partEvery = $2;
                        n->everyGenList = NIL; 
						n->pWithTnameStr = NULL;
                        n->location  = @1;
                        $$ = (Node *)n;
				}
            ;

OptTabPartitionBoundarySpec:
            TabPartitionBoundarySpec				{ $$ = $1; }
			| /*EMPTY*/								{ $$ = NULL; }
		;

multi_spec_value_list: '(' part_values_single ')'
				{
					ListCell *lc;
					List *out = NIL;

					foreach(lc, $2)
						out = lappend(out, linitial(lfirst(lc)));

					$$ = list_make1(out);
				}
			| multi_spec_value_list ',' '(' part_values_single ')'
				{
					ListCell *lc;
					List *out = NIL;

					foreach(lc, $4)
						out = lappend(out, linitial(lfirst(lc)));

					$$ = lappend($1, out);
				}
		;

part_values_single: tab_part_val_no_paran
				{
					$$ = list_make1(list_make1($1));
				}
			| part_values_single ',' tab_part_val_no_paran
				{
					$$ = lappend($1, list_make1($3));
				}
		;

part_values_clause:
			VALUES '(' part_values_single ')'
				{
					$$ = $3;
				}
			| VALUES '(' multi_spec_value_list ')'
				{
					$$ = $3;
				}
		;

part_values_or_spec_list: TabPartitionBoundarySpecValList { $$ = $1; }
			| part_values_clause { $$ = $1; }
		;

/* a "Partition Element" closely corresponds to a "Partition Declaration" */
TabPartitionElem: 
            TabPartitionNameDecl 
            OptTabPartitionBoundarySpec	OptTabPartitionStorageAttr
			OptTabPartitionColumnEncList
			OptTabSubPartitionSpec 
				{
                        PartitionElem *n = makeNode(PartitionElem); 
                        n->partName  = $1;
                        n->boundSpec = $2;
                        n->subSpec   = $5;
                        n->location  = @1;
                        n->isDefault = 0;
                        n->storeAttr = $3;
                        n->colencs   = $4;
                        n->AddPartDesc = NULL;
                        $$ = (Node *)n;
				}

/* allow boundary spec for default partition in parser, but complain later */
			| TabPartitionDefaultNameDecl 
              OptTabPartitionBoundarySpec
              OptTabPartitionStorageAttr
			  OptTabPartitionColumnEncList
			  OptTabSubPartitionSpec 
				{
                        PartitionElem *n = makeNode(PartitionElem); 
                        n->partName  = $1;
                        n->boundSpec = $2;
                        n->subSpec   = $5;
                        n->location  = @1;
                        n->isDefault = true;
                        n->storeAttr = $3;
                        n->colencs   = $4;
                        $$ = (Node *)n;
				}
			| TabPartitionBoundarySpec 
              OptTabPartitionStorageAttr
			  OptTabPartitionColumnEncList
			  OptTabSubPartitionSpec 
				{
                        PartitionElem *n = makeNode(PartitionElem); 
                        n->partName  = NULL;
                        n->boundSpec = $1;
                        n->subSpec   = $4;
                        n->location  = @1;
                        n->isDefault = 0;
                        n->storeAttr = $2;
                        n->colencs   = $3;
                        n->AddPartDesc = NULL;
                        $$ = (Node *)n;
				}
			| column_reference_storage_directive
				{
					$$ = (Node *)$1;
				}
            ;

TabSubPartitionElem: 
            TabSubPartitionNameDecl OptTabPartitionBoundarySpec	
			OptTabPartitionStorageAttr
			OptTabPartitionColumnEncList
            OptTabSubPartitionSpec
				{
                        PartitionElem *n = makeNode(PartitionElem); 
                        n->partName  = $1;
                        n->boundSpec = $2;
                        n->subSpec   = $5;
                        n->location  = @1;
                        n->isDefault = 0;
                        n->storeAttr = $3;
                        n->colencs   = $4;
                        n->AddPartDesc = NULL;
                        $$ = (Node *)n;
				}
/* allow boundary spec for default partition in parser, but complain later */
			| TabSubPartitionDefaultNameDecl OptTabPartitionBoundarySpec	
 			  OptTabPartitionStorageAttr
			  OptTabPartitionColumnEncList
              OptTabSubPartitionSpec
				{
                        PartitionElem *n = makeNode(PartitionElem); 
                        n->partName  = $1;
                        n->boundSpec = $2;
                        n->subSpec   = $5;
                        n->location  = @1;
                        n->isDefault = true;
                        n->storeAttr = $3;
                        n->colencs   = $4;
                        n->AddPartDesc = NULL;
                        $$ = (Node *)n;
				}
			| TabPartitionBoundarySpec
              OptTabPartitionStorageAttr
			  OptTabPartitionColumnEncList
 			  OptTabSubPartitionSpec	
				{
                        PartitionElem *n = makeNode(PartitionElem); 
                        n->partName  = NULL;
                        n->boundSpec = $1;
                        n->subSpec   = $4;
                        n->location  = @1;
                        n->isDefault = false;
                        n->colencs   = $3;
                        n->storeAttr = $2;
                        n->AddPartDesc = NULL;
                        $$ = (Node *)n;
				}
			| column_reference_storage_directive
				{
					$$ = (Node *)$1;
				}
            ;

TabPartitionNameDecl: PARTITION PartitionColId
				{
					$$ = $2;
				}
		;
TabPartitionDefaultNameDecl: DEFAULT PARTITION PartitionColId
				{
					$$ = $3;
				}
		;

TabSubPartitionNameDecl: SUBPARTITION PartitionColId
				{
					$$ = $2;
				}
		;

TabSubPartitionDefaultNameDecl: DEFAULT SUBPARTITION PartitionColId
				{
					$$ = $3;
				}
		;

TabPartitionByType:
			RANGE 				{ $$ = PARTTYP_RANGE; }
			| LIST				{ $$ = PARTTYP_LIST; }
			| /*EMPTY*/
				{
					$$ = PARTTYP_RANGE; 

					ereport(ERROR,
							(errcode(ERRCODE_SYNTAX_ERROR),
							 errmsg("PARTITION BY must specify RANGE or LIST")));
				}
		;

OptTabPartitionBy:
			PARTITION BY 
            TabPartitionByType '(' columnList ')'
			opt_list_subparts
            OptTabPartitionSpec						
				{
					PartitionBy *n = makeNode(PartitionBy); 
						
					n->partType = $3;
					n->keys     = $5; 
					n->subPart  = $7;
					if (PointerIsValid(n->subPart) &&
						!IsA(n->subPart, PartitionBy))
						parser_yyerror("syntax error");

					n->partSpec = $8;
					n->partDepth = 0;
					n->partQuiet = PART_VERBO_NODISTRO;
					n->location  = @3;
					n->partDefault = NULL;
					$$ = (Node *)n;
				}
			| /*EMPTY*/								{ $$ = NULL; }
		;

TabSubPartitionTemplate:
			SUBPARTITION TEMPLATE
			'(' TabSubPartitionElemList ')'
				{
					PartitionSpec *n = makeNode(PartitionSpec); 
					n->partElem  = $4;
					n->subSpec   = NULL;
					n->istemplate  = true;
					n->location  = @3;
					$$ = (Node *)n;

					/* a little (temporary?) syntax check on templates */
					if (n->partElem)
					{
						List *elems;
						ListCell *lc;
						Assert(IsA(n->partElem, List));

						elems = (List *)n->partElem;
						foreach(lc, elems)
						{
							PartitionElem *e = lfirst(lc);

							if (!IsA(e, PartitionElem)) continue;

							if (e->subSpec)
								ereport(ERROR,
										(errcode(ERRCODE_SYNTAX_ERROR),
										 errmsg("template cannot contain "
												"specification for child "
												"partition")));
						}

					}
				}
		;

opt_list_subparts: TabSubPartition { $$ = $1; }
			| /*EMPTY*/ { $$ = NULL; }
		;


TabSubPartitionBy: SUBPARTITION BY
			TabPartitionByType '(' columnList ')'
				{
					PartitionBy *n = makeNode(PartitionBy);
					n->partType = $3;
					n->keys = $5;
					n->subPart  = NULL;
					n->partSpec = NULL;
					n->partDepth = 0;
					n->partQuiet = PART_VERBO_NODISTRO;
					n->location  = @3;
					n->partDefault = NULL;
					$$ = (Node *)n;
				}
			;

TabSubPartition:
			TabSubPartitionBy TabSubPartitionTemplate
				{
					PartitionBy *pby = (PartitionBy *)$1;

					((PartitionBy *)pby)->partSpec = $2;

					$$ = $1;
				}
			| TabSubPartitionBy { $$ = $1; }
			|  TabSubPartitionBy TabSubPartition
				{
					PartitionBy *pby = (PartitionBy *)$1;
					pby->subPart = $2;
					$$ = (Node *)pby;
				}
			| TabSubPartitionBy TabSubPartitionTemplate TabSubPartition
				{
					PartitionBy *pby = (PartitionBy *)$1;
					pby->partSpec = $2;
					pby->subPart = $3;
					$$ = (Node *)pby;
				}
		;
/* END PARTITION RULES */


/*****************************************************************************
 *
 *		QUERY :
 *				CREATE TABLE relname AS SelectStmt [ WITH [NO] DATA ]
 *
 *
 * Note: SELECT ... INTO is a now-deprecated alternative for this.
 *
 *****************************************************************************/

CreateAsStmt:
		CREATE OptTemp TABLE create_as_target AS SelectStmt opt_with_data OptDistributedBy OptTabPartitionBy
				{
					CreateTableAsStmt *ctas = makeNode(CreateTableAsStmt);
					ctas->query = $6;
					ctas->into = $4;
					ctas->relkind = OBJECT_TABLE;
					ctas->is_select_into = false;
					/* cram additional flags into the IntoClause */
					$4->rel->relpersistence = $2;
					ctas->into->distributedBy = $8;

					if ($9)
						ereport(ERROR,
                                (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
								 errmsg("Cannot create a partitioned table using CREATE TABLE AS SELECT"),
                                 errhint("Use CREATE TABLE...LIKE (followed by INSERT...SELECT) instead")));

					$4->skipData = !($7);
					$$ = (Node *) ctas;
				}
		;

create_as_target:
			qualified_name opt_column_list OptWith OnCommitOption OptTableSpace
				{
					$$ = makeNode(IntoClause);
					$$->rel = $1;
					$$->colNames = $2;
					$$->options = $3;
					$$->onCommit = $4;
					$$->tableSpaceName = $5;
					$$->viewQuery = NULL;
					$$->skipData = false;		/* might get changed later */
				}
		;

opt_with_data:
			WITH DATA_P								{ $$ = TRUE; }
			| WITH NO DATA_P						{ $$ = FALSE; }
			| /*EMPTY*/								{ $$ = TRUE; }
		;

/*****************************************************************************
 *
 *		QUERY :
 *				CREATE EXTERNAL [WEB] TABLE relname
 *
 *****************************************************************************/
	
CreateExternalStmt:	CREATE OptWritable EXTERNAL OptWeb OptTemp TABLE qualified_name '(' OptExtTableElementList ')' 
					ExtTypedesc FORMAT Sconst format_opt ext_options_opt ext_opt_encoding_list ExtSingleRowErrorHandling OptDistributedBy
						{
							CreateExternalStmt *n = makeNode(CreateExternalStmt);
							n->iswritable = $2;
							n->isweb = $4;
							$7->relpersistence = $5;
							n->relation = $7;
							n->tableElts = $9;
							n->exttypedesc = (ExtTableTypeDesc *) $11;
							n->format = $13;
							n->formatOpts = $14;
							n->extOptions = $15;
							n->encoding = $16;
							n->sreh = $17;
							n->distributedBy = (DistributedBy *) $18;
							
							/* various syntax checks for EXECUTE external table */
							if(((ExtTableTypeDesc *) n->exttypedesc)->exttabletype == EXTTBL_TYPE_EXECUTE)
							{
								ExtTableTypeDesc *extdesc = (ExtTableTypeDesc *) n->exttypedesc;
								
								if(!n->isweb)
									ereport(ERROR,
											(errcode(ERRCODE_SYNTAX_ERROR),
										 	 errmsg("EXECUTE may not be used with a regular external table"),
										 	 errhint("Use CREATE EXTERNAL WEB TABLE instead")));							
								
								/* if no ON clause specified, default to "ON ALL" */
								if(extdesc->on_clause == NIL)
								{									
									extdesc->on_clause = lappend(extdesc->on_clause, 
										   				   		 makeDefElem("all", (Node *)makeInteger(TRUE)));
								}
								else if(n->iswritable)
								{
									ereport(ERROR,
											(errcode(ERRCODE_SYNTAX_ERROR),
									 		 errmsg("ON clause may not be used with a writable external table")));							
								}
							}

							if(n->sreh)
							{
								if (n->iswritable)
									ereport(ERROR,
										(errcode(ERRCODE_SYNTAX_ERROR),
										 errmsg("Single row error handling may not be used with a writable external table")));

								if (((SingleRowErrorDesc *)n->sreh)->log_errors_type == LOG_ERRORS_PERSISTENTLY)
								{
									n->extOptions = lappend(n->extOptions,
															makeDefElem("error_log_persistent", (Node *)makeString("true")));
								}
							}

							$$ = (Node *)n;							
						}
						;

OptWritable:	WRITABLE				{ $$ = TRUE; }
				| READABLE				{ $$ = FALSE; }
				| /*EMPTY*/				{ $$ = FALSE; }
				;

OptWeb:		WEB						{ $$ = TRUE; }
			| /*EMPTY*/				{ $$ = FALSE; }
			;

ExtTypedesc:
			LOCATION '(' cdb_string_list ')' ext_on_clause_list
			{
				ExtTableTypeDesc *n = makeNode(ExtTableTypeDesc);
				n->exttabletype = EXTTBL_TYPE_LOCATION;
				n->location_list = $3; 
				n->on_clause = $5;
				n->command_string = NULL;
				$$ = (Node *)n;
	
			}
			| EXECUTE Sconst ext_on_clause_list
			{
				ExtTableTypeDesc *n = makeNode(ExtTableTypeDesc);
				n->exttabletype = EXTTBL_TYPE_EXECUTE;
				n->location_list = NIL; 
				n->command_string = $2;
				n->on_clause = $3; /* default will get set later if needed */
						
				$$ = (Node *)n;
			}
			;

ext_on_clause_list:
			ext_on_clause_list ext_on_clause_item		{ $$ = lappend($1, $2); }
			| /*EMPTY*/									{ $$ = NIL; }
			;
	
ext_on_clause_item:
			ON ALL	
			{
				$$ = makeDefElem("all", (Node *)makeInteger(TRUE));
			}
			| ON HOST Sconst
			{
				$$ = makeDefElem("hostname", (Node *)makeString($3));
			}
			| ON HOST
			{
				$$ = makeDefElem("eachhost", (Node *)makeInteger(TRUE));
			}
			| ON MASTER
			{
				$$ = makeDefElem("master", (Node *)makeInteger(TRUE));
			}
			| ON SEGMENT Iconst
			{
				$$ = makeDefElem("segment", (Node *)makeInteger($3));
			}
			| ON Iconst
			{
				$$ = makeDefElem("random", (Node *)makeInteger($2));
			}
			;

format_opt: 
			  '(' format_opt_list ')'			{ $$ = $2; }
			| '(' format_def_list ')'			{ $$ = $2; }
			| '(' ')'							{ $$ = NIL; }
			| /*EMPTY*/							{ $$ = NIL; }
			;

format_opt_list:
			format_opt_item		
			{ 
				$$ = list_make1($1);
			}
			| format_opt_list format_opt_item		
			{ 
				$$ = lappend($1, $2); 
			}
			;

format_def_list:
			format_def_item		
			{ 
				$$ = list_make1($1);
			} 
			| format_def_list ',' format_def_item
			{
				$$ = lappend($1, $3);
			}
;

format_def_item:
    		ColLabel '=' def_arg
			{
				$$ = makeDefElem($1, $3);
			}
			| ColLabel '=' '(' columnList ')'
			{
				$$ = makeDefElem($1, (Node *) $4);
			}
;

format_opt_item:
			DELIMITER opt_as Sconst
			{
				$$ = makeDefElem("delimiter", (Node *)makeString($3));
			}
			| NULL_P opt_as Sconst
			{
				$$ = makeDefElem("null", (Node *)makeString($3));
			}
			| CSV
			{
				$$ = makeDefElem("csv", (Node *)makeInteger(TRUE));
			}
			| HEADER_P
			{
				$$ = makeDefElem("header", (Node *)makeInteger(TRUE));
			}
			| QUOTE opt_as Sconst
			{
				$$ = makeDefElem("quote", (Node *)makeString($3));
			}
			| ESCAPE opt_as Sconst
			{
				$$ = makeDefElem("escape", (Node *)makeString($3));
			}
			| FORCE NOT NULL_P columnList
			{
				$$ = makeDefElem("force_not_null", (Node *)$4);
			}
			| FORCE QUOTE columnList
			{
				$$ = makeDefElem("force_quote", (Node *)$3);
			}
			| FORCE QUOTE '*'
			{
				$$ = makeDefElem("force_quote", (Node *)makeNode(A_Star));
			}
			| FILL MISSING FIELDS
			{
				$$ = makeDefElem("fill_missing_fields", (Node *)makeInteger(TRUE));
			}
			| NEWLINE opt_as Sconst
			{
				$$ = makeDefElem("newline", (Node *)makeString($3));
			}
			;

ext_options_opt:
			OPTIONS ext_options					{ $$ = $2; }
			| /*EMPTY*/                         { $$ = NIL; }
			;

ext_options:
			'(' ext_options_list ')'           { $$ = $2; }
			| '(' ')'                           { $$ = NIL; }
			;

ext_options_list:
			ext_options_item
			{
				$$ = list_make1($1);
			}
			| ext_options_list ',' ext_options_item
			{
				$$ = lappend($1, $3);
			}
			;

ext_options_item:
			ColLabel Sconst
			{
				$$ = makeDefElem($1, (Node *)makeString($2));
			}
			;

OptExtTableElementList:
			ExtTableElementList				{ $$ = $1; }
			| /*EMPTY*/						{ $$ = NIL; }
			;

ExtTableElementList:
			ExtTableElement
			{
				$$ = list_make1($1);
			}
			| ExtTableElementList ',' ExtTableElement
			{
				$$ = lappend($1, $3);
			}
			;

ExtTableElement:
			ExtcolumnDef					{ $$ = $1; }
			| TableLikeClause				{ $$ = $1; }
			;

/* column def for ext table - allowed to have NOT NULL and DEFAULT constraints */
ExtcolumnDef:	ColId Typename ExtColQualList
		{
			ColumnDef *n = makeNode(ColumnDef);
			n->colname = $1;
			n->typeName = $2;
			n->is_local = true;
			n->is_not_null = false;
			n->raw_default = NULL;
			n->cooked_default = NULL;
			n->constraints = $3;
			n->location = @1;
			$$ = (Node *)n;
		}
		;

ExtColConstraintElem:
			NullColConstraintElem 					{ $$ = $1; }
			| DefaultColConstraintElem				{ $$ = $1; }
		;

ExtColQualList:
			ExtColQualList ExtColConstraintElem		{ $$ = lappend($1, $2); }
			| /*EMPTY*/								{ $$ = NIL; }
		;

/*
 * Single row error handling SQL
 */
OptSingleRowErrorHandling:
		OptLogErrorTable SEGMENT REJECT_P LIMIT Iconst OptSrehLimitType
		{
			SingleRowErrorDesc *n = makeNode(SingleRowErrorDesc);
			n->into_file = $1 == LOG_ERRORS_DISABLE ? false : true;
			n->log_errors_type = n->into_file ? LOG_ERRORS_ENABLE : LOG_ERRORS_DISABLE;
			n->rejectlimit = $5;
			n->is_limit_in_rows = $6; /* true for ROWS false for PERCENT */

			/* PERCENT value check */
			if(!n->is_limit_in_rows && (n->rejectlimit < 1 || n->rejectlimit > 100))
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
						 errmsg("invalid PERCENT value. Should be (1 - 100)")));
			
			/* ROW values check */
			if(n->is_limit_in_rows && n->rejectlimit < 2)
			   ereport(ERROR,
					   (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
						errmsg("invalid (ROWS) reject limit. Should be 2 or larger")));

			$$ = (Node *)n;
		}
		| /*EMPTY*/		{ $$ = NULL; }
		;
	
OptLogErrorTable:
		LOG_P ERRORS INTO qualified_name
		{
			if (gp_ignore_error_table) /* ignore the [INTO error-table] clause for backward compatibility */
			{
			ereport(WARNING,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("error table is not supported"),
					 errhint("Use gp_read_error_log() and gp_truncate_error_log() to view and manage the internal error log associated with your table.")));
			}
			else
			{
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("error table is not supported"),
					 errhint("Set gp_ignore_error_table to ignore the [INTO error-table] clause for backward compatibility."),
					 parser_errposition(@3)));
			}
			$$ = LOG_ERRORS_ENABLE;
		}
		| LOG_P ERRORS						{ $$ = LOG_ERRORS_ENABLE; }
		| /*EMPTY*/							{ $$ = LOG_ERRORS_DISABLE; }
		;
ExtSingleRowErrorHandling:
		ExtLogErrorTable SEGMENT REJECT_P LIMIT Iconst OptSrehLimitType
		{
			SingleRowErrorDesc *n = makeNode(SingleRowErrorDesc);
			n->log_errors_type = $1;
			n->into_file = n->log_errors_type == LOG_ERRORS_DISABLE ? false : true;
			n->rejectlimit = $5;
			n->is_limit_in_rows = $6; /* true for ROWS false for PERCENT */

			/* PERCENT value check */
			if(!n->is_limit_in_rows && (n->rejectlimit < 1 || n->rejectlimit > 100))
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
						 errmsg("invalid PERCENT value. Should be (1 - 100)")));

			/* ROW values check */
			if(n->is_limit_in_rows && n->rejectlimit < 2)
			   ereport(ERROR,
					   (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
						errmsg("invalid (ROWS) reject limit. Should be 2 or larger")));

			$$ = (Node *)n;
		}
		| /*EMPTY*/		{ $$ = NULL; }
		;

ExtLogErrorTable:
		OptLogErrorTable				{ $$ = $1; }
		| LOG_P ERRORS PERSISTENTLY		{ $$ = LOG_ERRORS_PERSISTENTLY; }
		;

OptSrehLimitType:		
		ROWS					{ $$ = TRUE; }
		| PERCENT				{ $$ = FALSE; }
		| /* default is ROWS */	{ $$ = TRUE; }
		;

/*
 * ENCODING. (we cheat a little and use a list, even though it's 1 item max).
 */
ext_opt_encoding_list:
		ext_opt_encoding_list ext_opt_encoding_item		{ $$ = lappend($1, $2); }
		| /*EMPTY*/										{ $$ = NIL; }
		;
	
ext_opt_encoding_item:
		ENCODING opt_equal Sconst
		{
			$$ = makeDefElem("encoding", (Node *)makeString($3));
		}
		| ENCODING opt_equal Iconst
		{
			$$ = makeDefElem("encoding", (Node *)makeInteger($3));
		}
		;

/*****************************************************************************
 *
 *		QUERY :
 *				CREATE MATERIALIZED VIEW relname AS SelectStmt
 *
 *****************************************************************************/

CreateMatViewStmt:
		CREATE OptNoLog MATERIALIZED VIEW create_mv_target AS SelectStmt opt_with_data OptDistributedBy
				{
					CreateTableAsStmt *ctas = makeNode(CreateTableAsStmt);
					ctas->query = $7;
					ctas->into = $5;
					ctas->relkind = OBJECT_MATVIEW;
					ctas->is_select_into = false;
					/* cram additional flags into the IntoClause */
					$5->rel->relpersistence = $2;
					$5->skipData = !($8);
					ctas->into->distributedBy = $9;

					$$ = (Node *) ctas;
				}
		;

create_mv_target:
			qualified_name opt_column_list opt_reloptions OptTableSpace
				{
					$$ = makeNode(IntoClause);
					$$->rel = $1;
					$$->colNames = $2;
					$$->options = $3;
					$$->onCommit = ONCOMMIT_NOOP;
					$$->tableSpaceName = $4;
					$$->viewQuery = NULL;		/* filled at analysis time */
					$$->skipData = false;		/* might get changed later */
				}
		;

OptNoLog:	UNLOGGED					{ $$ = RELPERSISTENCE_UNLOGGED; }
			| /*EMPTY*/					{ $$ = RELPERSISTENCE_PERMANENT; }
		;


/*****************************************************************************
 *
 *		QUERY :
 *				REFRESH MATERIALIZED VIEW qualified_name
 *
 *****************************************************************************/

RefreshMatViewStmt:
			REFRESH MATERIALIZED VIEW opt_concurrently qualified_name opt_with_data
				{
					RefreshMatViewStmt *n = makeNode(RefreshMatViewStmt);
					n->concurrent = $4;
					n->relation = $5;
					n->skipData = !($6);
					$$ = (Node *) n;
				}
		;


/*****************************************************************************
 *
 *		QUERY :
 *				CREATE SEQUENCE seqname
 *				ALTER SEQUENCE seqname
 *
 *****************************************************************************/

CreateSeqStmt:
			CREATE OptTemp SEQUENCE qualified_name OptSeqOptList
				{
					CreateSeqStmt *n = makeNode(CreateSeqStmt);
					$4->relpersistence = $2;
					n->sequence = $4;
					n->options = $5;
					n->ownerId = InvalidOid;
					$$ = (Node *)n;
				}
		;

AlterSeqStmt:
			ALTER SEQUENCE qualified_name SeqOptList
				{
					AlterSeqStmt *n = makeNode(AlterSeqStmt);
					n->sequence = $3;
					n->options = $4;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER SEQUENCE IF_P EXISTS qualified_name SeqOptList
				{
					AlterSeqStmt *n = makeNode(AlterSeqStmt);
					n->sequence = $5;
					n->options = $6;
					n->missing_ok = true;
					$$ = (Node *)n;
				}

		;

OptSeqOptList: SeqOptList							{ $$ = $1; }
			| /*EMPTY*/								{ $$ = NIL; }
		;

SeqOptList: SeqOptElem								{ $$ = list_make1($1); }
			| SeqOptList SeqOptElem					{ $$ = lappend($1, $2); }
		;

SeqOptElem: CACHE NumericOnly
				{
					$$ = makeDefElem("cache", (Node *)$2);
				}
			| CYCLE
				{
					$$ = makeDefElem("cycle", (Node *)makeInteger(TRUE));
				}
			| NO CYCLE
				{
					$$ = makeDefElem("cycle", (Node *)makeInteger(FALSE));
				}
			| INCREMENT opt_by NumericOnly
				{
					$$ = makeDefElem("increment", (Node *)$3);
				}
			| MAXVALUE NumericOnly
				{
					$$ = makeDefElem("maxvalue", (Node *)$2);
				}
			| MINVALUE NumericOnly
				{
					$$ = makeDefElem("minvalue", (Node *)$2);
				}
			| NO MAXVALUE
				{
					$$ = makeDefElem("maxvalue", NULL);
				}
			| NO MINVALUE
				{
					$$ = makeDefElem("minvalue", NULL);
				}
			| OWNED BY any_name
				{
					$$ = makeDefElem("owned_by", (Node *)$3);
				}
			| START opt_with NumericOnly
				{
					$$ = makeDefElem("start", (Node *)$3);
				}
			| RESTART
				{
					$$ = makeDefElem("restart", NULL);
				}
			| RESTART opt_with NumericOnly
				{
					$$ = makeDefElem("restart", (Node *)$3);
				}
		;

opt_by:		BY				{}
			| /* empty */	{}
	  ;

NumericOnly:
			FCONST								{ $$ = makeFloat($1); }
			| '+' FCONST						{ $$ = makeFloat($2); }
			| '-' FCONST
				{
					$$ = makeFloat($2);
					doNegateFloat($$);
				}
			| SignedIconst						{ $$ = makeInteger($1); }
		;

NumericOnly_list:	NumericOnly						{ $$ = list_make1($1); }
				| NumericOnly_list ',' NumericOnly	{ $$ = lappend($1, $3); }
		;

/*****************************************************************************
 *
 *		QUERIES :
 *				CREATE [OR REPLACE] [TRUSTED] [PROCEDURAL] LANGUAGE ...
 *				DROP [PROCEDURAL] LANGUAGE ...
 *
 *****************************************************************************/

CreatePLangStmt:
			CREATE opt_or_replace opt_trusted opt_procedural LANGUAGE NonReservedWord_or_Sconst
			{
				CreatePLangStmt *n = makeNode(CreatePLangStmt);
				n->replace = $2;
				n->plname = $6;
				/* parameters are all to be supplied by system */
				n->plhandler = NIL;
				n->plinline = NIL;
				n->plvalidator = NIL;
				n->pltrusted = false;
				$$ = (Node *)n;
			}
			| CREATE opt_or_replace opt_trusted opt_procedural LANGUAGE NonReservedWord_or_Sconst
			  HANDLER handler_name opt_inline_handler opt_validator
			{
				CreatePLangStmt *n = makeNode(CreatePLangStmt);
				n->replace = $2;
				n->plname = $6;
				n->plhandler = $8;
				n->plinline = $9;
				n->plvalidator = $10;
				n->pltrusted = $3;
				$$ = (Node *)n;
			}
		;

opt_trusted:
			TRUSTED									{ $$ = TRUE; }
			| /*EMPTY*/								{ $$ = FALSE; }
		;

/* This ought to be just func_name, but that causes reduce/reduce conflicts
 * (CREATE LANGUAGE is the only place where func_name isn't followed by '(').
 * Work around by using simple names, instead.
 */
handler_name:
			name						{ $$ = list_make1(makeString($1)); }
			| name attrs				{ $$ = lcons(makeString($1), $2); }
		;

opt_inline_handler:
			INLINE_P handler_name					{ $$ = $2; }
			| /*EMPTY*/								{ $$ = NIL; }
		;

validator_clause:
			VALIDATOR handler_name					{ $$ = $2; }
			| NO VALIDATOR							{ $$ = NIL; }
		;

opt_validator:
			validator_clause						{ $$ = $1; }
			| /*EMPTY*/								{ $$ = NIL; }
		;

DropPLangStmt:
			DROP opt_procedural LANGUAGE NonReservedWord_or_Sconst opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_LANGUAGE;
					n->objects = list_make1(list_make1(makeString($4)));
					n->arguments = NIL;
					n->behavior = $5;
					n->missing_ok = false;
					n->concurrent = false;
					$$ = (Node *)n;
				}
			| DROP opt_procedural LANGUAGE IF_P EXISTS NonReservedWord_or_Sconst opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_LANGUAGE;
					n->objects = list_make1(list_make1(makeString($6)));
					n->behavior = $7;
					n->missing_ok = true;
					n->concurrent = false;
					$$ = (Node *)n;
				}
		;

opt_procedural:
			PROCEDURAL								{}
			| /*EMPTY*/								{}
		;

/*****************************************************************************
 *
 *		QUERY:
 *             CREATE TABLESPACE tablespace LOCATION '/path/to/tablespace/'
 *
 *****************************************************************************/

CreateTableSpaceStmt: CREATE TABLESPACE name OptTableSpaceOwner LOCATION Sconst opt_reloptions
				{
					CreateTableSpaceStmt *n = makeNode(CreateTableSpaceStmt);
					n->tablespacename = $3;
					n->owner = $4;
					n->location = $6;
					n->options = $7;
					$$ = (Node *) n;
				}
		;

OptTableSpaceOwner: OWNER name			{ $$ = $2; }
			| /*EMPTY */				{ $$ = NULL; }
		;

/*****************************************************************************
 *
 *		QUERY :
 *				DROP TABLESPACE <tablespace>
 *
 *		No need for drop behaviour as we cannot implement dependencies for
 *		objects in other databases; we can only support RESTRICT.
 *
 ****************************************************************************/

DropTableSpaceStmt: DROP TABLESPACE name
				{
					DropTableSpaceStmt *n = makeNode(DropTableSpaceStmt);
					n->tablespacename = $3;
					n->missing_ok = false;
					$$ = (Node *) n;
				}
				|  DROP TABLESPACE IF_P EXISTS name
				{
					DropTableSpaceStmt *n = makeNode(DropTableSpaceStmt);
					n->tablespacename = $5;
					n->missing_ok = true;
					$$ = (Node *) n;
				}
		;

/*****************************************************************************
 *
 *		QUERY:
 *             CREATE EXTENSION extension
 *             [ WITH ] [ SCHEMA schema ] [ VERSION version ] [ FROM oldversion ]
 *
 *****************************************************************************/

CreateExtensionStmt: CREATE EXTENSION name opt_with create_extension_opt_list
				{
					CreateExtensionStmt *n = makeNode(CreateExtensionStmt);
					n->extname = $3;
					n->if_not_exists = false;
					n->options = $5;
					$$ = (Node *) n;
				}
				| CREATE EXTENSION IF_P NOT EXISTS name opt_with create_extension_opt_list
				{
					CreateExtensionStmt *n = makeNode(CreateExtensionStmt);
					n->extname = $6;
					n->if_not_exists = true;
					n->options = $8;
					$$ = (Node *) n;
				}
		;

create_extension_opt_list:
			create_extension_opt_list create_extension_opt_item
				{ $$ = lappend($1, $2); }
			| /* EMPTY */
				{ $$ = NIL; }
		;

create_extension_opt_item:
			SCHEMA name
				{
					$$ = makeDefElem("schema", (Node *)makeString($2));
				}
			| VERSION_P NonReservedWord_or_Sconst
				{
					$$ = makeDefElem("new_version", (Node *)makeString($2));
				}
			| FROM NonReservedWord_or_Sconst
				{
					$$ = makeDefElem("old_version", (Node *)makeString($2));
				}
		;

/*****************************************************************************
 *
 * ALTER EXTENSION name UPDATE [ TO version ]
 *
 *****************************************************************************/

AlterExtensionStmt: ALTER EXTENSION name UPDATE alter_extension_opt_list
				{
					AlterExtensionStmt *n = makeNode(AlterExtensionStmt);
					n->extname = $3;
					n->options = $5;
					$$ = (Node *) n;
				}
		;

alter_extension_opt_list:
			alter_extension_opt_list alter_extension_opt_item
				{ $$ = lappend($1, $2); }
			| /* EMPTY */
				{ $$ = NIL; }
		;

alter_extension_opt_item:
			TO NonReservedWord_or_Sconst
				{
					$$ = makeDefElem("new_version", (Node *)makeString($2));
				}
		;

/*****************************************************************************
 *
 * ALTER EXTENSION name ADD/DROP object-identifier
 *
 *****************************************************************************/

AlterExtensionContentsStmt:
			ALTER EXTENSION name add_drop AGGREGATE func_name aggr_args
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_AGGREGATE;
					n->objname = $6;
					n->objargs = extractAggrArgTypes($7);
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop CAST '(' Typename AS Typename ')'
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_CAST;
					n->objname = list_make1($7);
					n->objargs = list_make1($9);
					$$ = (Node *) n;
				}
			| ALTER EXTENSION name add_drop COLLATION any_name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_COLLATION;
					n->objname = $6;
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop CONVERSION_P any_name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_CONVERSION;
					n->objname = $6;
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop DOMAIN_P any_name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_DOMAIN;
					n->objname = $6;
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop FUNCTION function_with_argtypes
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_FUNCTION;
					n->objname = $6->funcname;
					n->objargs = $6->funcargs;
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop opt_procedural LANGUAGE name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_LANGUAGE;
					n->objname = list_make1(makeString($7));
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop OPERATOR any_operator oper_argtypes
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_OPERATOR;
					n->objname = $6;
					n->objargs = $7;
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop OPERATOR CLASS any_name USING access_method
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_OPCLASS;
					n->objname = $7;
					n->objargs = list_make1(makeString($9));
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop OPERATOR FAMILY any_name USING access_method
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_OPFAMILY;
					n->objname = $7;
					n->objargs = list_make1(makeString($9));
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop SCHEMA name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_SCHEMA;
					n->objname = list_make1(makeString($6));
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop EVENT TRIGGER name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_EVENT_TRIGGER;
					n->objname = list_make1(makeString($7));
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop TABLE any_name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_TABLE;
					n->objname = $6;
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop TEXT_P SEARCH PARSER any_name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_TSPARSER;
					n->objname = $8;
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop TEXT_P SEARCH DICTIONARY any_name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_TSDICTIONARY;
					n->objname = $8;
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop TEXT_P SEARCH TEMPLATE any_name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_TSTEMPLATE;
					n->objname = $8;
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop TEXT_P SEARCH CONFIGURATION any_name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_TSCONFIGURATION;
					n->objname = $8;
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop SEQUENCE any_name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_SEQUENCE;
					n->objname = $6;
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop VIEW any_name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_VIEW;
					n->objname = $6;
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop MATERIALIZED VIEW any_name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_MATVIEW;
					n->objname = $7;
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop FOREIGN TABLE any_name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_FOREIGN_TABLE;
					n->objname = $7;
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop FOREIGN DATA_P WRAPPER name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_FDW;
					n->objname = list_make1(makeString($8));
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop SERVER name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_FOREIGN_SERVER;
					n->objname = list_make1(makeString($6));
					$$ = (Node *)n;
				}
			| ALTER EXTENSION name add_drop TYPE_P any_name
				{
					AlterExtensionContentsStmt *n = makeNode(AlterExtensionContentsStmt);
					n->extname = $3;
					n->action = $4;
					n->objtype = OBJECT_TYPE;
					n->objname = $6;
					$$ = (Node *)n;
				}
		;

/*****************************************************************************
 *
 *		QUERY:
 *             CREATE FOREIGN DATA WRAPPER name options
 *
 *****************************************************************************/

CreateFdwStmt: CREATE FOREIGN DATA_P WRAPPER name opt_fdw_options create_generic_options
				{
					CreateFdwStmt *n = makeNode(CreateFdwStmt);
					n->fdwname = $5;
					n->func_options = $6;
					n->options = $7;
					$$ = (Node *) n;
				}
		;

fdw_option:
			HANDLER handler_name				{ $$ = makeDefElem("handler", (Node *)$2); }
			| NO HANDLER						{ $$ = makeDefElem("handler", NULL); }
			| VALIDATOR handler_name			{ $$ = makeDefElem("validator", (Node *)$2); }
			| NO VALIDATOR						{ $$ = makeDefElem("validator", NULL); }
		;

fdw_options:
			fdw_option							{ $$ = list_make1($1); }
			| fdw_options fdw_option			{ $$ = lappend($1, $2); }
		;

opt_fdw_options:
			fdw_options							{ $$ = $1; }
			| /*EMPTY*/							{ $$ = NIL; }
		;

/*****************************************************************************
 *
 *		QUERY :
 *				DROP FOREIGN DATA WRAPPER name
 *
 ****************************************************************************/

DropFdwStmt: DROP FOREIGN DATA_P WRAPPER name opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_FDW;
					n->objects = list_make1(list_make1(makeString($5)));
					n->arguments = NIL;
					n->missing_ok = false;
					n->behavior = $6;
					n->concurrent = false;
					$$ = (Node *) n;
				}
				|  DROP FOREIGN DATA_P WRAPPER IF_P EXISTS name opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_FDW;
					n->objects = list_make1(list_make1(makeString($7)));
					n->arguments = NIL;
					n->missing_ok = true;
					n->behavior = $8;
					n->concurrent = false;
					$$ = (Node *) n;
				}
		;

/*****************************************************************************
 *
 *		QUERY :
 *				ALTER FOREIGN DATA WRAPPER name options
 *
 ****************************************************************************/

AlterFdwStmt: ALTER FOREIGN DATA_P WRAPPER name opt_fdw_options alter_generic_options
				{
					AlterFdwStmt *n = makeNode(AlterFdwStmt);
					n->fdwname = $5;
					n->func_options = $6;
					n->options = $7;
					$$ = (Node *) n;
				}
			| ALTER FOREIGN DATA_P WRAPPER name fdw_options
				{
					AlterFdwStmt *n = makeNode(AlterFdwStmt);
					n->fdwname = $5;
					n->func_options = $6;
					n->options = NIL;
					$$ = (Node *) n;
				}
		;

/* Options definition for CREATE FDW, SERVER and USER MAPPING */
create_generic_options:
			OPTIONS '(' generic_option_list ')'			{ $$ = $3; }
			| /*EMPTY*/									{ $$ = NIL; }
		;

generic_option_list:
			generic_option_elem
				{
					$$ = list_make1($1);
				}
			| generic_option_list ',' generic_option_elem
				{
					$$ = lappend($1, $3);
				}
		;

/* Options definition for ALTER FDW, SERVER and USER MAPPING */
alter_generic_options:
			OPTIONS	'(' alter_generic_option_list ')'		{ $$ = $3; }
		;

alter_generic_option_list:
			alter_generic_option_elem
				{
					$$ = list_make1($1);
				}
			| alter_generic_option_list ',' alter_generic_option_elem
				{
					$$ = lappend($1, $3);
				}
		;

alter_generic_option_elem:
			generic_option_elem
				{
					$$ = $1;
				}
			| SET generic_option_elem
				{
					$$ = $2;
					$$->defaction = DEFELEM_SET;
				}
			| ADD_P generic_option_elem
				{
					$$ = $2;
					$$->defaction = DEFELEM_ADD;
				}
			| DROP generic_option_name
				{
					$$ = makeDefElemExtended(NULL, $2, NULL, DEFELEM_DROP);
				}
		;

generic_option_elem:
			generic_option_name generic_option_arg
				{
					$$ = makeDefElem($1, $2);
				}
		;

generic_option_name:
				ColLabel			{ $$ = $1; }
		;

/* We could use def_arg here, but the spec only requires string literals */
generic_option_arg:
				Sconst				{ $$ = (Node *) makeString($1); }
		;

/*****************************************************************************
 *
 *		QUERY:
 *             CREATE SERVER name [TYPE] [VERSION] [OPTIONS]
 *
 *****************************************************************************/

CreateForeignServerStmt: CREATE SERVER name opt_type opt_foreign_server_version
						 FOREIGN DATA_P WRAPPER name create_generic_options
				{
					CreateForeignServerStmt *n = makeNode(CreateForeignServerStmt);
					n->servername = $3;
					n->servertype = $4;
					n->version = $5;
					n->fdwname = $9;
					n->options = $10;
					$$ = (Node *) n;
				}
		;

opt_type:
			TYPE_P Sconst			{ $$ = $2; }
			| /*EMPTY*/				{ $$ = NULL; }
		;


foreign_server_version:
			VERSION_P Sconst		{ $$ = $2; }
		|	VERSION_P NULL_P		{ $$ = NULL; }
		;

opt_foreign_server_version:
			foreign_server_version	{ $$ = $1; }
			| /*EMPTY*/				{ $$ = NULL; }
		;

/*****************************************************************************
 *
 *		QUERY :
 *				DROP SERVER name
 *
 ****************************************************************************/

DropForeignServerStmt: DROP SERVER name opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_FOREIGN_SERVER;
					n->objects = list_make1(list_make1(makeString($3)));
					n->arguments = NIL;
					n->missing_ok = false;
					n->behavior = $4;
					n->concurrent = false;
					$$ = (Node *) n;
				}
				|  DROP SERVER IF_P EXISTS name opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_FOREIGN_SERVER;
					n->objects = list_make1(list_make1(makeString($5)));
					n->arguments = NIL;
					n->missing_ok = true;
					n->behavior = $6;
					n->concurrent = false;
					$$ = (Node *) n;
				}
		;

/*****************************************************************************
 *
 *		QUERY :
 *				ALTER SERVER name [VERSION] [OPTIONS]
 *
 ****************************************************************************/

AlterForeignServerStmt: ALTER SERVER name foreign_server_version alter_generic_options
				{
					AlterForeignServerStmt *n = makeNode(AlterForeignServerStmt);
					n->servername = $3;
					n->version = $4;
					n->options = $5;
					n->has_version = true;
					$$ = (Node *) n;
				}
			| ALTER SERVER name foreign_server_version
				{
					AlterForeignServerStmt *n = makeNode(AlterForeignServerStmt);
					n->servername = $3;
					n->version = $4;
					n->has_version = true;
					$$ = (Node *) n;
				}
			| ALTER SERVER name alter_generic_options
				{
					AlterForeignServerStmt *n = makeNode(AlterForeignServerStmt);
					n->servername = $3;
					n->options = $4;
					$$ = (Node *) n;
				}
		;

/*****************************************************************************
 *
 *		QUERY:
 *             CREATE FOREIGN TABLE relname (...) SERVER name (...)
 *
 *****************************************************************************/

CreateForeignTableStmt:
		CREATE FOREIGN TABLE qualified_name
			'(' OptTableElementList ')'
			SERVER name create_generic_options
				{
					CreateForeignTableStmt *n = makeNode(CreateForeignTableStmt);
					$4->relpersistence = RELPERSISTENCE_PERMANENT;
					n->base.relation = $4;
					n->base.tableElts = $6;
					n->base.inhRelations = NIL;
					n->base.if_not_exists = false;
					/* FDW-specific data */
					n->servername = $9;
					n->options = $10;
					$$ = (Node *) n;
				}
		| CREATE FOREIGN TABLE IF_P NOT EXISTS qualified_name
			'(' OptTableElementList ')'
			SERVER name create_generic_options
				{
					CreateForeignTableStmt *n = makeNode(CreateForeignTableStmt);
					$7->relpersistence = RELPERSISTENCE_PERMANENT;
					n->base.relation = $7;
					n->base.tableElts = $9;
					n->base.inhRelations = NIL;
					n->base.if_not_exists = true;
					/* FDW-specific data */
					n->servername = $12;
					n->options = $13;
					$$ = (Node *) n;
				}
		;

/*****************************************************************************
 *
 *		QUERY:
 *             ALTER FOREIGN TABLE relname [...]
 *
 *****************************************************************************/

AlterForeignTableStmt:
			ALTER FOREIGN TABLE relation_expr alter_table_cmds
				{
					AlterTableStmt *n = makeNode(AlterTableStmt);
					n->relation = $4;
					n->cmds = $5;
					n->relkind = OBJECT_FOREIGN_TABLE;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER FOREIGN TABLE IF_P EXISTS relation_expr alter_table_cmds
				{
					AlterTableStmt *n = makeNode(AlterTableStmt);
					n->relation = $6;
					n->cmds = $7;
					n->relkind = OBJECT_FOREIGN_TABLE;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
		;

/*****************************************************************************
 *
 *		QUERY:
 *             CREATE USER MAPPING FOR auth_ident SERVER name [OPTIONS]
 *
 *****************************************************************************/

CreateUserMappingStmt: CREATE USER MAPPING FOR auth_ident SERVER name create_generic_options
				{
					CreateUserMappingStmt *n = makeNode(CreateUserMappingStmt);
					n->username = $5;
					n->servername = $7;
					n->options = $8;
					$$ = (Node *) n;
				}
		;

/* User mapping authorization identifier */
auth_ident:
			CURRENT_USER	{ $$ = "current_user"; }
		|	USER			{ $$ = "current_user"; }
		|	RoleId			{ $$ = (strcmp($1, "public") == 0) ? NULL : $1; }
		;

/*****************************************************************************
 *
 *		QUERY :
 *				DROP USER MAPPING FOR auth_ident SERVER name
 *
 ****************************************************************************/

DropUserMappingStmt: DROP USER MAPPING FOR auth_ident SERVER name
				{
					DropUserMappingStmt *n = makeNode(DropUserMappingStmt);
					n->username = $5;
					n->servername = $7;
					n->missing_ok = false;
					$$ = (Node *) n;
				}
				|  DROP USER MAPPING IF_P EXISTS FOR auth_ident SERVER name
				{
					DropUserMappingStmt *n = makeNode(DropUserMappingStmt);
					n->username = $7;
					n->servername = $9;
					n->missing_ok = true;
					$$ = (Node *) n;
				}
		;

/*****************************************************************************
 *
 *		QUERY :
 *				ALTER USER MAPPING FOR auth_ident SERVER name OPTIONS
 *
 ****************************************************************************/

AlterUserMappingStmt: ALTER USER MAPPING FOR auth_ident SERVER name alter_generic_options
				{
					AlterUserMappingStmt *n = makeNode(AlterUserMappingStmt);
					n->username = $5;
					n->servername = $7;
					n->options = $8;
					$$ = (Node *) n;
				}
		;

/*****************************************************************************
 *
 *		QUERIES :
 *				CREATE TRIGGER ...
 *				DROP TRIGGER ...
 *
 *****************************************************************************/

CreateTrigStmt:
			CREATE TRIGGER name TriggerActionTime TriggerEvents ON
			qualified_name TriggerForSpec TriggerWhen
			EXECUTE PROCEDURE func_name '(' TriggerFuncArgs ')'
				{
					CreateTrigStmt *n = makeNode(CreateTrigStmt);
					n->trigname = $3;
					n->relation = $7;
					n->funcname = $12;
					n->args = $14;
					n->row = $8;
					n->timing = $4;
					n->events = intVal(linitial($5));
					n->columns = (List *) lsecond($5);
					n->whenClause = $9;
					n->isconstraint  = FALSE;
					n->deferrable	 = FALSE;
					n->initdeferred  = FALSE;
					n->constrrel = NULL;
					$$ = (Node *)n;
				}
			| CREATE CONSTRAINT TRIGGER name AFTER TriggerEvents ON
			qualified_name OptConstrFromTable ConstraintAttributeSpec
			FOR EACH ROW TriggerWhen
			EXECUTE PROCEDURE func_name '(' TriggerFuncArgs ')'
				{
					CreateTrigStmt *n = makeNode(CreateTrigStmt);
					n->trigname = $4;
					n->relation = $8;
					n->funcname = $17;
					n->args = $19;
					n->row = TRUE;
					n->timing = TRIGGER_TYPE_AFTER;
					n->events = intVal(linitial($6));
					n->columns = (List *) lsecond($6);
					n->whenClause = $14;
					n->isconstraint  = TRUE;
					processCASbits($10, @10, "TRIGGER",
								   &n->deferrable, &n->initdeferred, NULL,
								   NULL, yyscanner);
					n->constrrel = $9;
					$$ = (Node *)n;
				}
		;

TriggerActionTime:
			BEFORE								{ $$ = TRIGGER_TYPE_BEFORE; }
			| AFTER								{ $$ = TRIGGER_TYPE_AFTER; }
			| INSTEAD OF						{ $$ = TRIGGER_TYPE_INSTEAD; }
		;

TriggerEvents:
			TriggerOneEvent
				{ $$ = $1; }
			| TriggerEvents OR TriggerOneEvent
				{
					int		events1 = intVal(linitial($1));
					int		events2 = intVal(linitial($3));
					List   *columns1 = (List *) lsecond($1);
					List   *columns2 = (List *) lsecond($3);

					if (events1 & events2)
						parser_yyerror("duplicate trigger events specified");
					/*
					 * concat'ing the columns lists loses information about
					 * which columns went with which event, but so long as
					 * only UPDATE carries columns and we disallow multiple
					 * UPDATE items, it doesn't matter.  Command execution
					 * should just ignore the columns for non-UPDATE events.
					 */
					$$ = list_make2(makeInteger(events1 | events2),
									list_concat(columns1, columns2));
				}
		;

TriggerOneEvent:
			INSERT
				{ $$ = list_make2(makeInteger(TRIGGER_TYPE_INSERT), NIL); }
			| DELETE_P
				{ $$ = list_make2(makeInteger(TRIGGER_TYPE_DELETE), NIL); }
			| UPDATE
				{ $$ = list_make2(makeInteger(TRIGGER_TYPE_UPDATE), NIL); }
			| UPDATE OF columnList
				{ $$ = list_make2(makeInteger(TRIGGER_TYPE_UPDATE), $3); }
			| TRUNCATE
				{ $$ = list_make2(makeInteger(TRIGGER_TYPE_TRUNCATE), NIL); }
		;

TriggerForSpec:
			FOR TriggerForOptEach TriggerForType
				{
					$$ = $3;
				}
			| /* EMPTY */
				{
					/*
					 * If ROW/STATEMENT not specified, default to
					 * STATEMENT, per SQL
					 */
					$$ = FALSE;
				}
		;

TriggerForOptEach:
			EACH									{}
			| /*EMPTY*/								{}
		;

TriggerForType:
			ROW										{ $$ = TRUE; }
			| STATEMENT								{ $$ = FALSE; }
		;

TriggerWhen:
			WHEN '(' a_expr ')'						{ $$ = $3; }
			| /*EMPTY*/								{ $$ = NULL; }
		;

TriggerFuncArgs:
			TriggerFuncArg							{ $$ = list_make1($1); }
			| TriggerFuncArgs ',' TriggerFuncArg	{ $$ = lappend($1, $3); }
			| /*EMPTY*/								{ $$ = NIL; }
		;

TriggerFuncArg:
			Iconst
				{
					char buf[64];
					snprintf(buf, sizeof(buf), "%d", $1);
					$$ = makeString(pstrdup(buf));
				}
			| FCONST								{ $$ = makeString($1); }
			| Sconst								{ $$ = makeString($1); }
			| ColLabel								{ $$ = makeString($1); }
		;

OptConstrFromTable:
			FROM qualified_name						{ $$ = $2; }
			| /*EMPTY*/								{ $$ = NULL; }
		;

ConstraintAttributeSpec:
			/*EMPTY*/
				{ $$ = 0; }
			| ConstraintAttributeSpec ConstraintAttributeElem
				{
					/*
					 * We must complain about conflicting options.
					 * We could, but choose not to, complain about redundant
					 * options (ie, where $2's bit is already set in $1).
					 */
					int		newspec = $1 | $2;

					/* special message for this case */
					if ((newspec & (CAS_NOT_DEFERRABLE | CAS_INITIALLY_DEFERRED)) == (CAS_NOT_DEFERRABLE | CAS_INITIALLY_DEFERRED))
						ereport(ERROR,
								(errcode(ERRCODE_SYNTAX_ERROR),
								 errmsg("constraint declared INITIALLY DEFERRED must be DEFERRABLE"),
								 parser_errposition(@2)));
					/* generic message for other conflicts */
					if ((newspec & (CAS_NOT_DEFERRABLE | CAS_DEFERRABLE)) == (CAS_NOT_DEFERRABLE | CAS_DEFERRABLE) ||
						(newspec & (CAS_INITIALLY_IMMEDIATE | CAS_INITIALLY_DEFERRED)) == (CAS_INITIALLY_IMMEDIATE | CAS_INITIALLY_DEFERRED))
						ereport(ERROR,
								(errcode(ERRCODE_SYNTAX_ERROR),
								 errmsg("conflicting constraint properties"),
								 parser_errposition(@2)));
					$$ = newspec;
				}
		;

ConstraintAttributeElem:
			NOT DEFERRABLE					{ $$ = CAS_NOT_DEFERRABLE; }
			| DEFERRABLE					{ $$ = CAS_DEFERRABLE; }
			| INITIALLY IMMEDIATE			{ $$ = CAS_INITIALLY_IMMEDIATE; }
			| INITIALLY DEFERRED			{ $$ = CAS_INITIALLY_DEFERRED; }
			| NOT VALID						{ $$ = CAS_NOT_VALID; }
			| NO INHERIT					{ $$ = CAS_NO_INHERIT; }
		;


DropTrigStmt:
			DROP TRIGGER name ON any_name opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_TRIGGER;
					n->objects = list_make1(lappend($5, makeString($3)));
					n->arguments = NIL;
					n->behavior = $6;
					n->missing_ok = false;
					n->concurrent = false;
					$$ = (Node *) n;
				}
			| DROP TRIGGER IF_P EXISTS name ON any_name opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_TRIGGER;
					n->objects = list_make1(lappend($7, makeString($5)));
					n->arguments = NIL;
					n->behavior = $8;
					n->missing_ok = true;
					n->concurrent = false;
					$$ = (Node *) n;
				}
		;


/*****************************************************************************
 *
 *		QUERIES :
 *				CREATE EVENT TRIGGER ...
 *				ALTER EVENT TRIGGER ...
 *
 *****************************************************************************/

CreateEventTrigStmt:
			CREATE EVENT TRIGGER name ON ColLabel
			EXECUTE PROCEDURE func_name '(' ')'
				{
					CreateEventTrigStmt *n = makeNode(CreateEventTrigStmt);
					n->trigname = $4;
					n->eventname = $6;
					n->whenclause = NULL;
					n->funcname = $9;
					$$ = (Node *)n;
				}
		  | CREATE EVENT TRIGGER name ON ColLabel
			WHEN event_trigger_when_list
			EXECUTE PROCEDURE func_name '(' ')'
				{
					CreateEventTrigStmt *n = makeNode(CreateEventTrigStmt);
					n->trigname = $4;
					n->eventname = $6;
					n->whenclause = $8;
					n->funcname = $11;
					$$ = (Node *)n;
				}
		;

event_trigger_when_list:
		  event_trigger_when_item
			{ $$ = list_make1($1); }
		| event_trigger_when_list AND event_trigger_when_item
			{ $$ = lappend($1, $3); }
		;

event_trigger_when_item:
		ColId IN_P '(' event_trigger_value_list ')'
			{ $$ = makeDefElem($1, (Node *) $4); }
		;

event_trigger_value_list:
		  SCONST
			{ $$ = list_make1(makeString($1)); }
		| event_trigger_value_list ',' SCONST
			{ $$ = lappend($1, makeString($3)); }
		;

AlterEventTrigStmt:
			ALTER EVENT TRIGGER name enable_trigger
				{
					AlterEventTrigStmt *n = makeNode(AlterEventTrigStmt);
					n->trigname = $4;
					n->tgenabled = $5;
					$$ = (Node *) n;
				}
		;

enable_trigger:
			ENABLE_P					{ $$ = TRIGGER_FIRES_ON_ORIGIN; }
			| ENABLE_P REPLICA			{ $$ = TRIGGER_FIRES_ON_REPLICA; }
			| ENABLE_P ALWAYS			{ $$ = TRIGGER_FIRES_ALWAYS; }
			| DISABLE_P					{ $$ = TRIGGER_DISABLED; }
		;

/*****************************************************************************
 *
 *		QUERIES :
 *				CREATE ASSERTION ...
 *				DROP ASSERTION ...
 *
 *****************************************************************************/

CreateAssertStmt:
			CREATE ASSERTION name CHECK '(' a_expr ')'
			ConstraintAttributeSpec
				{
					CreateTrigStmt *n = makeNode(CreateTrigStmt);
					n->trigname = $3;
					n->args = list_make1($6);
					n->isconstraint  = TRUE;
					processCASbits($8, @8, "ASSERTION",
								   &n->deferrable, &n->initdeferred, NULL,
								   NULL, yyscanner);

					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("CREATE ASSERTION is not yet implemented")));

					$$ = (Node *)n;
				}
		;

DropAssertStmt:
			DROP ASSERTION name opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->objects = NIL;
					n->arguments = NIL;
					n->behavior = $4;
					n->removeType = OBJECT_TRIGGER; /* XXX */
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("DROP ASSERTION is not yet implemented")));
					$$ = (Node *) n;
				}
		;


/*****************************************************************************
 *
 *		QUERY :
 *				define (aggregate,operator,type)
 *
 *****************************************************************************/

DefineStmt:
			CREATE opt_ordered AGGREGATE func_name aggr_args definition
				{
					DefineStmt *n = makeNode(DefineStmt);
					n->kind = OBJECT_AGGREGATE;
					n->oldstyle = false;
					n->defnames = $4;
					n->args = $5;
					n->definition = $6;
					$$ = (Node *)n;
				}
			| CREATE opt_ordered AGGREGATE func_name old_aggr_definition
				{
					/* old-style (pre-8.2) syntax for CREATE AGGREGATE */
					DefineStmt *n = makeNode(DefineStmt);
					n->kind = OBJECT_AGGREGATE;
					n->oldstyle = true;
					n->defnames = $4;
					n->args = NIL;
					n->definition = $5;
					$$ = (Node *)n;
				}
			| CREATE OPERATOR any_operator definition
				{
					DefineStmt *n = makeNode(DefineStmt);
					n->kind = OBJECT_OPERATOR;
					n->oldstyle = false;
					n->defnames = $3;
					n->args = NIL;
					n->definition = $4;
					$$ = (Node *)n;
				}
			| CREATE TYPE_P any_name definition
				{
					DefineStmt *n = makeNode(DefineStmt);
					n->kind = OBJECT_TYPE;
					n->oldstyle = false;
					n->defnames = $3;
					n->args = NIL;
					n->definition = $4;
					$$ = (Node *)n;
				}
			| CREATE TYPE_P any_name
				{
					/* Shell type (identified by lack of definition) */
					DefineStmt *n = makeNode(DefineStmt);
					n->kind = OBJECT_TYPE;
					n->oldstyle = false;
					n->defnames = $3;
					n->args = NIL;
					n->definition = NIL;
					$$ = (Node *)n;
				}
			| CREATE TYPE_P any_name AS '(' OptTableFuncElementList ')'
				{
					CompositeTypeStmt *n = makeNode(CompositeTypeStmt);

					/* can't use qualified_name, sigh */
					n->typevar = makeRangeVarFromAnyName($3, @3, yyscanner);
					n->coldeflist = $6;
					$$ = (Node *)n;
				}
			| CREATE opt_or_replace opt_trusted PROTOCOL name definition
				{
					/*
					 * The opt_or_replace is here just to avoid a grammar conflict.
					 * It's not actually supported.
					 */
					if ($2)
						ereport(ERROR,
								(errcode(ERRCODE_SYNTAX_ERROR),
								 errmsg("syntax error"),
								 parser_errposition(@2)));

					DefineStmt *n = makeNode(DefineStmt);
					n->kind = OBJECT_EXTPROTOCOL;
					n->oldstyle = false;
					n->trusted = $3;
					n->defnames = list_make1(makeString($5));
					n->args = NIL;
					n->definition = $6;
					$$ = (Node *)n;
				}
			| CREATE TYPE_P any_name AS ENUM_P '(' opt_enum_val_list ')'
				{
					CreateEnumStmt *n = makeNode(CreateEnumStmt);
					n->typeName = $3;
					n->vals = $7;
					$$ = (Node *)n;
				}
			| CREATE TYPE_P any_name AS RANGE definition
				{
					CreateRangeStmt *n = makeNode(CreateRangeStmt);
					n->typeName = $3;
					n->params	= $6;
					$$ = (Node *)n;
				}
			| CREATE TEXT_P SEARCH PARSER any_name definition
				{
					DefineStmt *n = makeNode(DefineStmt);
					n->kind = OBJECT_TSPARSER;
					n->args = NIL;
					n->defnames = $5;
					n->definition = $6;
					$$ = (Node *)n;
				}
			| CREATE TEXT_P SEARCH DICTIONARY any_name definition
				{
					DefineStmt *n = makeNode(DefineStmt);
					n->kind = OBJECT_TSDICTIONARY;
					n->args = NIL;
					n->defnames = $5;
					n->definition = $6;
					$$ = (Node *)n;
				}
			| CREATE TEXT_P SEARCH TEMPLATE any_name definition
				{
					DefineStmt *n = makeNode(DefineStmt);
					n->kind = OBJECT_TSTEMPLATE;
					n->args = NIL;
					n->defnames = $5;
					n->definition = $6;
					$$ = (Node *)n;
				}
			| CREATE TEXT_P SEARCH CONFIGURATION any_name definition
				{
					DefineStmt *n = makeNode(DefineStmt);
					n->kind = OBJECT_TSCONFIGURATION;
					n->args = NIL;
					n->defnames = $5;
					n->definition = $6;
					$$ = (Node *)n;
				}
			| CREATE COLLATION any_name definition
				{
					DefineStmt *n = makeNode(DefineStmt);
					n->kind = OBJECT_COLLATION;
					n->args = NIL;
					n->defnames = $3;
					n->definition = $4;
					$$ = (Node *)n;
				}
			| CREATE COLLATION any_name FROM any_name
				{
					DefineStmt *n = makeNode(DefineStmt);
					n->kind = OBJECT_COLLATION;
					n->args = NIL;
					n->defnames = $3;
					n->definition = list_make1(makeDefElem("from", (Node *) $5));
					$$ = (Node *)n;
				}
		;

opt_ordered:	ORDERED	{ $$ = TRUE; }
			| /*EMPTY*/	{ $$ = FALSE; }
		;

definition: '(' def_list ')'						{ $$ = $2; }
		;

def_list:	def_elem								{ $$ = list_make1($1); }
			| def_list ',' def_elem					{ $$ = lappend($1, $3); }
		;

def_elem:	ColLabel '=' def_arg
				{
					/*
					 * appendoptimized is an alias for appendonly in order to
					 * provide a reloption syntax which better reflects the
					 * featureset of AO tables. It is implemented as a very
					 * thin alias, the reloptions and messaging will still
					 * say appendonly.
					 */
					if (strcmp($1, "appendoptimized") == 0)
						$$ = makeDefElem("appendonly", (Node *) $3);
					else
						$$ = makeDefElem($1, (Node *) $3);
				}
			| ColLabel
				{
					$$ = makeDefElem($1, NULL);
				}
		;

/* Note: any simple identifier will be returned as a type name! */
def_arg:	func_type						{ $$ = (Node *)$1; }
			/* MPP-6685: allow unquoted ROW keyword as "orientation" option */
			| ROW							{ $$ = (Node *)makeString(pstrdup("row")); }
			| reserved_keyword				{ $$ = (Node *)makeString(pstrdup($1)); }
			| qual_all_Op					{ $$ = (Node *)$1; }
			| NumericOnly					{ $$ = (Node *)$1; }
			| Sconst						{ $$ = (Node *)makeString($1); }

			/* 
			 * For compresstype=none in ENCODING clauses. Allows us to avoid
			 * promoting that to a reserved word or adding the column reserved
			 * list here which could get tricky.
			 */
			| NONE							{ $$ = (Node *)makeString(pstrdup("none")); }
		;

old_aggr_definition: '(' old_aggr_list ')'			{ $$ = $2; }
		;

old_aggr_list: old_aggr_elem						{ $$ = list_make1($1); }
			| old_aggr_list ',' old_aggr_elem		{ $$ = lappend($1, $3); }
		;

/*
 * Must use IDENT here to avoid reduce/reduce conflicts; fortunately none of
 * the item names needed in old aggregate definitions are likely to become
 * SQL keywords.
 */
old_aggr_elem:  IDENT '=' def_arg
				{
					$$ = makeDefElem($1, (Node *)$3);
				}
		;

opt_enum_val_list:
		enum_val_list							{ $$ = $1; }
		| /*EMPTY*/								{ $$ = NIL; }
		;

enum_val_list:	Sconst
				{ $$ = list_make1(makeString($1)); }
			| enum_val_list ',' Sconst
				{ $$ = lappend($1, makeString($3)); }
		;

/*****************************************************************************
 *
 *	ALTER TYPE enumtype ADD ...
 *
 *****************************************************************************/

AlterEnumStmt:
		ALTER TYPE_P any_name ADD_P VALUE_P opt_if_not_exists Sconst
			{
				AlterEnumStmt *n = makeNode(AlterEnumStmt);
				n->typeName = $3;
				n->newVal = $7;
				n->newValNeighbor = NULL;
				n->newValIsAfter = true;
				n->skipIfExists = $6;
				$$ = (Node *) n;
			}
		 | ALTER TYPE_P any_name ADD_P VALUE_P opt_if_not_exists Sconst BEFORE Sconst
			{
				AlterEnumStmt *n = makeNode(AlterEnumStmt);
				n->typeName = $3;
				n->newVal = $7;
				n->newValNeighbor = $9;
				n->newValIsAfter = false;
				n->skipIfExists = $6;
				$$ = (Node *) n;
			}
		 | ALTER TYPE_P any_name ADD_P VALUE_P opt_if_not_exists Sconst AFTER Sconst
			{
				AlterEnumStmt *n = makeNode(AlterEnumStmt);
				n->typeName = $3;
				n->newVal = $7;
				n->newValNeighbor = $9;
				n->newValIsAfter = true;
				n->skipIfExists = $6;
				$$ = (Node *) n;
			}
		 ;

opt_if_not_exists: IF_P NOT EXISTS              { $$ = true; }
		| /* empty */                          { $$ = false; }
		;


/*****************************************************************************
 *
 *		QUERIES :
 *				CREATE OPERATOR CLASS ...
 *				CREATE OPERATOR FAMILY ...
 *				ALTER OPERATOR FAMILY ...
 *				DROP OPERATOR CLASS ...
 *				DROP OPERATOR FAMILY ...
 *
 *****************************************************************************/

CreateOpClassStmt:
			CREATE OPERATOR CLASS any_name opt_default FOR TYPE_P Typename
			USING access_method opt_opfamily AS opclass_item_list
				{
					CreateOpClassStmt *n = makeNode(CreateOpClassStmt);
					n->opclassname = $4;
					n->isDefault = $5;
					n->datatype = $8;
					n->amname = $10;
					n->opfamilyname = $11;
					n->items = $13;
					$$ = (Node *) n;
				}
		;

opclass_item_list:
			opclass_item							{ $$ = list_make1($1); }
			| opclass_item_list ',' opclass_item	{ $$ = lappend($1, $3); }
		;

opclass_item:
			OPERATOR Iconst any_operator opclass_purpose opt_recheck
				{
					CreateOpClassItem *n = makeNode(CreateOpClassItem);
					n->itemtype = OPCLASS_ITEM_OPERATOR;
					n->name = $3;
					n->args = NIL;
					n->number = $2;
					n->order_family = $4;
					$$ = (Node *) n;
				}
			| OPERATOR Iconst any_operator oper_argtypes opclass_purpose
			  opt_recheck
				{
					CreateOpClassItem *n = makeNode(CreateOpClassItem);
					n->itemtype = OPCLASS_ITEM_OPERATOR;
					n->name = $3;
					n->args = $4;
					n->number = $2;
					n->order_family = $5;
					$$ = (Node *) n;
				}
			| FUNCTION Iconst func_name func_args
				{
					CreateOpClassItem *n = makeNode(CreateOpClassItem);
					n->itemtype = OPCLASS_ITEM_FUNCTION;
					n->name = $3;
					n->args = extractArgTypes($4);
					n->number = $2;
					$$ = (Node *) n;
				}
			| FUNCTION Iconst '(' type_list ')' func_name func_args
				{
					CreateOpClassItem *n = makeNode(CreateOpClassItem);
					n->itemtype = OPCLASS_ITEM_FUNCTION;
					n->name = $6;
					n->args = extractArgTypes($7);
					n->number = $2;
					n->class_args = $4;
					$$ = (Node *) n;
				}
			| STORAGE Typename
				{
					CreateOpClassItem *n = makeNode(CreateOpClassItem);
					n->itemtype = OPCLASS_ITEM_STORAGETYPE;
					n->storedtype = $2;
					$$ = (Node *) n;
				}
		;

opt_default:	DEFAULT						{ $$ = TRUE; }
			| /*EMPTY*/						{ $$ = FALSE; }
		;

opt_opfamily:	FAMILY any_name				{ $$ = $2; }
			| /*EMPTY*/						{ $$ = NIL; }
		;

opclass_purpose: FOR SEARCH					{ $$ = NIL; }
			| FOR ORDER BY any_name			{ $$ = $4; }
			| /*EMPTY*/						{ $$ = NIL; }
		;

opt_recheck:	RECHECK
				{
					/*
					 * RECHECK no longer does anything in opclass definitions,
					 * but we still accept it to ease porting of old database
					 * dumps.
					 */
					ereport(NOTICE,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("RECHECK is no longer required"),
							 errhint("Update your data type."),
							 parser_errposition(@1)));
					$$ = TRUE;
				}
			| /*EMPTY*/						{ $$ = FALSE; }
		;


CreateOpFamilyStmt:
			CREATE OPERATOR FAMILY any_name USING access_method
				{
					CreateOpFamilyStmt *n = makeNode(CreateOpFamilyStmt);
					n->opfamilyname = $4;
					n->amname = $6;
					$$ = (Node *) n;
				}
		;

AlterOpFamilyStmt:
			ALTER OPERATOR FAMILY any_name USING access_method ADD_P opclass_item_list
				{
					AlterOpFamilyStmt *n = makeNode(AlterOpFamilyStmt);
					n->opfamilyname = $4;
					n->amname = $6;
					n->isDrop = false;
					n->items = $8;
					$$ = (Node *) n;
				}
			| ALTER OPERATOR FAMILY any_name USING access_method DROP opclass_drop_list
				{
					AlterOpFamilyStmt *n = makeNode(AlterOpFamilyStmt);
					n->opfamilyname = $4;
					n->amname = $6;
					n->isDrop = true;
					n->items = $8;
					$$ = (Node *) n;
				}
		;

opclass_drop_list:
			opclass_drop							{ $$ = list_make1($1); }
			| opclass_drop_list ',' opclass_drop	{ $$ = lappend($1, $3); }
		;

opclass_drop:
			OPERATOR Iconst '(' type_list ')'
				{
					CreateOpClassItem *n = makeNode(CreateOpClassItem);
					n->itemtype = OPCLASS_ITEM_OPERATOR;
					n->number = $2;
					n->args = $4;
					$$ = (Node *) n;
				}
			| FUNCTION Iconst '(' type_list ')'
				{
					CreateOpClassItem *n = makeNode(CreateOpClassItem);
					n->itemtype = OPCLASS_ITEM_FUNCTION;
					n->number = $2;
					n->args = $4;
					$$ = (Node *) n;
				}
		;


DropOpClassStmt:
			DROP OPERATOR CLASS any_name USING access_method opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->objects = list_make1($4);
					n->arguments = list_make1(list_make1(makeString($6)));
					n->removeType = OBJECT_OPCLASS;
					n->behavior = $7;
					n->missing_ok = false;
					n->concurrent = false;
					$$ = (Node *) n;
				}
			| DROP OPERATOR CLASS IF_P EXISTS any_name USING access_method opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->objects = list_make1($6);
					n->arguments = list_make1(list_make1(makeString($8)));
					n->removeType = OBJECT_OPCLASS;
					n->behavior = $9;
					n->missing_ok = true;
					n->concurrent = false;
					$$ = (Node *) n;
				}
		;

DropOpFamilyStmt:
			DROP OPERATOR FAMILY any_name USING access_method opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->objects = list_make1($4);
					n->arguments = list_make1(list_make1(makeString($6)));
					n->removeType = OBJECT_OPFAMILY;
					n->behavior = $7;
					n->missing_ok = false;
					n->concurrent = false;
					$$ = (Node *) n;
				}
			| DROP OPERATOR FAMILY IF_P EXISTS any_name USING access_method opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->objects = list_make1($6);
					n->arguments = list_make1(list_make1(makeString($8)));
					n->removeType = OBJECT_OPFAMILY;
					n->behavior = $9;
					n->missing_ok = true;
					n->concurrent = false;
					$$ = (Node *) n;
				}
		;


/*****************************************************************************
 *
 *		QUERY:
 *
 *		DROP OWNED BY username [, username ...] [ RESTRICT | CASCADE ]
 *		REASSIGN OWNED BY username [, username ...] TO username
 *
 *****************************************************************************/
DropOwnedStmt:
			DROP OWNED BY role_list opt_drop_behavior
				{
					DropOwnedStmt *n = makeNode(DropOwnedStmt);
					n->roles = $4;
					n->behavior = $5;
					$$ = (Node *)n;
				}
		;

ReassignOwnedStmt:
			REASSIGN OWNED BY role_list TO name
				{
					ReassignOwnedStmt *n = makeNode(ReassignOwnedStmt);
					n->roles = $4;
					n->newrole = $6;
					$$ = (Node *)n;
				}
		;

/*****************************************************************************
 *
 *		QUERY:
 *
 *		DROP itemtype [ IF EXISTS ] itemname [, itemname ...]
 *           [ RESTRICT | CASCADE ]
 *
 *****************************************************************************/

DropStmt:	DROP drop_type IF_P EXISTS any_name_list opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = $2;
					n->missing_ok = TRUE;
					n->objects = $5;
					n->arguments = NIL;
					n->behavior = $6;
					n->concurrent = false;
					$$ = (Node *)n;
				}
			| DROP drop_type any_name_list opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = $2;
					n->missing_ok = FALSE;
					n->objects = $3;
					n->arguments = NIL;
					n->behavior = $4;
					n->concurrent = false;
					$$ = (Node *)n;
				}
			| DROP INDEX CONCURRENTLY any_name_list opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_INDEX;
					n->missing_ok = FALSE;
					n->objects = $4;
					n->arguments = NIL;
					n->behavior = $5;
					n->concurrent = true;
					$$ = (Node *)n;
				}
			| DROP INDEX CONCURRENTLY IF_P EXISTS any_name_list opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_INDEX;
					n->missing_ok = TRUE;
					n->objects = $6;
					n->arguments = NIL;
					n->behavior = $7;
					n->concurrent = true;
					$$ = (Node *)n;
				}
		;


drop_type:	TABLE									{ $$ = OBJECT_TABLE; }
			| EXTERNAL TABLE						{ $$ = OBJECT_EXTTABLE; }
			| EXTERNAL WEB TABLE					{ $$ = OBJECT_EXTTABLE; }	
			| SEQUENCE								{ $$ = OBJECT_SEQUENCE; }
			| VIEW									{ $$ = OBJECT_VIEW; }
			| MATERIALIZED VIEW						{ $$ = OBJECT_MATVIEW; }
			| INDEX									{ $$ = OBJECT_INDEX; }
			| FOREIGN TABLE							{ $$ = OBJECT_FOREIGN_TABLE; }
			| EVENT TRIGGER 						{ $$ = OBJECT_EVENT_TRIGGER; }
			| TYPE_P								{ $$ = OBJECT_TYPE; }
			| DOMAIN_P								{ $$ = OBJECT_DOMAIN; }
			| COLLATION								{ $$ = OBJECT_COLLATION; }
			| CONVERSION_P							{ $$ = OBJECT_CONVERSION; }
			| SCHEMA								{ $$ = OBJECT_SCHEMA; }
			| EXTENSION								{ $$ = OBJECT_EXTENSION; }
			| TEXT_P SEARCH PARSER					{ $$ = OBJECT_TSPARSER; }
			| TEXT_P SEARCH DICTIONARY				{ $$ = OBJECT_TSDICTIONARY; }
			| TEXT_P SEARCH TEMPLATE				{ $$ = OBJECT_TSTEMPLATE; }
			| TEXT_P SEARCH CONFIGURATION			{ $$ = OBJECT_TSCONFIGURATION; }
			| PROTOCOL								{ $$ = OBJECT_EXTPROTOCOL; }
		;

any_name_list:
			any_name								{ $$ = list_make1($1); }
			| any_name_list ',' any_name			{ $$ = lappend($1, $3); }
		;

any_name:	ColId						{ $$ = list_make1(makeString($1)); }
			| ColId attrs				{ $$ = lcons(makeString($1), $2); }
		;

attrs:		'.' attr_name
					{ $$ = list_make1(makeString($2)); }
			| attrs '.' attr_name
					{ $$ = lappend($1, makeString($3)); }
		;


/*****************************************************************************
 *
 *		QUERY:
 *				truncate table relname1, relname2, ...
 *
 *****************************************************************************/

TruncateStmt:
			TRUNCATE opt_table relation_expr_list opt_restart_seqs opt_drop_behavior
				{
					TruncateStmt *n = makeNode(TruncateStmt);
					n->relations = $3;
					n->restart_seqs = $4;
					n->behavior = $5;
					$$ = (Node *)n;
				}
		;

opt_restart_seqs:
			CONTINUE_P IDENTITY_P		{ $$ = false; }
			| RESTART IDENTITY_P		{ $$ = true; }
			| /* EMPTY */				{ $$ = false; }
		;

/*****************************************************************************
 *
 *	The COMMENT ON statement can take different forms based upon the type of
 *	the object associated with the comment. The form of the statement is:
 *
 *	COMMENT ON [ [ CONVERSION | COLLATION | DATABASE | DOMAIN |
 *                 EXTENSION | EVENT TRIGGER | FOREIGN DATA WRAPPER |
 *                 FOREIGN TABLE | INDEX | [PROCEDURAL] LANGUAGE |
 *                 MATERIALIZED VIEW | ROLE | SCHEMA | SEQUENCE |
 *                 SERVER | TABLE | TABLESPACE |
 *                 TEXT SEARCH CONFIGURATION | TEXT SEARCH DICTIONARY |
 *                 TEXT SEARCH PARSER | TEXT SEARCH TEMPLATE | TYPE |
 *                 VIEW] <objname> |
 *				 AGGREGATE <aggname> (arg1, ...) |
 *				 CAST (<src type> AS <dst type>) |
 *				 COLUMN <relname>.<colname> |
 *				 CONSTRAINT <constraintname> ON <relname> |
 *				 FUNCTION <funcname> (arg1, arg2, ...) |
 *				 LARGE OBJECT <oid> |
 *				 OPERATOR <op> (leftoperand_typ, rightoperand_typ) |
 *				 OPERATOR CLASS <name> USING <access-method> |
 *				 OPERATOR FAMILY <name> USING <access-method> |
 *				 RULE <rulename> ON <relname> |
 *				 TRIGGER <triggername> ON <relname> ]
 *			   IS 'text'
 *
 *****************************************************************************/

CommentStmt:
			COMMENT ON comment_type any_name IS comment_text
				{
					CommentStmt *n = makeNode(CommentStmt);
					n->objtype = $3;
					n->objname = $4;
					n->objargs = NIL;
					n->comment = $6;
					$$ = (Node *) n;
				}
			| COMMENT ON AGGREGATE func_name aggr_args IS comment_text
				{
					CommentStmt *n = makeNode(CommentStmt);
					n->objtype = OBJECT_AGGREGATE;
					n->objname = $4;
					n->objargs = extractAggrArgTypes($5);
					n->comment = $7;
					$$ = (Node *) n;
				}
			| COMMENT ON FUNCTION func_name func_args IS comment_text
				{
					CommentStmt *n = makeNode(CommentStmt);
					n->objtype = OBJECT_FUNCTION;
					n->objname = $4;
					n->objargs = extractArgTypes($5);
					n->comment = $7;
					$$ = (Node *) n;
				}
			| COMMENT ON OPERATOR any_operator oper_argtypes IS comment_text
				{
					CommentStmt *n = makeNode(CommentStmt);
					n->objtype = OBJECT_OPERATOR;
					n->objname = $4;
					n->objargs = $5;
					n->comment = $7;
					$$ = (Node *) n;
				}
			| COMMENT ON CONSTRAINT name ON any_name IS comment_text
				{
					CommentStmt *n = makeNode(CommentStmt);
					n->objtype = OBJECT_CONSTRAINT;
					n->objname = lappend($6, makeString($4));
					n->objargs = NIL;
					n->comment = $8;
					$$ = (Node *) n;
				}
			| COMMENT ON RULE name ON any_name IS comment_text
				{
					CommentStmt *n = makeNode(CommentStmt);
					n->objtype = OBJECT_RULE;
					n->objname = lappend($6, makeString($4));
					n->objargs = NIL;
					n->comment = $8;
					$$ = (Node *) n;
				}
			| COMMENT ON RULE name IS comment_text
				{
					/* Obsolete syntax supported for awhile for compatibility */
					CommentStmt *n = makeNode(CommentStmt);
					n->objtype = OBJECT_RULE;
					n->objname = list_make1(makeString($4));
					n->objargs = NIL;
					n->comment = $6;
					$$ = (Node *) n;
				}
			| COMMENT ON TRIGGER name ON any_name IS comment_text
				{
					CommentStmt *n = makeNode(CommentStmt);
					n->objtype = OBJECT_TRIGGER;
					n->objname = lappend($6, makeString($4));
					n->objargs = NIL;
					n->comment = $8;
					$$ = (Node *) n;
				}
			| COMMENT ON OPERATOR CLASS any_name USING access_method IS comment_text
				{
					CommentStmt *n = makeNode(CommentStmt);
					n->objtype = OBJECT_OPCLASS;
					n->objname = $5;
					n->objargs = list_make1(makeString($7));
					n->comment = $9;
					$$ = (Node *) n;
				}
			| COMMENT ON OPERATOR FAMILY any_name USING access_method IS comment_text
				{
					CommentStmt *n = makeNode(CommentStmt);
					n->objtype = OBJECT_OPFAMILY;
					n->objname = $5;
					n->objargs = list_make1(makeString($7));
					n->comment = $9;
					$$ = (Node *) n;
				}
			| COMMENT ON LARGE_P OBJECT_P NumericOnly IS comment_text
				{
					CommentStmt *n = makeNode(CommentStmt);
					n->objtype = OBJECT_LARGEOBJECT;
					n->objname = list_make1($5);
					n->objargs = NIL;
					n->comment = $7;
					$$ = (Node *) n;
				}
			| COMMENT ON CAST '(' Typename AS Typename ')' IS comment_text
				{
					CommentStmt *n = makeNode(CommentStmt);
					n->objtype = OBJECT_CAST;
					n->objname = list_make1($5);
					n->objargs = list_make1($7);
					n->comment = $10;
					$$ = (Node *) n;
				}
			| COMMENT ON opt_procedural LANGUAGE any_name IS comment_text
				{
					CommentStmt *n = makeNode(CommentStmt);
					n->objtype = OBJECT_LANGUAGE;
					n->objname = $5;
					n->objargs = NIL;
					n->comment = $7;
					$$ = (Node *) n;
				}
		;

comment_type:
			COLUMN								{ $$ = OBJECT_COLUMN; }
			| DATABASE							{ $$ = OBJECT_DATABASE; }
			| SCHEMA							{ $$ = OBJECT_SCHEMA; }
			| INDEX								{ $$ = OBJECT_INDEX; }
			| SEQUENCE							{ $$ = OBJECT_SEQUENCE; }
			| TABLE								{ $$ = OBJECT_TABLE; }
			| DOMAIN_P							{ $$ = OBJECT_DOMAIN; }
			| TYPE_P							{ $$ = OBJECT_TYPE; }
			| VIEW								{ $$ = OBJECT_VIEW; }
			| MATERIALIZED VIEW					{ $$ = OBJECT_MATVIEW; }
			| COLLATION							{ $$ = OBJECT_COLLATION; }
			| CONVERSION_P						{ $$ = OBJECT_CONVERSION; }
			| TABLESPACE						{ $$ = OBJECT_TABLESPACE; }
			| EXTENSION							{ $$ = OBJECT_EXTENSION; }
			| ROLE								{ $$ = OBJECT_ROLE; }
			| FOREIGN TABLE						{ $$ = OBJECT_FOREIGN_TABLE; }
			| SERVER							{ $$ = OBJECT_FOREIGN_SERVER; }
			| FOREIGN DATA_P WRAPPER			{ $$ = OBJECT_FDW; }
			| EVENT TRIGGER						{ $$ = OBJECT_EVENT_TRIGGER; }
			| TEXT_P SEARCH CONFIGURATION		{ $$ = OBJECT_TSCONFIGURATION; }
			| TEXT_P SEARCH DICTIONARY			{ $$ = OBJECT_TSDICTIONARY; }
			| TEXT_P SEARCH PARSER				{ $$ = OBJECT_TSPARSER; }
			| TEXT_P SEARCH TEMPLATE			{ $$ = OBJECT_TSTEMPLATE; }
			| RESOURCE QUEUE                    { $$ = OBJECT_RESQUEUE; }
			| RESOURCE GROUP_P					{ $$ = OBJECT_RESGROUP; }
		;

comment_text:
			Sconst								{ $$ = $1; }
			| NULL_P							{ $$ = NULL; }
		;


/*****************************************************************************
 *
 *  SECURITY LABEL [FOR <provider>] ON <object> IS <label>
 *
 *  As with COMMENT ON, <object> can refer to various types of database
 *  objects (e.g. TABLE, COLUMN, etc.).
 *
 *****************************************************************************/

SecLabelStmt:
			SECURITY LABEL opt_provider ON security_label_type any_name
			IS security_label
				{
					SecLabelStmt *n = makeNode(SecLabelStmt);
					n->provider = $3;
					n->objtype = $5;
					n->objname = $6;
					n->objargs = NIL;
					n->label = $8;
					$$ = (Node *) n;
				}
			| SECURITY LABEL opt_provider ON AGGREGATE func_name aggr_args
			  IS security_label
				{
					SecLabelStmt *n = makeNode(SecLabelStmt);
					n->provider = $3;
					n->objtype = OBJECT_AGGREGATE;
					n->objname = $6;
					n->objargs = extractAggrArgTypes($7);
					n->label = $9;
					$$ = (Node *) n;
				}
			| SECURITY LABEL opt_provider ON FUNCTION func_name func_args
			  IS security_label
				{
					SecLabelStmt *n = makeNode(SecLabelStmt);
					n->provider = $3;
					n->objtype = OBJECT_FUNCTION;
					n->objname = $6;
					n->objargs = extractArgTypes($7);
					n->label = $9;
					$$ = (Node *) n;
				}
			| SECURITY LABEL opt_provider ON LARGE_P OBJECT_P NumericOnly
			  IS security_label
				{
					SecLabelStmt *n = makeNode(SecLabelStmt);
					n->provider = $3;
					n->objtype = OBJECT_LARGEOBJECT;
					n->objname = list_make1($7);
					n->objargs = NIL;
					n->label = $9;
					$$ = (Node *) n;
				}
			| SECURITY LABEL opt_provider ON opt_procedural LANGUAGE any_name
			  IS security_label
				{
					SecLabelStmt *n = makeNode(SecLabelStmt);
					n->provider = $3;
					n->objtype = OBJECT_LANGUAGE;
					n->objname = $7;
					n->objargs = NIL;
					n->label = $9;
					$$ = (Node *) n;
				}
		;

opt_provider:	FOR NonReservedWord_or_Sconst	{ $$ = $2; }
				| /* empty */					{ $$ = NULL; }
		;

security_label_type:
			COLUMN								{ $$ = OBJECT_COLUMN; }
			| DATABASE							{ $$ = OBJECT_DATABASE; }
			| EVENT TRIGGER						{ $$ = OBJECT_EVENT_TRIGGER; }
			| FOREIGN TABLE						{ $$ = OBJECT_FOREIGN_TABLE; }
			| SCHEMA							{ $$ = OBJECT_SCHEMA; }
			| SEQUENCE							{ $$ = OBJECT_SEQUENCE; }
			| TABLE								{ $$ = OBJECT_TABLE; }
			| DOMAIN_P							{ $$ = OBJECT_TYPE; }
			| ROLE								{ $$ = OBJECT_ROLE; }
			| TABLESPACE						{ $$ = OBJECT_TABLESPACE; }
			| TYPE_P							{ $$ = OBJECT_TYPE; }
			| VIEW								{ $$ = OBJECT_VIEW; }
			| MATERIALIZED VIEW					{ $$ = OBJECT_MATVIEW; }
		;

security_label:	Sconst				{ $$ = $1; }
				| NULL_P			{ $$ = NULL; }
		;

/*****************************************************************************
 *
 *		QUERY:
 *			fetch/move
 *
 *****************************************************************************/

FetchStmt:	FETCH fetch_args
				{
					FetchStmt *n = (FetchStmt *) $2;
					n->ismove = FALSE;
					$$ = (Node *)n;
				}
			| MOVE fetch_args
				{
					FetchStmt *n = (FetchStmt *) $2;
					n->ismove = TRUE;
					$$ = (Node *)n;
				}
		;

fetch_args:	cursor_name
				{
					FetchStmt *n = makeNode(FetchStmt);
					n->portalname = $1;
					n->direction = FETCH_FORWARD;
					n->howMany = 1;
					$$ = (Node *)n;
				}
			| from_in cursor_name
				{
					FetchStmt *n = makeNode(FetchStmt);
					n->portalname = $2;
					n->direction = FETCH_FORWARD;
					n->howMany = 1;
					$$ = (Node *)n;
				}
			| NEXT opt_from_in cursor_name
				{
					FetchStmt *n = makeNode(FetchStmt);
					n->portalname = $3;
					n->direction = FETCH_FORWARD;
					n->howMany = 1;
					$$ = (Node *)n;
				}
			| PRIOR opt_from_in cursor_name
				{
					FetchStmt *n = makeNode(FetchStmt);
					n->portalname = $3;
					n->direction = FETCH_BACKWARD;
					n->howMany = 1;
					$$ = (Node *)n;
				}
			| FIRST_P opt_from_in cursor_name
				{
					FetchStmt *n = makeNode(FetchStmt);
					n->portalname = $3;
					n->direction = FETCH_ABSOLUTE;
					n->howMany = 1;
					$$ = (Node *)n;
				}
			| LAST_P opt_from_in cursor_name
				{
					FetchStmt *n = makeNode(FetchStmt);
					n->portalname = $3;
					n->direction = FETCH_ABSOLUTE;
					n->howMany = -1;
					$$ = (Node *)n;
				}
			| ABSOLUTE_P SignedIconst opt_from_in cursor_name
				{
					FetchStmt *n = makeNode(FetchStmt);
					n->portalname = $4;
					n->direction = FETCH_ABSOLUTE;
					n->howMany = $2;
					$$ = (Node *)n;
				}
			| RELATIVE_P SignedIconst opt_from_in cursor_name
				{
					FetchStmt *n = makeNode(FetchStmt);
					n->portalname = $4;
					n->direction = FETCH_RELATIVE;
					n->howMany = $2;
					$$ = (Node *)n;
				}
			| SignedIconst opt_from_in cursor_name
				{
					FetchStmt *n = makeNode(FetchStmt);
					n->portalname = $3;
					n->direction = FETCH_FORWARD;
					n->howMany = $1;
					$$ = (Node *)n;
				}
			| ALL opt_from_in cursor_name
				{
					FetchStmt *n = makeNode(FetchStmt);
					n->portalname = $3;
					n->direction = FETCH_FORWARD;
					n->howMany = FETCH_ALL;
					$$ = (Node *)n;
				}
			| FORWARD opt_from_in cursor_name
				{
					FetchStmt *n = makeNode(FetchStmt);
					n->portalname = $3;
					n->direction = FETCH_FORWARD;
					n->howMany = 1;
					$$ = (Node *)n;
				}
			| FORWARD SignedIconst opt_from_in cursor_name
				{
					FetchStmt *n = makeNode(FetchStmt);
					n->portalname = $4;
					n->direction = FETCH_FORWARD;
					n->howMany = $2;
					$$ = (Node *)n;
				}
			| FORWARD ALL opt_from_in cursor_name
				{
					FetchStmt *n = makeNode(FetchStmt);
					n->portalname = $4;
					n->direction = FETCH_FORWARD;
					n->howMany = FETCH_ALL;
					$$ = (Node *)n;
				}
			| BACKWARD opt_from_in cursor_name
				{
					FetchStmt *n = makeNode(FetchStmt);
					n->portalname = $3;
					n->direction = FETCH_BACKWARD;
					n->howMany = 1;
					$$ = (Node *)n;
				}
			| BACKWARD SignedIconst opt_from_in cursor_name
				{
					FetchStmt *n = makeNode(FetchStmt);
					n->portalname = $4;
					n->direction = FETCH_BACKWARD;
					n->howMany = $2;
					$$ = (Node *)n;
				}
			| BACKWARD ALL opt_from_in cursor_name
				{
					FetchStmt *n = makeNode(FetchStmt);
					n->portalname = $4;
					n->direction = FETCH_BACKWARD;
					n->howMany = FETCH_ALL;
					$$ = (Node *)n;
				}
		;

from_in:	FROM									{}
			| IN_P									{}
		;

opt_from_in:	from_in								{}
			| /* EMPTY */							{}
		;


/*****************************************************************************
 *
 * GRANT and REVOKE statements
 *
 *****************************************************************************/

GrantStmt:	GRANT privileges ON privilege_target TO grantee_list
			opt_grant_grant_option
				{
					GrantStmt *n = makeNode(GrantStmt);
					n->is_grant = true;
					n->privileges = $2;
					n->targtype = ($4)->targtype;
					n->objtype = ($4)->objtype;
					n->objects = ($4)->objs;
					n->grantees = $6;
					n->grant_option = $7;
					$$ = (Node*)n;
				}
		;

RevokeStmt:
			REVOKE privileges ON privilege_target
			FROM grantee_list opt_drop_behavior
				{
					GrantStmt *n = makeNode(GrantStmt);
					n->is_grant = false;
					n->grant_option = false;
					n->privileges = $2;
					n->targtype = ($4)->targtype;
					n->objtype = ($4)->objtype;
					n->objects = ($4)->objs;
					n->grantees = $6;
					n->behavior = $7;
					$$ = (Node *)n;
				}
			| REVOKE GRANT OPTION FOR privileges ON privilege_target
			FROM grantee_list opt_drop_behavior
				{
					GrantStmt *n = makeNode(GrantStmt);
					n->is_grant = false;
					n->grant_option = true;
					n->privileges = $5;
					n->targtype = ($7)->targtype;
					n->objtype = ($7)->objtype;
					n->objects = ($7)->objs;
					n->grantees = $9;
					n->behavior = $10;
					$$ = (Node *)n;
				}
		;


/*
 * Privilege names are represented as strings; the validity of the privilege
 * names gets checked at execution.  This is a bit annoying but we have little
 * choice because of the syntactic conflict with lists of role names in
 * GRANT/REVOKE.  What's more, we have to call out in the "privilege"
 * production any reserved keywords that need to be usable as privilege names.
 */

/* either ALL [PRIVILEGES] or a list of individual privileges */
privileges: privilege_list
				{ $$ = $1; }
			| ALL
				{ $$ = NIL; }
			| ALL PRIVILEGES
				{ $$ = NIL; }
			| ALL '(' columnList ')'
				{
					AccessPriv *n = makeNode(AccessPriv);
					n->priv_name = NULL;
					n->cols = $3;
					$$ = list_make1(n);
				}
			| ALL PRIVILEGES '(' columnList ')'
				{
					AccessPriv *n = makeNode(AccessPriv);
					n->priv_name = NULL;
					n->cols = $4;
					$$ = list_make1(n);
				}
		;

privilege_list:	privilege							{ $$ = list_make1($1); }
			| privilege_list ',' privilege			{ $$ = lappend($1, $3); }
		;

privilege:	SELECT opt_column_list
			{
				AccessPriv *n = makeNode(AccessPriv);
				n->priv_name = pstrdup($1);
				n->cols = $2;
				$$ = n;
			}
		| REFERENCES opt_column_list
			{
				AccessPriv *n = makeNode(AccessPriv);
				n->priv_name = pstrdup($1);
				n->cols = $2;
				$$ = n;
			}
		| CREATE opt_column_list
			{
				AccessPriv *n = makeNode(AccessPriv);
				n->priv_name = pstrdup($1);
				n->cols = $2;
				$$ = n;
			}
		| ColId opt_column_list
			{
				AccessPriv *n = makeNode(AccessPriv);
				n->priv_name = $1;
				n->cols = $2;
				$$ = n;
			}
		;


/* Don't bother trying to fold the first two rules into one using
 * opt_table.  You're going to get conflicts.
 */
privilege_target:
			qualified_name_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_OBJECT;
					n->objtype = ACL_OBJECT_RELATION;
					n->objs = $1;
					$$ = n;
				}
			| TABLE qualified_name_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_OBJECT;
					n->objtype = ACL_OBJECT_RELATION;
					n->objs = $2;
					$$ = n;
				}
			| SEQUENCE qualified_name_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_OBJECT;
					n->objtype = ACL_OBJECT_SEQUENCE;
					n->objs = $2;
					$$ = n;
				}
			| FOREIGN DATA_P WRAPPER name_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_OBJECT;
					n->objtype = ACL_OBJECT_FDW;
					n->objs = $4;
					$$ = n;
				}
			| FOREIGN SERVER name_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_OBJECT;
					n->objtype = ACL_OBJECT_FOREIGN_SERVER;
					n->objs = $3;
					$$ = n;
				}
			| FUNCTION function_with_argtypes_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_OBJECT;
					n->objtype = ACL_OBJECT_FUNCTION;
					n->objs = $2;
					$$ = n;
				}
			| DATABASE name_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_OBJECT;
					n->objtype = ACL_OBJECT_DATABASE;
					n->objs = $2;
					$$ = n;
				}
			| DOMAIN_P any_name_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_OBJECT;
					n->objtype = ACL_OBJECT_DOMAIN;
					n->objs = $2;
					$$ = n;
				}
			| LANGUAGE name_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_OBJECT;
					n->objtype = ACL_OBJECT_LANGUAGE;
					n->objs = $2;
					$$ = n;
				}
			| LARGE_P OBJECT_P NumericOnly_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_OBJECT;
					n->objtype = ACL_OBJECT_LARGEOBJECT;
					n->objs = $3;
					$$ = n;
				}
			| SCHEMA name_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_OBJECT;
					n->objtype = ACL_OBJECT_NAMESPACE;
					n->objs = $2;
					$$ = n;
				}
			| TABLESPACE name_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_OBJECT;
					n->objtype = ACL_OBJECT_TABLESPACE;
					n->objs = $2;
					$$ = n;
				}
			| PROTOCOL name_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_OBJECT;
					n->objtype = ACL_OBJECT_EXTPROTOCOL;
					n->objs = $2;
					$$ = n;
				}			
			| TYPE_P any_name_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_OBJECT;
					n->objtype = ACL_OBJECT_TYPE;
					n->objs = $2;
					$$ = n;
				}
			| ALL TABLES IN_P SCHEMA name_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_ALL_IN_SCHEMA;
					n->objtype = ACL_OBJECT_RELATION;
					n->objs = $5;
					$$ = n;
				}
			| ALL SEQUENCES IN_P SCHEMA name_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_ALL_IN_SCHEMA;
					n->objtype = ACL_OBJECT_SEQUENCE;
					n->objs = $5;
					$$ = n;
				}
			| ALL FUNCTIONS IN_P SCHEMA name_list
				{
					PrivTarget *n = (PrivTarget *) palloc(sizeof(PrivTarget));
					n->targtype = ACL_TARGET_ALL_IN_SCHEMA;
					n->objtype = ACL_OBJECT_FUNCTION;
					n->objs = $5;
					$$ = n;
				}
		;


grantee_list:
			grantee									{ $$ = list_make1($1); }
			| grantee_list ',' grantee				{ $$ = lappend($1, $3); }
		;

grantee:	RoleId
				{
					PrivGrantee *n = makeNode(PrivGrantee);
					/* This hack lets us avoid reserving PUBLIC as a keyword*/
					if (strcmp($1, "public") == 0)
						n->rolname = NULL;
					else
						n->rolname = $1;
					$$ = (Node *)n;
				}
			| GROUP_P RoleId
				{
					PrivGrantee *n = makeNode(PrivGrantee);
					/* Treat GROUP PUBLIC as a synonym for PUBLIC */
					if (strcmp($2, "public") == 0)
						n->rolname = NULL;
					else
						n->rolname = $2;
					$$ = (Node *)n;
				}
		;


opt_grant_grant_option:
			WITH GRANT OPTION { $$ = TRUE; }
			| /*EMPTY*/ { $$ = FALSE; }
		;

function_with_argtypes_list:
			function_with_argtypes					{ $$ = list_make1($1); }
			| function_with_argtypes_list ',' function_with_argtypes
													{ $$ = lappend($1, $3); }
		;

function_with_argtypes:
			func_name func_args
				{
					FuncWithArgs *n = makeNode(FuncWithArgs);
					n->funcname = $1;
					n->funcargs = extractArgTypes($2);
					$$ = n;
				}
		;

/*****************************************************************************
 *
 * GRANT and REVOKE ROLE statements
 *
 *****************************************************************************/

GrantRoleStmt:
			GRANT privilege_list TO role_list opt_grant_admin_option opt_granted_by
				{
					GrantRoleStmt *n = makeNode(GrantRoleStmt);
					n->is_grant = true;
					n->granted_roles = $2;
					n->grantee_roles = $4;
					n->admin_opt = $5;
					n->grantor = $6;
					$$ = (Node*)n;
				}
		;

RevokeRoleStmt:
			REVOKE privilege_list FROM role_list opt_granted_by opt_drop_behavior
				{
					GrantRoleStmt *n = makeNode(GrantRoleStmt);
					n->is_grant = false;
					n->admin_opt = false;
					n->granted_roles = $2;
					n->grantee_roles = $4;
					n->behavior = $6;
					$$ = (Node*)n;
				}
			| REVOKE ADMIN OPTION FOR privilege_list FROM role_list opt_granted_by opt_drop_behavior
				{
					GrantRoleStmt *n = makeNode(GrantRoleStmt);
					n->is_grant = false;
					n->admin_opt = true;
					n->granted_roles = $5;
					n->grantee_roles = $7;
					n->behavior = $9;
					$$ = (Node*)n;
				}
		;

opt_grant_admin_option: WITH ADMIN OPTION				{ $$ = TRUE; }
			| /*EMPTY*/									{ $$ = FALSE; }
		;

opt_granted_by: GRANTED BY RoleId						{ $$ = $3; }
			| /*EMPTY*/									{ $$ = NULL; }
		;

/*****************************************************************************
 *
 * ALTER DEFAULT PRIVILEGES statement
 *
 *****************************************************************************/

AlterDefaultPrivilegesStmt:
			ALTER DEFAULT PRIVILEGES DefACLOptionList DefACLAction
				{
					AlterDefaultPrivilegesStmt *n = makeNode(AlterDefaultPrivilegesStmt);
					n->options = $4;
					n->action = (GrantStmt *) $5;
					$$ = (Node*)n;
				}
		;

DefACLOptionList:
			DefACLOptionList DefACLOption			{ $$ = lappend($1, $2); }
			| /* EMPTY */							{ $$ = NIL; }
		;

DefACLOption:
			IN_P SCHEMA name_list
				{
					$$ = makeDefElem("schemas", (Node *)$3);
				}
			| FOR ROLE role_list
				{
					$$ = makeDefElem("roles", (Node *)$3);
				}
			| FOR USER role_list
				{
					$$ = makeDefElem("roles", (Node *)$3);
				}
		;

/*
 * This should match GRANT/REVOKE, except that individual target objects
 * are not mentioned and we only allow a subset of object types.
 */
DefACLAction:
			GRANT privileges ON defacl_privilege_target TO grantee_list
			opt_grant_grant_option
				{
					GrantStmt *n = makeNode(GrantStmt);
					n->is_grant = true;
					n->privileges = $2;
					n->targtype = ACL_TARGET_DEFAULTS;
					n->objtype = $4;
					n->objects = NIL;
					n->grantees = $6;
					n->grant_option = $7;
					$$ = (Node*)n;
				}
			| REVOKE privileges ON defacl_privilege_target
			FROM grantee_list opt_drop_behavior
				{
					GrantStmt *n = makeNode(GrantStmt);
					n->is_grant = false;
					n->grant_option = false;
					n->privileges = $2;
					n->targtype = ACL_TARGET_DEFAULTS;
					n->objtype = $4;
					n->objects = NIL;
					n->grantees = $6;
					n->behavior = $7;
					$$ = (Node *)n;
				}
			| REVOKE GRANT OPTION FOR privileges ON defacl_privilege_target
			FROM grantee_list opt_drop_behavior
				{
					GrantStmt *n = makeNode(GrantStmt);
					n->is_grant = false;
					n->grant_option = true;
					n->privileges = $5;
					n->targtype = ACL_TARGET_DEFAULTS;
					n->objtype = $7;
					n->objects = NIL;
					n->grantees = $9;
					n->behavior = $10;
					$$ = (Node *)n;
				}
		;

defacl_privilege_target:
			TABLES			{ $$ = ACL_OBJECT_RELATION; }
			| FUNCTIONS		{ $$ = ACL_OBJECT_FUNCTION; }
			| SEQUENCES		{ $$ = ACL_OBJECT_SEQUENCE; }
			| TYPES_P		{ $$ = ACL_OBJECT_TYPE; }
		;


/*****************************************************************************
 *
 *		QUERY: CREATE INDEX
 *
 * Note: we cannot put TABLESPACE clause after WHERE clause unless we are
 * willing to make TABLESPACE a fully reserved word.
 *****************************************************************************/

IndexStmt:	CREATE opt_unique INDEX opt_concurrently opt_index_name
			ON qualified_name access_method_clause '(' index_params ')'
			opt_reloptions OptTableSpace where_clause
				{
					IndexStmt *n = makeNode(IndexStmt);
					n->unique = $2;
					n->concurrent = $4;
					n->idxname = $5;
					n->relation = $7;
					n->accessMethod = $8;
					n->indexParams = $10;
					n->options = $12;
					n->tableSpace = $13;
					n->whereClause = $14;
					n->excludeOpNames = NIL;
					n->idxcomment = NULL;
					n->indexOid = InvalidOid;
					n->oldNode = InvalidOid;
					n->primary = false;
					n->isconstraint = false;
					n->deferrable = false;
					n->initdeferred = false;

                    if (n->concurrent)
					{
						ereport(ERROR,
								(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
								 errmsg("CREATE INDEX CONCURRENTLY is not supported")));

					}

					$$ = (Node *)n;
				}
		;

opt_unique:
			UNIQUE									{ $$ = TRUE; }
			| /*EMPTY*/								{ $$ = FALSE; }
		;

opt_concurrently:
			CONCURRENTLY							{ $$ = TRUE; }
			| /*EMPTY*/								{ $$ = FALSE; }
		;

opt_index_name:
			index_name								{ $$ = $1; }
			| /*EMPTY*/								{ $$ = NULL; }
		;

access_method_clause:
			USING access_method						{ $$ = $2; }
			| /*EMPTY*/								{ $$ = DEFAULT_INDEX_TYPE; }
		;

index_params:	index_elem							{ $$ = list_make1($1); }
			| index_params ',' index_elem			{ $$ = lappend($1, $3); }
		;

/*
 * Index attributes can be either simple column references, or arbitrary
 * expressions in parens.  For backwards-compatibility reasons, we allow
 * an expression that's just a function call to be written without parens.
 */
index_elem:	ColId opt_collate opt_class opt_asc_desc opt_nulls_order
				{
					$$ = makeNode(IndexElem);
					$$->name = $1;
					$$->expr = NULL;
					$$->indexcolname = NULL;
					$$->collation = $2;
					$$->opclass = $3;
					$$->ordering = $4;
					$$->nulls_ordering = $5;
				}
			| func_expr_windowless opt_collate opt_class opt_asc_desc opt_nulls_order
				{
					$$ = makeNode(IndexElem);
					$$->name = NULL;
					$$->expr = $1;
					$$->indexcolname = NULL;
					$$->collation = $2;
					$$->opclass = $3;
					$$->ordering = $4;
					$$->nulls_ordering = $5;
				}
			| '(' a_expr ')' opt_collate opt_class opt_asc_desc opt_nulls_order
				{
					$$ = makeNode(IndexElem);
					$$->name = NULL;
					$$->expr = $2;
					$$->indexcolname = NULL;
					$$->collation = $4;
					$$->opclass = $5;
					$$->ordering = $6;
					$$->nulls_ordering = $7;
				}
		;

opt_collate: COLLATE any_name						{ $$ = $2; }
			| /*EMPTY*/								{ $$ = NIL; }
		;

opt_class:	any_name								{ $$ = $1; }
			| USING any_name						{ $$ = $2; }
			| /*EMPTY*/								{ $$ = NIL; }
		;

opt_asc_desc: ASC							{ $$ = SORTBY_ASC; }
			| DESC							{ $$ = SORTBY_DESC; }
			| /*EMPTY*/						{ $$ = SORTBY_DEFAULT; }
		;

opt_nulls_order: NULLS_FIRST				{ $$ = SORTBY_NULLS_FIRST; }
			| NULLS_LAST					{ $$ = SORTBY_NULLS_LAST; }
			| /*EMPTY*/						{ $$ = SORTBY_NULLS_DEFAULT; }
		;


/*****************************************************************************
 *
 *		QUERY:
 *				create [or replace] function <fname>
 *						[(<type-1> { , <type-n>})]
 *						returns <type-r>
 *						as <filename or code in language as appropriate>
 *						language <lang> [with parameters]
 *
 *****************************************************************************/

CreateFunctionStmt:
			CREATE opt_or_replace FUNCTION func_name func_args_with_defaults
			RETURNS func_return createfunc_opt_list opt_definition
				{
					CreateFunctionStmt *n = makeNode(CreateFunctionStmt);
					n->replace = $2;
					n->funcname = $4;
					n->parameters = $5;
					n->returnType = $7;
					n->options = $8;
					n->withClause = $9;
					$$ = (Node *)n;
				}
			| CREATE opt_or_replace FUNCTION func_name func_args_with_defaults
			  RETURNS TABLE '(' table_func_column_list ')' createfunc_opt_list opt_definition
				{
					CreateFunctionStmt *n = makeNode(CreateFunctionStmt);
					n->replace = $2;
					n->funcname = $4;
					n->parameters = mergeTableFuncParameters($5, $9);
					n->returnType = TableFuncTypeName($9);
					n->returnType->location = @7;
					n->options = $11;
					n->withClause = $12;
					$$ = (Node *)n;
				}
			| CREATE opt_or_replace FUNCTION func_name func_args_with_defaults
			  createfunc_opt_list opt_definition
				{
					CreateFunctionStmt *n = makeNode(CreateFunctionStmt);
					n->replace = $2;
					n->funcname = $4;
					n->parameters = $5;
					n->returnType = NULL;
					n->options = $6;
					n->withClause = $7;
					$$ = (Node *)n;
				}
		;

opt_or_replace:
			OR REPLACE								{ $$ = TRUE; }
			| /*EMPTY*/								{ $$ = FALSE; }
		;

func_args:	'(' func_args_list ')'					{ $$ = $2; }
			| '(' ')'								{ $$ = NIL; }
		;

func_args_list:
			func_arg								{ $$ = list_make1($1); }
			| func_args_list ',' func_arg			{ $$ = lappend($1, $3); }
		;

/*
 * func_args_with_defaults is separate because we only want to accept
 * defaults in CREATE FUNCTION, not in ALTER etc.
 */
func_args_with_defaults:
		'(' func_args_with_defaults_list ')'		{ $$ = $2; }
		| '(' ')'									{ $$ = NIL; }
		;

func_args_with_defaults_list:
		func_arg_with_default						{ $$ = list_make1($1); }
		| func_args_with_defaults_list ',' func_arg_with_default
													{ $$ = lappend($1, $3); }
		;

/*
 * The style with arg_class first is SQL99 standard, but Oracle puts
 * param_name first; accept both since it's likely people will try both
 * anyway.  Don't bother trying to save productions by letting arg_class
 * have an empty alternative ... you'll get shift/reduce conflicts.
 *
 * We can catch over-specified arguments here if we want to,
 * but for now better to silently swallow typmod, etc.
 * - thomas 2000-03-22
 */
func_arg:
			arg_class param_name func_type
				{
					FunctionParameter *n = makeNode(FunctionParameter);
					n->name = $2;
					n->argType = $3;
					n->mode = $1;
					n->defexpr = NULL;
					$$ = n;
				}
			| param_name arg_class func_type
				{
					FunctionParameter *n = makeNode(FunctionParameter);
					n->name = $1;
					n->argType = $3;
					n->mode = $2;
					n->defexpr = NULL;
					$$ = n;
				}
			| param_name func_type
				{
					FunctionParameter *n = makeNode(FunctionParameter);
					n->name = $1;
					n->argType = $2;
					n->mode = FUNC_PARAM_IN;
					n->defexpr = NULL;
					$$ = n;
				}
			| arg_class func_type
				{
					FunctionParameter *n = makeNode(FunctionParameter);
					n->name = NULL;
					n->argType = $2;
					n->mode = $1;
					n->defexpr = NULL;
					$$ = n;
				}
			| func_type
				{
					FunctionParameter *n = makeNode(FunctionParameter);
					n->name = NULL;
					n->argType = $1;
					n->mode = FUNC_PARAM_IN;
					n->defexpr = NULL;
					$$ = n;
				}
		;

/* INOUT is SQL99 standard, IN OUT is for Oracle compatibility */
arg_class:	IN_P								{ $$ = FUNC_PARAM_IN; }
			| OUT_P								{ $$ = FUNC_PARAM_OUT; }
			| INOUT								{ $$ = FUNC_PARAM_INOUT; }
			| IN_P OUT_P						{ $$ = FUNC_PARAM_INOUT; }
			| VARIADIC							{ $$ = FUNC_PARAM_VARIADIC; }
		;

/*
 * Ideally param_name should be ColId, but that causes too many conflicts.
 */
param_name:	type_function_name
		;

func_return:
			func_type
				{
					/* We can catch over-specified results here if we want to,
					 * but for now better to silently swallow typmod, etc.
					 * - thomas 2000-03-22
					 */
					$$ = $1;
				}
		;

/*
 * We would like to make the %TYPE productions here be ColId attrs etc,
 * but that causes reduce/reduce conflicts.  type_function_name
 * is next best choice.
 */
func_type:	Typename								{ $$ = $1; }
			| type_function_name attrs '%' TYPE_P
				{
					$$ = makeTypeNameFromNameList(lcons(makeString($1), $2));
					$$->pct_type = true;
					$$->location = @1;
				}
			| SETOF type_function_name attrs '%' TYPE_P
				{
					$$ = makeTypeNameFromNameList(lcons(makeString($2), $3));
					$$->pct_type = true;
					$$->setof = TRUE;
					$$->location = @2;
				}
		;

func_arg_with_default:
		func_arg
				{
					$$ = $1;
				}
		| func_arg DEFAULT a_expr
				{
					$$ = $1;
					$$->defexpr = $3;
				}
		| func_arg '=' a_expr
				{
					$$ = $1;
					$$->defexpr = $3;
				}
		;

/* Aggregate args can be most things that function args can be */
aggr_arg:	func_arg
				{
					if (!($1->mode == FUNC_PARAM_IN ||
						  $1->mode == FUNC_PARAM_VARIADIC))
						ereport(ERROR,
								(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
								 errmsg("aggregates cannot have output arguments"),
								 parser_errposition(@1)));
					$$ = $1;
				}
		;

/*
 * The SQL standard offers no guidance on how to declare aggregate argument
 * lists, since it doesn't have CREATE AGGREGATE etc.  We accept these cases:
 *
 * (*)									- normal agg with no args
 * (aggr_arg,...)						- normal agg with args
 * (ORDER BY aggr_arg,...)				- ordered-set agg with no direct args
 * (aggr_arg,... ORDER BY aggr_arg,...)	- ordered-set agg with direct args
 *
 * The zero-argument case is spelled with '*' for consistency with COUNT(*).
 *
 * An additional restriction is that if the direct-args list ends in a
 * VARIADIC item, the ordered-args list must contain exactly one item that
 * is also VARIADIC with the same type.  This allows us to collapse the two
 * VARIADIC items into one, which is necessary to represent the aggregate in
 * pg_proc.  We check this at the grammar stage so that we can return a list
 * in which the second VARIADIC item is already discarded, avoiding extra work
 * in cases such as DROP AGGREGATE.
 *
 * The return value of this production is a two-element list, in which the
 * first item is a sublist of FunctionParameter nodes (with any duplicate
 * VARIADIC item already dropped, as per above) and the second is an integer
 * Value node, containing -1 if there was no ORDER BY and otherwise the number
 * of argument declarations before the ORDER BY.  (If this number is equal
 * to the first sublist's length, then we dropped a duplicate VARIADIC item.)
 * This representation is passed as-is to CREATE AGGREGATE; for operations
 * on existing aggregates, we can just apply extractArgTypes to the first
 * sublist.
 */
aggr_args:	'(' '*' ')'
				{
					$$ = list_make2(NIL, makeInteger(-1));
				}
			| '(' aggr_args_list ')'
				{
					$$ = list_make2($2, makeInteger(-1));
				}
			| '(' ORDER BY aggr_args_list ')'
				{
					$$ = list_make2($4, makeInteger(0));
				}
			| '(' aggr_args_list ORDER BY aggr_args_list ')'
				{
					/* this is the only case requiring consistency checking */
					$$ = makeOrderedSetArgs($2, $5, yyscanner);
				}
		;

aggr_args_list:
			aggr_arg								{ $$ = list_make1($1); }
			| aggr_args_list ',' aggr_arg			{ $$ = lappend($1, $3); }
		;

createfunc_opt_list:
			/* Must be at least one to prevent conflict */
			createfunc_opt_item						{ $$ = list_make1($1); }
			| createfunc_opt_list createfunc_opt_item { $$ = lappend($1, $2); }
	;

/*
 * Options common to both CREATE FUNCTION and ALTER FUNCTION
 */
common_func_opt_item:
			CALLED ON NULL_P INPUT_P
				{
					$$ = makeDefElem("strict", (Node *)makeInteger(FALSE));
				}
			| RETURNS NULL_P ON NULL_P INPUT_P
				{
					$$ = makeDefElem("strict", (Node *)makeInteger(TRUE));
				}
			| STRICT_P
				{
					$$ = makeDefElem("strict", (Node *)makeInteger(TRUE));
				}
			| IMMUTABLE
				{
					$$ = makeDefElem("volatility", (Node *)makeString("immutable"));
				}
			| STABLE
				{
					$$ = makeDefElem("volatility", (Node *)makeString("stable"));
				}
			| VOLATILE
				{
					$$ = makeDefElem("volatility", (Node *)makeString("volatile"));
				}
			| EXTERNAL SECURITY DEFINER
				{
					$$ = makeDefElem("security", (Node *)makeInteger(TRUE));
				}
			| EXTERNAL SECURITY INVOKER
				{
					$$ = makeDefElem("security", (Node *)makeInteger(FALSE));
				}
			| SECURITY DEFINER
				{
					$$ = makeDefElem("security", (Node *)makeInteger(TRUE));
				}
			| SECURITY INVOKER
				{
					$$ = makeDefElem("security", (Node *)makeInteger(FALSE));
				}
			| LEAKPROOF
				{
					$$ = makeDefElem("leakproof", (Node *)makeInteger(TRUE));
				}
			| NOT LEAKPROOF
				{
					$$ = makeDefElem("leakproof", (Node *)makeInteger(FALSE));
				}
			| COST NumericOnly
				{
					$$ = makeDefElem("cost", (Node *)$2);
				}
			| ROWS NumericOnly
				{
					$$ = makeDefElem("rows", (Node *)$2);
				}
			| FunctionSetResetClause
				{
					/* we abuse the normal content of a DefElem here */
					$$ = makeDefElem("set", (Node *)$1);
				}
			| NO SQL
				{
					$$ = makeDefElem("data_access", (Node *)makeString("none"));
				}
			| CONTAINS SQL
				{
					$$ = makeDefElem("data_access", (Node *)makeString("contains"));
				}
			| READS SQL DATA_P
				{
					$$ = makeDefElem("data_access", (Node *)makeString("reads"));
				}
			| MODIFIES SQL DATA_P
				{
					$$ = makeDefElem("data_access", (Node *)makeString("modifies"));
				}
			| EXECUTE ON ANY
				{
					$$ = makeDefElem("exec_location", (Node *)makeString("any"));
				}
			| EXECUTE ON MASTER
				{
					$$ = makeDefElem("exec_location", (Node *)makeString("master"));
				}
			| EXECUTE ON INITPLAN
				{
					$$ = makeDefElem("exec_location", (Node *)makeString("initplan"));
				}
			| EXECUTE ON ALL SEGMENTS
				{
					$$ = makeDefElem("exec_location", (Node *)makeString("all_segments"));
				}
		;

createfunc_opt_item:
			AS func_as
				{
					$$ = makeDefElem("as", (Node *)$2);
				}
			| LANGUAGE NonReservedWord_or_Sconst
				{
					$$ = makeDefElem("language", (Node *)makeString($2));
				}
			| WINDOW
				{
					$$ = makeDefElem("window", (Node *)makeInteger(TRUE));
				}
			| common_func_opt_item
				{
					$$ = $1;
				}
		;

func_as:	Sconst						{ $$ = list_make1(makeString($1)); }
			| Sconst ',' Sconst
				{
					$$ = list_make2(makeString($1), makeString($3));
				}
		;

opt_definition:
			WITH definition							{ $$ = $2; }
			| /*EMPTY*/								{ $$ = NIL; }
		;

table_func_column:	param_name func_type
				{
					FunctionParameter *n = makeNode(FunctionParameter);
					n->name = $1;
					n->argType = $2;
					n->mode = FUNC_PARAM_TABLE;
					n->defexpr = NULL;
					$$ = n;
				}
		;

table_func_column_list:
			table_func_column
				{
					$$ = list_make1($1);
				}
			| table_func_column_list ',' table_func_column
				{
					$$ = lappend($1, $3);
				}
		;

/*****************************************************************************
 * ALTER FUNCTION
 *
 * RENAME and OWNER subcommands are already provided by the generic
 * ALTER infrastructure, here we just specify alterations that can
 * only be applied to functions.
 *
 *****************************************************************************/
AlterFunctionStmt:
			ALTER FUNCTION function_with_argtypes alterfunc_opt_list opt_restrict
				{
					AlterFunctionStmt *n = makeNode(AlterFunctionStmt);
					n->func = $3;
					n->actions = $4;
					$$ = (Node *) n;
				}
		;

alterfunc_opt_list:
			/* At least one option must be specified */
			common_func_opt_item					{ $$ = list_make1($1); }
			| alterfunc_opt_list common_func_opt_item { $$ = lappend($1, $2); }
		;

/* Ignored, merely for SQL compliance */
opt_restrict:
			RESTRICT
			| /* EMPTY */
		;


/*****************************************************************************
 *
 *		QUERY:
 *
 *		DROP FUNCTION funcname (arg1, arg2, ...) [ RESTRICT | CASCADE ]
 *		DROP AGGREGATE aggname (arg1, ...) [ RESTRICT | CASCADE ]
 *		DROP OPERATOR opname (leftoperand_typ, rightoperand_typ) [ RESTRICT | CASCADE ]
 *
 *****************************************************************************/

RemoveFuncStmt:
			DROP FUNCTION func_name func_args opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_FUNCTION;
					n->objects = list_make1($3);
					n->arguments = list_make1(extractArgTypes($4));
					n->behavior = $5;
					n->missing_ok = false;
					n->concurrent = false;
					$$ = (Node *)n;
				}
			| DROP FUNCTION IF_P EXISTS func_name func_args opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_FUNCTION;
					n->objects = list_make1($5);
					n->arguments = list_make1(extractArgTypes($6));
					n->behavior = $7;
					n->missing_ok = true;
					n->concurrent = false;
					$$ = (Node *)n;
				}
		;

RemoveAggrStmt:
			DROP AGGREGATE func_name aggr_args opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_AGGREGATE;
					n->objects = list_make1($3);
					n->arguments = list_make1(extractAggrArgTypes($4));
					n->behavior = $5;
					n->missing_ok = false;
					n->concurrent = false;
					$$ = (Node *)n;
				}
			| DROP AGGREGATE IF_P EXISTS func_name aggr_args opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_AGGREGATE;
					n->objects = list_make1($5);
					n->arguments = list_make1(extractAggrArgTypes($6));
					n->behavior = $7;
					n->missing_ok = true;
					n->concurrent = false;
					$$ = (Node *)n;
				}
		;

RemoveOperStmt:
			DROP OPERATOR any_operator oper_argtypes opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_OPERATOR;
					n->objects = list_make1($3);
					n->arguments = list_make1($4);
					n->behavior = $5;
					n->missing_ok = false;
					n->concurrent = false;
					$$ = (Node *)n;
				}
			| DROP OPERATOR IF_P EXISTS any_operator oper_argtypes opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_OPERATOR;
					n->objects = list_make1($5);
					n->arguments = list_make1($6);
					n->behavior = $7;
					n->missing_ok = true;
					n->concurrent = false;
					$$ = (Node *)n;
				}
		;

oper_argtypes:
			'(' Typename ')'
				{
				   ereport(ERROR,
						   (errcode(ERRCODE_SYNTAX_ERROR),
							errmsg("missing argument"),
							errhint("Use NONE to denote the missing argument of a unary operator."),
							parser_errposition(@3)));
				}
			| '(' Typename ',' Typename ')'
					{ $$ = list_make2($2, $4); }
			| '(' NONE ',' Typename ')'					/* left unary */
					{ $$ = list_make2(NULL, $4); }
			| '(' Typename ',' NONE ')'					/* right unary */
					{ $$ = list_make2($2, NULL); }
		;

any_operator:
			all_Op
					{ $$ = list_make1(makeString($1)); }
			| ColId '.' any_operator
					{ $$ = lcons(makeString($1), $3); }
		;

/*****************************************************************************
 *
 *		DO <anonymous code block> [ LANGUAGE language ]
 *
 * We use a DefElem list for future extensibility, and to allow flexibility
 * in the clause order.
 *
 *****************************************************************************/

DoStmt: DO dostmt_opt_list
				{
					DoStmt *n = makeNode(DoStmt);
					n->args = $2;
					$$ = (Node *)n;
				}
		;

dostmt_opt_list:
			dostmt_opt_item						{ $$ = list_make1($1); }
			| dostmt_opt_list dostmt_opt_item	{ $$ = lappend($1, $2); }
		;

dostmt_opt_item:
			Sconst
				{
					$$ = makeDefElem("as", (Node *)makeString($1));
				}
			| LANGUAGE NonReservedWord_or_Sconst
				{
					$$ = makeDefElem("language", (Node *)makeString($2));
				}
		;

/*****************************************************************************
 *
 *		CREATE CAST / DROP CAST
 *
 *****************************************************************************/

CreateCastStmt: CREATE CAST '(' Typename AS Typename ')'
					WITH FUNCTION function_with_argtypes cast_context
				{
					CreateCastStmt *n = makeNode(CreateCastStmt);
					n->sourcetype = $4;
					n->targettype = $6;
					n->func = $10;
					n->context = (CoercionContext) $11;
					n->inout = false;
					$$ = (Node *)n;
				}
			| CREATE CAST '(' Typename AS Typename ')'
					WITHOUT FUNCTION cast_context
				{
					CreateCastStmt *n = makeNode(CreateCastStmt);
					n->sourcetype = $4;
					n->targettype = $6;
					n->func = NULL;
					n->context = (CoercionContext) $10;
					n->inout = false;
					$$ = (Node *)n;
				}
			| CREATE CAST '(' Typename AS Typename ')'
					WITH INOUT cast_context
				{
					CreateCastStmt *n = makeNode(CreateCastStmt);
					n->sourcetype = $4;
					n->targettype = $6;
					n->func = NULL;
					n->context = (CoercionContext) $10;
					n->inout = true;
					$$ = (Node *)n;
				}
		;

cast_context:  AS IMPLICIT_P					{ $$ = COERCION_IMPLICIT; }
		| AS ASSIGNMENT							{ $$ = COERCION_ASSIGNMENT; }
		| /*EMPTY*/								{ $$ = COERCION_EXPLICIT; }
		;


DropCastStmt: DROP CAST opt_if_exists '(' Typename AS Typename ')' opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_CAST;
					n->objects = list_make1(list_make1($5));
					n->arguments = list_make1(list_make1($7));
					n->behavior = $9;
					n->missing_ok = $3;
					n->concurrent = false;
					$$ = (Node *)n;
				}
		;

opt_if_exists: IF_P EXISTS						{ $$ = TRUE; }
		| /*EMPTY*/								{ $$ = FALSE; }
		;


/*****************************************************************************
 *
 *		QUERY:
 *
 *		REINDEX type <name> [FORCE]
 *
 * FORCE no longer does anything, but we accept it for backwards compatibility
 *****************************************************************************/

ReindexStmt:
			REINDEX reindex_type qualified_name opt_force
				{
					ReindexStmt *n = makeNode(ReindexStmt);
					n->kind = $2;
					n->relation = $3;
					n->name = NULL;
					$$ = (Node *)n;
				}
			| REINDEX SYSTEM_P name opt_force
				{
					ReindexStmt *n = makeNode(ReindexStmt);
					n->kind = OBJECT_DATABASE;
					n->name = $3;
					n->relation = NULL;
					n->do_system = true;
					n->do_user = false;
					$$ = (Node *)n;
				}
			| REINDEX DATABASE name opt_force
				{
					ReindexStmt *n = makeNode(ReindexStmt);
					n->kind = OBJECT_DATABASE;
					n->name = $3;
					n->relation = NULL;
					n->do_system = true;
					n->do_user = true;
					$$ = (Node *)n;
				}
		;

reindex_type:
			INDEX									{ $$ = OBJECT_INDEX; }
			| TABLE									{ $$ = OBJECT_TABLE; }
		;

opt_force:	FORCE									{  $$ = TRUE; }
			| /* EMPTY */							{  $$ = FALSE; }
		;

/*
 * ALTER TYPE ... SET DEFAULT ENCODING
 *
 * Used to set storage parameter defaults for types.
 */
AlterTypeStmt: ALTER TYPE_P any_name SET DEFAULT ENCODING definition
				{
					AlterTypeStmt *n = makeNode(AlterTypeStmt);

					n->typeName = $3;
					n->encoding = $7;
					$$ = (Node *)n;
				}
		;

/*****************************************************************************
 *
 * ALTER TABLESPACE
 *
 *****************************************************************************/

AlterTblSpcStmt:
			ALTER TABLESPACE name SET reloptions
				{
					AlterTableSpaceOptionsStmt *n =
						makeNode(AlterTableSpaceOptionsStmt);
					n->tablespacename = $3;
					n->options = $5;
					n->isReset = FALSE;
					$$ = (Node *)n;
				}
			| ALTER TABLESPACE name RESET reloptions
				{
					AlterTableSpaceOptionsStmt *n =
						makeNode(AlterTableSpaceOptionsStmt);
					n->tablespacename = $3;
					n->options = $5;
					n->isReset = TRUE;
					$$ = (Node *)n;
				}
		;

/*****************************************************************************
 *
 * ALTER THING name RENAME TO newname
 *
 *****************************************************************************/

RenameStmt: ALTER AGGREGATE func_name aggr_args RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_AGGREGATE;
					n->object = $3;
					n->objarg = extractAggrArgTypes($4);
					n->newname = $7;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER COLLATION any_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_COLLATION;
					n->object = $3;
					n->newname = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER CONVERSION_P any_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_CONVERSION;
					n->object = $3;
					n->newname = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER DATABASE database_name RENAME TO database_name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_DATABASE;
					n->subname = $3;
					n->newname = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER DOMAIN_P any_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_DOMAIN;
					n->object = $3;
					n->newname = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER DOMAIN_P any_name RENAME CONSTRAINT name TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_CONSTRAINT;
					n->relationType = OBJECT_DOMAIN;
					n->object = $3;
					n->subname = $6;
					n->newname = $8;
					$$ = (Node *)n;
				}
			| ALTER FOREIGN DATA_P WRAPPER name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_FDW;
					n->object = list_make1(makeString($5));
					n->newname = $8;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER FUNCTION function_with_argtypes RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_FUNCTION;
					n->object = $3->funcname;
					n->objarg = $3->funcargs;
					n->newname = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER GROUP_P RoleId RENAME TO RoleId
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_ROLE;
					n->subname = $3;
					n->newname = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER opt_procedural LANGUAGE name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_LANGUAGE;
					n->object = list_make1(makeString($4));
					n->newname = $7;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER OPERATOR CLASS any_name USING access_method RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_OPCLASS;
					n->object = $4;
					n->objarg = list_make1(makeString($6));
					n->newname = $9;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER OPERATOR FAMILY any_name USING access_method RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_OPFAMILY;
					n->object = $4;
					n->objarg = list_make1(makeString($6));
					n->newname = $9;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER SCHEMA name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_SCHEMA;
					n->subname = $3;
					n->newname = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER SERVER name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_FOREIGN_SERVER;
					n->object = list_make1(makeString($3));
					n->newname = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER TABLE relation_expr RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_TABLE;
					n->relation = $3;
					n->subname = NULL;
					n->newname = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER TABLE IF_P EXISTS relation_expr RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_TABLE;
					n->relation = $5;
					n->subname = NULL;
					n->newname = $8;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
			| ALTER SEQUENCE qualified_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_SEQUENCE;
					n->relation = $3;
					n->subname = NULL;
					n->newname = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER SEQUENCE IF_P EXISTS qualified_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_SEQUENCE;
					n->relation = $5;
					n->subname = NULL;
					n->newname = $8;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
			| ALTER VIEW qualified_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_VIEW;
					n->relation = $3;
					n->subname = NULL;
					n->newname = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER VIEW IF_P EXISTS qualified_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_VIEW;
					n->relation = $5;
					n->subname = NULL;
					n->newname = $8;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
			| ALTER MATERIALIZED VIEW qualified_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_MATVIEW;
					n->relation = $4;
					n->subname = NULL;
					n->newname = $7;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER MATERIALIZED VIEW IF_P EXISTS qualified_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_MATVIEW;
					n->relation = $6;
					n->subname = NULL;
					n->newname = $9;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
			| ALTER INDEX qualified_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_INDEX;
					n->relation = $3;
					n->subname = NULL;
					n->newname = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER INDEX IF_P EXISTS qualified_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_INDEX;
					n->relation = $5;
					n->subname = NULL;
					n->newname = $8;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
			| ALTER FOREIGN TABLE relation_expr RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_FOREIGN_TABLE;
					n->relation = $4;
					n->subname = NULL;
					n->newname = $7;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER FOREIGN TABLE IF_P EXISTS relation_expr RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_FOREIGN_TABLE;
					n->relation = $6;
					n->subname = NULL;
					n->newname = $9;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
			| ALTER TABLE relation_expr RENAME opt_column name TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_COLUMN;
					n->relationType = OBJECT_TABLE;
					n->relation = $3;
					n->subname = $6;
					n->newname = $8;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER TABLE IF_P EXISTS relation_expr RENAME opt_column name TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_COLUMN;
					n->relationType = OBJECT_TABLE;
					n->relation = $5;
					n->subname = $8;
					n->newname = $10;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
			| ALTER MATERIALIZED VIEW qualified_name RENAME opt_column name TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_COLUMN;
					n->relationType = OBJECT_MATVIEW;
					n->relation = $4;
					n->subname = $7;
					n->newname = $9;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER MATERIALIZED VIEW IF_P EXISTS qualified_name RENAME opt_column name TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_COLUMN;
					n->relationType = OBJECT_MATVIEW;
					n->relation = $6;
					n->subname = $9;
					n->newname = $11;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
			| ALTER TABLE relation_expr RENAME CONSTRAINT name TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_CONSTRAINT;
					n->relationType = OBJECT_TABLE;
					n->relation = $3;
					n->subname = $6;
					n->newname = $8;
					$$ = (Node *)n;
				}
			| ALTER FOREIGN TABLE relation_expr RENAME opt_column name TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_COLUMN;
					n->relationType = OBJECT_FOREIGN_TABLE;
					n->relation = $4;
					n->subname = $7;
					n->newname = $9;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER FOREIGN TABLE IF_P EXISTS relation_expr RENAME opt_column name TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_COLUMN;
					n->relationType = OBJECT_FOREIGN_TABLE;
					n->relation = $6;
					n->subname = $9;
					n->newname = $11;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
			| ALTER RULE name ON qualified_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_RULE;
					n->relation = $5;
					n->subname = $3;
					n->newname = $8;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER TRIGGER name ON qualified_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_TRIGGER;
					n->relation = $5;
					n->subname = $3;
					n->newname = $8;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER EVENT TRIGGER name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_EVENT_TRIGGER;
					n->object = list_make1(makeString($4));
					n->newname = $7;
					$$ = (Node *)n;
				}
			| ALTER ROLE RoleId RENAME TO RoleId
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_ROLE;
					n->subname = $3;
					n->newname = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER USER RoleId RENAME TO RoleId
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_ROLE;
					n->subname = $3;
					n->newname = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER TABLESPACE name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_TABLESPACE;
					n->subname = $3;
					n->newname = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER TEXT_P SEARCH PARSER any_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_TSPARSER;
					n->object = $5;
					n->newname = $8;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER TEXT_P SEARCH DICTIONARY any_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_TSDICTIONARY;
					n->object = $5;
					n->newname = $8;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER TEXT_P SEARCH TEMPLATE any_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_TSTEMPLATE;
					n->object = $5;
					n->newname = $8;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER TEXT_P SEARCH CONFIGURATION any_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_TSCONFIGURATION;
					n->object = $5;
					n->newname = $8;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER TYPE_P any_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_TYPE;
					n->object = $3;
					n->newname = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER TYPE_P any_name RENAME ATTRIBUTE name TO name opt_drop_behavior
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_ATTRIBUTE;
					n->relationType = OBJECT_TYPE;
					n->relation = makeRangeVarFromAnyName($3, @3, yyscanner);
					n->subname = $6;
					n->newname = $8;
					n->behavior = $9;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER PROTOCOL any_name RENAME TO name
				{
					RenameStmt *n = makeNode(RenameStmt);
					n->renameType = OBJECT_EXTPROTOCOL;
					n->object = $3;
					n->newname = $6;
					$$ = (Node *)n;
				}
		;

opt_column: COLUMN									{ $$ = COLUMN; }
			| /*EMPTY*/								{ $$ = 0; }
		;

opt_set_data: SET DATA_P							{ $$ = 1; }
			| /*EMPTY*/								{ $$ = 0; }
		;

/*****************************************************************************
 *
 * ALTER THING name SET SCHEMA name
 *
 *****************************************************************************/

AlterObjectSchemaStmt:
			ALTER AGGREGATE func_name aggr_args SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_AGGREGATE;
					n->object = $3;
					n->objarg = extractAggrArgTypes($4);
					n->newschema = $7;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER COLLATION any_name SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_COLLATION;
					n->object = $3;
					n->newschema = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER CONVERSION_P any_name SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_CONVERSION;
					n->object = $3;
					n->newschema = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER DOMAIN_P any_name SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_DOMAIN;
					n->object = $3;
					n->newschema = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER EXTENSION any_name SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_EXTENSION;
					n->object = $3;
					n->newschema = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER FUNCTION function_with_argtypes SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_FUNCTION;
					n->object = $3->funcname;
					n->objarg = $3->funcargs;
					n->newschema = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER OPERATOR any_operator oper_argtypes SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_OPERATOR;
					n->object = $3;
					n->objarg = $4;
					n->newschema = $7;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER OPERATOR CLASS any_name USING access_method SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_OPCLASS;
					n->object = $4;
					n->objarg = list_make1(makeString($6));
					n->newschema = $9;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER OPERATOR FAMILY any_name USING access_method SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_OPFAMILY;
					n->object = $4;
					n->objarg = list_make1(makeString($6));
					n->newschema = $9;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER TABLE relation_expr SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_TABLE;
					n->relation = $3;
					n->newschema = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER TABLE IF_P EXISTS relation_expr SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_TABLE;
					n->relation = $5;
					n->newschema = $8;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
			| ALTER TEXT_P SEARCH PARSER any_name SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_TSPARSER;
					n->object = $5;
					n->newschema = $8;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER TEXT_P SEARCH DICTIONARY any_name SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_TSDICTIONARY;
					n->object = $5;
					n->newschema = $8;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER TEXT_P SEARCH TEMPLATE any_name SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_TSTEMPLATE;
					n->object = $5;
					n->newschema = $8;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER TEXT_P SEARCH CONFIGURATION any_name SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_TSCONFIGURATION;
					n->object = $5;
					n->newschema = $8;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER SEQUENCE qualified_name SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_SEQUENCE;
					n->relation = $3;
					n->newschema = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER SEQUENCE IF_P EXISTS qualified_name SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_SEQUENCE;
					n->relation = $5;
					n->newschema = $8;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
			| ALTER VIEW qualified_name SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_VIEW;
					n->relation = $3;
					n->newschema = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER VIEW IF_P EXISTS qualified_name SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_VIEW;
					n->relation = $5;
					n->newschema = $8;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
			| ALTER MATERIALIZED VIEW qualified_name SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_MATVIEW;
					n->relation = $4;
					n->newschema = $7;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER MATERIALIZED VIEW IF_P EXISTS qualified_name SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_MATVIEW;
					n->relation = $6;
					n->newschema = $9;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
			| ALTER FOREIGN TABLE relation_expr SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_FOREIGN_TABLE;
					n->relation = $4;
					n->newschema = $7;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			| ALTER FOREIGN TABLE IF_P EXISTS relation_expr SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_FOREIGN_TABLE;
					n->relation = $6;
					n->newschema = $9;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
			| ALTER TYPE_P any_name SET SCHEMA name
				{
					AlterObjectSchemaStmt *n = makeNode(AlterObjectSchemaStmt);
					n->objectType = OBJECT_TYPE;
					n->object = $3;
					n->newschema = $6;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
		;

/*****************************************************************************
 *
 * ALTER THING name OWNER TO newname
 *
 *****************************************************************************/

AlterOwnerStmt: ALTER AGGREGATE func_name aggr_args OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_AGGREGATE;
					n->object = $3;
					n->objarg = extractAggrArgTypes($4);
					n->newowner = $7;
					$$ = (Node *)n;
				}
			| ALTER COLLATION any_name OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_COLLATION;
					n->object = $3;
					n->newowner = $6;
					$$ = (Node *)n;
				}
			| ALTER CONVERSION_P any_name OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_CONVERSION;
					n->object = $3;
					n->newowner = $6;
					$$ = (Node *)n;
				}
			| ALTER DATABASE database_name OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_DATABASE;
					n->object = list_make1(makeString($3));
					n->newowner = $6;
					$$ = (Node *)n;
				}
			| ALTER DOMAIN_P any_name OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_DOMAIN;
					n->object = $3;
					n->newowner = $6;
					$$ = (Node *)n;
				}
			| ALTER FUNCTION function_with_argtypes OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_FUNCTION;
					n->object = $3->funcname;
					n->objarg = $3->funcargs;
					n->newowner = $6;
					$$ = (Node *)n;
				}
			| ALTER opt_procedural LANGUAGE name OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_LANGUAGE;
					n->object = list_make1(makeString($4));
					n->newowner = $7;
					$$ = (Node *)n;
				}
			| ALTER LARGE_P OBJECT_P NumericOnly OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_LARGEOBJECT;
					n->object = list_make1($4);
					n->newowner = $7;
					$$ = (Node *)n;
				}
			| ALTER OPERATOR any_operator oper_argtypes OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_OPERATOR;
					n->object = $3;
					n->objarg = $4;
					n->newowner = $7;
					$$ = (Node *)n;
				}
			| ALTER OPERATOR CLASS any_name USING access_method OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_OPCLASS;
					n->object = $4;
					n->objarg = list_make1(makeString($6));
					n->newowner = $9;
					$$ = (Node *)n;
				}
			| ALTER OPERATOR FAMILY any_name USING access_method OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_OPFAMILY;
					n->object = $4;
					n->objarg = list_make1(makeString($6));
					n->newowner = $9;
					$$ = (Node *)n;
				}
			| ALTER SCHEMA name OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_SCHEMA;
					n->object = list_make1(makeString($3));
					n->newowner = $6;
					$$ = (Node *)n;
				}
			| ALTER TYPE_P any_name OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_TYPE;
					n->object = $3;
					n->newowner = $6;
					$$ = (Node *)n;
				}
			| ALTER TABLESPACE name OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_TABLESPACE;
					n->object = list_make1(makeString($3));
					n->newowner = $6;
					$$ = (Node *)n;
				}
			| ALTER PROTOCOL name OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_EXTPROTOCOL;
					n->object = list_make1(makeString($3));
					n->newowner = $6;
					$$ = (Node *)n;
				}
			| ALTER TEXT_P SEARCH DICTIONARY any_name OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_TSDICTIONARY;
					n->object = $5;
					n->newowner = $8;
					$$ = (Node *)n;
				}
			| ALTER TEXT_P SEARCH CONFIGURATION any_name OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_TSCONFIGURATION;
					n->object = $5;
					n->newowner = $8;
					$$ = (Node *)n;
				}
			| ALTER FOREIGN DATA_P WRAPPER name OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_FDW;
					n->object = list_make1(makeString($5));
					n->newowner = $8;
					$$ = (Node *)n;
				}
			| ALTER SERVER name OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_FOREIGN_SERVER;
					n->object = list_make1(makeString($3));
					n->newowner = $6;
					$$ = (Node *)n;
				}
			| ALTER EVENT TRIGGER name OWNER TO RoleId
				{
					AlterOwnerStmt *n = makeNode(AlterOwnerStmt);
					n->objectType = OBJECT_EVENT_TRIGGER;
					n->object = list_make1(makeString($4));
					n->newowner = $7;
					$$ = (Node *)n;
				}
		;


/*****************************************************************************
 *
 *		QUERY:	Define Rewrite Rule
 *
 *****************************************************************************/

RuleStmt:	CREATE opt_or_replace RULE name AS
			ON event TO qualified_name where_clause
			DO opt_instead RuleActionList
				{
					RuleStmt *n = makeNode(RuleStmt);
					n->replace = $2;
					n->relation = $9;
					n->rulename = $4;
					n->whereClause = $10;
					n->event = $7;
					n->instead = $12;
					n->actions = $13;
					$$ = (Node *)n;
				}
		;

RuleActionList:
			NOTHING									{ $$ = NIL; }
			| RuleActionStmt						{ $$ = list_make1($1); }
			| '(' RuleActionMulti ')'				{ $$ = $2; }
		;

/* the thrashing around here is to discard "empty" statements... */
RuleActionMulti:
			RuleActionMulti ';' RuleActionStmtOrEmpty
				{ if ($3 != NULL)
					$$ = lappend($1, $3);
				  else
					$$ = $1;
				}
			| RuleActionStmtOrEmpty
				{ if ($1 != NULL)
					$$ = list_make1($1);
				  else
					$$ = NIL;
				}
		;

RuleActionStmt:
			SelectStmt
			| InsertStmt
			| UpdateStmt
			| DeleteStmt
			| NotifyStmt
		;

RuleActionStmtOrEmpty:
			RuleActionStmt							{ $$ = $1; }
			|	/*EMPTY*/							{ $$ = NULL; }
		;

event:		SELECT									{ $$ = CMD_SELECT; }
			| UPDATE								{ $$ = CMD_UPDATE; }
			| DELETE_P								{ $$ = CMD_DELETE; }
			| INSERT								{ $$ = CMD_INSERT; }
		 ;

opt_instead:
			INSTEAD									{ $$ = TRUE; }
			| ALSO									{ $$ = FALSE; }
			| /*EMPTY*/								{ $$ = FALSE; }
		;


DropRuleStmt:
			DROP RULE name ON any_name opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_RULE;
					n->objects = list_make1(lappend($5, makeString($3)));
					n->arguments = NIL;
					n->behavior = $6;
					n->missing_ok = false;
					n->concurrent = false;
					$$ = (Node *) n;
				}
			| DROP RULE IF_P EXISTS name ON any_name opt_drop_behavior
				{
					DropStmt *n = makeNode(DropStmt);
					n->removeType = OBJECT_RULE;
					n->objects = list_make1(lappend($7, makeString($5)));
					n->arguments = NIL;
					n->behavior = $8;
					n->missing_ok = true;
					n->concurrent = false;
					$$ = (Node *) n;
				}
		;


/*****************************************************************************
 *
 *		QUERY:
 *				NOTIFY <identifier> can appear both in rule bodies and
 *				as a query-level command
 *
 *****************************************************************************/

NotifyStmt: NOTIFY ColId notify_payload
				{
					NotifyStmt *n = makeNode(NotifyStmt);
					n->conditionname = $2;
					n->payload = $3;
					$$ = (Node *)n;
				}
		;

notify_payload:
			',' Sconst							{ $$ = $2; }
			| /*EMPTY*/							{ $$ = NULL; }
		;

ListenStmt: LISTEN ColId
				{
					ListenStmt *n = makeNode(ListenStmt);
					n->conditionname = $2;
					$$ = (Node *)n;
				}
		;

UnlistenStmt:
			UNLISTEN ColId
				{
					UnlistenStmt *n = makeNode(UnlistenStmt);
					n->conditionname = $2;
					$$ = (Node *)n;
				}
			| UNLISTEN '*'
				{
					UnlistenStmt *n = makeNode(UnlistenStmt);
					n->conditionname = NULL;
					$$ = (Node *)n;
				}
		;


/*****************************************************************************
 *
 *		Transactions:
 *
 *		BEGIN / COMMIT / ROLLBACK
 *		(also older versions END / ABORT)
 *
 *****************************************************************************/

TransactionStmt:
			ABORT_P opt_transaction
				{
					TransactionStmt *n = makeNode(TransactionStmt);
					n->kind = TRANS_STMT_ROLLBACK;
					n->options = NIL;
					$$ = (Node *)n;
				}
			| BEGIN_P opt_transaction transaction_mode_list_or_empty
				{
					TransactionStmt *n = makeNode(TransactionStmt);
					n->kind = TRANS_STMT_BEGIN;
					n->options = $3;
					$$ = (Node *)n;
				}
			| START TRANSACTION transaction_mode_list_or_empty
				{
					TransactionStmt *n = makeNode(TransactionStmt);
					n->kind = TRANS_STMT_START;
					n->options = $3;
					$$ = (Node *)n;
				}
			| COMMIT opt_transaction
				{
					TransactionStmt *n = makeNode(TransactionStmt);
					n->kind = TRANS_STMT_COMMIT;
					n->options = NIL;
					$$ = (Node *)n;
				}
			| END_P opt_transaction
				{
					TransactionStmt *n = makeNode(TransactionStmt);
					n->kind = TRANS_STMT_COMMIT;
					n->options = NIL;
					$$ = (Node *)n;
				}
			| ROLLBACK opt_transaction
				{
					TransactionStmt *n = makeNode(TransactionStmt);
					n->kind = TRANS_STMT_ROLLBACK;
					n->options = NIL;
					$$ = (Node *)n;
				}
			| SAVEPOINT ColId
				{
					TransactionStmt *n = makeNode(TransactionStmt);
					n->kind = TRANS_STMT_SAVEPOINT;
					n->options = list_make1(makeDefElem("savepoint_name",
														(Node *)makeString($2)));
					$$ = (Node *)n;
				}
			| RELEASE SAVEPOINT ColId
				{
					TransactionStmt *n = makeNode(TransactionStmt);
					n->kind = TRANS_STMT_RELEASE;
					n->options = list_make1(makeDefElem("savepoint_name",
														(Node *)makeString($3)));
					$$ = (Node *)n;
				}
			| RELEASE ColId
				{
					TransactionStmt *n = makeNode(TransactionStmt);
					n->kind = TRANS_STMT_RELEASE;
					n->options = list_make1(makeDefElem("savepoint_name",
														(Node *)makeString($2)));
					$$ = (Node *)n;
				}
			| ROLLBACK opt_transaction TO SAVEPOINT ColId
				{
					TransactionStmt *n = makeNode(TransactionStmt);
					n->kind = TRANS_STMT_ROLLBACK_TO;
					n->options = list_make1(makeDefElem("savepoint_name",
														(Node *)makeString($5)));
					$$ = (Node *)n;
				}
			| ROLLBACK opt_transaction TO ColId
				{
					TransactionStmt *n = makeNode(TransactionStmt);
					n->kind = TRANS_STMT_ROLLBACK_TO;
					n->options = list_make1(makeDefElem("savepoint_name",
														(Node *)makeString($4)));
					$$ = (Node *)n;
				}
			| PREPARE TRANSACTION Sconst
				{
					TransactionStmt *n = makeNode(TransactionStmt);
					n->kind = TRANS_STMT_PREPARE;
					n->gid = $3;
					$$ = (Node *)n;
				}
			| COMMIT PREPARED Sconst
				{
					TransactionStmt *n = makeNode(TransactionStmt);
					n->kind = TRANS_STMT_COMMIT_PREPARED;
					n->gid = $3;
					$$ = (Node *)n;
				}
			| ROLLBACK PREPARED Sconst
				{
					TransactionStmt *n = makeNode(TransactionStmt);
					n->kind = TRANS_STMT_ROLLBACK_PREPARED;
					n->gid = $3;
					$$ = (Node *)n;
				}
		;

opt_transaction:	WORK							{}
			| TRANSACTION							{}
			| /*EMPTY*/								{}
		;

transaction_mode_item:
			ISOLATION LEVEL iso_level
					{ $$ = makeDefElem("transaction_isolation",
									   makeStringConst($3, @3)); }
			| READ ONLY
					{ $$ = makeDefElem("transaction_read_only",
									   makeIntConst(TRUE, @1)); }
			| READ WRITE
					{ $$ = makeDefElem("transaction_read_only",
									   makeIntConst(FALSE, @1)); }
			| DEFERRABLE
					{ $$ = makeDefElem("transaction_deferrable",
									   makeIntConst(TRUE, @1)); }
			| NOT DEFERRABLE
					{ $$ = makeDefElem("transaction_deferrable",
									   makeIntConst(FALSE, @1)); }
		;

/* Syntax with commas is SQL-spec, without commas is Postgres historical */
transaction_mode_list:
			transaction_mode_item
					{ $$ = list_make1($1); }
			| transaction_mode_list ',' transaction_mode_item
					{ $$ = lappend($1, $3); }
			| transaction_mode_list transaction_mode_item
					{ $$ = lappend($1, $2); }
		;

transaction_mode_list_or_empty:
			transaction_mode_list
			| /* EMPTY */
					{ $$ = NIL; }
		;


/*****************************************************************************
 *
 *	QUERY:
 *		CREATE [ OR REPLACE ] [ TEMP ] VIEW <viewname> '('target-list ')'
 *			AS <query> [ WITH [ CASCADED | LOCAL ] CHECK OPTION ]
 *
 *****************************************************************************/

ViewStmt: CREATE OptTemp VIEW qualified_name opt_column_list opt_reloptions
				AS SelectStmt opt_check_option
				{
					ViewStmt *n = makeNode(ViewStmt);
					n->view = $4;
					n->view->relpersistence = $2;
					n->aliases = $5;
					n->query = $8;
					n->replace = false;
					n->options = $6;
					n->withCheckOption = $9;
					$$ = (Node *) n;
				}
		| CREATE OR REPLACE OptTemp VIEW qualified_name opt_column_list opt_reloptions
				AS SelectStmt opt_check_option
				{
					ViewStmt *n = makeNode(ViewStmt);
					n->view = $6;
					n->view->relpersistence = $4;
					n->aliases = $7;
					n->query = $10;
					n->replace = true;
					n->options = $8;
					n->withCheckOption = $11;
					$$ = (Node *) n;
				}
		| CREATE OptTemp RECURSIVE VIEW qualified_name '(' columnList ')' opt_reloptions
				AS SelectStmt opt_check_option
				{
					ViewStmt *n = makeNode(ViewStmt);
					n->view = $5;
					n->view->relpersistence = $2;
					n->aliases = $7;
					n->query = makeRecursiveViewSelect(n->view->relname, n->aliases, $11);
					n->replace = false;
					n->options = $9;
					n->withCheckOption = $12;
					if (n->withCheckOption != NO_CHECK_OPTION)
						ereport(ERROR,
								(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
								 errmsg("WITH CHECK OPTION not supported on recursive views"),
								 parser_errposition(@12)));
					$$ = (Node *) n;
				}
		| CREATE OR REPLACE OptTemp RECURSIVE VIEW qualified_name '(' columnList ')' opt_reloptions
				AS SelectStmt opt_check_option
				{
					ViewStmt *n = makeNode(ViewStmt);
					n->view = $7;
					n->view->relpersistence = $4;
					n->aliases = $9;
					n->query = makeRecursiveViewSelect(n->view->relname, n->aliases, $13);
					n->replace = true;
					n->options = $11;
					n->withCheckOption = $14;
					if (n->withCheckOption != NO_CHECK_OPTION)
						ereport(ERROR,
								(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
								 errmsg("WITH CHECK OPTION not supported on recursive views"),
								 parser_errposition(@14)));
					$$ = (Node *) n;
				}
		;

opt_check_option:
		WITH CHECK OPTION				{ $$ = CASCADED_CHECK_OPTION; }
		| WITH CASCADED CHECK OPTION	{ $$ = CASCADED_CHECK_OPTION; }
		| WITH LOCAL CHECK OPTION		{ $$ = LOCAL_CHECK_OPTION; }
		| /* EMPTY */					{ $$ = NO_CHECK_OPTION; }
		;

/*****************************************************************************
 *
 *		QUERY:
 *				LOAD "filename"
 *
 *****************************************************************************/

LoadStmt:	LOAD file_name
				{
					LoadStmt *n = makeNode(LoadStmt);
					n->filename = $2;
					$$ = (Node *)n;
				}
		;


/*****************************************************************************
 *
 *		CREATE DATABASE
 *
 *****************************************************************************/

CreatedbStmt:
			CREATE DATABASE database_name opt_with createdb_opt_list
				{
					CreatedbStmt *n = makeNode(CreatedbStmt);
					n->dbname = $3;
					n->options = $5;
					$$ = (Node *)n;
				}
		;

createdb_opt_list:
			createdb_opt_list createdb_opt_item		{ $$ = lappend($1, $2); }
			| /* EMPTY */							{ $$ = NIL; }
		;

createdb_opt_item:
			TABLESPACE opt_equal name
				{
					$$ = makeDefElem("tablespace", (Node *)makeString($3));
				}
			| TABLESPACE opt_equal DEFAULT
				{
					$$ = makeDefElem("tablespace", NULL);
				}
			| LOCATION opt_equal Sconst
				{
					$$ = makeDefElem("location", (Node *)makeString($3));
				}
			| LOCATION opt_equal DEFAULT
				{
					$$ = makeDefElem("location", NULL);
				}
			| TEMPLATE opt_equal name
				{
					$$ = makeDefElem("template", (Node *)makeString($3));
				}
			| TEMPLATE opt_equal DEFAULT
				{
					$$ = makeDefElem("template", NULL);
				}
			| ENCODING opt_equal Sconst
				{
					$$ = makeDefElem("encoding", (Node *)makeString($3));
				}
			| ENCODING opt_equal Iconst
				{
					$$ = makeDefElem("encoding", (Node *)makeInteger($3));
				}
			| ENCODING opt_equal DEFAULT
				{
					$$ = makeDefElem("encoding", NULL);
				}
			| LC_COLLATE_P opt_equal Sconst
				{
					$$ = makeDefElem("lc_collate", (Node *)makeString($3));
				}
			| LC_COLLATE_P opt_equal DEFAULT
				{
					$$ = makeDefElem("lc_collate", NULL);
				}
			| LC_CTYPE_P opt_equal Sconst
				{
					$$ = makeDefElem("lc_ctype", (Node *)makeString($3));
				}
			| LC_CTYPE_P opt_equal DEFAULT
				{
					$$ = makeDefElem("lc_ctype", NULL);
				}
			| CONNECTION LIMIT opt_equal SignedIconst
				{
					$$ = makeDefElem("connectionlimit", (Node *)makeInteger($4));
				}
			| OWNER opt_equal name
				{
					$$ = makeDefElem("owner", (Node *)makeString($3));
				}
			| OWNER opt_equal DEFAULT
				{
					$$ = makeDefElem("owner", NULL);
				}
		;

/*
 *	Though the equals sign doesn't match other WITH options, pg_dump uses
 *	equals for backward compatibility, and it doesn't seem worth removing it.
 */
opt_equal:	'='										{}
			| /*EMPTY*/								{}
		;


/*****************************************************************************
 *
 *		ALTER DATABASE
 *
 *****************************************************************************/

AlterDatabaseStmt:
			ALTER DATABASE database_name opt_with alterdb_opt_list
				 {
					AlterDatabaseStmt *n = makeNode(AlterDatabaseStmt);
					n->dbname = $3;
					n->options = $5;
					$$ = (Node *)n;
				 }
			| ALTER DATABASE database_name SET TABLESPACE name
				 {
					AlterDatabaseStmt *n = makeNode(AlterDatabaseStmt);
					n->dbname = $3;
					n->options = list_make1(makeDefElem("tablespace",
													(Node *)makeString($6)));
					$$ = (Node *)n;
				 }
		;

AlterDatabaseSetStmt:
			ALTER DATABASE database_name SetResetClause
				{
					AlterDatabaseSetStmt *n = makeNode(AlterDatabaseSetStmt);
					n->dbname = $3;
					n->setstmt = $4;
					$$ = (Node *)n;
				}
		;


alterdb_opt_list:
			alterdb_opt_list alterdb_opt_item		{ $$ = lappend($1, $2); }
			| /* EMPTY */							{ $$ = NIL; }
		;

alterdb_opt_item:
			CONNECTION LIMIT opt_equal SignedIconst
				{
					$$ = makeDefElem("connectionlimit", (Node *)makeInteger($4));
				}
		;


/*****************************************************************************
 *
 *		DROP DATABASE [ IF EXISTS ]
 *
 * This is implicitly CASCADE, no need for drop behavior
 *****************************************************************************/

DropdbStmt: DROP DATABASE database_name
				{
					DropdbStmt *n = makeNode(DropdbStmt);
					n->dbname = $3;
					n->missing_ok = FALSE;
					$$ = (Node *)n;
				}
			| DROP DATABASE IF_P EXISTS database_name
				{
					DropdbStmt *n = makeNode(DropdbStmt);
					n->dbname = $5;
					n->missing_ok = TRUE;
					$$ = (Node *)n;
				}
		;


/*****************************************************************************
 *
 *		ALTER SYSTEM
 *
 * This is used to change configuration parameters persistently.
 *****************************************************************************/

AlterSystemStmt:
			ALTER SYSTEM_P SET generic_set
				{
					AlterSystemStmt *n = makeNode(AlterSystemStmt);
					n->setstmt = $4;
					$$ = (Node *)n;
				}
			| ALTER SYSTEM_P RESET generic_reset
				{
					AlterSystemStmt *n = makeNode(AlterSystemStmt);
					n->setstmt = $4;
					$$ = (Node *)n;
				}
		;


/*****************************************************************************
 *
 * Manipulate a domain
 *
 *****************************************************************************/

CreateDomainStmt:
			CREATE DOMAIN_P any_name opt_as Typename ColQualList
				{
					CreateDomainStmt *n = makeNode(CreateDomainStmt);
					n->domainname = $3;
					n->typeName = $5;
					SplitColQualList($6, &n->constraints, &n->collClause,
									 yyscanner);
					$$ = (Node *)n;
				}
		;

AlterDomainStmt:
			/* ALTER DOMAIN <domain> {SET DEFAULT <expr>|DROP DEFAULT} */
			ALTER DOMAIN_P any_name alter_column_default
				{
					AlterDomainStmt *n = makeNode(AlterDomainStmt);
					n->subtype = 'T';
					n->typeName = $3;
					n->def = $4;
					$$ = (Node *)n;
				}
			/* ALTER DOMAIN <domain> DROP NOT NULL */
			| ALTER DOMAIN_P any_name DROP NOT NULL_P
				{
					AlterDomainStmt *n = makeNode(AlterDomainStmt);
					n->subtype = 'N';
					n->typeName = $3;
					$$ = (Node *)n;
				}
			/* ALTER DOMAIN <domain> SET NOT NULL */
			| ALTER DOMAIN_P any_name SET NOT NULL_P
				{
					AlterDomainStmt *n = makeNode(AlterDomainStmt);
					n->subtype = 'O';
					n->typeName = $3;
					$$ = (Node *)n;
				}
			/* ALTER DOMAIN <domain> ADD CONSTRAINT ... */
			| ALTER DOMAIN_P any_name ADD_P TableConstraint
				{
					AlterDomainStmt *n = makeNode(AlterDomainStmt);
					n->subtype = 'C';
					n->typeName = $3;
					n->def = $5;
					$$ = (Node *)n;
				}
			/* ALTER DOMAIN <domain> DROP CONSTRAINT <name> [RESTRICT|CASCADE] */
			| ALTER DOMAIN_P any_name DROP CONSTRAINT name opt_drop_behavior
				{
					AlterDomainStmt *n = makeNode(AlterDomainStmt);
					n->subtype = 'X';
					n->typeName = $3;
					n->name = $6;
					n->behavior = $7;
					n->missing_ok = false;
					$$ = (Node *)n;
				}
			/* ALTER DOMAIN <domain> DROP CONSTRAINT IF EXISTS <name> [RESTRICT|CASCADE] */
			| ALTER DOMAIN_P any_name DROP CONSTRAINT IF_P EXISTS name opt_drop_behavior
				{
					AlterDomainStmt *n = makeNode(AlterDomainStmt);
					n->subtype = 'X';
					n->typeName = $3;
					n->name = $8;
					n->behavior = $9;
					n->missing_ok = true;
					$$ = (Node *)n;
				}
			/* ALTER DOMAIN <domain> VALIDATE CONSTRAINT <name> */
			| ALTER DOMAIN_P any_name VALIDATE CONSTRAINT name
				{
					AlterDomainStmt *n = makeNode(AlterDomainStmt);
					n->subtype = 'V';
					n->typeName = $3;
					n->name = $6;
					$$ = (Node *)n;
				}
			;

opt_as:		AS										{}
			| /* EMPTY */							{}
		;


/*****************************************************************************
 *
 * Manipulate a text search dictionary or configuration
 *
 *****************************************************************************/

AlterTSDictionaryStmt:
			ALTER TEXT_P SEARCH DICTIONARY any_name definition
				{
					AlterTSDictionaryStmt *n = makeNode(AlterTSDictionaryStmt);
					n->dictname = $5;
					n->options = $6;
					$$ = (Node *)n;
				}
		;

AlterTSConfigurationStmt:
			ALTER TEXT_P SEARCH CONFIGURATION any_name ADD_P MAPPING FOR name_list WITH any_name_list
				{
					AlterTSConfigurationStmt *n = makeNode(AlterTSConfigurationStmt);
					n->cfgname = $5;
					n->tokentype = $9;
					n->dicts = $11;
					n->override = false;
					n->replace = false;
					$$ = (Node*)n;
				}
			| ALTER TEXT_P SEARCH CONFIGURATION any_name ALTER MAPPING FOR name_list WITH any_name_list
				{
					AlterTSConfigurationStmt *n = makeNode(AlterTSConfigurationStmt);
					n->cfgname = $5;
					n->tokentype = $9;
					n->dicts = $11;
					n->override = true;
					n->replace = false;
					$$ = (Node*)n;
				}
			| ALTER TEXT_P SEARCH CONFIGURATION any_name ALTER MAPPING REPLACE any_name WITH any_name
				{
					AlterTSConfigurationStmt *n = makeNode(AlterTSConfigurationStmt);
					n->cfgname = $5;
					n->tokentype = NIL;
					n->dicts = list_make2($9,$11);
					n->override = false;
					n->replace = true;
					$$ = (Node*)n;
				}
			| ALTER TEXT_P SEARCH CONFIGURATION any_name ALTER MAPPING FOR name_list REPLACE any_name WITH any_name
				{
					AlterTSConfigurationStmt *n = makeNode(AlterTSConfigurationStmt);
					n->cfgname = $5;
					n->tokentype = $9;
					n->dicts = list_make2($11,$13);
					n->override = false;
					n->replace = true;
					$$ = (Node*)n;
				}
			| ALTER TEXT_P SEARCH CONFIGURATION any_name DROP MAPPING FOR name_list
				{
					AlterTSConfigurationStmt *n = makeNode(AlterTSConfigurationStmt);
					n->cfgname = $5;
					n->tokentype = $9;
					n->missing_ok = false;
					$$ = (Node*)n;
				}
			| ALTER TEXT_P SEARCH CONFIGURATION any_name DROP MAPPING IF_P EXISTS FOR name_list
				{
					AlterTSConfigurationStmt *n = makeNode(AlterTSConfigurationStmt);
					n->cfgname = $5;
					n->tokentype = $11;
					n->missing_ok = true;
					$$ = (Node*)n;
				}
		;


/*****************************************************************************
 *
 * Manipulate a conversion
 *
 *		CREATE [DEFAULT] CONVERSION <conversion_name>
 *		FOR <encoding_name> TO <encoding_name> FROM <func_name>
 *
 *****************************************************************************/

CreateConversionStmt:
			CREATE opt_default CONVERSION_P any_name FOR Sconst
			TO Sconst FROM any_name
			{
				CreateConversionStmt *n = makeNode(CreateConversionStmt);
				n->conversion_name = $4;
				n->for_encoding_name = $6;
				n->to_encoding_name = $8;
				n->func_name = $10;
				n->def = $2;
				$$ = (Node *)n;
			}
		;

/*****************************************************************************
 *
 *		QUERY:
 *				CLUSTER [VERBOSE] <qualified_name> [ USING <index_name> ]
 *				CLUSTER [VERBOSE]
 *				CLUSTER [VERBOSE] <index_name> ON <qualified_name> (for pre-8.3)
 *
 *****************************************************************************/

ClusterStmt:
			CLUSTER opt_verbose qualified_name cluster_index_specification
				{
					ClusterStmt *n = makeNode(ClusterStmt);
					n->relation = $3;
					n->indexname = $4;
					n->verbose = $2;
					$$ = (Node*)n;
				}
			| CLUSTER opt_verbose
				{
					ClusterStmt *n = makeNode(ClusterStmt);
					n->relation = NULL;
					n->indexname = NULL;
					n->verbose = $2;
					$$ = (Node*)n;
				}
			/* kept for pre-8.3 compatibility */
			| CLUSTER opt_verbose index_name ON qualified_name
				{
					ClusterStmt *n = makeNode(ClusterStmt);
					n->relation = $5;
					n->indexname = $3;
					n->verbose = $2;
					$$ = (Node*)n;
				}
		;

cluster_index_specification:
			USING index_name		{ $$ = $2; }
			| /*EMPTY*/				{ $$ = NULL; }
		;


/*****************************************************************************
 *
 *		QUERY:
 *				VACUUM
 *				ANALYZE
 *
 *****************************************************************************/

VacuumStmt: VACUUM opt_full opt_freeze opt_verbose
				{
					VacuumStmt *n = makeNode(VacuumStmt);
					n->options = VACOPT_VACUUM;
					if ($2)
						n->options |= VACOPT_FULL;
					if ($4)
						n->options |= VACOPT_VERBOSE;
					n->freeze_min_age = $3 ? 0 : -1;
					n->freeze_table_age = $3 ? 0 : -1;
					n->multixact_freeze_min_age = $3 ? 0 : -1;
					n->multixact_freeze_table_age = $3 ? 0 : -1;
					n->relation = NULL;
					n->va_cols = NIL;
					$$ = (Node *)n;
				}
			| VACUUM opt_full opt_freeze opt_verbose qualified_name
				{
					VacuumStmt *n = makeNode(VacuumStmt);
					n->options = VACOPT_VACUUM;
					if ($2)
						n->options |= VACOPT_FULL;
					if ($4)
						n->options |= VACOPT_VERBOSE;
					n->freeze_min_age = $3 ? 0 : -1;
					n->freeze_table_age = $3 ? 0 : -1;
					n->multixact_freeze_min_age = $3 ? 0 : -1;
					n->multixact_freeze_table_age = $3 ? 0 : -1;
					n->relation = $5;
					n->va_cols = NIL;
					$$ = (Node *)n;
				}
			| VACUUM opt_full opt_freeze opt_verbose AnalyzeStmt
				{
					VacuumStmt *n = (VacuumStmt *) $5;
					n->options |= VACOPT_VACUUM;
					if ($2)
						n->options |= VACOPT_FULL;
					if ($4)
						n->options |= VACOPT_VERBOSE;
					n->freeze_min_age = $3 ? 0 : -1;
					n->freeze_table_age = $3 ? 0 : -1;
					n->multixact_freeze_min_age = $3 ? 0 : -1;
					n->multixact_freeze_table_age = $3 ? 0 : -1;
					$$ = (Node *)n;
				}
			| VACUUM '(' vacuum_option_list ')'
				{
					VacuumStmt *n = makeNode(VacuumStmt);
					n->options = VACOPT_VACUUM | $3;
					if (n->options & VACOPT_FREEZE)
					{
						n->freeze_min_age = n->freeze_table_age = 0;
						n->multixact_freeze_min_age = 0;
						n->multixact_freeze_table_age = 0;
					}
					else
					{
						n->freeze_min_age = n->freeze_table_age = -1;
						n->multixact_freeze_min_age = -1;
						n->multixact_freeze_table_age = -1;
					}
					n->relation = NULL;
					n->va_cols = NIL;
					$$ = (Node *) n;
				}
			| VACUUM '(' vacuum_option_list ')' qualified_name opt_name_list
				{
					VacuumStmt *n = makeNode(VacuumStmt);
					n->options = VACOPT_VACUUM | $3;
					if (n->options & VACOPT_FREEZE)
					{
						n->freeze_min_age = n->freeze_table_age = 0;
						n->multixact_freeze_min_age = 0;
						n->multixact_freeze_table_age = 0;
					}
					else
					{
						n->freeze_min_age = n->freeze_table_age = -1;
						n->multixact_freeze_min_age = -1;
						n->multixact_freeze_table_age = -1;
					}
					n->relation = $5;
					n->va_cols = $6;
					if (n->va_cols != NIL)	/* implies analyze */
						n->options |= VACOPT_ANALYZE;
					$$ = (Node *) n;
				}
		;

vacuum_option_list:
			vacuum_option_elem								{ $$ = $1; }
			| vacuum_option_list ',' vacuum_option_elem		{ $$ = $1 | $3; }
		;

vacuum_option_elem:
			analyze_keyword		{ $$ = VACOPT_ANALYZE; }
			| VERBOSE			{ $$ = VACOPT_VERBOSE; }
			| FREEZE			{ $$ = VACOPT_FREEZE; }
			| FULL				{ $$ = VACOPT_FULL; }
		;

AnalyzeStmt:
			analyze_keyword opt_verbose opt_rootonly_all
				{
					VacuumStmt *n = makeNode(VacuumStmt);
					n->options = VACOPT_ANALYZE;
					if ($2)
						n->options |= VACOPT_VERBOSE;
					if ($3)
						n->options |= VACOPT_ROOTONLY;
					n->freeze_min_age = -1;
					n->freeze_table_age = -1;
					n->multixact_freeze_min_age = -1;
					n->multixact_freeze_table_age = -1;
					n->relation = NULL;
					n->va_cols = NIL;
					$$ = (Node *)n;
				}
			| analyze_keyword opt_verbose qualified_name opt_name_list
				{
					VacuumStmt *n = makeNode(VacuumStmt);
					n->options = VACOPT_ANALYZE;
					if ($2)
						n->options |= VACOPT_VERBOSE;
					n->freeze_min_age = -1;
					n->freeze_table_age = -1;
					n->multixact_freeze_min_age = -1;
					n->multixact_freeze_table_age = -1;
					n->relation = $3;
					n->va_cols = $4;
					$$ = (Node *)n;
				}
			| analyze_keyword opt_verbose FULLSCAN qualified_name opt_name_list
				{
					VacuumStmt *n = makeNode(VacuumStmt);
					n->options = VACOPT_ANALYZE;
					if ($2)
						n->options |= VACOPT_VERBOSE;
					n->options |= VACOPT_FULLSCAN;
					n->freeze_min_age = -1;
					n->relation = $4;
					n->va_cols = $5;
					$$ = (Node *)n;
				}
			| analyze_keyword opt_verbose ROOTPARTITION qualified_name opt_name_list
				{
					VacuumStmt *n = makeNode(VacuumStmt);
					n->options = VACOPT_ANALYZE;
					if ($2)
						n->options |= VACOPT_VERBOSE;
					n->options |= VACOPT_ROOTONLY;
					n->freeze_min_age = -1;
					n->relation = $4;
					n->va_cols = $5;
					$$ = (Node *)n;
				}
		;

analyze_keyword:
			ANALYZE									{}
			| ANALYSE /* British */					{}
		;

opt_verbose:
			VERBOSE									{ $$ = TRUE; }
			| /*EMPTY*/								{ $$ = FALSE; }
		;

opt_rootonly_all:
			ROOTPARTITION ALL						{ $$ = TRUE; }
			| /*EMPTY*/								{ $$ = FALSE; }
		;
			
opt_full:	FULL									{ $$ = TRUE; }
			| /*EMPTY*/								{ $$ = FALSE; }
		;

opt_freeze: FREEZE									{ $$ = TRUE; }
			| /*EMPTY*/								{ $$ = FALSE; }
		;

opt_name_list:
			'(' name_list ')'						{ $$ = $2; }
			| /*EMPTY*/								{ $$ = NIL; }
		;


/*****************************************************************************
 *
 *		QUERY:
 *				EXPLAIN [ANALYZE] [VERBOSE] query
 *				EXPLAIN ( options ) query
 *
 *****************************************************************************/

ExplainStmt:
		EXPLAIN ExplainableStmt
				{
					ExplainStmt *n = makeNode(ExplainStmt);
					n->query = $2;
					n->options = NIL;
					$$ = (Node *) n;
				}
		| EXPLAIN analyze_keyword opt_verbose opt_dxl ExplainableStmt
				{
					ExplainStmt *n = makeNode(ExplainStmt);
					n->query = $5;
					n->options = list_make1(makeDefElem("analyze", NULL));
					if ($3)
						n->options = lappend(n->options,
											 makeDefElem("verbose", NULL));
					if ($4)
						n->options = lappend(n->options,
											 makeDefElem("dxl", NULL));
					$$ = (Node *) n;
				}
		| EXPLAIN VERBOSE opt_dxl ExplainableStmt
				{
					ExplainStmt *n = makeNode(ExplainStmt);
					n->query = $4;
					n->options = list_make1(makeDefElem("verbose", NULL));
					if ($3)
						n->options = lappend(n->options,
											 makeDefElem("dxl", NULL));
					$$ = (Node *) n;
				}
		| EXPLAIN '(' explain_option_list ')' ExplainableStmt
				{
					ExplainStmt *n = makeNode(ExplainStmt);
					n->query = $5;
					n->options = $3;
					$$ = (Node *) n;
				}
		;

ExplainableStmt:
			SelectStmt
			| InsertStmt
			| UpdateStmt
			| DeleteStmt
			| DeclareCursorStmt
			| CreateAsStmt
			| CreateMatViewStmt
			| RefreshMatViewStmt
			| ExecuteStmt					/* by default all are $$=$1 */
			| CreateStmt
				{
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("cannot EXPLAIN CREATE TABLE without AS "
							 		"clause")));
				}
		;

opt_dxl:	DXL										{ $$ = TRUE; }
			| /*EMPTY*/								{ $$ = FALSE; }
		;

explain_option_list:
			explain_option_elem
				{
					$$ = list_make1($1);
				}
			| explain_option_list ',' explain_option_elem
				{
					$$ = lappend($1, $3);
				}
		;

explain_option_elem:
			explain_option_name explain_option_arg
				{
					$$ = makeDefElem($1, $2);
				}
		;

explain_option_name:
			NonReservedWord			{ $$ = $1; }
			| analyze_keyword		{ $$ = "analyze"; }
		;

explain_option_arg:
			opt_boolean_or_string	{ $$ = (Node *) makeString($1); }
			| NumericOnly			{ $$ = (Node *) $1; }
			| /* EMPTY */			{ $$ = NULL; }
		;

/*****************************************************************************
 *
 *		QUERY:
 *				PREPARE <plan_name> [(args, ...)] AS <query>
 *
 *****************************************************************************/

PrepareStmt: PREPARE name prep_type_clause AS PreparableStmt
				{
					PrepareStmt *n = makeNode(PrepareStmt);
					n->name = $2;
					n->argtypes = $3;
					n->query = $5;
					$$ = (Node *) n;
				}
		;

prep_type_clause: '(' type_list ')'			{ $$ = $2; }
				| /* EMPTY */				{ $$ = NIL; }
		;

PreparableStmt:
			SelectStmt
			| InsertStmt
			| UpdateStmt
			| DeleteStmt					/* by default all are $$=$1 */
		;

/*****************************************************************************
 *
 * EXECUTE <plan_name> [(params, ...)]
 * CREATE TABLE <name> AS EXECUTE <plan_name> [(params, ...)]
 *
 *****************************************************************************/

ExecuteStmt: EXECUTE name execute_param_clause
				{
					ExecuteStmt *n = makeNode(ExecuteStmt);
					n->name = $2;
					n->params = $3;
					$$ = (Node *) n;
				}
			| CREATE OptTemp TABLE create_as_target AS
				EXECUTE name execute_param_clause opt_with_data OptDistributedBy
				{
					CreateTableAsStmt *ctas = makeNode(CreateTableAsStmt);
					ExecuteStmt *n = makeNode(ExecuteStmt);
					n->name = $7;
					n->params = $8;
					ctas->query = (Node *) n;
					ctas->into = $4;
					ctas->relkind = OBJECT_TABLE;
					ctas->is_select_into = false;
					/* cram additional flags into the IntoClause */
					$4->rel->relpersistence = $2;
					ctas->into->distributedBy = $10;
					$4->skipData = !($9);
					$$ = (Node *) ctas;
				}
		;

execute_param_clause: '(' expr_list ')'				{ $$ = $2; }
					| /* EMPTY */					{ $$ = NIL; }
					;

/*****************************************************************************
 *
 *		QUERY:
 *				DEALLOCATE [PREPARE] <plan_name>
 *
 *****************************************************************************/

DeallocateStmt: DEALLOCATE name
					{
						DeallocateStmt *n = makeNode(DeallocateStmt);
						n->name = $2;
						$$ = (Node *) n;
					}
				| DEALLOCATE PREPARE name
					{
						DeallocateStmt *n = makeNode(DeallocateStmt);
						n->name = $3;
						$$ = (Node *) n;
					}
				| DEALLOCATE ALL
					{
						DeallocateStmt *n = makeNode(DeallocateStmt);
						n->name = NULL;
						$$ = (Node *) n;
					}
				| DEALLOCATE PREPARE ALL
					{
						DeallocateStmt *n = makeNode(DeallocateStmt);
						n->name = NULL;
						$$ = (Node *) n;
					}
		;

/*****************************************************************************
 *
 */




cdb_string_list:
			cdb_string							{ $$ = list_make1($1); }  
			| cdb_string_list ',' cdb_string
				{
					if (list_member($1, $3))
						ereport(ERROR,
								(errcode(ERRCODE_INVALID_TABLE_DEFINITION),
								 errmsg("duplicate location uri"),
								 parser_errposition(@3)));
					$$ = lappend($1, $3);
				}
		;


cdb_string:
			Sconst
				{
					$$ = (Node *) makeString($1);
				}
		;

/*****************************************************************************
 *
 *		QUERY:
 *				INSERT STATEMENTS
 *
 *****************************************************************************/

InsertStmt:
			opt_with_clause INSERT INTO qualified_name insert_rest returning_clause
				{
					$5->relation = $4;
					$5->returningList = $6;
					$5->withClause = $1;
					$$ = (Node *) $5;
				}
		;

insert_rest:
			SelectStmt
				{
					$$ = makeNode(InsertStmt);
					$$->cols = NIL;
					$$->selectStmt = $1;
				}
			| '(' insert_column_list ')' SelectStmt
				{
					$$ = makeNode(InsertStmt);
					$$->cols = $2;
					$$->selectStmt = $4;
				}
			| DEFAULT VALUES
				{
					$$ = makeNode(InsertStmt);
					$$->cols = NIL;
					$$->selectStmt = NULL;
				}
		;

insert_column_list:
			insert_column_item
					{ $$ = list_make1($1); }
			| insert_column_list ',' insert_column_item
					{ $$ = lappend($1, $3); }
		;

insert_column_item:
			ColId opt_indirection
				{
					$$ = makeNode(ResTarget);
					$$->name = $1;
					$$->indirection = check_indirection($2, yyscanner);
					$$->val = NULL;
					$$->location = @1;
				}
		;

returning_clause:
			RETURNING target_list		{ $$ = $2; }
			| /* EMPTY */				{ $$ = NIL; }
		;


/*****************************************************************************
 *
 *		QUERY:
 *				DELETE STATEMENTS
 *
 *****************************************************************************/

DeleteStmt: opt_with_clause DELETE_P FROM relation_expr_opt_alias
			using_clause where_or_current_clause returning_clause
				{
					DeleteStmt *n = makeNode(DeleteStmt);
					n->relation = $4;
					n->usingClause = $5;
					n->whereClause = $6;
					n->returningList = $7;
					n->withClause = $1;
					$$ = (Node *)n;
				}
		;

using_clause:
				USING from_list						{ $$ = $2; }
			| /*EMPTY*/								{ $$ = NIL; }
		;


/*****************************************************************************
 *
 *		QUERY:
 *				LOCK TABLE
 *
 *****************************************************************************/

LockStmt:	LOCK_P opt_table relation_expr_list opt_lock opt_nowait opt_masteronly
				{
					LockStmt *n = makeNode(LockStmt);

					n->relations = $3;
					n->mode = $4;
					n->nowait = $5;
					n->masteronly = $6;
					if (n->masteronly && n->mode != AccessShareLock)
					{
						ereport(ERROR,
								(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
								errmsg("provided lock mode is not supported for MASTER ONLY"),
							 	errhint("Only ACCESS SHARE mode is supported for MASTER ONLY."),
								parser_errposition(@4)));
					}
					$$ = (Node *)n;
				}
		;

opt_lock:	IN_P lock_type MODE				{ $$ = $2; }
			| /*EMPTY*/						{ $$ = AccessExclusiveLock; }
		;

lock_type:	ACCESS SHARE					{ $$ = AccessShareLock; }
			| ROW SHARE						{ $$ = RowShareLock; }
			| ROW EXCLUSIVE					{ $$ = RowExclusiveLock; }
			| SHARE UPDATE EXCLUSIVE		{ $$ = ShareUpdateExclusiveLock; }
			| SHARE							{ $$ = ShareLock; }
			| SHARE ROW EXCLUSIVE			{ $$ = ShareRowExclusiveLock; }
			| EXCLUSIVE						{ $$ = ExclusiveLock; }
			| ACCESS EXCLUSIVE				{ $$ = AccessExclusiveLock; }
		;

opt_nowait:	NOWAIT							{ $$ = TRUE; }
			| /*EMPTY*/						{ $$ = FALSE; }
		;

opt_masteronly: MASTER ONLY					{ $$ = true; }
			| /*EMPTY*/						{ $$ = false; }
		;

/*****************************************************************************
 *
 *		QUERY:
 *				UpdateStmt (UPDATE)
 *
 *****************************************************************************/

UpdateStmt: opt_with_clause UPDATE relation_expr_opt_alias
			SET set_clause_list
			from_clause
			where_or_current_clause
			returning_clause
				{
					UpdateStmt *n = makeNode(UpdateStmt);
					n->relation = $3;
					n->targetList = $5;
					n->fromClause = $6;
					n->whereClause = $7;
					n->returningList = $8;
					n->withClause = $1;
					$$ = (Node *)n;
				}
		;

set_clause_list:
			set_clause							{ $$ = $1; }
			| set_clause_list ',' set_clause	{ $$ = list_concat($1,$3); }
		;

set_clause:
			single_set_clause						{ $$ = list_make1($1); }
			| multiple_set_clause					{ $$ = $1; }
		;

single_set_clause:
			set_target '=' ctext_expr
				{
					$$ = $1;
					$$->val = (Node *) $3;
				}
		;

multiple_set_clause:
			'(' set_target_list ')' '=' ctext_row
				{
					ListCell *col_cell;
					ListCell *val_cell;

					/*
					 * Break the ctext_row apart, merge individual expressions
					 * into the destination ResTargets.  XXX this approach
					 * cannot work for general row expressions as sources.
					 */
					if (list_length($2) != list_length($5))
						ereport(ERROR,
								(errcode(ERRCODE_SYNTAX_ERROR),
								 errmsg("number of columns does not match number of values"),
								 parser_errposition(@1)));
					forboth(col_cell, $2, val_cell, $5)
					{
						ResTarget *res_col = (ResTarget *) lfirst(col_cell);
						Node *res_val = (Node *) lfirst(val_cell);

						res_col->val = res_val;
					}

					$$ = $2;
				}
		;

set_target:
			ColId opt_indirection
				{
					$$ = makeNode(ResTarget);
					$$->name = $1;
					$$->indirection = check_indirection($2, yyscanner);
					$$->val = NULL;	/* upper production sets this */
					$$->location = @1;
				}
		;

set_target_list:
			set_target								{ $$ = list_make1($1); }
			| set_target_list ',' set_target		{ $$ = lappend($1,$3); }
		;


/*****************************************************************************
 *
 *		QUERY:
 *				CURSOR STATEMENTS
 *
 *****************************************************************************/
DeclareCursorStmt: DECLARE cursor_name cursor_options CURSOR opt_hold FOR SelectStmt
				{
					DeclareCursorStmt *n = makeNode(DeclareCursorStmt);
					n->portalname = $2;
					/* currently we always set FAST_PLAN option */
					n->options = $3 | $5 | CURSOR_OPT_FAST_PLAN;
					n->query = $7;
					$$ = (Node *)n;
				}
		;

cursor_name:	name						{ $$ = $1; }
		;

cursor_options: /*EMPTY*/					{ $$ = 0; }
			| cursor_options NO SCROLL		{ $$ = $1 | CURSOR_OPT_NO_SCROLL; }
			| cursor_options SCROLL			{ $$ = $1 | CURSOR_OPT_SCROLL; }
			| cursor_options BINARY			{ $$ = $1 | CURSOR_OPT_BINARY; }
			| cursor_options INSENSITIVE	{ $$ = $1 | CURSOR_OPT_INSENSITIVE; }
			| cursor_options PARALLEL RETRIEVE	{ $$ = $1 | CURSOR_OPT_PARALLEL_RETRIEVE; }
		;

opt_hold: /* EMPTY */						{ $$ = 0; }
			| WITH HOLD						{ $$ = CURSOR_OPT_HOLD; }
			| WITHOUT HOLD					{ $$ = 0; }
		;

/*****************************************************************************
 *
 *		QUERY:
 *				SELECT STATEMENTS
 *
 *****************************************************************************/

/* A complete SELECT statement looks like this.
 *
 * The rule returns either a single SelectStmt node or a tree of them,
 * representing a set-operation tree.
 *
 * There is an ambiguity when a sub-SELECT is within an a_expr and there
 * are excess parentheses: do the parentheses belong to the sub-SELECT or
 * to the surrounding a_expr?  We don't really care, but bison wants to know.
 * To resolve the ambiguity, we are careful to define the grammar so that
 * the decision is staved off as long as possible: as long as we can keep
 * absorbing parentheses into the sub-SELECT, we will do so, and only when
 * it's no longer possible to do that will we decide that parens belong to
 * the expression.	For example, in "SELECT (((SELECT 2)) + 3)" the extra
 * parentheses are treated as part of the sub-select.  The necessity of doing
 * it that way is shown by "SELECT (((SELECT 2)) UNION SELECT 2)".	Had we
 * parsed "((SELECT 2))" as an a_expr, it'd be too late to go back to the
 * SELECT viewpoint when we see the UNION.
 *
 * This approach is implemented by defining a nonterminal select_with_parens,
 * which represents a SELECT with at least one outer layer of parentheses,
 * and being careful to use select_with_parens, never '(' SelectStmt ')',
 * in the expression grammar.  We will then have shift-reduce conflicts
 * which we can resolve in favor of always treating '(' <select> ')' as
 * a select_with_parens.  To resolve the conflicts, the productions that
 * conflict with the select_with_parens productions are manually given
 * precedences lower than the precedence of ')', thereby ensuring that we
 * shift ')' (and then reduce to select_with_parens) rather than trying to
 * reduce the inner <select> nonterminal to something else.  We use UMINUS
 * precedence for this, which is a fairly arbitrary choice.
 *
 * To be able to define select_with_parens itself without ambiguity, we need
 * a nonterminal select_no_parens that represents a SELECT structure with no
 * outermost parentheses.  This is a little bit tedious, but it works.
 *
 * In non-expression contexts, we use SelectStmt which can represent a SELECT
 * with or without outer parentheses.
 */

SelectStmt: select_no_parens			%prec UMINUS
			| select_with_parens		%prec UMINUS
		;

RetrieveStmt:
			RETRIEVE SignedIconst FROM ENDPOINT name
				{
					RetrieveStmt *n = makeNode(RetrieveStmt);
					n->endpoint_name = $5;
					n->count = $2;
					$$ = (Node *)n;
				}
			| RETRIEVE ALL FROM ENDPOINT name
				{
					RetrieveStmt *n = makeNode(RetrieveStmt);
					n->endpoint_name = $5;
					n->count = -1;
					n->is_all = true;
					$$ = (Node *)n;
				}
		;

select_with_parens:
			'(' select_no_parens ')'				{ $$ = $2; }
			| '(' select_with_parens ')'			{ $$ = $2; }
		;

/*
 * This rule parses the equivalent of the standard's <query expression>.
 * The duplicative productions are annoying, but hard to get rid of without
 * creating shift/reduce conflicts.
 *
 *	The locking clause (FOR UPDATE etc) may be before or after LIMIT/OFFSET.
 *	In <=7.2.X, LIMIT/OFFSET had to be after FOR UPDATE
 *	We now support both orderings, but prefer LIMIT/OFFSET before the locking
 * clause.
 *	2002-08-28 bjm
 */
select_no_parens:
			simple_select						{ $$ = $1; }
			| select_clause sort_clause
				{
					insertSelectOptions((SelectStmt *) $1, $2, NIL,
										NULL, NULL, NULL,
										yyscanner);
					$$ = $1;
				}
			| select_clause opt_sort_clause for_locking_clause opt_select_limit
				{
					insertSelectOptions((SelectStmt *) $1, $2, $3,
										list_nth($4, 0), list_nth($4, 1),
										NULL,
										yyscanner);
					$$ = $1;
				}
			| select_clause opt_sort_clause select_limit opt_for_locking_clause
				{
					insertSelectOptions((SelectStmt *) $1, $2, $4,
										list_nth($3, 0), list_nth($3, 1),
										NULL,
										yyscanner);
					$$ = $1;
				}
			| with_clause select_clause
				{
					insertSelectOptions((SelectStmt *) $2, NULL, NIL,
										NULL, NULL,
										$1,
										yyscanner);
					$$ = $2;
				}
			| with_clause select_clause sort_clause
				{
					insertSelectOptions((SelectStmt *) $2, $3, NIL,
										NULL, NULL,
										$1,
										yyscanner);
					$$ = $2;
				}
			| with_clause select_clause opt_sort_clause for_locking_clause opt_select_limit
				{
					insertSelectOptions((SelectStmt *) $2, $3, $4,
										list_nth($5, 0), list_nth($5, 1),
										$1,
										yyscanner);
					$$ = $2;
				}
			| with_clause select_clause opt_sort_clause select_limit opt_for_locking_clause
				{
					insertSelectOptions((SelectStmt *) $2, $3, $5,
										list_nth($4, 0), list_nth($4, 1),
										$1,
										yyscanner);
					$$ = $2;
				}
		;

select_clause:
			simple_select							{ $$ = $1; }
			| select_with_parens					{ $$ = $1; }
		;

/*
 * This rule parses SELECT statements that can appear within set operations,
 * including UNION, INTERSECT and EXCEPT.  '(' and ')' can be used to specify
 * the ordering of the set operations.	Without '(' and ')' we want the
 * operations to be ordered per the precedence specs at the head of this file.
 *
 * As with select_no_parens, simple_select cannot have outer parentheses,
 * but can have parenthesized subclauses.
 *
 * Note that sort clauses cannot be included at this level --- SQL requires
 *		SELECT foo UNION SELECT bar ORDER BY baz
 * to be parsed as
 *		(SELECT foo UNION SELECT bar) ORDER BY baz
 * not
 *		SELECT foo UNION (SELECT bar ORDER BY baz)
 * Likewise for WITH, FOR UPDATE and LIMIT.  Therefore, those clauses are
 * described as part of the select_no_parens production, not simple_select.
 * This does not limit functionality, because you can reintroduce these
 * clauses inside parentheses.
 *
 * NOTE: only the leftmost component SelectStmt should have INTO.
 * However, this is not checked by the grammar; parse analysis must check it.
 */
simple_select:
			SELECT opt_distinct opt_target_list
			into_clause from_clause where_clause
			group_clause having_clause window_clause
				{
					SelectStmt *n = makeNode(SelectStmt);
					n->distinctClause = $2;
					n->targetList = $3;
					n->intoClause = $4;
					n->fromClause = $5;
					n->whereClause = $6;
					n->groupClause = $7;
					n->havingClause = $8;
					n->windowClause = $9;
					$$ = (Node *)n;
				}
			| values_clause							{ $$ = $1; }
			| TABLE relation_expr
				{
					/* same as SELECT * FROM relation_expr */
					ColumnRef *cr = makeNode(ColumnRef);
					ResTarget *rt = makeNode(ResTarget);
					SelectStmt *n = makeNode(SelectStmt);

					cr->fields = list_make1(makeNode(A_Star));
					cr->location = -1;

					rt->name = NULL;
					rt->indirection = NIL;
					rt->val = (Node *)cr;
					rt->location = -1;

					n->targetList = list_make1(rt);
					n->fromClause = list_make1($2);
					$$ = (Node *)n;
				}
			| select_clause UNION opt_all select_clause
				{
					$$ = makeSetOp(SETOP_UNION, $3, $1, $4);
				}
			| select_clause INTERSECT opt_all select_clause
				{
					$$ = makeSetOp(SETOP_INTERSECT, $3, $1, $4);
				}
			| select_clause EXCEPT opt_all select_clause
				{
					$$ = makeSetOp(SETOP_EXCEPT, $3, $1, $4);
				}
		;

/*
 * SQL standard WITH clause looks like:
 *
 * WITH [ RECURSIVE ] <query name> [ (<column>,...) ]
 *		AS (query) [ SEARCH or CYCLE clause ]
 *
 * We don't currently support the SEARCH or CYCLE clause.
 */
with_clause:
		WITH cte_list
			{
				$$ = makeNode(WithClause);
				$$->ctes = $2;
				$$->recursive = false;
				$$->location = @1;
			}
		| WITH RECURSIVE cte_list
			{
				$$ = makeNode(WithClause);
				$$->ctes = $3;
				$$->recursive = true;
				$$->location = @1;
			}
		;

cte_list:
		common_table_expr						{ $$ = list_make1($1); }
		| cte_list ',' common_table_expr		{ $$ = lappend($1, $3); }
		;

common_table_expr:  name opt_name_list AS '(' PreparableStmt ')'
			{
				CommonTableExpr *n = makeNode(CommonTableExpr);
				n->ctename = $1;
				n->aliascolnames = $2;
				n->ctequery = $5;
				n->location = @1;
				$$ = (Node *) n;
			}
		;

opt_with_clause:
		with_clause								{ $$ = $1; }
		| /*EMPTY*/								{ $$ = NULL; }
		;

into_clause:
			INTO OptTempTableName
				{
					$$ = makeNode(IntoClause);
					$$->rel = $2;
					$$->colNames = NIL;
					$$->options = NIL;
					$$->onCommit = ONCOMMIT_NOOP;
					$$->tableSpaceName = NULL;
					$$->viewQuery = NULL;
					$$->skipData = false;
				}
			| /*EMPTY*/
				{ $$ = NULL; }
		;

/*
 * Redundancy here is needed to avoid shift/reduce conflicts,
 * since TEMP is not a reserved word.  See also OptTemp.
 */
OptTempTableName:
			TEMPORARY opt_table qualified_name
				{
					$$ = $3;
					$$->relpersistence = RELPERSISTENCE_TEMP;
				}
			| TEMP opt_table qualified_name
				{
					$$ = $3;
					$$->relpersistence = RELPERSISTENCE_TEMP;
				}
			| LOCAL TEMPORARY opt_table qualified_name
				{
					$$ = $4;
					$$->relpersistence = RELPERSISTENCE_TEMP;
				}
			| LOCAL TEMP opt_table qualified_name
				{
					$$ = $4;
					$$->relpersistence = RELPERSISTENCE_TEMP;
				}
			| GLOBAL TEMPORARY opt_table qualified_name
				{
					ereport(WARNING,
							(errmsg("GLOBAL is deprecated in temporary table creation"),
							 parser_errposition(@1)));
					$$ = $4;
					$$->relpersistence = RELPERSISTENCE_TEMP;
				}
			| GLOBAL TEMP opt_table qualified_name
				{
					ereport(WARNING,
							(errmsg("GLOBAL is deprecated in temporary table creation"),
							 parser_errposition(@1)));
					$$ = $4;
					$$->relpersistence = RELPERSISTENCE_TEMP;
				}
			| UNLOGGED opt_table qualified_name
				{
					$$ = $3;
					$$->relpersistence = RELPERSISTENCE_UNLOGGED;
				}
			| TABLE qualified_name
				{
					$$ = $2;
					$$->relpersistence = RELPERSISTENCE_PERMANENT;
				}
			| qualified_name
				{
					$$ = $1;
					$$->relpersistence = RELPERSISTENCE_PERMANENT;
				}
		;

opt_table:	TABLE									{}
			| /*EMPTY*/								{}
		;

opt_all:	ALL										{ $$ = TRUE; }
			| DISTINCT								{ $$ = FALSE; }
			| /*EMPTY*/								{ $$ = FALSE; }
		;

/* We use (NIL) as a placeholder to indicate that all target expressions
 * should be placed in the DISTINCT list during parsetree analysis.
 */
opt_distinct:
			DISTINCT								{ $$ = list_make1(NIL); }
			| DISTINCT ON '(' expr_list ')'			{ $$ = $4; }
			| ALL									{ $$ = NIL; }
			| /*EMPTY*/								{ $$ = NIL; }
		;

opt_sort_clause:
			sort_clause								{ $$ = $1;}
			| /*EMPTY*/								{ $$ = NIL; }
		;

sort_clause:
			ORDER BY sortby_list					{ $$ = $3; }
		;

sortby_list:
			sortby									{ $$ = list_make1($1); }
			| sortby_list ',' sortby				{ $$ = lappend($1, $3); }
		;

sortby:		a_expr USING qual_all_Op opt_nulls_order
				{
					$$ = makeNode(SortBy);
					$$->node = $1;
					$$->sortby_dir = SORTBY_USING;
					$$->sortby_nulls = $4;
					$$->useOp = $3;
					$$->location = @3;
				}
			| a_expr opt_asc_desc opt_nulls_order
				{
					$$ = makeNode(SortBy);
					$$->node = $1;
					$$->sortby_dir = $2;
					$$->sortby_nulls = $3;
					$$->useOp = NIL;
					$$->location = -1;		/* no operator */
				}
		;


select_limit:
			limit_clause offset_clause			{ $$ = list_make2($2, $1); }
			| offset_clause limit_clause		{ $$ = list_make2($1, $2); }
			| limit_clause						{ $$ = list_make2(NULL, $1); }
			| offset_clause						{ $$ = list_make2($1, NULL); }
		;

opt_select_limit:
			select_limit						{ $$ = $1; }
			| /* EMPTY */						{ $$ = list_make2(NULL,NULL); }
		;

limit_clause:
			LIMIT select_limit_value
				{ $$ = $2; }
			| LIMIT select_limit_value ',' select_offset_value
				{
					/* Disabled because it was too confusing, bjm 2002-02-18 */
					ereport(ERROR,
							(errcode(ERRCODE_SYNTAX_ERROR),
							 errmsg("LIMIT #,# syntax is not supported"),
							 errhint("Use separate LIMIT and OFFSET clauses."),
							 parser_errposition(@1)));
				}
			/* SQL:2008 syntax */
			/* to avoid shift/reduce conflicts, handle the optional value with
			 * a separate production rather than an opt_ expression.  The fact
			 * that ONLY is fully reserved means that this way, we defer any
			 * decision about what rule reduces ROW or ROWS to the point where
			 * we can see the ONLY token in the lookahead slot.
			 */
			| FETCH first_or_next select_fetch_first_value row_or_rows ONLY
				{ $$ = $3; }
			| FETCH first_or_next row_or_rows ONLY
				{ $$ = makeIntConst(1, -1); }
		;

offset_clause:
			OFFSET select_offset_value
				{ $$ = $2; }
			/* SQL:2008 syntax */
			| OFFSET select_fetch_first_value row_or_rows
				{ $$ = $2; }
		;

select_limit_value:
			a_expr									{ $$ = $1; }
			| ALL
				{
					/* LIMIT ALL is represented as a NULL constant */
					$$ = makeNullAConst(@1);
				}
		;

select_offset_value:
			a_expr									{ $$ = $1; }
		;

/*
 * Allowing full expressions without parentheses causes various parsing
 * problems with the trailing ROW/ROWS key words.  SQL spec only calls for
 * <simple value specification>, which is either a literal or a parameter (but
 * an <SQL parameter reference> could be an identifier, bringing up conflicts
 * with ROW/ROWS). We solve this by leveraging the presence of ONLY (see above)
 * to determine whether the expression is missing rather than trying to make it
 * optional in this rule.
 *
 * c_expr covers almost all the spec-required cases (and more), but it doesn't
 * cover signed numeric literals, which are allowed by the spec. So we include
 * those here explicitly. We need FCONST as well as ICONST because values that
 * don't fit in the platform's "long", but do fit in bigint, should still be
 * accepted here. (This is possible in 64-bit Windows as well as all 32-bit
 * builds.)
 */
select_fetch_first_value:
			c_expr									{ $$ = $1; }
			| '+' I_or_F_const
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "+", NULL, $2, @1); }
			| '-' I_or_F_const
				{ $$ = doNegate($2, @1); }
		;

I_or_F_const:
			Iconst									{ $$ = makeIntConst($1,@1); }
			| FCONST								{ $$ = makeFloatConst($1,@1); }
		;

/* noise words */
row_or_rows: ROW									{ $$ = 0; }
			| ROWS									{ $$ = 0; }
		;

first_or_next: FIRST_P								{ $$ = 0; }
			| NEXT									{ $$ = 0; }
		;


group_clause:
			GROUP_P BY group_elem_list				{ $$ = $3; }
			| /*EMPTY*/								{ $$ = NIL; }
		;

group_elem_list:
            group_elem                                { $$ = $1; }
            | group_elem_list ',' group_elem            { $$ = list_concat($1, $3); }
        ;

group_elem:
			a_expr                                  { $$ = list_make1($1); }
			| ROLLUP '(' expr_list ')'
                {
					GroupingClause *n = makeNode(GroupingClause);
					n->groupType = GROUPINGTYPE_ROLLUP;
					n->groupsets = $3;
					n->location = @1;
					$$ = list_make1 ((Node*)n);
				}
            | CUBE '(' expr_list ')'
                {
					GroupingClause *n = makeNode(GroupingClause);
					n->groupType = GROUPINGTYPE_CUBE;
					n->groupsets = $3;
					n->location = @1;
					$$ = list_make1 ((Node*)n);
				}
            | GROUPING SETS '(' group_elem_list ')'
                {
					GroupingClause *n = makeNode(GroupingClause);
					n->groupType = GROUPINGTYPE_GROUPING_SETS;
					n->groupsets = $4;
					n->location = @1;
					$$ = list_make1 ((Node*)n);
				}
            | '(' ')'
                { $$ = list_make1(NIL); }
        ;

having_clause:
			HAVING a_expr							{ $$ = $2; }
			| /*EMPTY*/								{ $$ = NULL; }
		;

for_locking_clause:
			for_locking_items						{ $$ = $1; }
			| FOR READ ONLY							{ $$ = NIL; }
		;

opt_for_locking_clause:
			for_locking_clause						{ $$ = $1; }
			| /* EMPTY */							{ $$ = NIL; }
		;

for_locking_items:
			for_locking_item						{ $$ = list_make1($1); }
			| for_locking_items for_locking_item	{ $$ = lappend($1, $2); }
		;

for_locking_item:
			for_locking_strength locked_rels_list opt_nowait
				{
					LockingClause *n = makeNode(LockingClause);
					n->lockedRels = $2;
					n->strength = $1;
					n->noWait = $3;
					$$ = (Node *) n;
				}
		;

for_locking_strength:
			FOR UPDATE 							{ $$ = LCS_FORUPDATE; }
			| FOR NO KEY UPDATE 				{ $$ = LCS_FORNOKEYUPDATE; }
			| FOR SHARE 						{ $$ = LCS_FORSHARE; }
			| FOR KEY SHARE 					{ $$ = LCS_FORKEYSHARE; }
		;

locked_rels_list:
			OF qualified_name_list					{ $$ = $2; }
			| /* EMPTY */							{ $$ = NIL; }
		;


values_clause:
			VALUES ctext_row
				{
					SelectStmt *n = makeNode(SelectStmt);
					n->valuesLists = list_make1($2);
					$$ = (Node *) n;
				}
			| values_clause ',' ctext_row
				{
					SelectStmt *n = (SelectStmt *) $1;
					n->valuesLists = lappend(n->valuesLists, $3);
					$$ = (Node *) n;
				}
		;


/*****************************************************************************
 *
 *	clauses common to all Optimizable Stmts:
 *		from_clause		- allow list of both JOIN expressions and table names
 *		where_clause	- qualifications for joins or restrictions
 *
 *****************************************************************************/

from_clause:
			FROM from_list							{ $$ = $2; }
			| /*EMPTY*/								{ $$ = NIL; }
		;

from_list:
			table_ref								{ $$ = list_make1($1); }
			| from_list ',' table_ref				{ $$ = lappend($1, $3); }
		;

/*
 * table_ref is where an alias clause can be attached.
 */
table_ref:	relation_expr opt_alias_clause
				{
					$1->alias = $2;
					$$ = (Node *) $1;
				}
			| func_table func_alias_clause
				{
					RangeFunction *n = (RangeFunction *) $1;
					n->alias = linitial($2);
					n->coldeflist = lsecond($2);
					$$ = (Node *) n;
				}
			| LATERAL_P func_table func_alias_clause
				{
					RangeFunction *n = (RangeFunction *) $2;
					n->lateral = true;
					n->alias = linitial($3);
					n->coldeflist = lsecond($3);
					$$ = (Node *) n;
				}
			| select_with_parens opt_alias_clause
				{
					RangeSubselect *n = makeNode(RangeSubselect);
					n->lateral = false;
					n->subquery = $1;
					n->alias = $2;
					/*
					 * The SQL spec does not permit a subselect
					 * (<derived_table>) without an alias clause,
					 * so we don't either.  This avoids the problem
					 * of needing to invent a unique refname for it.
					 * That could be surmounted if there's sufficient
					 * popular demand, but for now let's just implement
					 * the spec and see if anyone complains.
					 * However, it does seem like a good idea to emit
					 * an error message that's better than "syntax error".
					 */
					if ($2 == NULL)
					{
						if (IsA($1, SelectStmt) &&
							((SelectStmt *) $1)->valuesLists)
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("VALUES in FROM must have an alias"),
									 errhint("For example, FROM (VALUES ...) [AS] foo."),
									 parser_errposition(@1)));
						else
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("subquery in FROM must have an alias"),
									 errhint("For example, FROM (SELECT ...) [AS] foo."),
									 parser_errposition(@1)));
					}
					$$ = (Node *) n;
				}
			| LATERAL_P select_with_parens opt_alias_clause
				{
					RangeSubselect *n = makeNode(RangeSubselect);
					n->lateral = true;
					n->subquery = $2;
					n->alias = $3;
					/* same comment as above */
					if ($3 == NULL)
					{
						if (IsA($2, SelectStmt) &&
							((SelectStmt *) $2)->valuesLists)
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("VALUES in FROM must have an alias"),
									 errhint("For example, FROM (VALUES ...) [AS] foo."),
									 parser_errposition(@2)));
						else
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("subquery in FROM must have an alias"),
									 errhint("For example, FROM (SELECT ...) [AS] foo."),
									 parser_errposition(@2)));
					}
					$$ = (Node *) n;
				}
			| joined_table
				{
					$$ = (Node *) $1;
				}
			| '(' joined_table ')' alias_clause
				{
					$2->alias = $4;
					$$ = (Node *) $2;
				}
		;


/*
 * It may seem silly to separate joined_table from table_ref, but there is
 * method in SQL's madness: if you don't do it this way you get reduce-
 * reduce conflicts, because it's not clear to the parser generator whether
 * to expect alias_clause after ')' or not.  For the same reason we must
 * treat 'JOIN' and 'join_type JOIN' separately, rather than allowing
 * join_type to expand to empty; if we try it, the parser generator can't
 * figure out when to reduce an empty join_type right after table_ref.
 *
 * Note that a CROSS JOIN is the same as an unqualified
 * INNER JOIN, and an INNER JOIN/ON has the same shape
 * but a qualification expression to limit membership.
 * A NATURAL JOIN implicitly matches column names between
 * tables and the shape is determined by which columns are
 * in common. We'll collect columns during the later transformations.
 */

joined_table:
			'(' joined_table ')'
				{
					$$ = $2;
				}
			| table_ref CROSS JOIN table_ref
				{
					/* CROSS JOIN is same as unqualified inner join */
					JoinExpr *n = makeNode(JoinExpr);
					n->jointype = JOIN_INNER;
					n->isNatural = FALSE;
					n->larg = $1;
					n->rarg = $4;
					n->usingClause = NIL;
					n->quals = NULL;
					$$ = n;
				}
			| table_ref join_type JOIN table_ref join_qual
				{
					JoinExpr *n = makeNode(JoinExpr);
					n->jointype = $2;
					n->isNatural = FALSE;
					n->larg = $1;
					n->rarg = $4;
					if ($5 != NULL && IsA($5, List))
						n->usingClause = (List *) $5; /* USING clause */
					else
						n->quals = $5; /* ON clause */
					$$ = n;
				}
			| table_ref JOIN table_ref join_qual
				{
					/* letting join_type reduce to empty doesn't work */
					JoinExpr *n = makeNode(JoinExpr);
					n->jointype = JOIN_INNER;
					n->isNatural = FALSE;
					n->larg = $1;
					n->rarg = $3;
					if ($4 != NULL && IsA($4, List))
						n->usingClause = (List *) $4; /* USING clause */
					else
						n->quals = $4; /* ON clause */
					$$ = n;
				}
			| table_ref NATURAL join_type JOIN table_ref
				{
					JoinExpr *n = makeNode(JoinExpr);
					n->jointype = $3;
					n->isNatural = TRUE;
					n->larg = $1;
					n->rarg = $5;
					n->usingClause = NIL; /* figure out which columns later... */
					n->quals = NULL; /* fill later */
					$$ = n;
				}
			| table_ref NATURAL JOIN table_ref
				{
					/* letting join_type reduce to empty doesn't work */
					JoinExpr *n = makeNode(JoinExpr);
					n->jointype = JOIN_INNER;
					n->isNatural = TRUE;
					n->larg = $1;
					n->rarg = $4;
					n->usingClause = NIL; /* figure out which columns later... */
					n->quals = NULL; /* fill later */
					$$ = n;
				}
		;

alias_clause:
			AS ColId '(' name_list ')'
				{
					$$ = makeNode(Alias);
					$$->aliasname = $2;
					$$->colnames = $4;
				}
			| AS ColId
				{
					$$ = makeNode(Alias);
					$$->aliasname = $2;
				}
			| ColId '(' name_list ')'
				{
					$$ = makeNode(Alias);
					$$->aliasname = $1;
					$$->colnames = $3;
				}
			| ColId
				{
					$$ = makeNode(Alias);
					$$->aliasname = $1;
				}
		;

opt_alias_clause: alias_clause						{ $$ = $1; }
			| /*EMPTY*/								{ $$ = NULL; }
		;

/*
 * func_alias_clause can include both an Alias and a coldeflist, so we make it
 * return a 2-element list that gets disassembled by calling production.
 */
func_alias_clause:
			alias_clause
				{
					$$ = list_make2($1, NIL);
				}
			| AS '(' TableFuncElementList ')'
				{
					$$ = list_make2(NULL, $3);
				}
			| AS ColId '(' TableFuncElementList ')'
				{
					Alias *a = makeNode(Alias);
					a->aliasname = $2;
					$$ = list_make2(a, $4);
				}
			| ColId '(' TableFuncElementList ')'
				{
					Alias *a = makeNode(Alias);
					a->aliasname = $1;
					$$ = list_make2(a, $3);
				}
			| /*EMPTY*/
				{
					$$ = list_make2(NULL, NIL);
				}
		;

join_type:	FULL join_outer							{ $$ = JOIN_FULL; }
			| LEFT join_outer						{ $$ = JOIN_LEFT; }
			| RIGHT join_outer						{ $$ = JOIN_RIGHT; }
			| INNER_P								{ $$ = JOIN_INNER; }
		;

/* OUTER is just noise... */
join_outer: OUTER_P									{ $$ = NULL; }
			| /*EMPTY*/								{ $$ = NULL; }
		;

/* JOIN qualification clauses
 * Possibilities are:
 *	USING ( column list ) allows only unqualified column names,
 *						  which must match between tables.
 *	ON expr allows more general qualifications.
 *
 * We return USING as a List node, while an ON-expr will not be a List.
 */

join_qual:	USING '(' name_list ')'					{ $$ = (Node *) $3; }
			| ON a_expr								{ $$ = $2; }
		;


relation_expr:
			qualified_name
				{
					/* default inheritance */
					$$ = $1;
					$$->inhOpt = INH_DEFAULT;
					$$->alias = NULL;
				}
			| qualified_name '*'
				{
					/* inheritance query */
					$$ = $1;
					$$->inhOpt = INH_YES;
					$$->alias = NULL;
				}
			| ONLY qualified_name
				{
					/* no inheritance */
					$$ = $2;
					$$->inhOpt = INH_NO;
					$$->alias = NULL;
				}
			| ONLY '(' qualified_name ')'
				{
					/* no inheritance, SQL99-style syntax */
					$$ = $3;
					$$->inhOpt = INH_NO;
					$$->alias = NULL;
				}
		;


relation_expr_list:
			relation_expr							{ $$ = list_make1($1); }
			| relation_expr_list ',' relation_expr	{ $$ = lappend($1, $3); }
		;


/*
 * Given "UPDATE foo set set ...", we have to decide without looking any
 * further ahead whether the first "set" is an alias or the UPDATE's SET
 * keyword.  Since "set" is allowed as a column name both interpretations
 * are feasible.  We resolve the shift/reduce conflict by giving the first
 * relation_expr_opt_alias production a higher precedence than the SET token
 * has, causing the parser to prefer to reduce, in effect assuming that the
 * SET is not an alias.
 */
relation_expr_opt_alias: relation_expr					%prec UMINUS
				{
					$$ = $1;
				}
			| relation_expr ColId
				{
					Alias *alias = makeNode(Alias);
					alias->aliasname = $2;
					$1->alias = alias;
					$$ = $1;
				}
			| relation_expr AS ColId
				{
					Alias *alias = makeNode(Alias);
					alias->aliasname = $3;
					$1->alias = alias;
					$$ = $1;
				}
		;

/*
 * func_table represents a function invocation in a FROM list. It can be
 * a plain function call, like "foo(...)", or a ROWS FROM expression with
 * one or more function calls, "ROWS FROM (foo(...), bar(...))",
 * optionally with WITH ORDINALITY attached.
 * In the ROWS FROM syntax, a column definition list can be given for each
 * function, for example:
 *     ROWS FROM (foo() AS (foo_res_a text, foo_res_b text),
 *                bar() AS (bar_res_a text, bar_res_b text))
 * It's also possible to attach a column definition list to the RangeFunction
 * as a whole, but that's handled by the table_ref production.
 */
func_table: func_expr_windowless opt_ordinality
				{
					RangeFunction *n = makeNode(RangeFunction);
					n->lateral = false;
					n->ordinality = $2;
					n->is_rowsfrom = false;
					n->functions = list_make1(list_make2($1, NIL));
					/* alias and coldeflist are set by table_ref production */
					$$ = (Node *) n;
				}
			| ROWS FROM '(' rowsfrom_list ')' opt_ordinality
				{
					RangeFunction *n = makeNode(RangeFunction);
					n->lateral = false;
					n->ordinality = $6;
					n->is_rowsfrom = true;
					n->functions = $4;
					/* alias and coldeflist are set by table_ref production */
					$$ = (Node *) n;
				}
		;

rowsfrom_item: func_expr_windowless opt_col_def_list
				{ $$ = list_make2($1, $2); }
		;

rowsfrom_list:
			rowsfrom_item						{ $$ = list_make1($1); }
			| rowsfrom_list ',' rowsfrom_item	{ $$ = lappend($1, $3); }
		;

opt_col_def_list: AS '(' TableFuncElementList ')'	{ $$ = $3; }
			| /*EMPTY*/								{ $$ = NIL; }
		;

opt_ordinality: WITH_ORDINALITY						{ $$ = true; }
			| /*EMPTY*/								{ $$ = false; }
		;


where_clause:
			WHERE a_expr							{ $$ = $2; }
			| /*EMPTY*/								{ $$ = NULL; }
		;

/* variant for UPDATE and DELETE */
where_or_current_clause:
			WHERE a_expr							{ $$ = $2; }
			| WHERE CURRENT_P OF cursor_name
				{
					CurrentOfExpr *n = makeNode(CurrentOfExpr);
					/* cvarno is filled in by parse analysis */
					n->cursor_name = $4;
					n->cursor_param = 0;
					$$ = (Node *) n;
				}
			| /*EMPTY*/								{ $$ = NULL; }
		;


OptTableFuncElementList:
			TableFuncElementList				{ $$ = $1; }
			| /*EMPTY*/							{ $$ = NIL; }
		;

TableFuncElementList:
			TableFuncElement
				{
					$$ = list_make1($1);
				}
			| TableFuncElementList ',' TableFuncElement
				{
					$$ = lappend($1, $3);
				}
		;

TableFuncElement:	ColId Typename opt_collate_clause
				{
					ColumnDef *n = makeNode(ColumnDef);
					n->colname = $1;
					n->typeName = $2;
					n->inhcount = 0;
					n->is_local = true;
					n->is_not_null = false;
					n->is_from_type = false;
					n->storage = 0;
					n->raw_default = NULL;
					n->cooked_default = NULL;
					n->collClause = (CollateClause *) $3;
					n->collOid = InvalidOid;
					n->constraints = NIL;
					n->location = @1;
					$$ = (Node *)n;
				}
		;

/*****************************************************************************
 *
 *	Type syntax
 *		SQL introduces a large amount of type-specific syntax.
 *		Define individual clauses to handle these cases, and use
 *		 the generic case to handle regular type-extensible Postgres syntax.
 *		- thomas 1997-10-10
 *
 *****************************************************************************/

Typename:	SimpleTypename opt_array_bounds
				{
					$$ = $1;
					$$->arrayBounds = $2;
				}
			| SETOF SimpleTypename opt_array_bounds
				{
					$$ = $2;
					$$->arrayBounds = $3;
					$$->setof = TRUE;
				}
			/* SQL standard syntax, currently only one-dimensional */
			| SimpleTypename ARRAY '[' Iconst ']'
				{
					$$ = $1;
					$$->arrayBounds = list_make1(makeInteger($4));
				}
			| SETOF SimpleTypename ARRAY '[' Iconst ']'
				{
					$$ = $2;
					$$->arrayBounds = list_make1(makeInteger($5));
					$$->setof = TRUE;
				}
			| SimpleTypename ARRAY
				{
					$$ = $1;
					$$->arrayBounds = list_make1(makeInteger(-1));
				}
			| SETOF SimpleTypename ARRAY
				{
					$$ = $2;
					$$->arrayBounds = list_make1(makeInteger(-1));
					$$->setof = TRUE;
				}
		;

opt_array_bounds:
			opt_array_bounds '[' ']'
					{  $$ = lappend($1, makeInteger(-1)); }
			| opt_array_bounds '[' Iconst ']'
					{  $$ = lappend($1, makeInteger($3)); }
			| /*EMPTY*/
					{  $$ = NIL; }
		;

SimpleTypename:
			GenericType								{ $$ = $1; }
			| Numeric								{ $$ = $1; }
			| Bit									{ $$ = $1; }
			| Character								{ $$ = $1; }
			| ConstDatetime							{ $$ = $1; }
			| ConstInterval opt_interval
				{
					$$ = $1;
					$$->typmods = $2;
				}
			| ConstInterval '(' Iconst ')' opt_interval
				{
					$$ = $1;
					if ($5 != NIL)
					{
						if (list_length($5) != 1)
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("interval precision specified twice"),
									 parser_errposition(@1)));
						$$->typmods = lappend($5, makeIntConst($3, @3));
					}
					else
						$$->typmods = list_make2(makeIntConst(INTERVAL_FULL_RANGE, -1),
												 makeIntConst($3, @3));
				}
		;

/* We have a separate ConstTypename to allow defaulting fixed-length
 * types such as CHAR() and BIT() to an unspecified length.
 * SQL9x requires that these default to a length of one, but this
 * makes no sense for constructs like CHAR 'hi' and BIT '0101',
 * where there is an obvious better choice to make.
 * Note that ConstInterval is not included here since it must
 * be pushed up higher in the rules to accommodate the postfix
 * options (e.g. INTERVAL '1' YEAR). Likewise, we have to handle
 * the generic-type-name case in AExprConst to avoid premature
 * reduce/reduce conflicts against function names.
 */
ConstTypename:
			Numeric									{ $$ = $1; }
			| ConstBit								{ $$ = $1; }
			| ConstCharacter						{ $$ = $1; }
			| ConstDatetime							{ $$ = $1; }
		;

/*
 * GenericType covers all type names that don't have special syntax mandated
 * by the standard, including qualified names.  We also allow type modifiers.
 * To avoid parsing conflicts against function invocations, the modifiers
 * have to be shown as expr_list here, but parse analysis will only accept
 * constants for them.
 */
GenericType:
			type_function_name opt_type_modifiers
				{
					$$ = makeTypeName($1);
					$$->typmods = $2;
					$$->location = @1;
				}
			| type_function_name attrs opt_type_modifiers
				{
					$$ = makeTypeNameFromNameList(lcons(makeString($1), $2));
					$$->typmods = $3;
					$$->location = @1;
				}
		;

opt_type_modifiers: '(' expr_list ')'				{ $$ = $2; }
					| /* EMPTY */					{ $$ = NIL; }
		;

/*
 * SQL numeric data types
 */
Numeric:	INT_P
				{
					$$ = SystemTypeName("int4");
					$$->location = @1;
				}
			| INTEGER
				{
					$$ = SystemTypeName("int4");
					$$->location = @1;
				}
			| SMALLINT
				{
					$$ = SystemTypeName("int2");
					$$->location = @1;
				}
			| BIGINT
				{
					$$ = SystemTypeName("int8");
					$$->location = @1;
				}
			| REAL
				{
					$$ = SystemTypeName("float4");
					$$->location = @1;
				}
			| FLOAT_P opt_float
				{
					$$ = $2;
					$$->location = @1;
				}
			| DOUBLE_P PRECISION
				{
					$$ = SystemTypeName("float8");
					$$->location = @1;
				}
			| DECIMAL_P opt_type_modifiers
				{
					$$ = SystemTypeName("numeric");
					$$->typmods = $2;
					$$->location = @1;
				}
			| DEC opt_type_modifiers
				{
					$$ = SystemTypeName("numeric");
					$$->typmods = $2;
					$$->location = @1;
				}
			| NUMERIC opt_type_modifiers
				{
					$$ = SystemTypeName("numeric");
					$$->typmods = $2;
					$$->location = @1;
				}
			| BOOLEAN_P
				{
					$$ = SystemTypeName("bool");
					$$->location = @1;
				}
		;

opt_float:	'(' Iconst ')'
				{
					/*
					 * Check FLOAT() precision limits assuming IEEE floating
					 * types - thomas 1997-09-18
					 */
					if ($2 < 1)
						ereport(ERROR,
								(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
								 errmsg("precision for type float must be at least 1 bit"),
								 parser_errposition(@2)));
					else if ($2 <= 24)
						$$ = SystemTypeName("float4");
					else if ($2 <= 53)
						$$ = SystemTypeName("float8");
					else
						ereport(ERROR,
								(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
								 errmsg("precision for type float must be less than 54 bits"),
								 parser_errposition(@2)));
				}
			| /*EMPTY*/
				{
					$$ = SystemTypeName("float8");
				}
		;

/*
 * SQL bit-field data types
 * The following implements BIT() and BIT VARYING().
 */
Bit:		BitWithLength
				{
					$$ = $1;
				}
			| BitWithoutLength
				{
					$$ = $1;
				}
		;

/* ConstBit is like Bit except "BIT" defaults to unspecified length */
/* See notes for ConstCharacter, which addresses same issue for "CHAR" */
ConstBit:	BitWithLength
				{
					$$ = $1;
				}
			| BitWithoutLength
				{
					$$ = $1;
					$$->typmods = NIL;
				}
		;

BitWithLength:
			BIT opt_varying '(' expr_list ')'
				{
					char *typname;

					typname = $2 ? "varbit" : "bit";
					$$ = SystemTypeName(typname);
					$$->typmods = $4;
					$$->location = @1;
				}
		;

BitWithoutLength:
			BIT opt_varying
				{
					/* bit defaults to bit(1), varbit to no limit */
					if ($2)
					{
						$$ = SystemTypeName("varbit");
					}
					else
					{
						$$ = SystemTypeName("bit");
						$$->typmods = list_make1(makeIntConst(1, -1));
					}
					$$->location = @1;
				}
		;


/*
 * SQL character data types
 * The following implements CHAR() and VARCHAR().
 */
Character:  CharacterWithLength
				{
					$$ = $1;
				}
			| CharacterWithoutLength
				{
					$$ = $1;
				}
		;

ConstCharacter:  CharacterWithLength
				{
					$$ = $1;
				}
			| CharacterWithoutLength
				{
					/* Length was not specified so allow to be unrestricted.
					 * This handles problems with fixed-length (bpchar) strings
					 * which in column definitions must default to a length
					 * of one, but should not be constrained if the length
					 * was not specified.
					 */
					$$ = $1;
					$$->typmods = NIL;
				}
		;

CharacterWithLength:  character '(' Iconst ')' opt_charset
				{
					if (($5 != NULL) && (strcmp($5, "sql_text") != 0))
						$1 = psprintf("%s_%s", $1, $5);

					$$ = SystemTypeName($1);
					$$->typmods = list_make1(makeIntConst($3, @3));
					$$->location = @1;
				}
		;

CharacterWithoutLength:	 character opt_charset
				{
					if (($2 != NULL) && (strcmp($2, "sql_text") != 0))
						$1 = psprintf("%s_%s", $1, $2);

					$$ = SystemTypeName($1);

					/* char defaults to char(1), varchar to no limit */
					if (strcmp($1, "bpchar") == 0)
						$$->typmods = list_make1(makeIntConst(1, -1));

					$$->location = @1;
				}
		;

character:	CHARACTER opt_varying
										{ $$ = $2 ? "varchar": "bpchar"; }
			| CHAR_P opt_varying
										{ $$ = $2 ? "varchar": "bpchar"; }
			| VARCHAR
										{ $$ = "varchar"; }
			| NATIONAL CHARACTER opt_varying
										{ $$ = $3 ? "varchar": "bpchar"; }
			| NATIONAL CHAR_P opt_varying
										{ $$ = $3 ? "varchar": "bpchar"; }
			| NCHAR opt_varying
										{ $$ = $2 ? "varchar": "bpchar"; }
		;

opt_varying:
			VARYING									{ $$ = TRUE; }
			| /*EMPTY*/								{ $$ = FALSE; }
		;

opt_charset:
			CHARACTER SET ColId						{ $$ = $3; }
			| /*EMPTY*/								{ $$ = NULL; }
		;

/*
 * SQL date/time types
 */
ConstDatetime:
			TIMESTAMP '(' Iconst ')' opt_timezone
				{
					if ($5)
						$$ = SystemTypeName("timestamptz");
					else
						$$ = SystemTypeName("timestamp");
					$$->typmods = list_make1(makeIntConst($3, @3));
					$$->location = @1;
				}
			| TIMESTAMP opt_timezone
				{
					if ($2)
						$$ = SystemTypeName("timestamptz");
					else
						$$ = SystemTypeName("timestamp");
					$$->location = @1;
				}
			| TIME '(' Iconst ')' opt_timezone
				{
					if ($5)
						$$ = SystemTypeName("timetz");
					else
						$$ = SystemTypeName("time");
					$$->typmods = list_make1(makeIntConst($3, @3));
					$$->location = @1;
				}
			| TIME opt_timezone
				{
					if ($2)
						$$ = SystemTypeName("timetz");
					else
						$$ = SystemTypeName("time");
					$$->location = @1;
				}
		;

ConstInterval:
			INTERVAL
				{
					$$ = SystemTypeName("interval");
					$$->location = @1;
				}
		;

opt_timezone:
			WITH_TIME ZONE							{ $$ = TRUE; }
			| WITHOUT TIME ZONE						{ $$ = FALSE; }
			| /*EMPTY*/								{ $$ = FALSE; }
		;

opt_interval:
			YEAR_P
				{ $$ = list_make1(makeIntConst(INTERVAL_MASK(YEAR), @1)); }
			| MONTH_P
				{ $$ = list_make1(makeIntConst(INTERVAL_MASK(MONTH), @1)); }
			| DAY_P
				{ $$ = list_make1(makeIntConst(INTERVAL_MASK(DAY), @1)); }
			| HOUR_P
				{ $$ = list_make1(makeIntConst(INTERVAL_MASK(HOUR), @1)); }
			| MINUTE_P
				{ $$ = list_make1(makeIntConst(INTERVAL_MASK(MINUTE), @1)); }
			| interval_second
				{ $$ = $1; }
			| YEAR_P TO MONTH_P
				{
					$$ = list_make1(makeIntConst(INTERVAL_MASK(YEAR) |
												 INTERVAL_MASK(MONTH), @1));
				}
			| DAY_P TO HOUR_P
				{
					$$ = list_make1(makeIntConst(INTERVAL_MASK(DAY) |
												 INTERVAL_MASK(HOUR), @1));
				}
			| DAY_P TO MINUTE_P
				{
					$$ = list_make1(makeIntConst(INTERVAL_MASK(DAY) |
												 INTERVAL_MASK(HOUR) |
												 INTERVAL_MASK(MINUTE), @1));
				}
			| DAY_P TO interval_second
				{
					$$ = $3;
					linitial($$) = makeIntConst(INTERVAL_MASK(DAY) |
												INTERVAL_MASK(HOUR) |
												INTERVAL_MASK(MINUTE) |
												INTERVAL_MASK(SECOND), @1);
				}
			| HOUR_P TO MINUTE_P
				{
					$$ = list_make1(makeIntConst(INTERVAL_MASK(HOUR) |
												 INTERVAL_MASK(MINUTE), @1));
				}
			| HOUR_P TO interval_second
				{
					$$ = $3;
					linitial($$) = makeIntConst(INTERVAL_MASK(HOUR) |
												INTERVAL_MASK(MINUTE) |
												INTERVAL_MASK(SECOND), @1);
				}
			| MINUTE_P TO interval_second
				{
					$$ = $3;
					linitial($$) = makeIntConst(INTERVAL_MASK(MINUTE) |
												INTERVAL_MASK(SECOND), @1);
				}
			| /*EMPTY*/
				{ $$ = NIL; }
		;

interval_second:
			SECOND_P
				{
					$$ = list_make1(makeIntConst(INTERVAL_MASK(SECOND), @1));
				}
			| SECOND_P '(' Iconst ')'
				{
					$$ = list_make2(makeIntConst(INTERVAL_MASK(SECOND), @1),
									makeIntConst($3, @3));
				}
		;


/*****************************************************************************
 *
 *	expression grammar
 *
 *****************************************************************************/

/*
 * General expressions
 * This is the heart of the expression syntax.
 *
 * We have two expression types: a_expr is the unrestricted kind, and
 * b_expr is a subset that must be used in some places to avoid shift/reduce
 * conflicts.  For example, we can't do BETWEEN as "BETWEEN a_expr AND a_expr"
 * because that use of AND conflicts with AND as a boolean operator.  So,
 * b_expr is used in BETWEEN and we remove boolean keywords from b_expr.
 *
 * Note that '(' a_expr ')' is a b_expr, so an unrestricted expression can
 * always be used by surrounding it with parens.
 *
 * c_expr is all the productions that are common to a_expr and b_expr;
 * it's factored out just to eliminate redundant coding.
 */
a_expr:		c_expr									{ $$ = $1; }
			| a_expr TYPECAST Typename
					{ $$ = makeTypeCast($1, $3, @2); }
			| a_expr COLLATE any_name
				{
					CollateClause *n = makeNode(CollateClause);
					n->arg = $1;
					n->collname = $3;
					n->location = @2;
					$$ = (Node *) n;
				}
			| a_expr AT TIME ZONE a_expr			%prec AT
				{
					$$ = (Node *) makeFuncCall(SystemFuncName("timezone"),
											   list_make2($5, $1),
											   @2);
				}
		/*
		 * These operators must be called out explicitly in order to make use
		 * of bison's automatic operator-precedence handling.  All other
		 * operator names are handled by the generic productions using "Op",
		 * below; and all those operators will have the same precedence.
		 *
		 * If you add more explicitly-known operators, be sure to add them
		 * also to b_expr and to the MathOp list above.
		 */
			| '+' a_expr					%prec UMINUS
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "+", NULL, $2, @1); }
			| '-' a_expr					%prec UMINUS
				{ $$ = doNegate($2, @1); }
			| a_expr '+' a_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "+", $1, $3, @2); }
			| a_expr '-' a_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "-", $1, $3, @2); }
			| a_expr '*' a_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "*", $1, $3, @2); }
			| a_expr '/' a_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "/", $1, $3, @2); }
			| a_expr '%' a_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "%", $1, $3, @2); }
			| a_expr '^' a_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "^", $1, $3, @2); }
			| a_expr '<' a_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "<", $1, $3, @2); }
			| a_expr '>' a_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, ">", $1, $3, @2); }
			| a_expr '=' a_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "=", $1, $3, @2); }

			| a_expr qual_Op a_expr				%prec Op
				{ $$ = (Node *) makeA_Expr(AEXPR_OP, $2, $1, $3, @2); }
			| qual_Op a_expr					%prec Op
				{ $$ = (Node *) makeA_Expr(AEXPR_OP, $1, NULL, $2, @1); }
			| a_expr qual_Op					%prec POSTFIXOP
				{ $$ = (Node *) makeA_Expr(AEXPR_OP, $2, $1, NULL, @2); }

			| a_expr AND a_expr
				{ $$ = (Node *) makeA_Expr(AEXPR_AND, NIL, $1, $3, @2); }
			| a_expr OR a_expr
				{ $$ = (Node *) makeA_Expr(AEXPR_OR, NIL, $1, $3, @2); }
			| NOT a_expr
				{ $$ = (Node *) makeA_Expr(AEXPR_NOT, NIL, NULL, $2, @1); }

			| a_expr LIKE a_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "~~", $1, $3, @2); }
			| a_expr LIKE a_expr ESCAPE a_expr
				{
					FuncCall *n = makeFuncCall(SystemFuncName("like_escape"),
											   list_make2($3, $5),
											   @2);
					$$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "~~", $1, (Node *) n, @2);
				}
			| a_expr NOT LIKE a_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "!~~", $1, $4, @2); }
			| a_expr NOT LIKE a_expr ESCAPE a_expr
				{
					FuncCall *n = makeFuncCall(SystemFuncName("like_escape"),
											   list_make2($4, $6),
											   @2);
					$$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "!~~", $1, (Node *) n, @2);
				}
			| a_expr ILIKE a_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "~~*", $1, $3, @2); }
			| a_expr ILIKE a_expr ESCAPE a_expr
				{
					FuncCall *n = makeFuncCall(SystemFuncName("like_escape"),
											   list_make2($3, $5),
											   @2);
					$$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "~~*", $1, (Node *) n, @2);
				}
			| a_expr NOT ILIKE a_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "!~~*", $1, $4, @2); }
			| a_expr NOT ILIKE a_expr ESCAPE a_expr
				{
					FuncCall *n = makeFuncCall(SystemFuncName("like_escape"),
											   list_make2($4, $6),
											   @2);
					$$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "!~~*", $1, (Node *) n, @2);
				}

			| a_expr SIMILAR TO a_expr				%prec SIMILAR
				{
					FuncCall *n = makeFuncCall(SystemFuncName("similar_escape"),
											   list_make2($4, makeNullAConst(-1)),
											   @2);
					$$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "~", $1, (Node *) n, @2);
				}
			| a_expr SIMILAR TO a_expr ESCAPE a_expr
				{
					FuncCall *n = makeFuncCall(SystemFuncName("similar_escape"),
											   list_make2($4, $6),
											   @2);
					$$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "~", $1, (Node *) n, @2);
				}
			| a_expr NOT SIMILAR TO a_expr			%prec SIMILAR
				{
					FuncCall *n = makeFuncCall(SystemFuncName("similar_escape"),
											   list_make2($5, makeNullAConst(-1)),
											   @2);
					$$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "!~", $1, (Node *) n, @2);
				}
			| a_expr NOT SIMILAR TO a_expr ESCAPE a_expr
				{
					FuncCall *n = makeFuncCall(SystemFuncName("similar_escape"),
											   list_make2($5, $7),
											   @2);
					$$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "!~", $1, (Node *) n, @2);
				}

			/* NullTest clause
			 * Define SQL-style Null test clause.
			 * Allow two forms described in the standard:
			 *	a IS NULL
			 *	a IS NOT NULL
			 * Allow two SQL extensions
			 *	a ISNULL
			 *	a NOTNULL
			 */
			| a_expr IS NULL_P							%prec IS
				{
					NullTest *n = makeNode(NullTest);
					n->arg = (Expr *) $1;
					n->nulltesttype = IS_NULL;
					$$ = (Node *)n;
				}
			| a_expr ISNULL
				{
					NullTest *n = makeNode(NullTest);
					n->arg = (Expr *) $1;
					n->nulltesttype = IS_NULL;
					$$ = (Node *)n;
				}
			| a_expr IS NOT NULL_P						%prec IS
				{
					NullTest *n = makeNode(NullTest);
					n->arg = (Expr *) $1;
					n->nulltesttype = IS_NOT_NULL;
					$$ = (Node *)n;
				}
			| a_expr NOTNULL
				{
					NullTest *n = makeNode(NullTest);
					n->arg = (Expr *) $1;
					n->nulltesttype = IS_NOT_NULL;
					$$ = (Node *)n;
				}
			| row OVERLAPS row
				{
					if (list_length($1) != 2)
						ereport(ERROR,
								(errcode(ERRCODE_SYNTAX_ERROR),
								 errmsg("wrong number of parameters on left side of OVERLAPS expression"),
								 parser_errposition(@1)));
					if (list_length($3) != 2)
						ereport(ERROR,
								(errcode(ERRCODE_SYNTAX_ERROR),
								 errmsg("wrong number of parameters on right side of OVERLAPS expression"),
								 parser_errposition(@3)));
					$$ = (Node *) makeFuncCall(SystemFuncName("overlaps"),
											   list_concat($1, $3),
											   @2);
				}
			| a_expr IS TRUE_P							%prec IS
				{
					BooleanTest *b = makeNode(BooleanTest);
					b->arg = (Expr *) $1;
					b->booltesttype = IS_TRUE;
					$$ = (Node *)b;
				}
			| a_expr IS NOT TRUE_P						%prec IS
				{
					BooleanTest *b = makeNode(BooleanTest);
					b->arg = (Expr *) $1;
					b->booltesttype = IS_NOT_TRUE;
					$$ = (Node *)b;
				}
			| a_expr IS FALSE_P							%prec IS
				{
					BooleanTest *b = makeNode(BooleanTest);
					b->arg = (Expr *) $1;
					b->booltesttype = IS_FALSE;
					$$ = (Node *)b;
				}
			| a_expr IS NOT FALSE_P						%prec IS
				{
					BooleanTest *b = makeNode(BooleanTest);
					b->arg = (Expr *) $1;
					b->booltesttype = IS_NOT_FALSE;
					$$ = (Node *)b;
				}
			| a_expr IS UNKNOWN							%prec IS
				{
					BooleanTest *b = makeNode(BooleanTest);
					b->arg = (Expr *) $1;
					b->booltesttype = IS_UNKNOWN;
					$$ = (Node *)b;
				}
			| a_expr IS NOT UNKNOWN						%prec IS
				{
					BooleanTest *b = makeNode(BooleanTest);
					b->arg = (Expr *) $1;
					b->booltesttype = IS_NOT_UNKNOWN;
					$$ = (Node *)b;
				}
			| a_expr IS DISTINCT FROM a_expr			%prec IS
				{
					$$ = (Node *) makeSimpleA_Expr(AEXPR_DISTINCT, "=", $1, $5, @2);
				}
			| a_expr IS NOT DISTINCT FROM a_expr		%prec IS
				{
					$$ = (Node *) makeA_Expr(AEXPR_NOT, NIL, NULL,
									(Node *) makeSimpleA_Expr(AEXPR_DISTINCT,
															  "=", $1, $6, @2),
											 @2);

				}
			| a_expr IS OF '(' type_list ')'			%prec IS
				{
					$$ = (Node *) makeSimpleA_Expr(AEXPR_OF, "=", $1, (Node *) $5, @2);
				}
			| a_expr IS NOT OF '(' type_list ')'		%prec IS
				{
					$$ = (Node *) makeSimpleA_Expr(AEXPR_OF, "<>", $1, (Node *) $6, @2);
				}
			/*
			 *	Ideally we would not use hard-wired operators below but
			 *	instead use opclasses.  However, mixed data types and other
			 *	issues make this difficult:
			 *	http://archives.postgresql.org/pgsql-hackers/2008-08/msg01142.php
			 */
			| a_expr BETWEEN opt_asymmetric b_expr AND b_expr		%prec BETWEEN
				{
					$$ = (Node *) makeA_Expr(AEXPR_AND, NIL,
						(Node *) makeSimpleA_Expr(AEXPR_OP, ">=", $1, $4, @2),
						(Node *) makeSimpleA_Expr(AEXPR_OP, "<=", $1, $6, @2),
											 @2);
				}
			| a_expr NOT BETWEEN opt_asymmetric b_expr AND b_expr	%prec BETWEEN
				{
					$$ = (Node *) makeA_Expr(AEXPR_OR, NIL,
						(Node *) makeSimpleA_Expr(AEXPR_OP, "<", $1, $5, @2),
						(Node *) makeSimpleA_Expr(AEXPR_OP, ">", $1, $7, @2),
											 @2);
				}
			| a_expr BETWEEN SYMMETRIC b_expr AND b_expr			%prec BETWEEN
				{
					$$ = (Node *) makeA_Expr(AEXPR_OR, NIL,
						(Node *) makeA_Expr(AEXPR_AND, NIL,
							(Node *) makeSimpleA_Expr(AEXPR_OP, ">=", $1, $4, @2),
							(Node *) makeSimpleA_Expr(AEXPR_OP, "<=", $1, $6, @2),
											@2),
						(Node *) makeA_Expr(AEXPR_AND, NIL,
							(Node *) makeSimpleA_Expr(AEXPR_OP, ">=", $1, $6, @2),
							(Node *) makeSimpleA_Expr(AEXPR_OP, "<=", $1, $4, @2),
											@2),
											 @2);
				}
			| a_expr NOT BETWEEN SYMMETRIC b_expr AND b_expr		%prec BETWEEN
				{
					$$ = (Node *) makeA_Expr(AEXPR_AND, NIL,
						(Node *) makeA_Expr(AEXPR_OR, NIL,
							(Node *) makeSimpleA_Expr(AEXPR_OP, "<", $1, $5, @2),
							(Node *) makeSimpleA_Expr(AEXPR_OP, ">", $1, $7, @2),
											@2),
						(Node *) makeA_Expr(AEXPR_OR, NIL,
							(Node *) makeSimpleA_Expr(AEXPR_OP, "<", $1, $7, @2),
							(Node *) makeSimpleA_Expr(AEXPR_OP, ">", $1, $5, @2),
											@2),
											 @2);
				}
			| a_expr IN_P in_expr
				{
					/* in_expr returns a SubLink or a list of a_exprs */
					if (IsA($3, SubLink))
					{
						/* generate foo = ANY (subquery) */
						SubLink *n = (SubLink *) $3;
						n->subLinkType = ANY_SUBLINK;
						n->testexpr = $1;
						n->operName = list_make1(makeString("="));
						n->location = @2;
						$$ = (Node *)n;
					}
					else
					{
						/* generate scalar IN expression */
						$$ = (Node *) makeSimpleA_Expr(AEXPR_IN, "=", $1, $3, @2);
					}
				}
			| a_expr NOT IN_P in_expr
				{
					/* in_expr returns a SubLink or a list of a_exprs */
					if (IsA($4, SubLink))
					{
						/* generate NOT (foo = ANY (subquery)) */
						/* Make an = ANY node */
						SubLink *n = (SubLink *) $4;
						n->subLinkType = ANY_SUBLINK;
						n->testexpr = $1;
						n->operName = list_make1(makeString("="));
						n->location = @3;
						/* Stick a NOT on top */
						$$ = (Node *) makeA_Expr(AEXPR_NOT, NIL, NULL, (Node *) n, @2);
					}
					else
					{
						/* generate scalar NOT IN expression */
						$$ = (Node *) makeSimpleA_Expr(AEXPR_IN, "<>", $1, $4, @2);
					}
				}
			| a_expr subquery_Op sub_type select_with_parens	%prec Op
				{
					SubLink *n = makeNode(SubLink);
					n->subLinkType = $3;
					n->testexpr = $1;
					n->operName = $2;
					n->subselect = $4;
					n->location = @2;
					$$ = (Node *)n;
				}
			| a_expr subquery_Op sub_type '(' a_expr ')'		%prec Op
				{
					if ($3 == ANY_SUBLINK)
						$$ = (Node *) makeA_Expr(AEXPR_OP_ANY, $2, $1, $5, @2);
					else
						$$ = (Node *) makeA_Expr(AEXPR_OP_ALL, $2, $1, $5, @2);
				}
			| UNIQUE select_with_parens
				{
					/* Not sure how to get rid of the parentheses
					 * but there are lots of shift/reduce errors without them.
					 *
					 * Should be able to implement this by plopping the entire
					 * select into a node, then transforming the target expressions
					 * from whatever they are into count(*), and testing the
					 * entire result equal to one.
					 * But, will probably implement a separate node in the executor.
					 */
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("UNIQUE predicate is not yet implemented"),
							 parser_errposition(@1)));
				}
			| a_expr IS DOCUMENT_P					%prec IS
				{
					$$ = makeXmlExpr(IS_DOCUMENT, NULL, NIL,
									 list_make1($1), @2);
				}
			| a_expr IS NOT DOCUMENT_P				%prec IS
				{
					$$ = (Node *) makeA_Expr(AEXPR_NOT, NIL, NULL,
											 makeXmlExpr(IS_DOCUMENT, NULL, NIL,
														 list_make1($1), @2),
											 @2);
				}
		;

/*
 * Restricted expressions
 *
 * b_expr is a subset of the complete expression syntax defined by a_expr.
 *
 * Presently, AND, NOT, IS, and IN are the a_expr keywords that would
 * cause trouble in the places where b_expr is used.  For simplicity, we
 * just eliminate all the boolean-keyword-operator productions from b_expr.
 */
b_expr:		c_expr
				{ $$ = $1; }
			| b_expr TYPECAST Typename
				{ $$ = makeTypeCast($1, $3, @2); }
			| '+' b_expr					%prec UMINUS
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "+", NULL, $2, @1); }
			| '-' b_expr					%prec UMINUS
				{ $$ = doNegate($2, @1); }
			| b_expr '+' b_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "+", $1, $3, @2); }
			| b_expr '-' b_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "-", $1, $3, @2); }
			| b_expr '*' b_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "*", $1, $3, @2); }
			| b_expr '/' b_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "/", $1, $3, @2); }
			| b_expr '%' b_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "%", $1, $3, @2); }
			| b_expr '^' b_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "^", $1, $3, @2); }
			| b_expr '<' b_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "<", $1, $3, @2); }
			| b_expr '>' b_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, ">", $1, $3, @2); }
			| b_expr '=' b_expr
				{ $$ = (Node *) makeSimpleA_Expr(AEXPR_OP, "=", $1, $3, @2); }
			| b_expr qual_Op b_expr				%prec Op
				{ $$ = (Node *) makeA_Expr(AEXPR_OP, $2, $1, $3, @2); }
			| qual_Op b_expr					%prec Op
				{ $$ = (Node *) makeA_Expr(AEXPR_OP, $1, NULL, $2, @1); }
			| b_expr qual_Op					%prec POSTFIXOP
				{ $$ = (Node *) makeA_Expr(AEXPR_OP, $2, $1, NULL, @2); }
			| b_expr IS DISTINCT FROM b_expr		%prec IS
				{
					$$ = (Node *) makeSimpleA_Expr(AEXPR_DISTINCT, "=", $1, $5, @2);
				}
			| b_expr IS NOT DISTINCT FROM b_expr	%prec IS
				{
					$$ = (Node *) makeA_Expr(AEXPR_NOT, NIL,
						NULL, (Node *) makeSimpleA_Expr(AEXPR_DISTINCT, "=", $1, $6, @2), @2);
				}
			| b_expr IS OF '(' type_list ')'		%prec IS
				{
					$$ = (Node *) makeSimpleA_Expr(AEXPR_OF, "=", $1, (Node *) $5, @2);
				}
			| b_expr IS NOT OF '(' type_list ')'	%prec IS
				{
					$$ = (Node *) makeSimpleA_Expr(AEXPR_OF, "<>", $1, (Node *) $6, @2);
				}
			| b_expr IS DOCUMENT_P					%prec IS
				{
					$$ = makeXmlExpr(IS_DOCUMENT, NULL, NIL,
									 list_make1($1), @2);
				}
			| b_expr IS NOT DOCUMENT_P				%prec IS
				{
					$$ = (Node *) makeA_Expr(AEXPR_NOT, NIL, NULL,
											 makeXmlExpr(IS_DOCUMENT, NULL, NIL,
														 list_make1($1), @2),
											 @2);
				}
		;

/*
 * Productions that can be used in both a_expr and b_expr.
 *
 * Note: productions that refer recursively to a_expr or b_expr mostly
 * cannot appear here.	However, it's OK to refer to a_exprs that occur
 * inside parentheses, such as function arguments; that cannot introduce
 * ambiguity to the b_expr syntax.
 */
c_expr:		columnref								{ $$ = $1; }
			| AexprConst							{ $$ = $1; }
			| PARAM opt_indirection
				{
					ParamRef *p = makeNode(ParamRef);
					p->number = $1;
					p->location = @1;
					if ($2)
					{
						A_Indirection *n = makeNode(A_Indirection);
						n->arg = (Node *) p;
						n->indirection = check_indirection($2, yyscanner);
						$$ = (Node *) n;
					}
					else
						$$ = (Node *) p;
				}
			| '(' a_expr ')' opt_indirection
				{
					if ($4)
					{
						A_Indirection *n = makeNode(A_Indirection);
						n->arg = $2;
						n->indirection = check_indirection($4, yyscanner);
						$$ = (Node *)n;
					}
					else
						$$ = $2;
				}
			| case_expr
				{ $$ = $1; }
			| func_expr
				{ $$ = $1; }
			| decode_expr
				{ $$ = $1; }
			| select_with_parens			%prec UMINUS
				{
					SubLink *n = makeNode(SubLink);
					n->subLinkType = EXPR_SUBLINK;
					n->testexpr = NULL;
					n->operName = NIL;
					n->subselect = $1;
					n->location = @1;
					$$ = (Node *)n;
				}
			| select_with_parens indirection
				{
					/*
					 * Because the select_with_parens nonterminal is designed
					 * to "eat" as many levels of parens as possible, the
					 * '(' a_expr ')' opt_indirection production above will
					 * fail to match a sub-SELECT with indirection decoration;
					 * the sub-SELECT won't be regarded as an a_expr as long
					 * as there are parens around it.  To support applying
					 * subscripting or field selection to a sub-SELECT result,
					 * we need this redundant-looking production.
					 */
					SubLink *n = makeNode(SubLink);
					A_Indirection *a = makeNode(A_Indirection);
					n->subLinkType = EXPR_SUBLINK;
					n->testexpr = NULL;
					n->operName = NIL;
					n->subselect = $1;
					n->location = @1;
					a->arg = (Node *)n;
					a->indirection = check_indirection($2, yyscanner);
					$$ = (Node *)a;
				}
			| EXISTS select_with_parens
				{
					SubLink *n = makeNode(SubLink);
					n->subLinkType = EXISTS_SUBLINK;
					n->testexpr = NULL;
					n->operName = NIL;
					n->subselect = $2;
					n->location = @1;
					$$ = (Node *)n;
				}
			| ARRAY select_with_parens
				{
					SubLink *n = makeNode(SubLink);
					n->subLinkType = ARRAY_SUBLINK;
					n->testexpr = NULL;
					n->operName = NIL;
					n->subselect = $2;
					n->location = @1;
					$$ = (Node *)n;
				}
			| ARRAY array_expr
				{
					A_ArrayExpr *n = (A_ArrayExpr *) $2;
					Assert(IsA(n, A_ArrayExpr));
					/* point outermost A_ArrayExpr to the ARRAY keyword */
					n->location = @1;
					$$ = (Node *)n;
				}
            | TABLE '(' table_value_select_clause ')'
				{
					TableValueExpr *n = makeNode(TableValueExpr);
					n->subquery = $3;
					n->location = @1;
					$$ = (Node *)n;
				}
			| row
				{
					RowExpr *r = makeNode(RowExpr);
					r->args = $1;
					r->row_typeid = InvalidOid;	/* not analyzed yet */
					r->colnames = NIL;	/* to be filled in during analysis */
					r->location = @1;
					$$ = (Node *)r;
				}
		;

scatter_clause:
		/* EMPTY */						{ $$ = NIL; }
		| SCATTER RANDOMLY				{ $$ = list_make1(NULL); }
		| SCATTER BY expr_list 			{ $$ = $3; }
  		;

table_value_select_clause:
		SelectStmt scatter_clause
		{
			SelectStmt	*s	 = (SelectStmt *) $1;
			s->scatterClause = $2;
			$$ = (Node *) s;
		}
  		;

func_application: func_name '(' ')'
				{
					$$ = (Node *) makeFuncCall($1, NIL, @1);
				}
			| func_name '(' func_arg_list opt_sort_clause ')'
				{
					FuncCall *n = makeFuncCall($1, $3, @1);
					n->agg_order = $4;
					$$ = (Node *)n;
				}
			| func_name '(' VARIADIC func_arg_expr opt_sort_clause ')'
				{
					FuncCall *n = makeFuncCall($1, list_make1($4), @1);
					n->func_variadic = TRUE;
					n->agg_order = $5;
					$$ = (Node *)n;
				}
			| func_name '(' func_arg_list ',' VARIADIC func_arg_expr opt_sort_clause ')'
				{
					FuncCall *n = makeFuncCall($1, lappend($3, $6), @1);
					n->func_variadic = TRUE;
					n->agg_order = $7;
					$$ = (Node *)n;
				}
			| func_name '(' ALL func_arg_list opt_sort_clause ')'
				{
					FuncCall *n = makeFuncCall($1, $4, @1);
					n->agg_order = $5;
					/* Ideally we'd mark the FuncCall node to indicate
					 * "must be an aggregate", but there's no provision
					 * for that in FuncCall at the moment.
					 */
					n->func_variadic = FALSE;
					n->location = @1;
					n->over = NULL;
					$$ = (Node *)n;
				}
			| func_name '(' DISTINCT func_arg_list opt_sort_clause ')'
				{
					FuncCall *n = makeFuncCall($1, $4, @1);
					n->agg_order = $5;
					n->agg_distinct = TRUE;
					$$ = (Node *)n;
				}
			| func_name '(' '*' ')'
				{
					/*
					 * We consider AGGREGATE(*) to invoke a parameterless
					 * aggregate.  This does the right thing for COUNT(*),
					 * and there are no other aggregates in SQL that accept
					 * '*' as parameter.
					 *
					 * The FuncCall node is also marked agg_star = true,
					 * so that later processing can detect what the argument
					 * really was.
					 */
					FuncCall *n = makeFuncCall($1, NIL, @1);
					n->agg_star = TRUE;
					$$ = (Node *)n;
				}
		;


/*
 * func_expr and its cousin func_expr_windowless are split out from c_expr just
 * so that we have classifications for "everything that is a function call or
 * looks like one".  This isn't very important, but it saves us having to
 * document which variants are legal in places like "FROM function()" or the
 * backwards-compatible functional-index syntax for CREATE INDEX.
 * (Note that many of the special SQL functions wouldn't actually make any
 * sense as functional index entries, but we ignore that consideration here.)
 */
func_expr: func_application within_group_clause filter_clause over_clause
				{
					FuncCall *n = (FuncCall *) $1;
					/*
					 * The order clause for WITHIN GROUP and the one for
					 * plain-aggregate ORDER BY share a field, so we have to
					 * check here that at most one is present.  We also check
					 * for DISTINCT and VARIADIC here to give a better error
					 * location.  Other consistency checks are deferred to
					 * parse analysis.
					 */
					if ($2 != NIL)
					{
						if (n->agg_order != NIL)
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("cannot use multiple ORDER BY clauses with WITHIN GROUP"),
									 parser_errposition(@2)));
						if (n->agg_distinct)
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("cannot use DISTINCT with WITHIN GROUP"),
									 parser_errposition(@2)));
						if (n->func_variadic)
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("cannot use VARIADIC with WITHIN GROUP"),
									 parser_errposition(@2)));
						n->agg_order = $2;
						n->agg_within_group = TRUE;
					}
					n->agg_filter = $3;
					n->over = $4;
					$$ = (Node *) n;
				}
			| func_expr_common_subexpr
				{ $$ = $1; }
		;

/*
 * As func_expr but does not accept WINDOW functions directly
 * (but they can still be contained in arguments for functions etc).
 * Use this when window expressions are not allowed, where needed to
 * disambiguate the grammar (e.g. in CREATE INDEX).
 */
func_expr_windowless:
			func_application						{ $$ = $1; }
			| func_expr_common_subexpr				{ $$ = $1; }
		;

/*
 * Special expressions that are considered to be functions.
 */
func_expr_common_subexpr:
			COLLATION FOR '(' a_expr ')'
				{
					$$ = (Node *) makeFuncCall(SystemFuncName("pg_collation_for"),
											   list_make1($4),
											   @1);
				}
			| CURRENT_DATE
				{
					/*
					 * Translate as "'now'::text::date".
					 *
					 * We cannot use "'now'::date" because coerce_type() will
					 * immediately reduce that to a constant representing
					 * today's date.  We need to delay the conversion until
					 * runtime, else the wrong things will happen when
					 * CURRENT_DATE is used in a column default value or rule.
					 *
					 * This could be simplified if we had a way to generate
					 * an expression tree representing runtime application
					 * of type-input conversion functions.  (As of PG 7.3
					 * that is actually possible, but not clear that we want
					 * to rely on it.)
					 *
					 * The token location is attached to the run-time
					 * typecast, not to the Const, for the convenience of
					 * pg_stat_statements (which doesn't want these constructs
					 * to appear to be replaceable constants).
					 */
					Node *n;
					n = makeStringConstCast("now", -1, SystemTypeName("text"));
					$$ = makeTypeCast(n, SystemTypeName("date"), @1);
				}
			| CURRENT_TIME
				{
					/*
					 * Translate as "'now'::text::timetz".
					 * See comments for CURRENT_DATE.
					 */
					Node *n;
					n = makeStringConstCast("now", -1, SystemTypeName("text"));
					$$ = makeTypeCast(n, SystemTypeName("timetz"), @1);
				}
			| CURRENT_TIME '(' Iconst ')'
				{
					/*
					 * Translate as "'now'::text::timetz(n)".
					 * See comments for CURRENT_DATE.
					 */
					Node *n;
					TypeName *d;
					n = makeStringConstCast("now", -1, SystemTypeName("text"));
					d = SystemTypeName("timetz");
					d->typmods = list_make1(makeIntConst($3, @3));
					$$ = makeTypeCast(n, d, @1);
				}
			| CURRENT_TIMESTAMP
				{
					/*
					 * Translate as "now()", since we have a function that
					 * does exactly what is needed.
					 */
					$$ = (Node *) makeFuncCall(SystemFuncName("now"), NIL, @1);
				}
			| CURRENT_TIMESTAMP '(' Iconst ')'
				{
					/*
					 * Translate as "'now'::text::timestamptz(n)".
					 * See comments for CURRENT_DATE.
					 */
					Node *n;
					TypeName *d;
					n = makeStringConstCast("now", -1, SystemTypeName("text"));
					d = SystemTypeName("timestamptz");
					d->typmods = list_make1(makeIntConst($3, @3));
					$$ = makeTypeCast(n, d, @1);
				}
			| LOCALTIME
				{
					/*
					 * Translate as "'now'::text::time".
					 * See comments for CURRENT_DATE.
					 */
					Node *n;
					n = makeStringConstCast("now", -1, SystemTypeName("text"));
					$$ = makeTypeCast((Node *)n, SystemTypeName("time"), @1);
				}
			| LOCALTIME '(' Iconst ')'
				{
					/*
					 * Translate as "'now'::text::time(n)".
					 * See comments for CURRENT_DATE.
					 */
					Node *n;
					TypeName *d;
					n = makeStringConstCast("now", -1, SystemTypeName("text"));
					d = SystemTypeName("time");
					d->typmods = list_make1(makeIntConst($3, @3));
					$$ = makeTypeCast((Node *)n, d, @1);
				}
			| LOCALTIMESTAMP
				{
					/*
					 * Translate as "'now'::text::timestamp".
					 * See comments for CURRENT_DATE.
					 */
					Node *n;
					n = makeStringConstCast("now", -1, SystemTypeName("text"));
					$$ = makeTypeCast(n, SystemTypeName("timestamp"), @1);
				}
			| LOCALTIMESTAMP '(' Iconst ')'
				{
					/*
					 * Translate as "'now'::text::timestamp(n)".
					 * See comments for CURRENT_DATE.
					 */
					Node *n;
					TypeName *d;
					n = makeStringConstCast("now", -1, SystemTypeName("text"));
					d = SystemTypeName("timestamp");
					d->typmods = list_make1(makeIntConst($3, @3));
					$$ = makeTypeCast(n, d, @1);
				}
			| CURRENT_ROLE
				{
					$$ = (Node *) makeFuncCall(SystemFuncName("current_user"), NIL, @1);
				}
			| CURRENT_USER
				{
					$$ = (Node *) makeFuncCall(SystemFuncName("current_user"), NIL, @1);
				}
			| SESSION_USER
				{
					$$ = (Node *) makeFuncCall(SystemFuncName("session_user"), NIL, @1);
				}
			| USER
				{
					$$ = (Node *) makeFuncCall(SystemFuncName("current_user"), NIL, @1);
				}
			| CURRENT_CATALOG
				{
					$$ = (Node *) makeFuncCall(SystemFuncName("current_database"), NIL, @1);
				}
			| CURRENT_SCHEMA
				{
					$$ = (Node *) makeFuncCall(SystemFuncName("current_schema"), NIL, @1);
				}
			| CAST '(' a_expr AS Typename ')'
				{ $$ = makeTypeCast($3, $5, @1); }
			| EXTRACT '(' extract_list ')'
				{
					$$ = (Node *) makeFuncCall(SystemFuncName("date_part"), $3, @1);
				}
			| OVERLAY '(' overlay_list ')'
				{
					/* overlay(A PLACING B FROM C FOR D) is converted to
					 * overlay(A, B, C, D)
					 * overlay(A PLACING B FROM C) is converted to
					 * overlay(A, B, C)
					 */
					$$ = (Node *) makeFuncCall(SystemFuncName("overlay"), $3, @1);
				}
			| POSITION '(' position_list ')'
				{
					/* position(A in B) is converted to position(B, A) */
					$$ = (Node *) makeFuncCall(SystemFuncName("position"), $3, @1);
				}
			| SUBSTRING '(' substr_list ')'
				{
					/* substring(A from B for C) is converted to
					 * substring(A, B, C) - thomas 2000-11-28
					 */
					$$ = (Node *) makeFuncCall(SystemFuncName("substring"), $3, @1);
				}
			| TREAT '(' a_expr AS Typename ')'
				{
					/* TREAT(expr AS target) converts expr of a particular type to target,
					 * which is defined to be a subtype of the original expression.
					 * In SQL99, this is intended for use with structured UDTs,
					 * but let's make this a generally useful form allowing stronger
					 * coercions than are handled by implicit casting.
					 *
					 * Convert SystemTypeName() to SystemFuncName() even though
					 * at the moment they result in the same thing.
					 */
					$$ = (Node *) makeFuncCall(SystemFuncName(((Value *)llast($5->names))->val.str),
												list_make1($3),
												@1);
				}
			| TRIM '(' BOTH trim_list ')'
				{
					/* various trim expressions are defined in SQL
					 * - thomas 1997-07-19
					 */
					$$ = (Node *) makeFuncCall(SystemFuncName("btrim"), $4, @1);
				}
			| TRIM '(' LEADING trim_list ')'
				{
					$$ = (Node *) makeFuncCall(SystemFuncName("ltrim"), $4, @1);
				}
			| TRIM '(' TRAILING trim_list ')'
				{
					$$ = (Node *) makeFuncCall(SystemFuncName("rtrim"), $4, @1);
				}
			| TRIM '(' trim_list ')'
				{
					$$ = (Node *) makeFuncCall(SystemFuncName("btrim"), $3, @1);
				}
			| NULLIF '(' a_expr ',' a_expr ')'
				{
					$$ = (Node *) makeSimpleA_Expr(AEXPR_NULLIF, "=", $3, $5, @1);
				}
			| COALESCE '(' expr_list ')'
				{
					CoalesceExpr *c = makeNode(CoalesceExpr);
					c->args = $3;
					c->location = @1;
					$$ = (Node *)c;
				}
			| GREATEST '(' expr_list ')'
				{
					MinMaxExpr *v = makeNode(MinMaxExpr);
					v->args = $3;
					v->op = IS_GREATEST;
					v->location = @1;
					$$ = (Node *)v;
				}
			| LEAST '(' expr_list ')'
				{
					MinMaxExpr *v = makeNode(MinMaxExpr);
					v->args = $3;
					v->op = IS_LEAST;
					v->location = @1;
					$$ = (Node *)v;
				}
            | GROUPING '(' expr_list ')'
                {
					GroupingFunc *f = makeNode(GroupingFunc);
					f->args = $3;
					$$ = (Node*)f;
				}

			| GROUP_ID '(' ')'
				{
					GroupId *gid = makeNode(GroupId);
					$$ = (Node *)gid;
				}
			| MEDIAN '(' a_expr ')'
				{
					/*
					 * MEDIAN is parsed as an alias to percentile_cont(0.5).
					 * We keep track of original expression to deparse
					 * it later in views, etc.
					 */
					FuncCall   *n;
					SortBy	   *sortby;

					n = makeNode(FuncCall);
					n->funcname = SystemFuncName("median");
					n->args = list_make1(makeAConst(makeFloat(pstrdup("0.5")), @1));

					sortby = makeNode(SortBy);
					sortby->node = $3;
					sortby->sortby_dir = SORTBY_DEFAULT;
					sortby->sortby_nulls = SORTBY_NULLS_DEFAULT;
					sortby->useOp = NIL;
					sortby->location = -1;		/* no operator */
					n->agg_order = list_make1(sortby);

					n->agg_within_group = TRUE;
					n->agg_filter = NULL;
					n->over = NULL;
					n->location = @1;
					$$ = (Node *) n;
				}
			| DECODE '(' a_expr ',' a_expr ')'
				{
					FuncCall *n = makeNode(FuncCall);
					n->funcname = list_make1(makeString("decode"));
					n->args = list_make2($3, $5);
                    n->agg_order = NIL;
					n->agg_star = FALSE;
					n->agg_distinct = FALSE;
					n->func_variadic = FALSE;
					n->agg_filter = NULL;
					n->location = @1;
					n->over = NULL;
					$$ = (Node *)n;
				}
			| XMLCONCAT '(' expr_list ')'
				{
					$$ = makeXmlExpr(IS_XMLCONCAT, NULL, NIL, $3, @1);
				}
			| XMLELEMENT '(' NAME_P ColLabel ')'
				{
					$$ = makeXmlExpr(IS_XMLELEMENT, $4, NIL, NIL, @1);
				}
			| XMLELEMENT '(' NAME_P ColLabel ',' xml_attributes ')'
				{
					$$ = makeXmlExpr(IS_XMLELEMENT, $4, $6, NIL, @1);
				}
			| XMLELEMENT '(' NAME_P ColLabel ',' expr_list ')'
				{
					$$ = makeXmlExpr(IS_XMLELEMENT, $4, NIL, $6, @1);
				}
			| XMLELEMENT '(' NAME_P ColLabel ',' xml_attributes ',' expr_list ')'
				{
					$$ = makeXmlExpr(IS_XMLELEMENT, $4, $6, $8, @1);
				}
			| XMLEXISTS '(' c_expr xmlexists_argument ')'
				{
					/* xmlexists(A PASSING [BY REF] B [BY REF]) is
					 * converted to xmlexists(A, B)*/
					$$ = (Node *) makeFuncCall(SystemFuncName("xmlexists"), list_make2($3, $4), @1);
				}
			/*
			 * GPDB: In versions 4.3 of GPDB, we had the xmlexists(text, xml)
			 * function, but not this syntactic sugar, and XMLEXISTS was not
			 * a keyword. So there might be applications out there calling
			 * it like "SELECT xmlexists(foo, bar)", which will fail in
			 * PostgreSQL because XMLEXISTS is a keyword. Support that
			 * old syntax, for backwards-compatibiltiy.
			 */
			| XMLEXISTS '(' a_expr ',' a_expr ')'
				{
					FuncCall *n = makeNode(FuncCall);
					n->funcname = SystemFuncName("xmlexists");
					n->args = list_make2($3, $5);
					n->agg_order = NIL;
					n->agg_star = FALSE;
					n->agg_distinct = FALSE;
					n->func_variadic = FALSE;
					n->over = NULL;
					n->location = @1;
					$$ = (Node *)n;
				}
			| XMLFOREST '(' xml_attribute_list ')'
				{
					$$ = makeXmlExpr(IS_XMLFOREST, NULL, $3, NIL, @1);
				}
			| XMLPARSE '(' document_or_content a_expr xml_whitespace_option ')'
				{
					XmlExpr *x = (XmlExpr *)
						makeXmlExpr(IS_XMLPARSE, NULL, NIL,
									list_make2($4, makeBoolAConst($5, -1)),
									@1);
					x->xmloption = $3;
					$$ = (Node *)x;
				}
			| XMLPI '(' NAME_P ColLabel ')'
				{
					$$ = makeXmlExpr(IS_XMLPI, $4, NULL, NIL, @1);
				}
			| XMLPI '(' NAME_P ColLabel ',' a_expr ')'
				{
					$$ = makeXmlExpr(IS_XMLPI, $4, NULL, list_make1($6), @1);
				}
			| XMLROOT '(' a_expr ',' xml_root_version opt_xml_root_standalone ')'
				{
					$$ = makeXmlExpr(IS_XMLROOT, NULL, NIL,
									 list_make3($3, $5, $6), @1);
				}
			| XMLSERIALIZE '(' document_or_content a_expr AS SimpleTypename ')'
				{
					XmlSerialize *n = makeNode(XmlSerialize);
					n->xmloption = $3;
					n->expr = $4;
					n->typeName = $6;
					n->location = @1;
					$$ = (Node *)n;
				}
		;

/*
 * SQL/XML support
 */
xml_root_version: VERSION_P a_expr
				{ $$ = $2; }
			| VERSION_P NO VALUE_P
				{ $$ = makeNullAConst(-1); }
		;

opt_xml_root_standalone: ',' STANDALONE_P YES_P
				{ $$ = makeIntConst(XML_STANDALONE_YES, -1); }
			| ',' STANDALONE_P NO
				{ $$ = makeIntConst(XML_STANDALONE_NO, -1); }
			| ',' STANDALONE_P NO VALUE_P
				{ $$ = makeIntConst(XML_STANDALONE_NO_VALUE, -1); }
			| /*EMPTY*/
				{ $$ = makeIntConst(XML_STANDALONE_OMITTED, -1); }
		;

xml_attributes: XMLATTRIBUTES '(' xml_attribute_list ')'	{ $$ = $3; }
		;

xml_attribute_list:	xml_attribute_el					{ $$ = list_make1($1); }
			| xml_attribute_list ',' xml_attribute_el	{ $$ = lappend($1, $3); }
		;

xml_attribute_el: a_expr AS ColLabel
				{
					$$ = makeNode(ResTarget);
					$$->name = $3;
					$$->indirection = NIL;
					$$->val = (Node *) $1;
					$$->location = @1;
				}
			| a_expr
				{
					$$ = makeNode(ResTarget);
					$$->name = NULL;
					$$->indirection = NIL;
					$$->val = (Node *) $1;
					$$->location = @1;
				}
		;

document_or_content: DOCUMENT_P						{ $$ = XMLOPTION_DOCUMENT; }
			| CONTENT_P								{ $$ = XMLOPTION_CONTENT; }
		;

xml_whitespace_option: PRESERVE WHITESPACE_P		{ $$ = TRUE; }
			| STRIP_P WHITESPACE_P					{ $$ = FALSE; }
			| /*EMPTY*/								{ $$ = FALSE; }
		;

/* We allow several variants for SQL and other compatibility. */
xmlexists_argument:
			PASSING c_expr
				{
					$$ = $2;
				}
			| PASSING c_expr BY REF
				{
					$$ = $2;
				}
			| PASSING BY REF c_expr
				{
					$$ = $4;
				}
			| PASSING BY REF c_expr BY REF
				{
					$$ = $4;
				}
		;


/*
 * Aggregate decoration clauses
 */
within_group_clause:
			WITHIN GROUP_P '(' sort_clause ')'		{ $$ = $4; }
			| /*EMPTY*/								{ $$ = NIL; }
		;

filter_clause:
			FILTER '(' WHERE a_expr ')'				{ $$ = $4; }
			| /*EMPTY*/								{ $$ = NULL; }
		;


/*
 * Window Definitions
 */
window_clause:
			WINDOW window_definition_list			{ $$ = $2; }
			| /*EMPTY*/								{ $$ = NIL; }
		;

window_definition_list:
			window_definition						{ $$ = list_make1($1); }
			| window_definition_list ',' window_definition
													{ $$ = lappend($1, $3); }
		;

window_definition:
			ColId AS window_specification
				{
					WindowDef *n = $3;
					n->name = $1;
					$$ = n;
				}
		;

over_clause: OVER window_specification
				{ $$ = $2; }
			| OVER ColId
				{
					WindowDef *n = makeNode(WindowDef);
					n->name = $2;
					n->refname = NULL;
					n->partitionClause = NIL;
					n->orderClause = NIL;
					n->frameOptions = FRAMEOPTION_DEFAULTS;
					n->startOffset = NULL;
					n->endOffset = NULL;
					n->location = @2;
					$$ = n;
				}
			| /*EMPTY*/
				{ $$ = NULL; }
		;

window_specification: '(' opt_existing_window_name opt_partition_clause
						opt_sort_clause opt_frame_clause ')'
				{
					WindowDef *n = makeNode(WindowDef);
					n->name = NULL;
					n->refname = $2;
					n->partitionClause = $3;
					n->orderClause = $4;
					/* copy relevant fields of opt_frame_clause */
					n->frameOptions = $5->frameOptions;
					n->startOffset = $5->startOffset;
					n->endOffset = $5->endOffset;
					n->location = @1;
					$$ = n;
				}
		;

/*
 * If we see PARTITION, RANGE, or ROWS as the first token after the '('
 * of a window_specification, we want the assumption to be that there is
 * no existing_window_name; but those keywords are unreserved and so could
 * be ColIds.  We fix this by making them have the same precedence as IDENT
 * and giving the empty production here a slightly higher precedence, so
 * that the shift/reduce conflict is resolved in favor of reducing the rule.
 * These keywords are thus precluded from being an existing_window_name but
 * are not reserved for any other purpose.
 */
opt_existing_window_name: ColId						{ $$ = $1; }
			| /*EMPTY*/				%prec Op		{ $$ = NULL; }
		;

opt_partition_clause: PARTITION BY sortby_list { $$ = $3; }
			| /*EMPTY*/ { $$ = NIL; }
		;

/*
 * For frame clauses, we return a WindowDef, but only some fields are used:
 * frameOptions, startOffset, and endOffset.
 *
 * This is only a subset of the full SQL:2008 frame_clause grammar.
 * We don't support <window frame exclusion> yet.
 */
opt_frame_clause:
			RANGE frame_extent
				window_frame_exclusion
				{
					WindowDef *n = $2;
					n->frameOptions |= FRAMEOPTION_NONDEFAULT | FRAMEOPTION_RANGE;
#if 0
					if (n->frameOptions & (FRAMEOPTION_START_VALUE_PRECEDING |
										   FRAMEOPTION_END_VALUE_PRECEDING))
						ereport(ERROR,
								(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
								 errmsg("RANGE PRECEDING is only supported with UNBOUNDED"),
								 parser_errposition(@1)));
					if (n->frameOptions & (FRAMEOPTION_START_VALUE_FOLLOWING |
										   FRAMEOPTION_END_VALUE_FOLLOWING))
						ereport(ERROR,
								(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
								 errmsg("RANGE FOLLOWING is only supported with UNBOUNDED"),
								 parser_errposition(@1)));
#endif
					$$ = n;
				}
			| ROWS frame_extent
				window_frame_exclusion
				{
					WindowDef *n = $2;
					n->frameOptions |= FRAMEOPTION_NONDEFAULT | FRAMEOPTION_ROWS;
					$$ = n;
				}
			| /*EMPTY*/
				{
					WindowDef *n = makeNode(WindowDef);
					n->frameOptions = FRAMEOPTION_DEFAULTS;
					n->startOffset = NULL;
					n->endOffset = NULL;
					$$ = n;
				}
		;

frame_extent: frame_bound
				{
					WindowDef *n = $1;
					/* reject invalid cases */
					if (n->frameOptions & FRAMEOPTION_START_UNBOUNDED_FOLLOWING)
						ereport(ERROR,
								(errcode(ERRCODE_WINDOWING_ERROR),
								 errmsg("frame start cannot be UNBOUNDED FOLLOWING"),
								 parser_errposition(@1)));
					if (n->frameOptions & FRAMEOPTION_START_VALUE_FOLLOWING)
						ereport(ERROR,
								(errcode(ERRCODE_WINDOWING_ERROR),
								 errmsg("frame starting from following row cannot end with current row"),
								 parser_errposition(@1)));
					n->frameOptions |= FRAMEOPTION_END_CURRENT_ROW;
					$$ = n;
				}
			| BETWEEN frame_bound AND frame_bound
				{
					WindowDef *n1 = $2;
					WindowDef *n2 = $4;
					/* form merged options */
					int		frameOptions = n1->frameOptions;
					/* shift converts START_ options to END_ options */
					frameOptions |= n2->frameOptions << 1;
					frameOptions |= FRAMEOPTION_BETWEEN;
					/* reject invalid cases */
					if (frameOptions & FRAMEOPTION_START_UNBOUNDED_FOLLOWING)
						ereport(ERROR,
								(errcode(ERRCODE_WINDOWING_ERROR),
								 errmsg("frame start cannot be UNBOUNDED FOLLOWING"),
								 parser_errposition(@2)));
					if (frameOptions & FRAMEOPTION_END_UNBOUNDED_PRECEDING)
						ereport(ERROR,
								(errcode(ERRCODE_WINDOWING_ERROR),
								 errmsg("frame end cannot be UNBOUNDED PRECEDING"),
								 parser_errposition(@4)));
					if ((frameOptions & FRAMEOPTION_START_CURRENT_ROW) &&
						(frameOptions & FRAMEOPTION_END_VALUE_PRECEDING))
						ereport(ERROR,
								(errcode(ERRCODE_WINDOWING_ERROR),
								 errmsg("frame starting from current row cannot have preceding rows"),
								 parser_errposition(@4)));
					if ((frameOptions & FRAMEOPTION_START_VALUE_FOLLOWING) &&
						(frameOptions & (FRAMEOPTION_END_VALUE_PRECEDING |
										 FRAMEOPTION_END_CURRENT_ROW)))
						ereport(ERROR,
								(errcode(ERRCODE_WINDOWING_ERROR),
								 errmsg("frame starting from following row cannot have preceding rows"),
								 parser_errposition(@4)));
					n1->frameOptions = frameOptions;
					n1->endOffset = n2->startOffset;
					$$ = n1;
				}
		;

/*
 * This is used for both frame start and frame end, with output set up on
 * the assumption it's frame start; the frame_extent productions must reject
 * invalid cases.
 */
frame_bound:
			UNBOUNDED PRECEDING
				{
					WindowDef *n = makeNode(WindowDef);
					n->frameOptions = FRAMEOPTION_START_UNBOUNDED_PRECEDING;
					n->startOffset = NULL;
					n->endOffset = NULL;
					$$ = n;
				}
			| UNBOUNDED FOLLOWING
				{
					WindowDef *n = makeNode(WindowDef);
					n->frameOptions = FRAMEOPTION_START_UNBOUNDED_FOLLOWING;
					n->startOffset = NULL;
					n->endOffset = NULL;
					$$ = n;
				}
			| CURRENT_P ROW
				{
					WindowDef *n = makeNode(WindowDef);
					n->frameOptions = FRAMEOPTION_START_CURRENT_ROW;
					n->startOffset = NULL;
					n->endOffset = NULL;
					$$ = n;
				}
			| a_expr PRECEDING
				{
					WindowDef *n = makeNode(WindowDef);
					n->frameOptions = FRAMEOPTION_START_VALUE_PRECEDING;
					n->startOffset = $1;
					n->endOffset = NULL;
					$$ = n;
				}
			| a_expr FOLLOWING
				{
					WindowDef *n = makeNode(WindowDef);
					n->frameOptions = FRAMEOPTION_START_VALUE_FOLLOWING;
					n->startOffset = $1;
					n->endOffset = NULL;
					$$ = n;
				}
		;

window_frame_exclusion: EXCLUDE CURRENT_P ROW { checkWindowExclude(); $$ = 0; }
			| EXCLUDE GROUP_P { checkWindowExclude(); $$ = 0; }
			| EXCLUDE TIES { checkWindowExclude(); $$ = 0; }
			| EXCLUDE NO OTHERS { checkWindowExclude(); $$ = 0; }
			| /*EMPTY*/ { $$ = 0; }
		;


/*
 * Supporting nonterminals for expressions.
 */

/* Explicit row production.
 *
 * SQL99 allows an optional ROW keyword, so we can now do single-element rows
 * without conflicting with the parenthesized a_expr production.  Without the
 * ROW keyword, there must be more than one a_expr inside the parens.
 */
row:		ROW '(' expr_list ')'					{ $$ = $3; }
			| ROW '(' ')'							{ $$ = NIL; }
			| '(' expr_list ',' a_expr ')'			{ $$ = lappend($2, $4); }
		;

sub_type:	ANY										{ $$ = ANY_SUBLINK; }
			| SOME									{ $$ = ANY_SUBLINK; }
			| ALL									{ $$ = ALL_SUBLINK; }
		;

all_Op:		Op										{ $$ = $1; }
			| MathOp								{ $$ = $1; }
		;

MathOp:		 '+'									{ $$ = "+"; }
			| '-'									{ $$ = "-"; }
			| '*'									{ $$ = "*"; }
			| '/'									{ $$ = "/"; }
			| '%'									{ $$ = "%"; }
			| '^'									{ $$ = "^"; }
			| '<'									{ $$ = "<"; }
			| '>'									{ $$ = ">"; }
			| '='									{ $$ = "="; }
		;

qual_Op:	Op
					{ $$ = list_make1(makeString($1)); }
			| OPERATOR '(' any_operator ')'
					{ $$ = $3; }
		;

qual_all_Op:
			all_Op
					{ $$ = list_make1(makeString($1)); }
			| OPERATOR '(' any_operator ')'
					{ $$ = $3; }
		;

subquery_Op:
			all_Op
					{ $$ = list_make1(makeString($1)); }
			| OPERATOR '(' any_operator ')'
					{ $$ = $3; }
			| LIKE
					{ $$ = list_make1(makeString("~~")); }
			| NOT LIKE
					{ $$ = list_make1(makeString("!~~")); }
			| ILIKE
					{ $$ = list_make1(makeString("~~*")); }
			| NOT ILIKE
					{ $$ = list_make1(makeString("!~~*")); }
/* cannot put SIMILAR TO here, because SIMILAR TO is a hack.
 * the regular expression is preprocessed by a function (similar_escape),
 * and the ~ operator for posix regular expressions is used.
 *        x SIMILAR TO y     ->    x ~ similar_escape(y)
 * this transformation is made on the fly by the parser upwards.
 * however the SubLink structure which handles any/some/all stuff
 * is not ready for such a thing.
 */
			;

expr_list:	a_expr
				{
					$$ = list_make1($1);
				}
			| expr_list ',' a_expr
				{
					$$ = lappend($1, $3);
				}
		;

/* function arguments can have names */
func_arg_list:  func_arg_expr
				{
					$$ = list_make1($1);
				}
			| func_arg_list ',' func_arg_expr
				{
					$$ = lappend($1, $3);
				}
		;

func_arg_expr:  a_expr
				{
					$$ = $1;
				}
			| param_name COLON_EQUALS a_expr
				{
					NamedArgExpr *na = makeNode(NamedArgExpr);
					na->name = $1;
					na->arg = (Expr *) $3;
					na->argnumber = -1;		/* until determined */
					na->location = @1;
					$$ = (Node *) na;
				}
		;

type_list:	Typename								{ $$ = list_make1($1); }
			| type_list ',' Typename				{ $$ = lappend($1, $3); }
		;

array_expr: '[' expr_list ']'
				{
					$$ = makeAArrayExpr($2, @1);
				}
			| '[' array_expr_list ']'
				{
					$$ = makeAArrayExpr($2, @1);
				}
			| '[' ']'
				{
					$$ = makeAArrayExpr(NIL, @1);
				}
		;

array_expr_list: array_expr							{ $$ = list_make1($1); }
			| array_expr_list ',' array_expr		{ $$ = lappend($1, $3); }
		;


extract_list:
			extract_arg FROM a_expr
				{
					$$ = list_make2(makeStringConst($1, @1), $3);
				}
			| /*EMPTY*/								{ $$ = NIL; }
		;

/* Allow delimited string Sconst in extract_arg as an SQL extension.
 * - thomas 2001-04-12
 */
extract_arg:
			IDENT									{ $$ = $1; }
			| YEAR_P								{ $$ = "year"; }
			| MONTH_P								{ $$ = "month"; }
			| DAY_P									{ $$ = "day"; }
			| HOUR_P								{ $$ = "hour"; }
			| MINUTE_P								{ $$ = "minute"; }
			| SECOND_P								{ $$ = "second"; }
			| Sconst								{ $$ = $1; }
		;

/* OVERLAY() arguments
 * SQL99 defines the OVERLAY() function:
 * o overlay(text placing text from int for int)
 * o overlay(text placing text from int)
 * and similarly for binary strings
 */
overlay_list:
			a_expr overlay_placing substr_from substr_for
				{
					$$ = list_make4($1, $2, $3, $4);
				}
			| a_expr overlay_placing substr_from
				{
					$$ = list_make3($1, $2, $3);
				}
		;

overlay_placing:
			PLACING a_expr
				{ $$ = $2; }
		;

/* position_list uses b_expr not a_expr to avoid conflict with general IN */

position_list:
			b_expr IN_P b_expr						{ $$ = list_make2($3, $1); }
			| /*EMPTY*/								{ $$ = NIL; }
		;

/* SUBSTRING() arguments
 * SQL9x defines a specific syntax for arguments to SUBSTRING():
 * o substring(text from int for int)
 * o substring(text from int) get entire string from starting point "int"
 * o substring(text for int) get first "int" characters of string
 * o substring(text from pattern) get entire string matching pattern
 * o substring(text from pattern for escape) same with specified escape char
 * We also want to support generic substring functions which accept
 * the usual generic list of arguments. So we will accept both styles
 * here, and convert the SQL9x style to the generic list for further
 * processing. - thomas 2000-11-28
 */
substr_list:
			a_expr substr_from substr_for
				{
					$$ = list_make3($1, $2, $3);
				}
			| a_expr substr_for substr_from
				{
					/* not legal per SQL99, but might as well allow it */
					$$ = list_make3($1, $3, $2);
				}
			| a_expr substr_from
				{
					$$ = list_make2($1, $2);
				}
			| a_expr substr_for
				{
					/*
					 * Since there are no cases where this syntax allows
					 * a textual FOR value, we forcibly cast the argument
					 * to int4.  The possible matches in pg_proc are
					 * substring(text,int4) and substring(text,text),
					 * and we don't want the parser to choose the latter,
					 * which it is likely to do if the second argument
					 * is unknown or doesn't have an implicit cast to int4.
					 */
					$$ = list_make3($1, makeIntConst(1, -1),
									makeTypeCast($2,
												 SystemTypeName("int4"), -1));
				}
			| expr_list
				{
					$$ = $1;
				}
			| /*EMPTY*/
				{ $$ = NIL; }
		;

substr_from:
			FROM a_expr								{ $$ = $2; }
		;

substr_for: FOR a_expr								{ $$ = $2; }
		;

trim_list:	a_expr FROM expr_list					{ $$ = lappend($3, $1); }
			| FROM expr_list						{ $$ = $2; }
			| expr_list								{ $$ = $1; }
		;

in_expr:	select_with_parens
				{
					SubLink *n = makeNode(SubLink);
					n->subselect = $1;
					/* other fields will be filled later */
					$$ = (Node *)n;
				}
			| '(' expr_list ')'						{ $$ = (Node *)$2; }
		;

/*
 * Define SQL-style CASE clause.
 * - Full specification
 *	CASE WHEN a = b THEN c ... ELSE d END
 * - Implicit argument
 *	CASE a WHEN b THEN c ... ELSE d END
 */
case_expr:	CASE case_arg when_clause_list case_default END_P
				{
					CaseExpr *c = makeNode(CaseExpr);
					c->casetype = InvalidOid; /* not analyzed yet */
					c->arg = (Expr *) $2;
					c->args = $3;
					c->defresult = (Expr *) $4;
					c->location = @1;
					$$ = (Node *)c;
				}
		;

when_clause_list:
			/* There must be at least one */
			when_clause								{ $$ = list_make1($1); }
			| when_clause_list when_clause			{ $$ = lappend($1, $2); }
		;

when_clause:
			WHEN when_operand THEN a_expr
				{
					CaseWhen *w = makeNode(CaseWhen);
					w->expr = (Expr *) $2;
					w->result = (Expr *) $4;
					w->location = @1;
					$$ = (Node *)w;
				}
			;

when_operand:
			a_expr							{ $$ = $1; }
			| IS NOT DISTINCT FROM a_expr	{ $$ = makeIsNotDistinctFromNode($5,@2); }
		;

case_default:
			ELSE a_expr								{ $$ = $2; }
			| /*EMPTY*/								{ $$ = NULL; }
		;

case_arg:	a_expr									{ $$ = $1; }
			| /*EMPTY*/								{ $$ = NULL; }
		;


/*
 * Oracle-compatible DECODE function:
 * DECODE(lhs, rhs, res [, rhs2, res2 ]... [, def_res]): 
 * 		returns resX if lhs = rhsX, or def_res if no match found
 * It is transformed into: 
 *		CASE lhs WHEN IS NOT DISTINCT FROM rhs THEN res
 *				[WHEN IS NOT DISTINCT FROM rhs2 THEN res2] ... 
 *			ELSE def_res END
 */
decode_expr:	
			DECODE '(' a_expr search_result_list decode_default ')'
				{
					CaseExpr *c = makeNode(CaseExpr);
					c->casetype = InvalidOid; /* not analyzed yet */
					c->arg = (Expr *) $3;
					c->args = $4;
					c->defresult = (Expr *) $5;
					$$ = (Node *) c;
				}
		;
			
search_result_list: 
			search_result							{ $$ = list_make1($1); }
			| search_result_list search_result		{ $$ = lappend($1, $2); }
		;

search_result:
			',' a_expr ',' a_expr
				{
					Node *n = makeIsNotDistinctFromNode($2,@2);
					CaseWhen *w = makeNode(CaseWhen);
					w->expr = (Expr *) n;
					w->result = (Expr *) $4;
					$$ = (Node *) w;
				}
		;
				
decode_default: 	
			',' a_expr	 					{ $$ = $2; }
			| /*EMPTY*/						{ $$ = NULL; }
		;


columnref:	ColId
				{
					$$ = makeColumnRef($1, NIL, @1, yyscanner);
				}
			| ColId indirection
				{
					$$ = makeColumnRef($1, $2, @1, yyscanner);
				}
		;

indirection_el:
			'.' attr_name
				{
					$$ = (Node *) makeString($2);
				}
			| '.' '*'
				{
					$$ = (Node *) makeNode(A_Star);
				}
			| '[' a_expr ']'
				{
					A_Indices *ai = makeNode(A_Indices);
					ai->lidx = NULL;
					ai->uidx = $2;
					$$ = (Node *) ai;
				}
			| '[' a_expr ':' a_expr ']'
				{
					A_Indices *ai = makeNode(A_Indices);
					ai->lidx = $2;
					ai->uidx = $4;
					$$ = (Node *) ai;
				}
		;

indirection:
			indirection_el							{ $$ = list_make1($1); }
			| indirection indirection_el			{ $$ = lappend($1, $2); }
		;

opt_indirection:
			/*EMPTY*/								{ $$ = NIL; }
			| opt_indirection indirection_el		{ $$ = lappend($1, $2); }
		;

opt_asymmetric: ASYMMETRIC
			| /*EMPTY*/
		;

/*
 * The SQL spec defines "contextually typed value expressions" and
 * "contextually typed row value constructors", which for our purposes
 * are the same as "a_expr" and "row" except that DEFAULT can appear at
 * the top level.
 */

ctext_expr:
			a_expr					{ $$ = (Node *) $1; }
			| DEFAULT
				{
					SetToDefault *n = makeNode(SetToDefault);
					n->location = @1;
					$$ = (Node *) n;
				}
		;

ctext_expr_list:
			ctext_expr								{ $$ = list_make1($1); }
			| ctext_expr_list ',' ctext_expr		{ $$ = lappend($1, $3); }
		;

/*
 * We should allow ROW '(' ctext_expr_list ')' too, but that seems to require
 * making VALUES a fully reserved word, which will probably break more apps
 * than allowing the noise-word is worth.
 */
ctext_row: '(' ctext_expr_list ')'					{ $$ = $2; }
		;


/*****************************************************************************
 *
 *	target list for SELECT
 *
 *****************************************************************************/

opt_target_list: target_list						{ $$ = $1; }
			| /* EMPTY */							{ $$ = NIL; }
		;

target_list:
			target_el								{ $$ = list_make1($1); }
			| target_list ',' target_el				{ $$ = lappend($1, $3); }
		;

target_el:	a_expr AS ColLabel
				{
					$$ = makeNode(ResTarget);
					$$->name = $3;
					$$->indirection = NIL;
					$$->val = (Node *)$1;
					$$->location = @1;
				}
			/*
			 * Postgres supports omitting AS only for column labels that aren't
			 * any known keyword.  There is an ambiguity against postfix
			 * operators: is "a ! b" an infix expression, or a postfix
			 * expression and a column label?  We prefer to resolve this
			 * as an infix expression, which we accomplish by assigning
			 * IDENT a precedence higher than POSTFIXOP.
			 *
			 * In GPDB, we extend this to allow most unreserved_keywords by
			 * also assigning them a precedence.  There are certain keywords
			 * that can't work without the as: reserved_keywords, the date
			 * modifier suffixes (DAY, MONTH, YEAR, etc) and a few other
			 * obscure cases.
			 */
			| a_expr IDENT
				{
					$$ = makeNode(ResTarget);
					$$->name = $2;
					$$->indirection = NIL;
					$$->val = (Node *)$1;
					$$->location = @1;
				}
			| a_expr ColLabelNoAs
				{
					$$ = makeNode(ResTarget);
					$$->name = $2;
					$$->indirection = NIL;
					$$->val = (Node *)$1;
					$$->location = @1;
				}
			| a_expr
				{
					$$ = makeNode(ResTarget);
					$$->name = NULL;
					$$->indirection = NIL;
					$$->val = (Node *)$1;
					$$->location = @1;
				}
			| '*'
				{
					ColumnRef *n = makeNode(ColumnRef);
					n->fields = list_make1(makeNode(A_Star));
					n->location = @1;

					$$ = makeNode(ResTarget);
					$$->name = NULL;
					$$->indirection = NIL;
					$$->val = (Node *)n;
					$$->location = @1;
				}
		;


/*****************************************************************************
 *
 *	Names and constants
 *
 *****************************************************************************/

qualified_name_list:
			qualified_name							{ $$ = list_make1($1); }
			| qualified_name_list ',' qualified_name { $$ = lappend($1, $3); }
		;

/*
 * The production for a qualified relation name has to exactly match the
 * production for a qualified func_name, because in a FROM clause we cannot
 * tell which we are parsing until we see what comes after it ('(' for a
 * func_name, something else for a relation). Therefore we allow 'indirection'
 * which may contain subscripts, and reject that case in the C code.
 */
qualified_name:
			ColId
				{
					$$ = makeRangeVar(NULL, $1, @1);
				}
			| ColId indirection
				{
					check_qualified_name($2, yyscanner);
					$$ = makeRangeVar(NULL, NULL, @1);
					switch (list_length($2))
					{
						case 1:
							$$->catalogname = NULL;
							$$->schemaname = $1;
							$$->relname = strVal(linitial($2));
							break;
						case 2:
							$$->catalogname = $1;
							$$->schemaname = strVal(linitial($2));
							$$->relname = strVal(lsecond($2));
							break;
						default:
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("improper qualified name (too many dotted names): %s",
											NameListToString(lcons(makeString($1), $2))),
									 parser_errposition(@1)));
							break;
					}
				}
		;

name_list:	name
					{ $$ = list_make1(makeString($1)); }
			| name_list ',' name
					{ $$ = lappend($1, makeString($3)); }
		;


name:		ColId									{ $$ = $1; };

database_name:
			ColId									{ $$ = $1; };

access_method:
			ColId									{ $$ = $1; };

attr_name:	ColLabel								{ $$ = $1; };

index_name: ColId									{ $$ = $1; };

file_name:	Sconst									{ $$ = $1; };

/*
 * The production for a qualified func_name has to exactly match the
 * production for a qualified columnref, because we cannot tell which we
 * are parsing until we see what comes after it ('(' or Sconst for a func_name,
 * anything else for a columnref).  Therefore we allow 'indirection' which
 * may contain subscripts, and reject that case in the C code.  (If we
 * ever implement SQL99-like methods, such syntax may actually become legal!)
 */
func_name:	type_function_name
					{ $$ = list_make1(makeString($1)); }
			| ColId indirection
					{
						$$ = check_func_name(lcons(makeString($1), $2),
											 yyscanner);
					}
		;


/*
 * Constants
 */
AexprConst: Iconst
				{
					$$ = makeIntConst($1, @1);
				}
			| FCONST
				{
					$$ = makeFloatConst($1, @1);
				}
			| Sconst
				{
					$$ = makeStringConst($1, @1);
				}
			| BCONST
				{
					$$ = makeBitStringConst($1, @1);
				}
			| XCONST
				{
					/* This is a bit constant per SQL99:
					 * Without Feature F511, "BIT data type",
					 * a <general literal> shall not be a
					 * <bit string literal> or a <hex string literal>.
					 */
					$$ = makeBitStringConst($1, @1);
				}
			| func_name Sconst
				{
					/* generic type 'literal' syntax */
					TypeName *t = makeTypeNameFromNameList($1);
					t->location = @1;
					$$ = makeStringConstCast($2, @2, t);
				}
			| func_name '(' func_arg_list opt_sort_clause ')' Sconst
				{
					/* generic syntax with a type modifier */
					TypeName *t = makeTypeNameFromNameList($1);
					ListCell *lc;

					/*
					 * We must use func_arg_list and opt_sort_clause in the
					 * production to avoid reduce/reduce conflicts, but we
					 * don't actually wish to allow NamedArgExpr in this
					 * context, nor ORDER BY.
					 */
					foreach(lc, $3)
					{
						NamedArgExpr *arg = (NamedArgExpr *) lfirst(lc);

						if (IsA(arg, NamedArgExpr))
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("type modifier cannot have parameter name"),
									 parser_errposition(arg->location)));
					}
					if ($4 != NIL)
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("type modifier cannot have ORDER BY"),
									 parser_errposition(@4)));

					t->typmods = $3;
					t->location = @1;
					$$ = makeStringConstCast($6, @6, t);
				}
			| ConstTypename Sconst
				{
					$$ = makeStringConstCast($2, @2, $1);
				}
			| ConstInterval Sconst opt_interval
				{
					TypeName *t = $1;
					t->typmods = $3;
					$$ = makeStringConstCast($2, @2, t);
				}
			| ConstInterval '(' Iconst ')' Sconst opt_interval
				{
					TypeName *t = $1;
					if ($6 != NIL)
					{
						if (list_length($6) != 1)
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("interval precision specified twice"),
									 parser_errposition(@1)));
						t->typmods = lappend($6, makeIntConst($3, @3));
					}
					else
						t->typmods = list_make2(makeIntConst(INTERVAL_FULL_RANGE, -1),
												makeIntConst($3, @3));
					$$ = makeStringConstCast($5, @5, t);
				}
			| TRUE_P
				{
					$$ = makeBoolAConst(TRUE, @1);
				}
			| FALSE_P
				{
					$$ = makeBoolAConst(FALSE, @1);
				}
			| NULL_P
				{
					$$ = makeNullAConst(@1);
				}
		;

Iconst:		ICONST									{ $$ = $1; };
Sconst:		SCONST									{ $$ = $1; };
RoleId:		NonReservedWord							{ $$ = $1; };
QueueId:	NonReservedWord							{ $$ = $1; };

role_list:	RoleId
					{ $$ = list_make1(makeString($1)); }
			| role_list ',' RoleId
					{ $$ = lappend($1, makeString($3)); }
		;

SignedIconst: Iconst								{ $$ = $1; }
			| '+' Iconst							{ $$ = + $2; }
			| '-' Iconst							{ $$ = - $2; }
		;

/*
 * Name classification hierarchy.
 *
 * IDENT is the lexeme returned by the lexer for identifiers that match
 * no known keyword.  In most cases, we can accept certain keywords as
 * names, not only IDENTs.	We prefer to accept as many such keywords
 * as possible to minimize the impact of "reserved words" on programmers.
 * So, we divide names into several possible classes.  The classification
 * is chosen in part to make keywords acceptable as names wherever possible.
 */

/* Column identifier --- names that can be column, table, etc names.
 */
ColId:		IDENT									{ $$ = $1; }
			| unreserved_keyword					{ $$ = pstrdup($1); }
			| col_name_keyword						{ $$ = pstrdup($1); }
		;

/* Type/function identifier --- names that can be type or function names.
 */
type_function_name:	IDENT							{ $$ = $1; }
			| unreserved_keyword					{ $$ = pstrdup($1); }
			| type_func_name_keyword				{ $$ = pstrdup($1); }
		;

/* Any not-fully-reserved word --- these names can be, eg, role names.
 */
NonReservedWord:	IDENT							{ $$ = $1; }
			| unreserved_keyword					{ $$ = pstrdup($1); }
			| col_name_keyword						{ $$ = pstrdup($1); }
			| type_func_name_keyword				{ $$ = pstrdup($1); }
		;

/* Column label --- allowed labels in "AS" clauses.
 * This presently includes *all* Postgres keywords.
 */
ColLabel:	IDENT									{ $$ = $1; }
			| unreserved_keyword					{ $$ = pstrdup($1); }
			| col_name_keyword						{ $$ = pstrdup($1); }
			| type_func_name_keyword				{ $$ = pstrdup($1); }
			| reserved_keyword						{ $$ = pstrdup($1); }
		;


/*
 * Keyword category lists.  Generally, every keyword present in
 * the Postgres grammar should appear in exactly one of these lists.
 *
 * Put a new keyword into the first list that it can go into without causing
 * shift or reduce conflicts.  The earlier lists define "less reserved"
 * categories of keywords.
 *
 * Make sure that each keyword's category in kwlist.h matches where
 * it is listed here.  (Someday we may be able to generate these lists and
 * kwlist.h's table from a common master list.)
 */

/* "Unreserved" keywords --- available for use as any kind of name.
 */
unreserved_keyword:
			  ABORT_P
			| ABSOLUTE_P
			| ACCESS
			| ACTION
			| ACTIVE
			| ADD_P
			| ADMIN
			| AFTER
			| AGGREGATE
			| ALSO
			| ALTER
			| ALWAYS
			| ASSERTION
			| ASSIGNMENT
			| AT
			| ATTRIBUTE
			| BACKWARD
			| BEFORE
			| BEGIN_P
			| BY
			| CACHE
			| CALLED
			| CASCADE
			| CASCADED
			| CATALOG_P
			| CHAIN
			| CHARACTERISTICS
			| CHECKPOINT
			| CLASS
			| CLOSE
			| CLUSTER
			| COMMENT
			| COMMENTS
			| COMMIT
			| COMMITTED
			| CONCURRENCY
			| CONFIGURATION
			| CONNECTION
			| CONSTRAINTS
			| CONTAINS
			| CONTENT_P
			| CONTINUE_P
			| CONVERSION_P
			| COPY
			| COST
			| CPUSET
			| CPU_RATE_LIMIT
			| CREATEEXTTABLE
			| CSV
			| CUBE
			| CURRENT_P
			| CURSOR
			| CYCLE
			| DATA_P
			| DATABASE
			| DAY_P
			| DEALLOCATE
			| DECLARE
			| DEFAULTS
			| DEFERRED
			| DEFINER
			| DELETE_P
			| DELIMITER
			| DELIMITERS
			| DENY
			| DICTIONARY
			| DISABLE_P
			| DISCARD
			| DOCUMENT_P
			| DOMAIN_P
			| DOUBLE_P
			| DROP
			| DXL
			| EACH
			| ENABLE_P
			| ENCODING
			| ENCRYPTED
			| ENDPOINT
			| ENUM_P
			| ERRORS
			| ESCAPE
			| EVENT
			| EVERY
			| EXCHANGE
			| EXCLUDING
			| EXCLUSIVE
			| EXECUTE
			| EXPAND
			| EXPLAIN
			| EXTENSION
			| EXTERNAL
			| FAMILY
			| FIELDS
			| FILL
			| FILTER
			| FIRST_P
			| FORCE
			| FORMAT
			| FORWARD
			| FULLSCAN
			| FUNCTION
			| FUNCTIONS
			| GLOBAL
			| GRANTED
			| HANDLER
			| HASH
			| HEADER_P
			| HOLD
			| HOST
			| HOUR_P
			| IDENTITY_P
			| IF_P
			| IGNORE_P
			| IMMEDIATE
			| IMMUTABLE
			| IMPLICIT_P
			| INCLUDING
			| INCLUSIVE
			| INCREMENT
			| INDEX
			| INDEXES
			| INHERIT
			| INHERITS
			| INITPLAN
			| INLINE_P
			| INPUT_P
			| INSENSITIVE
			| INSERT
			| INSTEAD
			| INVOKER
			| ISOLATION
			| KEY
			| LABEL
			| LANGUAGE
			| LARGE_P
			| LAST_P
			| LC_COLLATE_P
			| LC_CTYPE_P
			| LEAKPROOF
			| LEVEL
			| LIST
			| LISTEN
			| LOAD
			| LOCAL
			| LOCATION
			| LOCK_P
			| LOG_P
			| MAPPING
			| MASTER
			| MATCH
			| MATERIALIZED
			| MAXVALUE
			| MEMORY_LIMIT
			| MEMORY_SHARED_QUOTA
			| MEMORY_SPILL_RATIO
			| MINUTE_P
			| MINVALUE
			| MISSING
			| MODE
			| MODIFIES
			| MONTH_P
			| MOVE
			| NAME_P
			| NAMES
			| NEWLINE
			| NEXT
			| NO
			| NOCREATEEXTTABLE
			| NOOVERCOMMIT
			| NOTHING
			| NOTIFY
			| NOWAIT
			| NULLS_P
			| OBJECT_P
			| OF
			| OFF
			| OIDS
			| OPERATOR
			| OPTION
			| OPTIONS
			| ORDERED
			| ORDINALITY
			| OTHERS
			| OVER
			| OVERCOMMIT
			| OWNED
			| OWNER
			| PARALLEL
			| PARSER
			| PARTIAL
			| PARTITIONS
			| PASSING
			| PASSWORD
			| PERCENT
			| PERSISTENTLY
			| PLANS
			| PREPARE
			| PREPARED
			| PRESERVE
			| PRIOR
			| PRIVILEGES
			| PROCEDURAL
			| PROCEDURE
			| PROGRAM
			| PROTOCOL
			| QUEUE
			| QUOTE
			| RANDOMLY /* gp */
			| RANGE
			| READ
			| READABLE
			| READS
			| REASSIGN
			| RECHECK
			| RECURSIVE
			| REF
			| REFRESH
			| REINDEX
			| REJECT_P /* gp */
			| RELATIVE_P
			| RELEASE
			| RENAME
			| REPEATABLE
			| REPLACE
			| REPLICA
			| REPLICATED
			| RESET
			| RESOURCE
			| RESTART
			| RESTRICT
			| RETRIEVE
			| RETURNS
			| REVOKE
			| ROLE
			| ROLLBACK
			| ROOTPARTITION
			| ROWS
			| RULE
			| SAVEPOINT
			| SCHEMA
			| SCROLL
			| SEARCH
			| SECOND_P
			| SECURITY
			| SEGMENT
			| SEGMENTS
			| SEQUENCE
			| SEQUENCES
			| SERIALIZABLE
			| SERVER
			| SESSION
			| SET
			| SHARE
			| SHOW
			| SIMPLE
			| SNAPSHOT
			| SPLIT
			| SQL
			| STABLE
			| STANDALONE_P
			| START
			| STATEMENT
			| STATISTICS
			| STDIN
			| STDOUT
			| STORAGE
			| STRICT_P
			| STRIP_P
			| SUBPARTITION
			| SYSID
			| SYSTEM_P
			| TABLES
			| TABLESPACE
			| TEMP
			| TEMPLATE
			| TEMPORARY
			| TEXT_P
			| THRESHOLD
			| TIES
			| TRANSACTION
			| TRIGGER
			| TRUNCATE
			| TRUSTED
			| TYPE_P
			| TYPES_P
			| UNCOMMITTED
			| UNENCRYPTED
			| UNKNOWN
			| UNLISTEN
			| UNLOGGED
			| UNTIL
			| UPDATE
			| VACUUM
			| VALID
			| VALIDATE
			| VALIDATION /* gp */
			| VALIDATOR
			| VALUE_P
			| VARYING
			| VERSION_P
			| VIEW
			| VIEWS
			| VOLATILE
			| WEB /* gp */
			| WHITESPACE_P
			| WITHIN
			| WITHOUT
			| WORK
			| WRAPPER
			| WRITABLE
			| WRITE
			| XML_P
			| YEAR_P
			| YES_P
			| ZONE
		;

/*
 * ColLabelNoAs is used for SELECT element aliases that don't have the
 * AS keyword.  We always allow IDENT, so anything in double-quotes is
 * also OK.  Beyond that, any keywords listed here can be a column
 * alias even when you omit the AS keyword.
 *
 * We could add some of the reserved_keywords to this list, but I'm
 * reluctant to do so because it might restrict future enhancements to
 * the grammar.
 */

ColLabelNoAs:   keywords_ok_in_alias_no_as   { $$=pstrdup($1); }
				;

keywords_ok_in_alias_no_as: PartitionIdentKeyword
			| TABLESPACE
			| ADD_P
			| ALTER
			| AT
			;

PartitionColId: PartitionIdentKeyword { $$ = pstrdup($1); }
			| IDENT { $$ = pstrdup($1); }
			;

PartitionIdentKeyword: ABORT_P
			| ABSOLUTE_P
			| ACCESS
			| ACTION
			| ACTIVE
			| ADMIN
			| AFTER
			| AGGREGATE
			| ALSO
			| ASSERTION
			| ASSIGNMENT
			| BACKWARD
			| BEFORE
			| BEGIN_P
			| BY
			| CACHE
			| CALLED
			| CASCADE
			| CASCADED
			| CHAIN
			| CHARACTERISTICS
			| CHECKPOINT
			| CLASS
			| CLOSE
			| CLUSTER
			| COMMENT
			| COMMIT
			| COMMITTED
			| CONCURRENCY
			| CONNECTION
			| CONSTRAINTS
			| CONTAINS
			| CONTENT_P
			| CONVERSION_P
			| COPY
			| COST
			| CPUSET
			| CPU_RATE_LIMIT
			| CREATEEXTTABLE
			| CSV
			| CURSOR
			| CYCLE
			| DATABASE
			| DEALLOCATE
			| DECLARE
			| DEFAULTS
			| DEFERRED
			| DEFINER
			| DELETE_P
			| DELIMITER
			| DELIMITERS
			| DISABLE_P
			| DOMAIN_P
			| DOUBLE_P
			| DROP
			| EACH
			| ENABLE_P
			| ENCODING
			| ENCRYPTED
			| ENDPOINT
			| ERRORS
			| ENUM_P
			| ESCAPE
			| EVERY
			| EXCHANGE
			| EXCLUDING
			| EXCLUSIVE
			| EXECUTE
			| EXPLAIN
			| EXTERNAL
			| FIELDS
			| FILL
			| FIRST_P
			| FORCE
			| FORMAT
			| FORWARD
			| FUNCTION
			| GLOBAL
			| GRANTED
			| HANDLER
			| HASH
			| HEADER_P
			| HOLD
			| HOST
			| IF_P
			| IMMEDIATE
			| IMMUTABLE
			| IMPLICIT_P
			| INCLUDING
			| INCLUSIVE
			| INCREMENT
			| INDEX
			| INDEXES
			| INHERIT
			| INHERITS
			| INPUT_P
			| INSENSITIVE
			| INSERT
			| INSTEAD
			| INVOKER
			| ISOLATION
			| KEY
			| LANGUAGE
			| LARGE_P
			| LAST_P
			| LEVEL
			| LIST
			| LISTEN
			| LOAD
			| LOCAL
			| LOCATION
			| LOCK_P
			| MASTER
			| MATCH
			| MAXVALUE
			| MEMORY_LIMIT
			| MEMORY_SHARED_QUOTA
			| MEMORY_SPILL_RATIO
			| MINVALUE
			| MISSING
			| MODE
			| MODIFIES
			| MOVE
			| NAME_P
			| NAMES
			| NEWLINE
			| NEXT
			| NO
			| NOOVERCOMMIT
			| NOTHING
			| NOTIFY
			| NOWAIT
			| NULLS_P
			| OBJECT_P
			| OF
			| OIDS
			| OPERATOR
			| OPTION
			| OPTIONS
			| OTHERS
			| OVERCOMMIT
			| OWNED
			| OWNER
			| PARALLEL
			| PARTIAL
			| PARTITIONS
			| PASSWORD
			| PERCENT
			| PERSISTENTLY
			| PREPARE
			| PREPARED
			| PRESERVE
			| PRIOR
			| PRIVILEGES
			| PROCEDURAL
			| PROCEDURE
			| PROTOCOL
			| QUEUE
			| QUOTE
			| RANGE
			| READ
			| REASSIGN
			| RECHECK
			| REINDEX
			| RELATIVE_P
			| RELEASE
			| RENAME
			| REPEATABLE
			| REPLACE
			| RESET
			| RESOURCE
			| RESTART
			| RESTRICT
			| RETURNS
			| REVOKE
			| ROLE
			| ROLLBACK
			| ROWS
			| RULE
			| SAVEPOINT
			| SCHEMA
			| SCROLL
			| SEARCH
			| SECURITY
			| SEGMENT
			| SEGMENTS
			| SEQUENCE
			| SERIALIZABLE
			| SESSION
			| SET
			| SHARE
			| SHOW
			| SIMPLE
			| SPLIT
			| SQL
			| STABLE
			| START
			| STATEMENT
			| STATISTICS
			| STDIN
			| STDOUT
			| STORAGE
			| STRICT_P
			| SUBPARTITION
			| SYSID
			| SYSTEM_P
			| TEMP
			| TEMPLATE
			| TEMPORARY
			| THRESHOLD
			| TIES
			| TRANSACTION
			| TRIGGER
			| TRUNCATE
			| TRUSTED
			| TYPE_P
			| UNCOMMITTED
			| UNENCRYPTED
			| UNKNOWN
			| UNLISTEN
			| UNTIL
			| UPDATE
			| VACUUM
			| VALID
			| VALIDATOR
			| VERSION_P
			| VIEW
			| VALUE_P
			| VOLATILE
			| WORK
			| WRITE
			| ZONE
			| BIGINT
			| BIT
			| BOOLEAN_P
			| COALESCE
			| CUBE
			| DEC
			| DECIMAL_P
			| EXISTS
			| EXTRACT
			| FLOAT_P
			| GREATEST
			| GROUP_ID
			| GROUPING
			| INOUT
			| INT_P
			| INTEGER
			| INTERVAL
			| LEAST
			| NATIONAL
			| NCHAR
			| NONE
			| NULLIF
			| NUMERIC
			| OUT_P
			| OVERLAY
			| POSITION
			| PRECISION
			| REAL
			| ROLLUP
			| ROW
			| SETOF
			| SETS
			| SMALLINT
			| SUBSTRING
			| TIME
			| TIMESTAMP
			| TREAT
			| TRIM
			| VALUES
			| VARCHAR
			| AUTHORIZATION
			| BINARY
			| FREEZE
			| LOG_P
			| OUTER_P
			| VERBOSE
			;

/* Column identifier --- keywords that can be column, table, etc names.
 *
 * Many of these keywords will in fact be recognized as type or function
 * names too; but they have special productions for the purpose, and so
 * can't be treated as "generic" type or function names.
 *
 * The type names appearing here are not usable as function names
 * because they can be followed by '(' in typename productions, which
 * looks too much like a function call for an LR(1) parser.
 */
col_name_keyword:
			  BETWEEN
			| BIGINT
			| BIT
			| BOOLEAN_P
			| CHAR_P
			| CHARACTER
			| COALESCE
			| DEC
			| DECIMAL_P
			| EXISTS
			| EXTRACT
			| FLOAT_P
			| GREATEST
			| GROUPING
			| GROUP_ID
			| INOUT
			| INT_P
			| INTEGER
			| INTERVAL
			| LEAST
			| MEDIAN
			| NATIONAL
			| NCHAR
			| NONE
			| NULLIF
			| NUMERIC
			| OUT_P
			| OVERLAY
			| POSITION
			| PRECISION
			| REAL
			| ROLLUP
			| ROW
			| SETOF
			| SETS
			| SMALLINT
			| SUBSTRING
			| TIME
			| TIMESTAMP
			| TREAT
			| TRIM
			| VALUES
			| VARCHAR
			| XMLATTRIBUTES
			| XMLCONCAT
			| XMLELEMENT
			| XMLEXISTS
			| XMLFOREST
			| XMLPARSE
			| XMLPI
			| XMLROOT
			| XMLSERIALIZE
		;

/* Type/function identifier --- keywords that can be type or function names.
 *
 * Most of these are keywords that are used as operators in expressions;
 * in general such keywords can't be column names because they would be
 * ambiguous with variables, but they are unambiguous as function identifiers.
 *
 * Do not include POSITION, SUBSTRING, etc here since they have explicit
 * productions in a_expr to support the goofy SQL9x argument syntax.
 * - thomas 2000-11-28
 */
type_func_name_keyword:
			  AUTHORIZATION
			| BINARY
			| COLLATION
			| CONCURRENTLY
			| CROSS
			| CURRENT_SCHEMA
			| FREEZE
			| FULL
			| ILIKE
			| INNER_P
			| IS
			| ISNULL
			| JOIN
			| LEFT
			| LIKE
			| NATURAL
			| NOTNULL
			| OUTER_P
			| OVERLAPS
			| RIGHT
			| SIMILAR
			| VERBOSE
		;

/* Reserved keyword --- these keywords are usable only as a ColLabel.
 *
 * Keywords appear here if they could not be distinguished from variable,
 * type, or function names in some contexts.  Don't put things here unless
 * forced to.
 */
reserved_keyword:
			  ALL
			| ANALYSE
			| ANALYZE
			| AND
			| ANY
			| ARRAY
			| AS
			| ASC
			| ASYMMETRIC
			| BOTH
			| CASE
			| CAST
			| CHECK
			| COLLATE
			| COLUMN
			| CONSTRAINT
			| CREATE
			| CURRENT_CATALOG
			| CURRENT_DATE
			| CURRENT_ROLE
			| CURRENT_TIME
			| CURRENT_TIMESTAMP
			| CURRENT_USER
			| DECODE
			| DEFAULT
			| DEFERRABLE
			| DESC
			| DISTINCT
			| DISTRIBUTED /* gp */
			| DO
			| ELSE
			| END_P
			| EXCEPT
			| EXCLUDE 
			| FALSE_P
			| FETCH
			| FOLLOWING
			| FOR
			| FOREIGN
			| FROM
			| GRANT
			| GROUP_P
			| HAVING
			| IN_P
			| INITIALLY
			| INTERSECT
			| INTO
			| LATERAL_P
			| LEADING
			| LIMIT
			| LOCALTIME
			| LOCALTIMESTAMP
			| NOT
			| NULL_P
			| OFFSET
			| ON
			| ONLY
			| OR
			| ORDER
			| PARTITION
			| PLACING
			| PRECEDING
			| PRIMARY
			| REFERENCES
			| RETURNING
			| SCATTER  /* gp */
			| SELECT
			| SESSION_USER
			| SOME
			| SYMMETRIC
			| TABLE
			| THEN
			| TO
			| TRAILING
			| TRUE_P
			| UNBOUNDED
			| UNION
			| UNIQUE
			| USER
			| USING
			| VARIADIC
			| WHEN
			| WHERE
			| WINDOW
			| WITH
		;

%%

/*
 * The signature of this function is required by bison.  However, we
 * ignore the passed yylloc and instead use the last token position
 * available from the scanner.
 */
static void
base_yyerror(YYLTYPE *yylloc, core_yyscan_t yyscanner, const char *msg)
{
	parser_yyerror(msg);
}

static Node *
makeColumnRef(char *colname, List *indirection,
			  int location, core_yyscan_t yyscanner)
{
	/*
	 * Generate a ColumnRef node, with an A_Indirection node added if there
	 * is any subscripting in the specified indirection list.  However,
	 * any field selection at the start of the indirection list must be
	 * transposed into the "fields" part of the ColumnRef node.
	 */
	ColumnRef  *c = makeNode(ColumnRef);
	int		nfields = 0;
	ListCell *l;

	c->location = location;
	foreach(l, indirection)
	{
		if (IsA(lfirst(l), A_Indices))
		{
			A_Indirection *i = makeNode(A_Indirection);

			if (nfields == 0)
			{
				/* easy case - all indirection goes to A_Indirection */
				c->fields = list_make1(makeString(colname));
				i->indirection = check_indirection(indirection, yyscanner);
			}
			else
			{
				/* got to split the list in two */
				i->indirection = check_indirection(list_copy_tail(indirection,
																  nfields),
												   yyscanner);
				indirection = list_truncate(indirection, nfields);
				c->fields = lcons(makeString(colname), indirection);
			}
			i->arg = (Node *) c;
			return (Node *) i;
		}
		else if (IsA(lfirst(l), A_Star))
		{
			/* We only allow '*' at the end of a ColumnRef */
			if (lnext(l) != NULL)
				parser_yyerror("improper use of \"*\"");
		}
		nfields++;
	}
	/* No subscripting, so all indirection gets added to field list */
	c->fields = lcons(makeString(colname), indirection);
	return (Node *) c;
}

static Node *
makeTypeCast(Node *arg, TypeName *typename, int location)
{
	TypeCast *n = makeNode(TypeCast);
	n->arg = arg;
	n->typeName = typename;
	n->location = location;
	return (Node *) n;
}

static Node *
makeStringConst(char *str, int location)
{
	A_Const *n = makeNode(A_Const);

	n->val.type = T_String;
	n->val.val.str = str;
	n->location = location;

	return (Node *)n;
}

static Node *
makeStringConstCast(char *str, int location, TypeName *typename)
{
	Node *s = makeStringConst(str, location);

	return makeTypeCast(s, typename, -1);
}

static Node *
makeIntConst(int val, int location)
{
	A_Const *n = makeNode(A_Const);

	n->val.type = T_Integer;
	n->val.val.ival = val;
	n->location = location;

	return (Node *)n;
}

static Node *
makeFloatConst(char *str, int location)
{
	A_Const *n = makeNode(A_Const);

	n->val.type = T_Float;
	n->val.val.str = str;
	n->location = location;

	return (Node *)n;
}

static Node *
makeBitStringConst(char *str, int location)
{
	A_Const *n = makeNode(A_Const);

	n->val.type = T_BitString;
	n->val.val.str = str;
	n->location = location;

	return (Node *)n;
}

static Node *
makeNullAConst(int location)
{
	A_Const *n = makeNode(A_Const);

	n->val.type = T_Null;
	n->location = location;

	return (Node *)n;
}

static Node *
makeAConst(Value *v, int location)
{
	Node *n;

	switch (v->type)
	{
		case T_Float:
			n = makeFloatConst(v->val.str, location);
			break;

		case T_Integer:
			n = makeIntConst(v->val.ival, location);
			break;

		case T_String:
		default:
			n = makeStringConst(v->val.str, location);
			break;
	}

	return n;
}

/* makeBoolAConst()
 * Create an A_Const string node and put it inside a boolean cast.
 */
static Node *
makeBoolAConst(bool state, int location)
{
	A_Const *n = makeNode(A_Const);

	n->val.type = T_String;
	n->val.val.str = (state ? "t" : "f");
	n->location = location;

	return makeTypeCast((Node *)n, SystemTypeName("bool"), -1);
}

/* check_qualified_name --- check the result of qualified_name production
 *
 * It's easiest to let the grammar production for qualified_name allow
 * subscripts and '*', which we then must reject here.
 */
static void
check_qualified_name(List *names, core_yyscan_t yyscanner)
{
	ListCell   *i;

	foreach(i, names)
	{
		if (!IsA(lfirst(i), String))
			parser_yyerror("syntax error");
	}
}

/* check_func_name --- check the result of func_name production
 *
 * It's easiest to let the grammar production for func_name allow subscripts
 * and '*', which we then must reject here.
 */
static List *
check_func_name(List *names, core_yyscan_t yyscanner)
{
	ListCell   *i;

	foreach(i, names)
	{
		if (!IsA(lfirst(i), String))
			parser_yyerror("syntax error");
	}
	return names;
}

/* check_indirection --- check the result of indirection production
 *
 * We only allow '*' at the end of the list, but it's hard to enforce that
 * in the grammar, so do it here.
 */
static List *
check_indirection(List *indirection, core_yyscan_t yyscanner)
{
	ListCell *l;

	foreach(l, indirection)
	{
		if (IsA(lfirst(l), A_Star))
		{
			if (lnext(l) != NULL)
				parser_yyerror("improper use of \"*\"");
		}
	}
	return indirection;
}

/* extractArgTypes()
 * Given a list of FunctionParameter nodes, extract a list of just the
 * argument types (TypeNames) for input parameters only.  This is what
 * is needed to look up an existing function, which is what is wanted by
 * the productions that use this call.
 */
static List *
extractArgTypes(List *parameters)
{
	List	   *result = NIL;
	ListCell   *i;

	foreach(i, parameters)
	{
		FunctionParameter *p = (FunctionParameter *) lfirst(i);

		if (p->mode != FUNC_PARAM_OUT && p->mode != FUNC_PARAM_TABLE)
			result = lappend(result, p->argType);
	}
	return result;
}

/* extractAggrArgTypes()
 * As above, but work from the output of the aggr_args production.
 */
static List *
extractAggrArgTypes(List *aggrargs)
{
	Assert(list_length(aggrargs) == 2);
	return extractArgTypes((List *) linitial(aggrargs));
}

/* makeOrderedSetArgs()
 * Build the result of the aggr_args production (which see the comments for).
 * This handles only the case where both given lists are nonempty, so that
 * we have to deal with multiple VARIADIC arguments.
 */
static List *
makeOrderedSetArgs(List *directargs, List *orderedargs,
				   core_yyscan_t yyscanner)
{
	FunctionParameter *lastd = (FunctionParameter *) llast(directargs);
	int			ndirectargs;

	/* No restriction unless last direct arg is VARIADIC */
	if (lastd->mode == FUNC_PARAM_VARIADIC)
	{
		FunctionParameter *firsto = (FunctionParameter *) linitial(orderedargs);

		/*
		 * We ignore the names, though the aggr_arg production allows them;
		 * it doesn't allow default values, so those need not be checked.
		 */
		if (list_length(orderedargs) != 1 ||
			firsto->mode != FUNC_PARAM_VARIADIC ||
			!equal(lastd->argType, firsto->argType))
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("an ordered-set aggregate with a VARIADIC direct argument must have one VARIADIC aggregated argument of the same data type"),
					 parser_errposition(exprLocation((Node *) firsto))));

		/* OK, drop the duplicate VARIADIC argument from the internal form */
		orderedargs = NIL;
	}

	/* don't merge into the next line, as list_concat changes directargs */
	ndirectargs = list_length(directargs);

	return list_make2(list_concat(directargs, orderedargs),
					  makeInteger(ndirectargs));
}

/* insertSelectOptions()
 * Insert ORDER BY, etc into an already-constructed SelectStmt.
 *
 * This routine is just to avoid duplicating code in SelectStmt productions.
 */
static void
insertSelectOptions(SelectStmt *stmt,
					List *sortClause, List *lockingClause,
					Node *limitOffset, Node *limitCount,
					WithClause *withClause,
					core_yyscan_t yyscanner)
{
	Assert(IsA(stmt, SelectStmt));

	/*
	 * Tests here are to reject constructs like
	 *	(SELECT foo ORDER BY bar) ORDER BY baz
	 */
	if (sortClause)
	{
		if (stmt->sortClause)
			ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					 errmsg("multiple ORDER BY clauses not allowed"),
					 parser_errposition(exprLocation((Node *) sortClause))));
		stmt->sortClause = sortClause;
	}
	/* We can handle multiple locking clauses, though */
	stmt->lockingClause = list_concat(stmt->lockingClause, lockingClause);
	if (limitOffset)
	{
		if (stmt->limitOffset)
			ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					 errmsg("multiple OFFSET clauses not allowed"),
					 parser_errposition(exprLocation(limitOffset))));
		stmt->limitOffset = limitOffset;
	}
	if (limitCount)
	{
		if (stmt->limitCount)
			ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					 errmsg("multiple LIMIT clauses not allowed"),
					 parser_errposition(exprLocation(limitCount))));
		stmt->limitCount = limitCount;
	}
	if (withClause)
	{
		if (stmt->withClause)
			ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					 errmsg("multiple WITH clauses not allowed"),
					 parser_errposition(exprLocation((Node *) withClause))));
		stmt->withClause = withClause;
	}
}

static Node *
makeSetOp(SetOperation op, bool all, Node *larg, Node *rarg)
{
	SelectStmt *n = makeNode(SelectStmt);

	n->op = op;
	n->all = all;
	n->larg = (SelectStmt *) larg;
	n->rarg = (SelectStmt *) rarg;
	return (Node *) n;
}

/* SystemFuncName()
 * Build a properly-qualified reference to a built-in function.
 */
List *
SystemFuncName(char *name)
{
	return list_make2(makeString("pg_catalog"), makeString(name));
}

/* SystemTypeName()
 * Build a properly-qualified reference to a built-in type.
 *
 * typmod is defaulted, but may be changed afterwards by caller.
 * Likewise for the location.
 */
TypeName *
SystemTypeName(char *name)
{
	return makeTypeNameFromNameList(list_make2(makeString("pg_catalog"),
											   makeString(name)));
}

/* doNegate()
 * Handle negation of a numeric constant.
 *
 * Formerly, we did this here because the optimizer couldn't cope with
 * indexquals that looked like "var = -4" --- it wants "var = const"
 * and a unary minus operator applied to a constant didn't qualify.
 * As of Postgres 7.0, that problem doesn't exist anymore because there
 * is a constant-subexpression simplifier in the optimizer.  However,
 * there's still a good reason for doing this here, which is that we can
 * postpone committing to a particular internal representation for simple
 * negative constants.	It's better to leave "-123.456" in string form
 * until we know what the desired type is.
 */
static Node *
doNegate(Node *n, int location)
{
	if (IsA(n, A_Const))
	{
		A_Const *con = (A_Const *)n;

		/* report the constant's location as that of the '-' sign */
		con->location = location;

		if (con->val.type == T_Integer)
		{
			con->val.val.ival = -con->val.val.ival;
			return n;
		}
		if (con->val.type == T_Float)
		{
			doNegateFloat(&con->val);
			return n;
		}
	}

	return (Node *) makeSimpleA_Expr(AEXPR_OP, "-", NULL, n, location);
}

static void
doNegateFloat(Value *v)
{
	char   *oldval = v->val.str;

	Assert(IsA(v, Float));
	if (*oldval == '+')
		oldval++;
	if (*oldval == '-')
		v->val.str = oldval+1;	/* just strip the '-' */
	else
		v->val.str = psprintf("-%s", oldval);
}

static Node *
makeAArrayExpr(List *elements, int location)
{
	A_ArrayExpr *n = makeNode(A_ArrayExpr);

	n->elements = elements;
	n->location = location;
	return (Node *) n;
}

static Node *
makeXmlExpr(XmlExprOp op, char *name, List *named_args, List *args,
			int location)
{
	XmlExpr		*x = makeNode(XmlExpr);

	x->op = op;
	x->name = name;
	/*
	 * named_args is a list of ResTarget; it'll be split apart into separate
	 * expression and name lists in transformXmlExpr().
	 */
	x->named_args = named_args;
	x->arg_names = NIL;
	x->args = args;
	/* xmloption, if relevant, must be filled in by caller */
	/* type and typmod will be filled in during parse analysis */
	x->type = InvalidOid;			/* marks the node as not analyzed */
	x->location = location;
	return (Node *) x;
}

/*
 * Merge the input and output parameters of a table function.
 */
static List *
mergeTableFuncParameters(List *func_args, List *columns)
{
	ListCell   *lc;

	/* Explicit OUT and INOUT parameters shouldn't be used in this syntax */
	foreach(lc, func_args)
	{
		FunctionParameter *p = (FunctionParameter *) lfirst(lc);

		switch (p->mode)
		{
			/* Input modes */
			case FUNC_PARAM_IN:
			case FUNC_PARAM_VARIADIC:
				break;  

			/* Output modes */
			case FUNC_PARAM_TABLE:
				Insist(false);  /* not feasible */
				break;
			case FUNC_PARAM_OUT:
				ereport(ERROR,
						(errcode(ERRCODE_SYNTAX_ERROR),
						 errmsg("OUT arguments aren't allowed in TABLE functions")));
				break;
			case FUNC_PARAM_INOUT:
				ereport(ERROR,
						(errcode(ERRCODE_SYNTAX_ERROR),
						 errmsg("INOUT arguments aren't allowed in TABLE functions")));
				break;
		}
	}

	return list_concat(func_args, columns);
}

/*
 * Determine return type of a TABLE function.  A single result column
 * returns setof that column's type; otherwise return setof record.
 */
static TypeName *
TableFuncTypeName(List *columns)
{
	TypeName *result;

	if (list_length(columns) == 1)
	{
		FunctionParameter *p = (FunctionParameter *) linitial(columns);

		result = (TypeName *) copyObject(p->argType);
	}
	else
		result = SystemTypeName("record");

	result->setof = true;

	return result;
}

static void 
checkWindowExclude(void)
{
	/*
	 * because the syntax has historically existed without doing anything
	 * we have chosen to add a guc to allow simply ignoring the exclude clause
	 * rather than raising an error.
	 */
	if (gp_ignore_window_exclude)
		return;

	/* MPP-13628 */
	ereport(ERROR,
			(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
			 errmsg("window EXCLUDE clause not yet implemented")));
}

/*
 * Create the IS_NOT_DISTINCT_FROM expression node
 *     used by CASE x WHEN IS NOT DISTINCT FROM and DECODE()
 */
static Node*
makeIsNotDistinctFromNode(Node *expr, int position)
{
	Node *n = (Node *) makeA_Expr(AEXPR_NOT, NIL, NULL,
								(Node *) makeSimpleA_Expr(AEXPR_DISTINCT, 
	 													"=", NULL, expr, position), position);
	return n;
}

/*
 * Convert a list of (dotted) names to a RangeVar (like
 * makeRangeVarFromNameList, but with position support).  The
 * "AnyName" refers to the any_name production in the grammar.
 */
static RangeVar *
makeRangeVarFromAnyName(List *names, int position, core_yyscan_t yyscanner)
{
	RangeVar *r = makeNode(RangeVar);

	switch (list_length(names))
	{
		case 1:
			r->catalogname = NULL;
			r->schemaname = NULL;
			r->relname = strVal(linitial(names));
			break;
		case 2:
			r->catalogname = NULL;
			r->schemaname = strVal(linitial(names));
			r->relname = strVal(lsecond(names));
			break;
		case 3:
			r->catalogname = strVal(linitial(names));
			r->schemaname = strVal(lsecond(names));
			r->relname = strVal(lthird(names));
			break;
		default:
			ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					 errmsg("improper qualified name (too many dotted names): %s",
							NameListToString(names)),
					 parser_errposition(position)));
			break;
	}

	r->relpersistence = RELPERSISTENCE_PERMANENT;
	r->location = position;

	return r;
}

/* Separate Constraint nodes from COLLATE clauses in a ColQualList */
static void
SplitColQualList(List *qualList,
				 List **constraintList, CollateClause **collClause,
				 core_yyscan_t yyscanner)
{
	ListCell   *cell;
	ListCell   *prev;
	ListCell   *next;

	*collClause = NULL;
	prev = NULL;
	for (cell = list_head(qualList); cell; cell = next)
	{
		Node   *n = (Node *) lfirst(cell);

		next = lnext(cell);
		if (IsA(n, Constraint))
		{
			/* keep it in list */
			prev = cell;
			continue;
		}
		if (IsA(n, CollateClause))
		{
			CollateClause *c = (CollateClause *) n;

			if (*collClause)
				ereport(ERROR,
						(errcode(ERRCODE_SYNTAX_ERROR),
						 errmsg("multiple COLLATE clauses not allowed"),
						 parser_errposition(c->location)));
			*collClause = c;
		}
		else
			elog(ERROR, "unexpected node type %d", (int) n->type);
		/* remove non-Constraint nodes from qualList */
		qualList = list_delete_cell(qualList, cell, prev);
	}
	*constraintList = qualList;
}

/*
 * Process result of ConstraintAttributeSpec, and set appropriate bool flags
 * in the output command node.  Pass NULL for any flags the particular
 * command doesn't support.
 */
static void
processCASbits(int cas_bits, int location, const char *constrType,
			   bool *deferrable, bool *initdeferred, bool *not_valid,
			   bool *no_inherit, core_yyscan_t yyscanner)
{
	/* defaults */
	if (deferrable)
		*deferrable = false;
	if (initdeferred)
		*initdeferred = false;
	if (not_valid)
		*not_valid = false;

	if (cas_bits & (CAS_DEFERRABLE | CAS_INITIALLY_DEFERRED))
	{
		if (deferrable)
			*deferrable = true;
		else
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 /* translator: %s is CHECK, UNIQUE, or similar */
					 errmsg("%s constraints cannot be marked DEFERRABLE",
							constrType),
					 parser_errposition(location)));
	}

	if (cas_bits & CAS_INITIALLY_DEFERRED)
	{
		if (initdeferred)
			*initdeferred = true;
		else
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 /* translator: %s is CHECK, UNIQUE, or similar */
					 errmsg("%s constraints cannot be marked DEFERRABLE",
							constrType),
					 parser_errposition(location)));
	}

	if (cas_bits & CAS_NOT_VALID)
	{
		if (not_valid)
			*not_valid = true;
		else
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 /* translator: %s is CHECK, UNIQUE, or similar */
					 errmsg("%s constraints cannot be marked NOT VALID",
							constrType),
					 parser_errposition(location)));
	}

	if (cas_bits & CAS_NO_INHERIT)
	{
		if (no_inherit)
			*no_inherit = true;
		else
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 /* translator: %s is CHECK, UNIQUE, or similar */
					 errmsg("%s constraints cannot be marked NO INHERIT",
							constrType),
					 parser_errposition(location)));
	}
}

/*----------
 * Recursive view transformation
 *
 * Convert
 *
 *     CREATE RECURSIVE VIEW relname (aliases) AS query
 *
 * to
 *
 *     CREATE VIEW relname (aliases) AS
 *         WITH RECURSIVE relname (aliases) AS (query)
 *         SELECT aliases FROM relname
 *
 * Actually, just the WITH ... part, which is then inserted into the original
 * view definition as the query.
 * ----------
 */
static Node *
makeRecursiveViewSelect(char *relname, List *aliases, Node *query)
{
	SelectStmt *s = makeNode(SelectStmt);
	WithClause *w = makeNode(WithClause);
	CommonTableExpr *cte = makeNode(CommonTableExpr);
	List	   *tl = NIL;
	ListCell   *lc;

	/* create common table expression */
	cte->ctename = relname;
	cte->aliascolnames = aliases;
	cte->ctequery = query;
	cte->location = -1;

	/* create WITH clause and attach CTE */
	w->recursive = true;
	w->ctes = list_make1(cte);
	w->location = -1;

	/* create target list for the new SELECT from the alias list of the
	 * recursive view specification */
	foreach (lc, aliases)
	{
		ResTarget *rt = makeNode(ResTarget);

		rt->name = NULL;
		rt->indirection = NIL;
		rt->val = makeColumnRef(strVal(lfirst(lc)), NIL, -1, 0);
		rt->location = -1;

		tl = lappend(tl, rt);
	}

	/* create new SELECT combining WITH clause, target list, and fake FROM
	 * clause */
	s->withClause = w;
	s->targetList = tl;
	s->fromClause = list_make1(makeRangeVar(NULL, relname, -1));

	return (Node *) s;
}

/* parser_init()
 * Initialize to parse one query string
 */
void
parser_init(base_yy_extra_type *yyext)
{
	yyext->parsetree = NIL;		/* in case grammar forgets to set it */
}
