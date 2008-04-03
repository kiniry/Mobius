%{
--
-- The Extended BON Toolsuite: Parser
-- Copyright (c) 2001 Joseph Kiniry
-- All Rights Reserved
--

--
-- $Id: ebon_parser.y,v 1.1 2005/05/02 22:58:29 kiniry Exp $
--

indexing
   description: "The Extended BON parser."
   project:     "The Extended BON Toolsuite"
   author:      "Joseph R. Kiniry <kiniry@acm.org>"
   copyright:   "Copyright (C) 2001 Joseph R. Kiniry"
   version:     "$Id: ebon_parser.y,v 1.1 2005/05/02 22:58:29 kiniry Exp $"
   license:     "Eiffel Forum Freeware License v1 (see forum.txt)"

class EBON_PARSER
   -- A parser for the Extended BON specification language.

   -- todo: "Consider using nonterminal symbols to automatically type %
   --        %expressions to fixed types in the MOG.  @see %
   --        %gobo/doc/geyacc/declarations.html for more information."

inherit
   -- All core code for parser is in the skeleton.
   EBON_PARSER_SKELETON

creation
   make_parser, execute, benchmark
%}

-- Geyacc options (currently undefined, Aug 9, 2001)

-- %option 

-- Token Declarations: Each terminal symbol that is not a single-character
-- literal must be declared here. (Single-character literals normally don't
-- need to be declared.)

-- Typed token declarations for some basic generic tokens.

-- The Identifier construct is defined as a sequence of alphanumeric -
-- characters including underscore. An identifier must begin with an
-- alphanumeric character and must not end with an underscore (whose
-- purpose really is to mimic word separation). Letter case is not
-- significant, but using consistent style rules is important.

%token <STRING> IDENTIFIER_TOKEN

-- Basic non-numeric types.

%token <CHARACTER> CHARACTER_TOKEN

-- Integers and Real are the basic numeric types.

%token <INTEGER> INTEGER_TOKEN
%token <REAL> REAL_TOKEN

-- Tokens for string handling.  @see "Strings" section of ebon/docs/BON.txt.
-- We currently do not support redefining String_begin and String_end.

%token STRING_DELIMITER_TOKEN
%token <STRING> SIMPLE_STRING_TOKEN

-- The FREE_OPERATOR_TOKEN represents feature names used as infix and
-- prefix operations. Such operations may be textual keywords, such as the
-- boolean "and" and "or", but are more often composed of special
-- characters, like "+", "**", "=>", etc.

%token <STRING> FREE_OPERATOR_TOKEN

-- The BON reserved words.

%token CURRENT_TOKEN
%token RESULT_TOKEN
%token VOID_TOKEN
%token ACTION_TOKEN
%token CALLS_TOKEN
%token CLASS_TOKEN
%token CLASS_CHART_TOKEN
%token CLIENT_TOKEN
%token CLUSTER_TOKEN
%token CLUSTER_CHART_TOKEN
%token COMMAND_TOKEN
%token COMPONENT_TOKEN
%token CONCATENATOR_TOKEN
%token CONSTRAINT_TOKEN
%token CREATES_TOKEN
%token CREATION_CHART_TOKEN
%token CREATOR_TOKEN
%token DEFERRED_TOKEN
%token DESCRIPTION_TOKEN
%token DICTIONARY_TOKEN
%token DYNAMIC_DIAGRAM_TOKEN
%token EFFECTIVE_TOKEN
%token END_TOKEN
%token ENSURE_TOKEN
%token EVENT_TOKEN
%token EVENT_CHART_TOKEN
%token EXISTS_TOKEN
%token EXPLANATION_TOKEN
%token FALSE_TOKEN
%token FEATURE_TOKEN
%token FOR_ALL_TOKEN
%token INCOMING_TOKEN
%token INDEXING_TOKEN
%token INFIX_TOKEN
%token INHERIT_TOKEN
%token INTERFACED_TOKEN
%token INVARIANT_TOKEN
%token INVOLVES_TOKEN
%token IT_HOLDS_TOKEN
%token KEYWORD_PREFIX_TOKEN
%token NAMELESS_TOKEN
%token OBJECT_TOKEN
%token OBJECT_GROUP_TOKEN
%token OBJECT_STACK_TOKEN
%token OUTGOING_TOKEN
%token PART_TOKEN
%token PERSISTENT_TOKEN
%token PREFIX_TOKEN
%token QUERY_TOKEN
%token REDEFINED_TOKEN
%token REQUIRE_TOKEN
%token REUSED_TOKEN
%token ROOT_TOKEN
%token SCENARIO_TOKEN
%token SCENARIO_CHART_TOKEN
%token STATIC_DIAGRAM_TOKEN
%token STRING_MARKS_TOKEN
%token SUCH_THAT_TOKEN
%token SYSTEM_CHART_TOKEN
%token TRUE_TOKEN

-- Relative operator precedence is determined by their specification order 
-- in the grammar.  Also, each mathematical operator is left or right 
-- associative, as declared by the %left and %right precedence 
-- declarations.  Precedence goes from low to high as we list operators.

-- We have to add the dummy token UNARY_DUMMY for unary minus and plus
-- because they have the highest precedence of all and must be used to
-- disambiguate operator precedence based upon context.  @see the final
-- section of gobo/doc/geyacc/precedence.html for details.

%right IMPLIES_TOKEN EQUIVALENT_TO_TOKEN
%left MEMBER_OF_TOKEN ':'
%left AND_TOKEN OR_TOKEN XOR_TOKEN
%right NOT_TOKEN
%left '<' LESS_THAN_OR_EQUAL_TOKEN '>' GREATER_THAN_OR_EQUAL_TOKEN '=' NOT_EQUAL_TOKEN
%left '+' '-'
%left '*' '/' DOUBLE_SLASH_TOKEN DOUBLE_BACKSLASH_TOKEN
%left '^'
%left UNARY_DUMMY
%right OLD_TOKEN DELTA_TOKEN

-- BON special symbols that are at least two characters long.  Uncommented 
-- symbols are those that didn't need to have precedence set above.

-- Introduces comments   
%token DOUBLE_DASH_TOKEN "--"

-- Integer division operator
-- DOUBLE_SLASH_TOKEN "//"

-- Modulo operator
-- DOUBLE_BACKSLASH_TOKEN "\\"

-- Relational operators 
-- LESS_THAN_OR_EQUAL_TOKEN "<="
-- GREATER_THAN_OR_EQUAL_TOKEN ">="

-- Equality and non-equality  
-- NOT_EQUAL_TOKEN "/="

-- Feature arguments, constrained genericity, logical implication 
-- IMPLIES_TOKEN "->"

-- Logical equivalence 
-- EQUIVALENT_TO_TOKEN "<->"

-- Interval marker 
%token DOUBLE_DOT_TOKEN ".."

-- Indicates aggregate supplier
%token AGGREGATE_MARK_TOKEN ":{"

-- Undocumented tokens in original BON grammar.

%token ELLIPSES_TOKEN "..."

-- Basic constructs

-- The recommended BON standard is to use all upper case names for class
-- and cluster names, all lower case for feature names, and lower case
-- beginning with a capital for object groups and constants values. We also
-- strongly recommend using underscore for word separation rather than, for
-- example, in-word capitalization, since this greatly enhances
-- readability.  

-- @design kiniry - Aug 24, 2001 - These tokens are currently not used but
-- are reserved for potential future use.

%token <STRING> CLASS_NAME_TOKEN
%token <STRING> CLUSTER_NAME_TOKEN
%token <STRING> ALL_CAPS_IDENTIFIER_TOKEN
%token <STRING> FEATURE_NAME_TOKEN
%token <STRING> OBJECT_GROUP_OR_CONSTANT_NAME_TOKEN

-- Indicate how many shift/reduce conflicts we expect.  This is only used
-- to simplify grammar debugging.  Our total is 1 for the rules involving
-- At_least_one_Line_comment, Optional_Line_comments, and Line_Comment.

%expect 1

%%

-- Grammar rules

-- We have rewritten the BON specification from the text using the
-- following methodology.

-- Every rule of the form:
--     Rule = [ Foobar ]
-- becomes
--     Rule: Optional_Foobar_clause ;
--     Optional_Foobar_clause: -- Empty
--                             | Foobar ;
--     Foobar: ...whatever... ;

-- Likewise, every rule of the form:
--     Rule = { Foobar } +
-- becomes
--     Rule: At_least_one_Foobar ;
--     At_least_one_Foobar: Foobar
--                          Optional_Foobars ;
--     Optional_Foobars: -- Empty
--                       | Optional_Foobars Foobar ;
--     Foobar: ...whatever... ;

-- Finally, every rule of the form:
--     Rule = { Foobar }
-- becomes
--     Rule: Zero_or_more_Foobars ;
--     Zero_or_more_Foobars: -- Empty
--                           | Zero_or_more_Foobars Foobar ;
--     Foobar: ...whatever... ;

-- Some of these blind EBNF->Geyacc rewrites result in reduce/reduce
-- conflicts that need to be handled.  @see Gobo document 
-- gobo/doc/geyacc/algorithm.html for more information on typical
-- reduce/reduce situations and solutions.

-- For the most part, these grammars can be simplified by eliminating rules
-- that are simply intermediates nodes in the parse tree
-- (e.g. At_least_one_Specification_element below) but at a potential loss
-- in clarity.  The plan is to keep it in its simplest form for now, then
-- later try the optimization and see if it makes a serious difference.  I
-- doubt that it will.

-- Constucts of binary or triplet form have names indicating such.  E.g.
--    { Simple_string New_line ...} +
-- becomes
--    At_least_one_Simple_string_New_line_pair: 
--         SIMPLE_STRING_New_line_pair
--         Optional_Simple_string_New_line_pairs ;

-- Optional use of tokens like
--   [ nameless ]
-- are rewritten to rules of the form
--   Optional_Nameless

-- We are not following the Geyacc convensions of all rules are lowercase
-- because we wish to follow the original EBNF BON grammar as precisely as
-- possible.  BON is a large language and getting a perfectly working parser
-- is hard enough at times.

-- A.3 BON SPECIFICATION 

Bon_specification: At_least_one_Specification_element ;

At_least_one_Specification_element: Specification_element 
                                    Optional_Specification_elements ;

Optional_Specification_elements: -- Empty
                    | Optional_Specification_elements Specification_element;

Specification_element: Comment 
                       | Informal_chart 
                       | Class_dictionary_rule
                       | Static_diagram_rule
                       | Dynamic_diagram_rule
                       | Notational_tuning ;

-- A.4 INFORMAL CHARTS 

Informal_chart: System_chart_rule
                | Cluster_chart_rule
                | Class_chart_rule
                | Event_chart_rule
                | Scenario_chart_rule
                | Creation_chart_rule;

Class_dictionary_rule: DICTIONARY_TOKEN System_name 
                       At_least_one_Dictionary_entry
                       END_TOKEN ;

At_least_one_Dictionary_entry: Dictionary_entry
                               Optional_Dictionary_entries ;

Optional_Dictionary_entries: -- Empty
                             | Optional_Dictionary_entries Dictionary_entry ;

Dictionary_entry: CLASS_TOKEN Class_name
                  CLUSTER_TOKEN Cluster_name 
                  DESCRIPTION_TOKEN Manifest_textblock ;

-- @design kiniry - Sep 3, 2001 - Experimenting with error tokens for error
-- recovery.

System_chart_rule: SYSTEM_CHART_TOKEN System_name 
                   Optional_Indexing_Index_list
                   Optional_Explanation_Manifest_string
                   Optional_Part_Manifest_string
                   Optional_Cluster_entries_rule
                   END_TOKEN
                   | SYSTEM_CHART_TOKEN System_name error END_TOKEN ;

Optional_Indexing_Index_list: -- Empty
                              | INDEXING_TOKEN Index_list ;

Optional_Explanation_Manifest_string: -- Empty
                                      | EXPLANATION_TOKEN Manifest_string ;

Optional_Part_Manifest_string: -- Empty
                               | PART_TOKEN Manifest_string ;

Optional_Cluster_entries_rule: -- Empty
                               | Cluster_entries ;

Cluster_entries: At_least_one_Cluster_entry ;

At_least_one_Cluster_entry: Cluster_entry
                            Optional_Cluster_entries ;

Optional_Cluster_entries: -- Empty
                          | Optional_Cluster_entries Cluster_entry ;

Cluster_entry: CLUSTER_TOKEN Cluster_name 
               DESCRIPTION_TOKEN Manifest_textblock ;

System_name: IDENTIFIER_TOKEN ;

Index_list: At_least_one_Index_clause ;

At_least_one_Index_clause: Index_clause 
                           Optional_Index_clauses ;

Optional_Index_clauses: -- Empty
                        | Optional_Index_clauses ';' Index_clause ;

Index_clause: IDENTIFIER_TOKEN ':' Index_term_list ;

Index_term_list: At_least_one_Index_string ;

At_least_one_Index_string: Index_string
                           Optional_Index_strings ;

Optional_Index_strings: -- Empty
                        | Optional_Index_strings ',' Index_string ;

Index_string: Manifest_string ;

Cluster_chart_rule: CLUSTER_CHART_TOKEN Cluster_name 
                    Optional_Indexing_Index_list
                    Optional_Explanation_Manifest_string
                    Optional_Part_Manifest_string
                    Optional_Class_entries_rule
                    Optional_Cluster_entries_rule
                    END_TOKEN ;

Optional_Class_entries_rule: -- Empty
                             | Class_entries ;

Class_entries: At_least_one_Class_entry ;

At_least_one_Class_entry: Class_entry
                          Optional_Class_entries ;

Optional_Class_entries:  -- Empty
                         | Optional_Class_entries Class_entry ;

Class_entry: CLASS_TOKEN Class_name 
             DESCRIPTION_TOKEN Manifest_textblock ;

Cluster_name: ALL_CAPS_IDENTIFIER_TOKEN ;

Class_chart_rule: CLASS_CHART_TOKEN Class_name 
                  Optional_Indexing_Index_list
                  Optional_Explanation_Manifest_string
                  Optional_Part_Manifest_string
                  Optional_Inherit_Class_name_list
                  Optional_Query_Query_list
                  Optional_Command_Command_list
                  Optional_Constraint_Constraint_list
                  END_TOKEN ;

Optional_Inherit_Class_name_list: -- Empty
                                  | INHERIT_TOKEN Class_name_list ;

Optional_Query_Query_list: -- Empty
                           | QUERY_TOKEN Query_list ;

Optional_Command_Command_list: -- Empty
                               | COMMAND_TOKEN Command_list ;

Optional_Constraint_Constraint_list: -- Empty
                                     | CONSTRAINT_TOKEN Constraint_list ;

Query_list: At_least_one_Manifest_string ;

Command_list: At_least_one_Manifest_string ;

Constraint_list: At_least_one_Manifest_string ;

At_least_one_Manifest_string: Manifest_string 
                              Optional_Manifest_strings ;

Optional_Manifest_strings: -- Empty
                           | Optional_Manifest_strings ',' Manifest_string ;

Class_name_list: At_least_one_Class_name ;

At_least_one_Class_name: Class_name
                         Optional_Class_names ;

Optional_Class_names: -- Empty
                      | Optional_Class_names ',' Class_name ;

Class_name: ALL_CAPS_IDENTIFIER_TOKEN ;

-- @todo kiniry - Sep 3, 2001 - Class_name_list likely has to be extended
-- for referral to clusters (e.g. "(Cluster_name)") as a shortcut for
-- referring to all classes of the cluster.  @see MONITORING_SYSTEM event
-- charts for an example.

Event_chart_rule: EVENT_CHART_TOKEN System_name 
                  Optional_Incoming_or_Outgoing_clause
                  Optional_Indexing_Index_list
                  Optional_Explanation_Manifest_string
                  Optional_Part_Manifest_string
                  Optional_Event_entries_clause
                  END_TOKEN ;

Optional_Incoming_or_Outgoing_clause: -- Empty
                                      | INCOMING_TOKEN
                                      | OUTGOING_TOKEN ;

Optional_Event_entries_clause: -- Empty
                               | Event_entries ;

Event_entries: At_least_one_Event_entry ;

At_least_one_Event_entry: Event_entry
                          Optional_Event_entries ;

Optional_Event_entries: -- Empty
                        | Optional_Event_entries Event_entry ;

Event_entry: EVENT_TOKEN Manifest_string INVOLVES_TOKEN Class_name_list ;

Scenario_chart_rule: SCENARIO_CHART_TOKEN System_name 
                     Optional_Indexing_Index_list
                     Optional_Explanation_Manifest_string
                     Optional_Part_Manifest_string
                     Optional_Scenario_entries_clause
                     END_TOKEN ;

Optional_Scenario_entries_clause: -- Empty
                                  | Scenario_entries ;

Scenario_entries: At_least_one_Scenario_entry ;

At_least_one_Scenario_entry: Scenario_entry
                             Optional_Scenario_entries ;

Optional_Scenario_entries: -- Empty
                           | Optional_Scenario_entries Scenario_entry ;

Scenario_entry: SCENARIO_TOKEN Manifest_string 
                DESCRIPTION_TOKEN Manifest_textblock ;

Creation_chart_rule: CREATION_CHART_TOKEN System_name 
                     Optional_Indexing_Index_list
                     Optional_Explanation_Manifest_string
                     Optional_Part_Manifest_string
                     Optional_Creation_entries_clause
                     END_TOKEN ;

Optional_Creation_entries_clause: -- Empty
                         | Optional_Creation_entries_clause Creation_entry ;

Creation_entry: CREATOR_TOKEN Class_name CREATES_TOKEN Class_name_list ;

-- A.5 STATIC DIAGRAMS 

Static_diagram_rule: STATIC_DIAGRAM_TOKEN 
                     Optional_Extended_id 
                     Optional_Comment
                     COMPONENT_TOKEN 
                     Static_block 
                     END_TOKEN ;

Optional_Extended_id: -- Empty
                      | Extended_id ;

Extended_id: IDENTIFIER_TOKEN
             | INTEGER_TOKEN ;

Optional_Comment:  -- Empty
                   | Comment ;

Comment: At_least_one_Line_comment ;

-- The following three rules will exhibit a shift/reduce conflict.

At_least_one_Line_comment: Line_Comment
                           Optional_Line_comments ;

Optional_Line_comments: -- Empty
                        | Optional_Line_comments Line_comment ;

Line_comment: DOUBLE_DASH_TOKEN SIMPLE_STRING_TOKEN ;

Static_block: Zero_or_more_Static_components ;

Zero_or_more_Static_components: -- Empty
                             | Zero_or_more_Static_components Static_component;

Static_component: Cluster_rule
                  | Class_rule
                  | Static_relation
                  | ELLIPSES_TOKEN ;

Cluster_rule: CLUSTER_TOKEN Cluster_name 
              Optional_Reused 
              Optional_Comment
              Optional_Cluster_components ;

Optional_Reused: -- Empty
                 | REUSED_TOKEN ;

Optional_Cluster_components: -- Empty
                             | Cluster_components ;

Cluster_components: COMPONENT_TOKEN Static_block END_TOKEN ;
 
Class_rule: Optional_Root_or_Deferred_or_Effective
            CLASS_TOKEN Class_name 
            Optional_Formal_generics_clause
            Optional_Reused 
            Optional_Persistent 
            Optional_Interfaced 
            Optional_Comment
            Optional_Class_interface ;

Optional_Root_or_Deferred_or_Effective: -- Empty
                                        | ROOT_TOKEN
                                        | DEFERRED_TOKEN
                                        | EFFECTIVE_TOKEN ;

Optional_Persistent: -- Empty
                     | PERSISTENT_TOKEN ;

Optional_Interfaced: -- Empty
                     | INTERFACED_TOKEN ;

Optional_Class_interface: -- Empty
                          | Class_interface ;

Static_relation:           Inheritance_relation 
                           | Client_relation ;

Inheritance_relation:      Child INHERIT_TOKEN 
                           Optional_Multiplicity_clause
                           Parent Optional_Semantic_label ;

Optional_Multiplicity_clause: -- Empty
                              | '{' Multiplicity '}' ;

Optional_Semantic_label: -- Empty
                         | Semantic_label ;

Client_relation: Client CLIENT_TOKEN
                 Optional_Client_entities
                 Optional_Type_mark 
                 Supplier 
                 Optional_Semantic_label ;

Optional_Type_mark: -- Empty
                    | Type_mark ;

Optional_Client_entities: -- Empty
                          | Client_entities ;

Client_entities: '{' Client_entity_expression '}' ;

Client_entity_expression: Client_entity_list 
                          | Multiplicity ;

Client_entity_list: At_least_one_Client_entity ;

At_least_one_Client_entity: Client_entity
                            Remaining_Client_entities ;

Remaining_Client_entities: -- Empty
                           | Remaining_Client_entities ',' Client_entity ;

Client_entity: Feature_name 
               | Supplier_indirection 
               | Parent_indirection ;

Supplier_indirection: Optional_Indirection_feature_part
                      Generic_indirection ;

Optional_Indirection_feature_part: -- Empty
                                   | Indirection_feature_part ':' ;

Indirection_feature_part: Feature_name 
                          | Indirection_feature_list ;

Indirection_feature_list: '(' Feature_name_list ')' ;

Parent_indirection: IMPLIES_TOKEN Generic_indirection ;

Generic_indirection:  Formal_generic_name 
                      | Named_indirection ;

Named_indirection: Class_name '[' Indirection_list ']' ;

Indirection_list: At_least_one_Indirection_element ;

At_least_one_Indirection_element: Indirection_element 
                                  Optional_Indirection_elements ;

Optional_Indirection_elements: -- Empty
                      | Optional_Indirection_elements ',' Indirection_element ;

Indirection_element: ELLIPSES_TOKEN
                     | Generic_indirection ;

Type_mark: ':' 
           | AGGREGATE_MARK_TOKEN
           | Shared_mark ;

Shared_mark: ':' '(' Multiplicity ')' ;

Child: Static_ref ;

Parent: Static_ref ;

Client: Static_ref ;

Supplier: Static_ref ;

Static_ref: Zero_or_more_Cluster_prefixes Static_component_name ;

Zero_or_more_Cluster_prefixes: -- Empty
                               | Zero_or_more_Cluster_prefixes Cluster_prefix ;

Cluster_prefix: Cluster_name '.' ;

Static_component_name: Class_name 
                       | Cluster_name ;

Multiplicity: INTEGER_TOKEN ;
 
Semantic_label: Manifest_string ;

-- A.6 CLASS INTERFACE DESCRIPTION 

Class_interface: Optional_Indexing_Index_list
                 Optional_Inherit_Parent_class_list
                 Features 
                 Optional_Invariant_Class_invariant
                 END_TOKEN ;

Optional_Inherit_Parent_class_list: -- Empty
                                    | INHERIT_TOKEN Parent_class_list ;

Optional_Invariant_Class_invariant: -- Empty
                                    | INVARIANT_TOKEN Class_invariant ;
 
Class_invariant:    Assertion ;

Parent_class_list:  At_least_one_Class_type ;

At_least_one_Class_type: Class_type
                         Optional_Class_types ;

Optional_Class_types: -- Empty
                      | Optional_Class_types ';' Class_type ;

Features: At_least_one_Feature_clause ;

At_least_one_Feature_clause: Feature_clause
                             Optional_Feature_clauses ;

Optional_Feature_clauses: -- Empty
                          | Optional_Feature_clauses Feature_clause ;

Feature_clause: FEATURE_TOKEN Optional_Selective_export
                Optional_Comment
                Feature_specifications ;

Optional_Selective_export: -- Empty
                           | Selective_export ;

Feature_specifications:  At_least_one_Feature_specification ;

At_least_one_Feature_specification: Feature_specification
                                    Optional_Feature_specifications ;

Optional_Feature_specifications: -- Empty
                      | Optional_Feature_specifications Feature_specification ;

Feature_specification: Optional_Deferred_or_Effective_or_Redefined
                       Feature_name_list 
                       Optional_Type_mark_Type
                       Optional_Rename_clause
                       Optional_Comment
                       Optional_Feature_arguments_clause
                       Optional_Contract_clause ;

Optional_Deferred_or_Effective_or_Redefined: -- Empty
                                             | DEFERRED_TOKEN
                                             | EFFECTIVE_TOKEN
                                             | REDEFINED_TOKEN ;

Optional_Type_mark_Type: -- Empty
                         | Type_mark Type ;

Optional_Rename_clause: -- Empty
                        | Rename_clause ;

Optional_Feature_arguments_clause: -- Empty
                                   | Feature_arguments ;

Optional_Contract_clause: -- Empty
                          | Contract_clause ;

Contract_clause: Contracting_conditions 
                 END_TOKEN ;

Contracting_conditions: Precondition 
                        | Postcondition 
                        | Pre_and_post ;

Precondition: REQUIRE_TOKEN Assertion ;
Postcondition: ENSURE_TOKEN Assertion ;

Pre_and_post: Precondition Postcondition ;

Selective_export: '{' Class_name_list '}' ;
 
Feature_name_list: At_least_one_Feature_name ;

At_least_one_Feature_name: Feature_name 
                           Optional_Feature_names ;

Optional_Feature_names: -- Empty
                        | Optional_Feature_names ',' Feature_name ;

Feature_name: IDENTIFIER_TOKEN
              | Prefix_rule 
              | Infix_rule ;

Rename_clause: '{' Renaming '}' ;
 
Renaming: '^' Class_name '.' Feature_name ;

Feature_arguments: At_least_one_Feature_argument ;

At_least_one_Feature_argument: Feature_argument
                               Optional_Feature_arguments ;

Optional_Feature_arguments: -- Empty
                            | Optional_Feature_arguments Feature_argument ;

Feature_argument: IMPLIES_TOKEN Optional_Identifier_list Type ;

Optional_Identifier_list: -- Empty
                          | Identifier_list ':' ;

Identifier_list: At_least_one_Identifier ;

At_least_one_Identifier: IDENTIFIER_TOKEN 
                         Optional_Identifiers ;

Optional_Identifiers: -- Empty
                      | Optional_Identifiers ',' IDENTIFIER_TOKEN ;

Prefix_rule: PREFIX_TOKEN '"' Prefix_operator '"' ;

Infix_rule: INFIX_TOKEN '"' Infix_operator '"' ;

Prefix_operator: Unary 
                 | FREE_OPERATOR_TOKEN ;

Infix_operator: Binary 
                | FREE_OPERATOR_TOKEN ;

Optional_Formal_generics_clause: -- Empty
                                 | Formal_generics ;

Formal_generics: '[' Formal_generic_list ']' ;

Formal_generic_list: At_least_one_Formal_generic ;

At_least_one_Formal_generic: Formal_generic 
                             Optional_Formal_generics ;

Optional_Formal_generics: -- Empty
                          | Optional_Formal_generics ',' Formal_generic ;

Formal_generic: Formal_generic_name Optional_Implies_Class_type ;

Optional_Implies_Class_type: -- Empty
                             | IMPLIES_TOKEN Class_type ;

Formal_generic_name: ALL_CAPS_IDENTIFIER_TOKEN ;
 
Class_type: Class_name Optional_Actual_generics ;

Optional_Actual_generics: -- Empty
                          | Actual_generics ;

Actual_generics: '[' Type_list ']' ;
 
Type_list: At_least_one_Type ;

At_least_one_Type: Type
                   Optional_Types ;

Optional_Types: -- Empty
                | Optional_Types ',' Type ;

Type: Class_type 
      | Formal_generic_name ;

Unary: DELTA_TOKEN
       | OLD_TOKEN 
       | NOT_TOKEN
       | '+' 
       | '-'
       ; 

Binary: '+' 
        | '-' 
        | '*' 
        | '/' 
        | '<' 
        | '>'
        | LESS_THAN_OR_EQUAL_TOKEN
        | GREATER_THAN_OR_EQUAL_TOKEN
        | '=' 
        | NOT_EQUAL_TOKEN
        | DOUBLE_SLASH_TOKEN
        | DOUBLE_BACKSLASH_TOKEN
        | '^'
        | OR_TOKEN
        | XOR_TOKEN 
        | AND_TOKEN 
        | IMPLIES_TOKEN
        | EQUIVALENT_TO_TOKEN
        | MEMBER_OF_TOKEN 
        | ':' 
        ;

-- A.7 FORMAL ASSERTIONS 

Assertion: At_least_one_Assertion_clause ;

At_least_one_Assertion_clause: Assertion_clause 
                               Optional_Assertion_clauses ;

Optional_Assertion_clauses: -- Empty
                            | Optional_Assertion_clauses ';' Assertion_clause ;

Assertion_clause: Boolean_expression 
                  | Comment ;

Boolean_expression: Expression ;

Expression: Quantification 
            | Call 
            | Operator_expression 
            | Constant ;

Quantification: Quantifier Range_expression 
                Optional_Restriction Proposition ;

Quantifier: FOR_ALL_TOKEN
            | EXISTS_TOKEN ;

Range_expression: At_least_one_Variable_range ;

At_least_one_Variable_range: Variable_range 
                             Optional_Variable_ranges ;

Optional_Variable_ranges: -- Empty
                          | Optional_Variable_ranges ';' Variable_range ;

Optional_Restriction: -- Empty
                      | Restriction ;

Restriction: SUCH_THAT_TOKEN Boolean_expression ;

Proposition: IT_HOLDS_TOKEN Boolean_expression ;

Variable_range: Member_range 
                | Type_range ;

Member_range: Identifier_list MEMBER_OF_TOKEN Set_expression ;

Type_range: Identifier_list ':' Type ;

Call: Optional_Parenthesized_qualifier Call_chain ;

Optional_Parenthesized_qualifier: -- Empty
                                  | Parenthesized_qualifier ;

Parenthesized_qualifier: Parenthesized '.' ;

Call_chain: At_least_one_Unqualified_call ;

At_least_one_Unqualified_call: Unqualified_call '.'
                               Optional_Unqualified_calls ;

Optional_Unqualified_calls: -- Empty
                            | Optional_Unqualified_calls Unqualified_call '.' ;

Unqualified_call: IDENTIFIER_TOKEN Optional_Actual_arguments ;

Optional_Actual_arguments: -- Empty
                           | Actual_arguments ;
 
Actual_arguments: '(' Expression_list ')' ;

Expression_list: At_least_one_Expression ;

At_least_one_Expression: Expression 
                         Optional_Expressions ;

Optional_Expressions: -- Empty
                      | Optional_Expressions ',' Expression ;

Operator_expression: Parenthesized 
                     | Unary_expression %prec UNARY_DUMMY
                     | Binary_expression ;

Parenthesized: '(' Expression ')' ; 

Unary_expression: Prefix_operator Expression ;

Binary_expression: Expression Infix_operator Expression ;

Set_expression: Enumerated_set 
                | Call 
                | Operator_expression ;

Enumerated_set: '{' Enumeration_list '}' ;
 
Enumeration_list: At_least_one_Enumeration_element ;

At_least_one_Enumeration_element: Enumeration_element 
                                  Optional_Enumeration_elements ;

Optional_Enumeration_elements: -- Empty
                      | Optional_Enumeration_elements ',' Enumeration_element ;

Enumeration_element: Expression 
                     | Interval ;

Interval: Integer_interval 
          | Character_interval ;

Integer_interval: Integer_constant DOUBLE_DOT_TOKEN Integer_constant ;

Character_interval: Character_constant DOUBLE_DOT_TOKEN Character_constant ;

-- @design kiniry - Aug 26, 2001 - Added RESULT_TOKEN to this rule since, 
-- at first blush, it seems to be the right place for it.  See bug id TODO 
-- for more details.

Constant: Manifest_constant 
          | RESULT_TOKEN
          | CURRENT_TOKEN 
          | VOID_TOKEN ;

Manifest_constant: Boolean_constant 
                   | Character_constant 
                   | Integer_constant 
                   | Real_constant
                   | Manifest_string ;

Optional_Sign: -- Empty
               | Sign ;

Sign: '+' 
      | '-' ; 

Boolean_constant: TRUE_TOKEN 
                  | FALSE_TOKEN ;

Character_constant: '\'' CHARACTER_TOKEN '\'' ;

Integer_constant: Optional_Sign INTEGER_TOKEN ;

Real_constant: Optional_Sign REAL_TOKEN ;

-- @todo: This specification is incorrect.  Manifest textblocks can 
-- include multiple New_line separated string.

Manifest_textblock: String_begin SIMPLE_STRING_TOKEN String_end ;

Manifest_string: String_begin SIMPLE_STRING_TOKEN String_end ;

String_begin: STRING_DELIMITER_TOKEN ;

String_end: STRING_DELIMITER_TOKEN ;

-- A.8 DYNAMIC DIAGRAMS 

Dynamic_diagram_rule: DYNAMIC_DIAGRAM_TOKEN Optional_Extended_id 
                      Optional_Comment
                      COMPONENT_TOKEN 
                      Dynamic_block 
                      END_TOKEN ;

Dynamic_block: -- Empty
               | Dynamic_block Dynamic_component ;

Dynamic_component: Scenario_description 
                   | Object_group_rule
                   | Object_stack_rule
                   | Object_rule
                   | Message_relation ;

Scenario_description: SCENARIO_TOKEN Scenario_name 
                      Optional_Comment 
                      ACTION_TOKEN Labeled_actions 
                      END_TOKEN ;

Labeled_actions: At_least_one_Labeled_action ;

At_least_one_Labeled_action: Labeled_action
                             Optional_Labeled_actions ;

Optional_Labeled_actions: -- Empty
                          | Optional_Labeled_actions Labeled_action ;

Labeled_action: Action_label Action_description ;

Action_label: Manifest_string ;

Action_description: Manifest_textblock ;

Scenario_name: Manifest_string ;

Object_group_rule: Optional_Nameless 
                   OBJECT_GROUP_TOKEN Group_name 
                   Optional_Comment 
                   Optional_Group_components ; 

Optional_Nameless: -- Empty
                   | NAMELESS_TOKEN ;

Optional_Group_components: -- Empty
                           | Group_components ;

Group_components: COMPONENT_TOKEN Dynamic_block END_TOKEN ;

Object_stack_rule: OBJECT_STACK_TOKEN Object_name Optional_Comment ;

Object_rule: OBJECT_TOKEN Object_name Optional_Comment ;

Message_relation: Caller CALLS_TOKEN Receiver Optional_Message_label ;

Optional_Message_label: -- Empty
                        | Message_label ;
 
Caller: Dynamic_ref ;

Receiver: Dynamic_ref ;

Dynamic_ref: Zero_or_more_Group_prefixes Dynamic_component_name ;

Zero_or_more_Group_prefixes: -- Empty
                             | Zero_or_more_Group_prefixes Group_prefix ;

Group_prefix: Group_name '.' ;
 
Dynamic_component_name: Object_name
                        | Group_name ;

Object_name: Class_name Optional_Extended_id_clause ;

Optional_Extended_id_clause: -- Empty
                             | '.' Extended_id ;

Group_name: Extended_id ;

Message_label: Manifest_string ;

-- A.9 NOTATIONAL TUNING 

Notational_tuning: Change_string_marks
                   | Change_concatenator
                   | Change_prefix ;

Change_string_marks: STRING_MARKS_TOKEN Manifest_string Manifest_string ;

Change_concatenator: CONCATENATOR_TOKEN Manifest_string ;

Change_prefix: KEYWORD_PREFIX_TOKEN Manifest_string ;

-- END OF BON GRAMMAR

%%
end -- class EBON_PARSER

-- Local Variables:
-- mode:eiffel
-- End:
