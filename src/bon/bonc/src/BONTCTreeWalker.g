/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */

tree grammar BONTCTreeWalker;
options {
  tokenVocab=BON;
  ASTLabelType=CommonTree;
  superClass=AbstractBONTCWalker;  
}


@header {
  package ie.ucd.bon.parser; 
  
  import java.util.LinkedList;
  
  import ie.ucd.bon.ast.BONType;
}

/**********************************************  
 ##############################################
 ###   Parser...                            ###
 ##############################################
 **********************************************/

prog  :  ^( PROG indexing? bon_specification )
        |
         ^( PROG PARSE_ERROR )
      ;

/**********************************************  
 ***   BON Specification                    ***
 **********************************************/

bon_specification  :  (specification_element)+   
                   ;

specification_element  :    informal_chart
                          | class_dictionary
                          | static_diagram
                          | dynamic_diagram
                          | notational_tuning
                       ;

/**********************************************  
 ***   Informal charts                      ***
 **********************************************/

informal_chart  :    system_chart
                   | cluster_chart
                   | class_chart
                   | event_chart
                   | scenario_chart
                   | creation_chart
                ;
			
class_dictionary  :^(
                     CLASS_DICTIONARY system_name 
                     { getITC().checkSystemName($system_name.text,getSLoc($system_name.start.token)); }
                     (indexing)?
                     (explanation)? 
                     (part)? 
                     (dictionary_entry)+ 
                    )
                   |
                   ^( CLASS_DICTIONARY  PARSE_ERROR )
                  ;
			
dictionary_entry  :^(
                     DICTIONARY_ENTRY class_name
                     { getITC().checkValidClassType($class_name.text, getSLoc($class_name.start.token));
                       getContext().enterDictionaryEntry($class_name.text, $DICTIONARY_ENTRY.token); 
                     }
                     cluster_name_list                      
                     description 
                     { getContext().leaveDictionaryEntry(); }
                    )
                  ;

/**********************************************/

system_chart  :^(
                 SYSTEM_CHART system_name
                 (indexing)?
                 (explanation)? 
                 (part)? 
                 (cluster_entries)? 
                )
              ;

explanation  :^(
                EXPLANATION manifest_textblock
               )
              |
              ^( EXPLANATION PARSE_ERROR )
             ;

indexing  :^(
             INDEXING index_list
            )
           |
           ^( INDEXING PARSE_ERROR )
          ;

part  :^(
         PART MANIFEST_STRING
        )
       |
       ^( PART PARSE_ERROR )
      ;

description  :^(
                DESCRIPTION manifest_textblock
               )
             ;

cluster_entries  :^(
                    CLUSTER_ENTRIES (cluster_entry)+ 
                   )
                 ;
                 
cluster_entry  :^(
                  CLUSTER_ENTRY cluster_name description 
                  { getITC().checkValidClusterType($cluster_name.text,getSLoc($cluster_name.start.token)); }
                 )
               ;
               
system_name  :^(
                SYSTEM_NAME IDENTIFIER
               )
             ;

/**********************************************/

index_list  :^(
               INDEX_LIST (index_clause)+
              )
            ;
            
index_clause  :^(
                 INDEX_CLAUSE IDENTIFIER index_term_list
                )
               | 
               ^( INDEX_CLAUSE PARSE_ERROR )
              ;
                
index_term_list  :^(
                    INDEX_TERM_LIST (index_string)+
                   )
                 ;
                 
index_string  :^(
                 INDEX_STRING MANIFEST_STRING
                )
              ;

/**********************************************/

cluster_chart  :^(
                  CLUSTER_CHART cluster_name 
                  (indexing)? 
                  (explanation)? 
                  (part)? 
                  (class_entries)? 
                  (cluster_entries)? 
                 )
               ;
               
class_entries  :^(
                  CLASS_ENTRIES (class_entry)+ 
                 )
               ;
               
class_entry  :^(
                CLASS_ENTRY class_name description 
                { getITC().checkValidClassType($class_name.text,getSLoc($class_name.start.token)); }
               )
             ;
             
cluster_name  :^(
                 CLUSTER_NAME IDENTIFIER
                )
              ;

/**********************************************/

class_chart  :^( 
                CLASS_CHART class_name
                (indexing)? 
                (explanation)? 
                (part)? 
                (inherits)?
                (queries)? 
                (commands)? 
                (constraints)?
               )
             ;

inherits  :  ^(
               INHERITS
               { getContext().enterInheritsClause(); } 
               class_name_list
               { getContext().leaveInheritsClause(); }
              )
            |
             ^( INHERITS PARSE_ERROR )
          ;

queries  : ^(QUERIES query_list)
         ;
         
commands  : ^(COMMANDS command_list)
          ;

constraints  : ^(CONSTRAINTS constraint_list)
             ;

query_list  :^(
               QUERY_LIST (manifest_textblock)+
              )
            ;
            
command_list  :^(
                 COMMAND_LIST (manifest_textblock)+
                )
              ;
              
constraint_list  :^(
                    CONSTRAINT_LIST (manifest_textblock)+
                   )
                 ;

class_name_list  :^(
                    CLASS_NAME_LIST 
                    ( class_name 
                      { getFTC().checkValidClassTypeByContext($class_name.text, getSLoc($class_name.start.token));
                        getITC().checkValidClassTypeByContext($class_name.text, getSLoc($class_name.start.token)); 
                      } )+
                   )
                 ;
     
cluster_name_list  :^(
                      CLUSTER_NAME_LIST ( cluster_name { getITC().checkValidClusterTypeByContext($cluster_name.text, getSLoc($cluster_name.start.token)); } )+
                     )
                   ;
                 
class_or_cluster_name_list  :  ^( CLASS_OR_CLUSTER_NAME_LIST 
                                  ( class_name
                                    { getITC().checkValidClassTypeByContext($class_name.text, getSLoc($class_name.start.token));
                                      //Only can be in informal here, so leave FTC alone 
                                    }
                                  )* 
                                  ( cluster_name
                                    { getITC().checkValidClusterType($cluster_name.text, getSLoc($cluster_name.start.token));  }
                                  )+ 
                                )
                             |
                               ^( CLASS_OR_CLUSTER_NAME_LIST class_name_list ) 
                            ;
                 
class_name  :^(
               CLASS_NAME IDENTIFIER
              )
            ;

/**********************************************/

event_chart  :^(
                EVENT_CHART
                system_name  
                { getITC().checkSystemName($system_name.text,getSLoc($system_name.start.token)); }
                ('incoming')? ('outgoing')?
                (indexing)?
                (explanation)?
                (part)?
                (event_entries)?
               )
             ;
             
event_entries  :^(
                  EVENT_ENTRIES
                  (event_entry)+
                 )
               ;
               
event_entry  :^(
                EVENT_ENTRY
                { getContext().enterEventEntry(); }
                manifest_textblock
                class_or_cluster_name_list
                { getContext().leaveEventEntry(); }
               )
              |
              ^(EVENT_ENTRY PARSE_ERROR)
             ;

/**********************************************/

scenario_chart  :^(
                   SCENARIO_CHART
                   system_name
                   { getITC().checkSystemName($system_name.text,getSLoc($system_name.start.token)); }
                   (indexing)?
                   (explanation)?
                   (part)?
                   (scenario_entries)?
                  )
                ;
                
scenario_entries  :^(
                     SCENARIO_ENTRIES
                     (scenario_entry)+ 
                    )                 
                  ;
                  
scenario_entry  :^(
                   SCENARIO_ENTRY
                   MANIFEST_STRING description 
                  )
                ;

/**********************************************/

creation_chart  :^(
                   CREATION_CHART
                   system_name
                   { getITC().checkSystemName($system_name.text,getSLoc($system_name.start.token)); }
                   (indexing)?
                   (explanation)?
                   (part)?
                   (creation_entries)?
                  )
                ;
                
creation_entries  :^(
                     CREATION_ENTRIES
                     (creation_entry)+
                    )
                  ;
                  
creation_entry  :^(
                   CREATION_ENTRY
                   class_name 
                   { getITC().checkValidClassType($class_name.text,getSLoc($class_name.start.token)); 
                     getContext().enterCreationEntry(); }
                   class_or_cluster_name_list
                   { getContext().leaveCreationEntry(); } 
                  )
                ;

/**********************************************  
 ***   Static Diagrams                      ***
 **********************************************/
 
static_diagram  :^(
                   STATIC_DIAGRAM
                   (extended_id)? (COMMENT)?  //Comment ignored anyway (hidden channel)...? 
                   (static_block)? 
                  )
                ;
                
extended_id  :^(
                EXTENDED_ID IDENTIFIER
               )
              |
              ^(
                EXTENDED_ID INTEGER
               )
             ;
             
static_block  :^(
                 STATIC_BLOCK (static_component)+
                )
              ;

//NB renamed "class" rule to "classX" as class is a reserved keyword in Java              
static_component  : ^(
                      STATIC_COMPONENT cluster
                     )
                    |
                    ^(
                      STATIC_COMPONENT classX
                     )
                    |
                    ^(
                      STATIC_COMPONENT static_relation
                     )
                  ;

/**********************************************/

cluster  :^(
            CLUSTER cluster_name
            ('reused')? (COMMENT)? 
            (cluster_components)?
           )
         ;
         
cluster_components  :^(
                       CLUSTER_COMPONENTS (static_block)?
                      )
                    ;
                    
classX  :^(
           CLASS
           ('root')? ('deferred')? ('effective')? 
           class_name
           { getContext().enterClass($class_name.text); } 
           (formal_generics)?
           ('reused')? ('persistent')?  ('interfaced')? (COMMENT)?
           (class_interface)? 
           { getContext().leaveClass(); }
          )
        ;
            
static_relation  :^(
                    STATIC_RELATION inheritance_relation
                   )
                  |
                  ^(
                    STATIC_RELATION client_relation
                   )
                 ;

/**********************************************/

inheritance_relation  :^(
                         INHERITANCE_RELATION
                         child (multiplicity)? 
                         parent (semantic_label)?
                        )
                      ;
                    
client_relation  :^(
                    CLIENT_RELATION
                    client (client_entities)? (type_mark)? 
                    supplier (semantic_label)? 
                   )
                 ;
                 
client_entities  :^(
                    CLIENT_ENTITIES
                    client_entity_expression
                   )
                 ;
                 
client_entity_expression  :^(
                             CLIENT_ENTITY_EXPRESSION client_entity_list
                            )
                           |
                           ^(
                             CLIENT_ENTITY_EXPRESSION multiplicity
                            )
                          ;
                          
client_entity_list  :^(
                       CLIENT_ENTITY_LIST (client_entity)+
                      )
                    ;
                    
client_entity  :  ^(
                    CLIENT_ENTITY prefix
                   )
                  | 
                  ^(
                    CLIENT_ENTITY infix
                   )
                  | 
                  ^(
                    CLIENT_ENTITY supplier_indirection
                   )
                  | 
                  ^(
                    CLIENT_ENTITY parent_indirection
                   )
               ;
               
supplier_indirection  :^(
                         SUPPLIER_INDIRECTION (indirection_feature_part)? generic_indirection 
                        )
                      ;
                      
indirection_feature_part  :^(
                             INDIRECTION_FEATURE_PART feature_name
                            )
                           |
                           ^(
                             INDIRECTION_FEATURE_PART indirection_feature_list
                            )
                          ;	
                          
indirection_feature_list  :^(
                             INDIRECTION_FEATURE_LIST feature_name_list
                            )
                          ;
                          
parent_indirection  :^(
                       PARENT_INDIRECTION generic_indirection
                      )
                    ;

/**********************************************/

generic_indirection  :
//^(
//                        GENERIC_INDIRECTION formal_generic_name
//                       )
//                      |
                      ^(
                        GENERIC_INDIRECTION indirection_element
                       )
                     ;
                     
named_indirection  :^(
                      NAMED_INDIRECTION class_name indirection_list
                     )
                    |
                    ^(NAMED_INDIRECTION PARSE_ERROR)
                   ;
                   
indirection_list  :^(
                     INDIRECTION_LIST (indirection_element)+
                    )
                  ;
                  
indirection_element  : ^(
                         INDIRECTION_ELEMENT '...'
                        )
                      | 
                       ^(
                         INDIRECTION_ELEMENT named_indirection
                        )
                      | 
                       ^(
                       	 INDIRECTION_ELEMENT class_name
                       	)
                     ;

                     
type_mark  :^(
              TYPE_MARK ':'
             )
            |
            ^(
              TYPE_MARK ':{'
             )
            | 
            ^(
              TYPE_MARK shared_mark
             )
           ;
           
shared_mark  :^(
                SHARED_MARK multiplicity
               )
             ;

/**********************************************/

child  :^(
          CHILD static_ref
         )
       ;
       
parent  :^(
           PARENT static_ref
          )
        ;
        
client  :^(
           CLIENT static_ref
          )
        ;
        
supplier  :^(
             SUPPLIER static_ref
            )
          ;
          
static_ref  : ^(
                STATIC_REF p=cluster_prefix n=static_component_name 
                { getFTC().checkValidStaticRef($p.text,getSLoc($p.start.token),$n.text,getSLoc($n.start.token)); }
               )
             |
              ^(
                STATIC_REF n=static_component_name
                { getFTC().checkValidStaticRef(null,null,$n.text,getSLoc($n.start.token)); }
               )
            ;
            
cluster_prefix  :^(
                   CLUSTER_PREFIX (cluster_name)+
                  )
                ;
  
static_component_name  :^(
                          STATIC_COMPONENT_NAME IDENTIFIER
                         )
                       ;
                       
multiplicity  :^(
                 MULTIPLICITY INTEGER
                )
              ;
              
semantic_label  :^(
                   SEMANTIC_LABEL MANIFEST_STRING
                  )
                ;

/**********************************************  
 ***   Class Interface Description          ***
 **********************************************/

class_interface  :^(
                    CLASS_INTERFACE
                    (indexing)?
                    (parent_class_list)?
                    features
                    (class_invariant)?
                   )
                 ;
                    
class_invariant  :^(
                    CLASS_INVARIANT assertion
                   )
                 ;
                 
parent_class_list  :^(
                      PARENT_CLASS_LIST (class_type { getFTC().checkValidClassType($class_type.text,getSLoc($class_type.start.token),true); } )+
                     )
                    |
                    ^(PARENT_CLASS_LIST PARSE_ERROR )
                   ;
                   
features  :^(
             FEATURES (feature_clause)+
            )
          ;
          
/**********************************************/

feature_clause  :^(
                   FEATURE_CLAUSE
                   (selective_export)? 
                   (COMMENT)? 
                   feature_specifications 
                  )
                ;
                
feature_specifications  :^(
                           FEATURE_SPECIFICATIONS
                           (feature_specification)+
                          )
                        ;
                        
feature_specification  :^(
                          FEATURE_SPECIFICATION
                          ('deferred')? ('effective')? ('redefined')?
                          feature_name_list (has_type)?
                          (rename_clause)?
                          (COMMENT)?
                          (feature_arguments)?
                          (contract_clause)? 
                         )
                       ;

has_type  : ^(HAS_TYPE type_mark type)
          ;

/**********************************************/

contract_clause  :^(
                    CONTRACT_CLAUSE contracting_conditions
                   ) 
                 ;
             
contracting_conditions  :^(
                           CONTRACTING_CONDITIONS (precondition)? (postcondition)?
                          )
                        ;
        
precondition  :^(
                 PRECONDITION assertion
                )
              ;
              
postcondition  :^(
                  POSTCONDITION assertion
                 )
               ;

/**********************************************/

selective_export  :^(
                     SELECTIVE_EXPORT
                     { getContext().enterSelectiveExport(); } 
                     class_name_list
                     { getContext().leaveSelectiveExport(); }
                    )
                  ;
                  
feature_name_list  :^(
                      FEATURE_NAME_LIST (feature_name)+
                     )
                   ;
                   
feature_name  :^(
                 FEATURE_NAME IDENTIFIER
                )
               | 
               ^(
                 FEATURE_NAME prefix
                )
               | 
               ^(
                 FEATURE_NAME infix
                )
              ;
              
rename_clause  :^(
                  RENAME_CLAUSE renaming
                 )
               ;
               
renaming  :^(
             RENAMING class_name feature_name { getFTC().checkRenaming($class_name.text, $feature_name.text, getSLoc($class_name.start.token)); }
            )
          ;
          
feature_arguments  :^(
                      FEATURE_ARGUMENTS (feature_argument)+ 
                     )
                   ;
                   
feature_argument  :^(
                     FEATURE_ARGUMENT (identifier_list)? type
                    )
                  ;
                  
identifier_list  :^(
                    IDENTIFIER_LIST (IDENTIFIER)+
                   )
                 ;
              
prefix  :^(
           PREFIX prefix_operator
          )
        ;
        
infix  :^(
          INFIX infix_operator
         )
       ;
       
prefix_operator  :^(
                    PREFIX_OPERATOR unary
                   )
                 ;                

infix_operator  :^(
                   INFIX_OPERATOR binary
                  )
                ;

/**********************************************/

formal_generics  :^(
                    FORMAL_GENERICS formal_generic_list
                   )
                 ;
                 
formal_generic_list  :^(
                        FORMAL_GENERIC_LIST (formal_generic)+
                       )
                     ;
                     
formal_generic  :^(
                   FORMAL_GENERIC formal_generic_name (class_type)?
                  )
                ;
                
formal_generic_name  :^(
                        FORMAL_GENERIC_NAME IDENTIFIER
                       )
                     ;
                     
class_type  :^(
               CLASS_TYPE class_name (actual_generics)? 
              )
            ;
            
actual_generics  :^(
                    ACTUAL_GENERICS type_list
                   )
                 ;
                 
type_list  :^(
              TYPE_LIST (type)+
             )
           ;

type  :^(
         TYPE IDENTIFIER (actual_generics)?
        )
      ;

/**********************************************  
 ***   Formal Assertions                    ***
 **********************************************/

assertion  :^(
              ASSERTION (assertion_clause)+
             )
           ;
           
assertion_clause  :^(
                     ASSERTION_CLAUSE boolean_expression
                    )
                  ;
                 
boolean_expression  :^(
                       be=BOOLEAN_EXPRESSION 
                       { getFTC().checkType("BOOL", getSLoc($be.token)); }
                       { getContext().addTypeRequirement(BONType.mk("BOOL")); } 
                       expression
                       { getContext().removeTypeRequirement(); }
                      )
                    ;
            
quantification  :^(
                   q=QUANTIFICATION
                   { getFTC().checkType("BOOL", getSLoc($q.token)); }
                   quantifier  
                   
                   { getContext().enterQuantification(); }
                   range_expression
                    
                   (restriction)? 
                   proposition 
                   
                   { getContext().enterQuantification(); }
                  )
                ;
                
quantifier  :^(
               QUANTIFIER 'for_all'
              )
             |
             ^(
               QUANTIFIER 'exists'
              )
            ;
            
range_expression  :^(
                     RANGE_EXPRESSION (variable_range)+
                    )
                  ;
                  
restriction  :^(
                RESTRICTION boolean_expression
               )
             ;
             
proposition  :^(
                PROPOSITION boolean_expression
               )
             ;
             
variable_range  :^(
                   VARIABLE_RANGE member_range
                  )
                 |
                 ^(
                   VARIABLE_RANGE type_range
                  )
                ;
                
member_range  :^(
                 MEMBER_RANGE identifier_list expression
                )
              ;
              
type_range  :^(
               TYPE_RANGE identifier_list type
              )
            ;

/**********************************************/

//call  :^(
//         CALL
//         (expression)? call_chain
//        )
//      ;
                         
call_chain  :^(
               CALL_CHAIN (unqualified_call)+ { getContext().clearLastCallChainType(); }
              )
            ;
            
unqualified_call
@init { BONType t = null; }  
                  :^(
                     UNQUALIFIED_CALL 
                     i=IDENTIFIER 
                     { t = getFTC().getTypeForCall($i.text,getSLoc($i.token)); }
                     (actual_arguments)?
                     { if (t!=null) { getContext().setLastCallChainType(t); } }
                    )
                  ;
                  
actual_arguments  :^(
                     ACTUAL_ARGUMENTS expression_list?
                    )
                  ;
              
expression_list  :^(
                    EXPRESSION_LIST (expression)+
                   )
                 ;

/**********************************************/
                
enumerated_set  :^(
                   ENUMERATED_SET enumeration_list
                  )
                ;
                
enumeration_list  :^(
                     ENUMERATION_LIST (enumeration_element)+
                    )
                  ;
         
enumeration_element  :^(
                        ENUMERATION_ELEMENT expression
                       )
                      | 
                      ^(
                        ENUMERATION_ELEMENT interval
                       )
                     ;
                     
interval  :^(
             INTERVAL integer_interval
            ) 
           | 
           ^(
             INTERVAL character_interval
            ) 
          ;
          
integer_interval  :^(
                     INTEGER_INTERVAL integer_constant integer_constant
                    )
                  ;
                  
character_interval  :^(
                       CHARACTER_INTERVAL CHARACTER_CONSTANT CHARACTER_CONSTANT
                      )
                    ;
/**********************************************/

constant  :^(
             CONSTANT manifest_constant
            )
           |
           ^(
             c=CONSTANT { getFTC().checkType(getContext().getClassName(),getSLoc($c.token)); } 'Current'
            )
           |
           ^(
             c=CONSTANT { getFTC().checkType("Void",getSLoc($c.token)); } 'Void'
            )
          ;

manifest_constant  : ^(
                       MANIFEST_CONSTANT boolean_constant
                      )
                     | 
                     ^(
                       mc=MANIFEST_CONSTANT { getFTC().checkType("CHAR",getSLoc($mc.token)); } CHARACTER_CONSTANT
                      )
                     | 
                     ^(
                       MANIFEST_CONSTANT integer_constant
                      )
                     | 
                     ^(
                       MANIFEST_CONSTANT real_constant
                      )
                     | 
                     ^(
                       mc=MANIFEST_CONSTANT { getFTC().checkType("STRING",getSLoc($mc.token)); } MANIFEST_STRING
                      )
                     | 
                     ^(
                     	 MANIFEST_CONSTANT enumerated_set
                     	)
                   ;
                   
sign  :^(
         SIGN add_sub_op
        )
      ;
      
boolean_constant  :^(
                     bc=BOOLEAN_CONSTANT { getFTC().checkType("BOOL",getSLoc($bc.token)); } 'true'
                    )
                   |
                   ^(
                     bc=BOOLEAN_CONSTANT { getFTC().checkType("BOOL",getSLoc($bc.token)); } 'false'
                    )
                  ;
                    
integer_constant  :^(
                     ic=INTEGER_CONSTANT
                     { getFTC().checkType("VALUE",getSLoc($ic.token)); }
                     (sign)? INTEGER
                    )
                  ;
                  
real_constant  :^(
                  rc=REAL_CONSTANT
                  { getFTC().checkType("VALUE",getSLoc($rc.token)); }
                  (sign)? REAL
                 )
               ;

/**********************************************  
 ***   Dynamic Diagrams                     ***
 **********************************************/

dynamic_diagram  :^(
                    DYNAMIC_DIAGRAM
                    (extended_id)? (COMMENT)?
                    (dynamic_block)?
                   )
                 ;
                 
dynamic_block  :^(
                  DYNAMIC_BLOCK
                  (dynamic_component)+
                 )
               ;
               
dynamic_component  : ^(
                       DYNAMIC_COMPONENT scenario_description
                      )
                     |
                     ^(
                       DYNAMIC_COMPONENT object_group
                      )
                     |
                     ^(
                       DYNAMIC_COMPONENT object_stack
                      )
                     | 
                     ^(
                       DYNAMIC_COMPONENT object
                      )
                     | 
                     ^(
                       DYNAMIC_COMPONENT message_relation
                      )
                   ; 

/**********************************************/

scenario_description  :^(
                         SCENARIO_DESCRIPTION 
                         scenario_name (COMMENT)?
                         labelled_actions 
                        )
                      ;
                      
labelled_actions  :^(
                     LABELLED_ACTIONS (labelled_action)+
                    )
                  ;
                  
labelled_action  :^(
                    LABELLED_ACTION action_label action_description
                   )
                 ;
                 
action_label  :^(
                 ACTION_LABEL MANIFEST_STRING
                )
              ;
              
action_description  :^(
                       ACTION_DESCRIPTION manifest_textblock
                      )
                    ;
                    
scenario_name  :^(
                  SCENARIO_NAME manifest_textblock
                 )
               ;

/**********************************************/

object_group  :^(
                 OBJECT_GROUP ('nameless')? group_name (COMMENT)? (group_components)? 
                )
              ;
              
group_components  :^(
                     GROUP_COMPONENTS dynamic_block
                    )
                  ;
                  
object_stack  :^(
                 OBJECT_STACK object_name (COMMENT)?
                )
              ;
              
object  :^(
           OBJECT object_name (COMMENT)?
          )
        ;

/**********************************************/

message_relation  :^(
                     MESSAGE_RELATION caller receiver (message_label)?
                    )
                  ;
                  
caller  :^(
           RECEIVER dynamic_ref
          )
        ;
        
receiver  :^(
             RECEIVER dynamic_ref
            )
          ;
          
dynamic_ref  :^(
                DYNAMIC_REF (extended_id)+
               )
             ;

dynamic_component_name  :^(
                           DYNAMIC_COMPONENT_NAME IDENTIFIER (extended_id)?
                          )
                         |
                         ^(
                           DYNAMIC_COMPONENT_NAME INTEGER
                          )
                        ;

object_name  :^(
                OBJECT_NAME class_name (extended_id)?
               )
             ;
             
group_name  :^(
               GROUP_NAME extended_id
              )
            ;
            
message_label  :^(
                  MESSAGE_LABEL MANIFEST_STRING
                 )
               ;

/**********************************************  
 ***   Notational Tuning                    ***
 **********************************************/
notational_tuning  :^(
                      NOTATIONAL_TUNING change_string_marks
                     )
                    |
                    ^(
                      NOTATIONAL_TUNING change_concatenator
                     )
                    | 
                    ^(
                      NOTATIONAL_TUNING change_prefix
                     )
                   ;
                   
change_string_marks  :^(
                        CHANGE_STRING_MARKS MANIFEST_STRING MANIFEST_STRING
                       )
                     ;
                     
change_concatenator  :^(
                        CHANGE_CONCATENATOR MANIFEST_STRING
                       )
                     ;
                     
change_prefix  :^(
                  CHANGE_PREFIX MANIFEST_STRING
                 )
               ;
    
/**********************************************  
 ***   Expressions                          ***
 **********************************************/

expression  :^(
               EXPRESSION equivalence_expression
              )
             | 
             ^(
               EXPRESSION quantification
              )  
            ;

equivalence_expression	:  ^( s='<->'
                              { getFTC().checkType("BOOL",getSLoc($s.token)); }
                              { getContext().addTypeRequirement(BONType.mk("BOOL")); } 
                              equivalence_expression 
                              equivalence_expression
                              { getContext().removeTypeRequirement(); } 
                            )
													| implies_expression
                        ;

//Right associative
implies_expression  :  ^( s='->'
                          { getFTC().checkType("BOOL",getSLoc($s.token)); }
                          { getContext().addTypeRequirement(BONType.mk("BOOL")); } 
                          implies_expression 
                          implies_expression
                          { getContext().removeTypeRequirement(); } 
                        )
                      | and_or_xor_expression
                    ;

and_or_xor_expression  :  ^( s=and_or_xor_op
                             { getFTC().checkType("BOOL",getSLoc($s.start.token)); }
                             { getContext().addTypeRequirement(BONType.mk("BOOL")); } 
                             and_or_xor_expression 
                             and_or_xor_expression
                             { getContext().removeTypeRequirement(); }
                           )
												 | comparison_expression
                       ;

comparison_expression  :  ^( n=normal_comparison_op
                             { getFTC().checkType("BOOL",getSLoc($n.start.token)); }
                             { getContext().addTypeRequirement(BONType.mk("VALUE")); }
                             comparison_expression 
                             comparison_expression
                             { getContext().removeTypeRequirement(); }
                           )
                         |
                          ^( member_type_comparison_op
                             comparison_expression 
                             comparison_expression
                           )
												 | add_sub_expression
                       ;

add_sub_expression  :  ^( a=add_sub_op 
                          { getFTC().checkType("VALUE",getSLoc($a.start.token)); }
                          { getContext().addTypeRequirement(BONType.mk("VALUE")); }
                          add_sub_expression 
                          add_sub_expression
                          { getContext().removeTypeRequirement(); }
                        )
											| mul_div_expression
                    ;

mul_div_expression  :   ^( m=mul_div_op
                           { getFTC().checkType("VALUE",getSLoc($m.start.token)); }
                           { getContext().addTypeRequirement(BONType.mk("VALUE")); } 
                           mul_div_expression 
                           mul_div_expression
                           { getContext().removeTypeRequirement(); }
                         )
											| mod_pow_expression
                    ;

//Right-associative
mod_pow_expression  :  ^( m=MOD_POW_OP 
                          { getFTC().checkType("VALUE",getSLoc($m.token)); }
                          { getContext().addTypeRequirement(BONType.mk("VALUE")); }
                          mod_pow_expression 
                          mod_pow_expression
                          { getContext().removeTypeRequirement(); }
                        )
                     | lowest_expression
                    ;

lowest_expression  :  constant
                    | a=add_sub_op 
                      { getFTC().checkType("VALUE",getSLoc($a.start.token)); }
                      { getContext().addTypeRequirement(BONType.mk("VALUE")); }
                      lowest_expression
                      { getContext().removeTypeRequirement(); }
										|	d=delta
										  { getFTC().checkType("VALUE",getSLoc($d.start.token)); }
										  //TODO - how to typecheck below? 
										  lowest_expression
										| old lowest_expression
										| n=not 
										  { getFTC().checkType("BOOL",getSLoc($n.start.token)); }
                      { getContext().addTypeRequirement(BONType.mk("BOOL")); }
										  lowest_expression
										  { getContext().removeTypeRequirement(); }
      					    | '(' 
      					      expression 
      					      ')' 
      					      ('.' call_chain)?
      					    | call_chain
        					 ;


/*############################################*  
 ###   Lexer...                             ###
 ##############################################
 *############################################*/


manifest_textblock  :   MANIFEST_STRING
											|	MANIFEST_TEXTBLOCK_START
												(MANIFEST_TEXTBLOCK_MIDDLE)*
												MANIFEST_TEXTBLOCK_END 
                    ;


/**********************************************  
 ***   Operatives                           ***
 **********************************************/

add_sub_op  :  '+'
             | '-'
            ;

and_or_xor_op  :  'and'
                | 'or'
                | 'xor'
               ; 

unary   :   other_unary
          | add_sub_op
        ;

other_unary  :  delta 
              | old 
              | not
             ;
             
delta : 'delta'
      ;

old : 'old'
    ;
    
not : 'not'
    ;           	 
               
binary  :   add_sub_op
          | mul_div_op
          | comparison_op
          | MOD_POW_OP
          | and_or_xor_op
          | '->' 
          | '<->'
          ;

comparison_op  :   normal_comparison_op
                 | member_type_comparison_op 
               ;
                  
normal_comparison_op :   '<' 
                       | '>'
                       | '<='
                       | '>='
                       | '='
                       | '/='
                      ;
                      
member_type_comparison_op :  'member_of'
                           | NOT_MEMBER_OF
                           | ':'
                          ; 

       
mul_div_op  :  '*'
             | '/'
             | '//'
            ;
               
//mod_pow_op  :  '\\\\' 
//             | '^'
//             ;
