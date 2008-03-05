/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */

tree grammar BONSTTreeWalker;
options {
  tokenVocab=BON;
  ASTLabelType=CommonTree;  
  superClass=AbstractBONSTWalker;
  output=template;
}


@header {
  package ie.ucd.bon.parser; 
  
  import java.util.LinkedList;
  
  import ie.ucd.bon.util.StringUtil;
}

/**********************************************  
 ##############################################
 ###   Parser...                            ###
 ##############################################
 **********************************************/

prog  :  ^( PROG bon_specification ) -> prog(p={$bon_specification.st})
        |
         ^( PROG indexing bon_specification ) -> prog(p={$bon_specification.st},i={$indexing.st})
        |
         ^( PROG PARSE_ERROR )
      ;

/**********************************************  
 ***   BON Specification                    ***
 **********************************************/

bon_specification  :  (b+=specification_element)+  -> bonSpecification(bs={$b})   
                   ;

specification_element  :    informal_chart     -> specificationElement(s={$informal_chart.st})
                          | class_dictionary   -> specificationElement(s={$class_dictionary.st})
                          | static_diagram     -> specificationElement(s={$static_diagram.st})
                          | dynamic_diagram    -> specificationElement(s={$dynamic_diagram.st})
                          | notational_tuning  -> specificationElement(s={$notational_tuning.st})
                       ;

/**********************************************  
 ***   Informal charts                      ***
 **********************************************/

informal_chart  :    system_chart    -> informalChart(i={$system_chart.st})
                   | cluster_chart   -> informalChart(i={$cluster_chart.st})
                   | class_chart     -> informalChart(i={$class_chart.st})
                   | event_chart     -> informalChart(i={$event_chart.st})
                   | scenario_chart  -> informalChart(i={$scenario_chart.st})
                   | creation_chart  -> informalChart(i={$creation_chart.st})
                ;
			
class_dictionary  :^(
                     CLASS_DICTIONARY system_name 
                     (ds += dictionary_entry)+ 
                    )
                   ->
                     classDictionary(name={$system_name.st}, dicEntries={$ds})
                   |
                   ^( CLASS_DICTIONARY PARSE_ERROR )
                  ;
			
dictionary_entry  :^(
                     DICTIONARY_ENTRY class_name
                     cluster_name description 
                    )
                   ->
                   	 dictionaryEntry(name={$class_name.st},clusterName={$cluster_name.st},desc={$description.st})
                  ;

/**********************************************/

system_chart  :^(
                 SYSTEM_CHART system_name
                 (i+=indexing)?
                 (e+=explanation)? 
                 (p+=part)? 
                 (c+=cluster_entries)? 
                )
               -> 
               	 systemChart(name={$system_name.text},indexing={$i},explanation={$e},part={$p},cluster_entries={$c})
              ;

explanation  :^(
                EXPLANATION manifest_textblock
               )
              ->
                explanation(s={$manifest_textblock.st})
              |
              ^( EXPLANATION PARSE_ERROR )
             ;

indexing  :^(
             INDEXING index_list
            ) 
           ->
             indexing(i={$index_list.st})
           |
           ^( INDEXING PARSE_ERROR )
          ;

part  :^(
         PART MANIFEST_STRING
        )
       ->
         part(s={stripRemovingSpeechMarksIfNecessary($MANIFEST_STRING.text)})
       |
        ^( PART PARSE_ERROR )
      ;

description  :^(
                DESCRIPTION manifest_textblock
               )  
              -> 
                description(s={$manifest_textblock.st})
             ;

cluster_entries  :^(
                    CLUSTER_ENTRIES (c+=cluster_entry)+ 
                   )
                  ->
                    clusterEntries(cs={$c})
                 ;
                 
cluster_entry  :^(
                  CLUSTER_ENTRY cluster_name description
                 )
                ->
                  clusterEntry(name={$cluster_name.st},desc={$description.st})
               ;
               
system_name  :^(
                SYSTEM_NAME IDENTIFIER
               )
              ->
                systemName(name={$IDENTIFIER.text})
             ;

/**********************************************/

index_list  :^(
               INDEX_LIST (i+=index_clause)+
              )
             ->
               indexList(i={$i})
            ;
            
index_clause  :^(
                 INDEX_CLAUSE IDENTIFIER index_term_list
                )
               ->
                 indexClause(id={$IDENTIFIER.text},i={$index_term_list.st})
               |
               ^( INDEX_CLAUSE PARSE_ERROR )
              ;
                
index_term_list  :^(
                    INDEX_TERM_LIST (i+=index_string)+
                   )
                  ->
                    indexTermList(i={$i})
                 ;
                 
index_string  :^(
                 INDEX_STRING MANIFEST_STRING
                )
               ->
                 indexString(s={$MANIFEST_STRING.text})
              ;

/**********************************************/

cluster_chart  :^(
                  CLUSTER_CHART cluster_name 
                  (i+=indexing)? 
                  (e+=explanation)? 
                  (p+=part)? 
                  (cl+=class_entries)? 
                  (clu+=cluster_entries)? 
                 )
                ->
                  clusterChart(name={$cluster_name.text},indexing={$i},explanation={$e},part={$p},class_entries={$cl},cluster_entries={$clu})
               ;
               
class_entries  :^(
                  CLASS_ENTRIES (c+=class_entry)+ 
                 )
                -> 
                  classEntries(cs={$c})
               ;
               
class_entry  :^(
                CLASS_ENTRY class_name description
               )
              ->
                classEntry(name={$class_name.st},desc={$description.st})
             ;
             
cluster_name  :^(
                 CLUSTER_NAME IDENTIFIER
                )
               ->
                 clusterName(name={$IDENTIFIER.text})
              ;

/**********************************************/

class_chart  :^( 
                CLASS_CHART class_name
                (i+=indexing)? 
                (e+=explanation)? 
                (p+=part)? 
                (in+=inherits)?
                (q+=queries)? 
                (com+=commands)? 
                (con+=constraints)?
               )
              ->
               classChart(name={$class_name.text},indexing={$i},explanation={$e},part={$p},inherits={$in},queries={$q},commands={$com},constraints={$con})
             ;

inherits  :  ^(INHERITS class_name_list) -> inherits(l={$class_name_list.st})
            |
             ^(INHERITS PARSE_ERROR)
          ;

queries  : ^(QUERIES query_list) -> queries(l={$query_list.st})
         ;
         
commands  : ^(COMMANDS command_list) -> commands(l={$command_list.st})
          ;

constraints  : ^(CONSTRAINTS constraint_list) -> constraints(l={$constraint_list.st})
             ;

query_list  :^(
               QUERY_LIST (l+=manifest_textblock )+
              )
             ->
               queryList(qs={$l})
            ;
            
command_list  :^(
                 COMMAND_LIST (l+=manifest_textblock )+
                )
               ->
                 commandList(cs={$l})
              ;
              
constraint_list  :^(
                    CONSTRAINT_LIST (l+=manifest_textblock )+
                   )
                  ->
                    constraintList(cs={$l})
                 ;

class_name_list  :^(
                    CLASS_NAME_LIST (c+=class_name)+
                   )
                  ->
                    classNameList(cs={$c})
                 ;
                 
class_or_cluster_name_list  :  ^( CLASS_OR_CLUSTER_NAME_LIST (classes+=class_name)* (clusters+=cluster_name)+ )
                              ->
                                classOrClusterNameList(classes={$classes},clusters={$clusters})
                             |
                               ^( CLASS_OR_CLUSTER_NAME_LIST class_name_list )
                              ->
                                asIs(x={$class_name_list.st}) 
                             ;
                             
class_name  :^(
               CLASS_NAME IDENTIFIER
              )
             ->
               className(name={$IDENTIFIER.text})
            ;

/**********************************************/

event_chart  :^(
                EVENT_CHART
                system_name 
                'incoming'
                (i+=indexing)?
                (e+=explanation)?
                (p+=part)?
                (ee+=event_entries)?
               )
              ->
                incomingEventChart(name={$system_name.st},indexing={$i},explanation={$e},part={$p},event_entries={$ee},event_id={getPT().addEventChart()})
             | 
              ^(
                EVENT_CHART
                system_name 
                'outgoing'
                (i+=indexing)?
                (e+=explanation)?
                (p+=part)?
                (ee+=event_entries)?
               )
              ->
                outgoingEventChart(name={$system_name.st},indexing={$i},explanation={$e},part={$p},event_entries={$ee},event_id={getPT().addEventChart()})
             ;
             
event_entries  :^(
                  EVENT_ENTRIES
                  (l+=event_entry)+
                 )
                ->
                  eventEntries(e={$l})
               ;
               
event_entry  :^(
                EVENT_ENTRY
                manifest_textblock
                class_or_cluster_name_list
               )
              ->
                eventEntry(text={$manifest_textblock.st},cnl={$class_or_cluster_name_list.st})
              |
              ^(EVENT_ENTRY PARSE_ERROR) 
             ;

/**********************************************/

scenario_chart  :^(
                   SCENARIO_CHART
                   system_name
                   (i+=indexing)?
                   (e+=explanation)?
                   (p+=part)?
                   (se+=scenario_entries)?
                  )
                 ->
                   scenarioChart(name={$system_name.st},indexing={$i},explanation={$e},part={$p},scenario_entries={$se},scenario_chart_id={getPT().addScenarioChart()})
                ;
                
scenario_entries  :^(
                     SCENARIO_ENTRIES
                     (l+=scenario_entry)+ 
                    ) 
                   ->    
                     scenarioEntries(e={$l})                 
                  ;
                  
scenario_entry  :^(
                   SCENARIO_ENTRY
                   MANIFEST_STRING description 
                  )
                 ->
                   scenarioEntry(s={stripRemovingSpeechMarksIfNecessary($MANIFEST_STRING.text)},d={$description.st})
                ;

/**********************************************/

creation_chart  :^(
                   CREATION_CHART
                   system_name
                   (i+=indexing)?
                   (e+=explanation)?
                   (p+=part)?
                   (ce+=creation_entries)?
                  )
                 ->
                   creationChart(name={$system_name.st},indexing={$i},explanation={$e},part={$p},creation_entries={$ce},creation_chart_id={getPT().addCreationChart()})
                ;
                
creation_entries  :^(
                     CREATION_ENTRIES
                     (l+=creation_entry)+
                    )
                   ->
                     creationEntries(l={$l})
                  ;
                  
creation_entry  :^(
                   CREATION_ENTRY
                   class_name 
                   class_or_cluster_name_list 
                  )
                 -> 
                   creationEntry(name={$class_name.st},cnl={$class_or_cluster_name_list.st})
                ;

/**********************************************  
 ***   Static Diagrams                      ***
 **********************************************/
 
static_diagram  :^(
                   STATIC_DIAGRAM
                   (p+=extended_id)? (COMMENT)?  //Comment ignored anyway (hidden channel)...? 
                   (s+=static_block)? 
                  )
                 ->
                   staticDiagram(ps={$p},sb={$s})
                ;
                
extended_id  :^(
                EXTENDED_ID IDENTIFIER
               )
              ->
                extendedID(s={$IDENTIFIER.text})
              |
              ^(
                EXTENDED_ID INTEGER
               )
              ->
                extendedID(s={$INTEGER.text})
             ;
             
static_block  :^(
                 STATIC_BLOCK (c+=static_component)+
                )
               ->
                 staticBlock(cs={$c})
              ;

//NB renamed "class" rule to "classX" as class is a reserved keyword in Java              
static_component  : ^(
                      STATIC_COMPONENT cluster
                     )
                    ->
                      staticComponent(sc={$cluster.st})
                    |
                    ^(
                      STATIC_COMPONENT classX
                     )
                    ->
                      staticComponent(sc={$classX.st})
                    |
                    ^(
                      STATIC_COMPONENT static_relation
                     )
                    ->
                      staticComponent(sc={$static_relation.st})
                  ;

/**********************************************/

cluster  :^(
            CLUSTER cluster_name
            (k+='reused')? (COMMENT)? 
            (o+=cluster_components)?
           )
          ->
            cluster(name={$cluster_name.st},key={$k},components={$o})
         ;
         
cluster_components  :^(
                       CLUSTER_COMPONENTS (o+=static_block)?
                      ) 
                     ->
                       clusterComponents(block={$o})
                    ;
                    
classX  :^(
           CLASS
           (k1+='root')? (k1+='deferred')? (k1+='effective')? 
           class_name (fg+=formal_generics)?
           (k2+='reused')? (k2+='persistent')?  (k2+='interfaced')? (COMMENT)?
           (i+=class_interface)? 
          )
         -> 
           classX(keywords1={$k1},name={$class_name.st},fgen={$fg},keywords2={$k2},interface={$i})
        ;
            
static_relation  :^(
                    STATIC_RELATION inheritance_relation
                   )
                  -> staticRelation(r={$inheritance_relation.st})
                  |
                  ^(
                    STATIC_RELATION client_relation
                   )
                  -> staticRelation(r={$client_relation.st})
                 ;

/**********************************************/

inheritance_relation  :^(
                         INHERITENCE_RELATION
                         child (m+=multiplicity)? 
                         parent (s+=semantic_label)? 
                        )
                       ->
                         inheritenceRelation(child={$child.st},mult={$m},parent={$parent.st},sem={$s})
                      ;
                    
client_relation  :^(
                    CLIENT_RELATION
                    client (ce+=client_entities)? (tm+=type_mark)? 
                    supplier (s+=semantic_label)? 
                   )
                  ->
                    clientRelation(client={$client.st},ce={$ce},tm={$tm},supplier={$supplier.st},sem={$s})
                 ;
                 
client_entities  :^(
                    CLIENT_ENTITIES
                    client_entity_expression
                   )
                  ->
                    clientEntities(cee={$client_entity_expression.st})
                 ;
                 
client_entity_expression  :^(
                             CLIENT_ENTITY_EXPRESSION client_entity_list
                            )
                           ->
                             clientEntityExpression(e={$client_entity_list.st})
                           |
                           ^(
                             CLIENT_ENTITY_EXPRESSION multiplicity
                            )
                           ->
                             clientEntityExpression(e={$multiplicity.st})
                          ;
                          
client_entity_list  :^(
                       CLIENT_ENTITY_LIST (l+=client_entity)+
                      )
                     ->
                       clientEntityList(l={$l})
                    ;
                    
client_entity  :  ^(
                    CLIENT_ENTITY prefix
                   )
                  ->
                    clientEntity(e={$prefix.st})
                  | 
                  ^(
                    CLIENT_ENTITY infix
                   )
                  ->
                    clientEntity(e={$infix.st})
                  | 
                  ^(
                    CLIENT_ENTITY supplier_indirection
                   )
                  ->
                    clientEntity(e={$supplier_indirection.st})
                  | 
                  ^(
                    CLIENT_ENTITY parent_indirection
                   )
                  ->
                    clientEntity(e={$parent_indirection.st})
               ;
               
supplier_indirection  :^(
                         SUPPLIER_INDIRECTION (ifp+=indirection_feature_part)? generic_indirection 
                        )
                       ->
                         supplierIndirection(ifp={$ifp},gi={$generic_indirection.st})
                      ;
                      
indirection_feature_part  :^(
                             INDIRECTION_FEATURE_PART feature_name
                            )
                           ->
                             indirectionFeaturePart(ifp={$feature_name.st})
                           |
                           ^(
                             INDIRECTION_FEATURE_PART indirection_feature_list
                            )
                           ->
                             indirectionFeaturePart(ifp={$indirection_feature_list.st})
                          ;	
                          
indirection_feature_list  :^(
                             INDIRECTION_FEATURE_LIST feature_name_list
                            )
                           ->
                             indirectionFeatureList(ifl={$feature_name_list.st})
                          ;
                          
parent_indirection  :^(
                       PARENT_INDIRECTION generic_indirection
                      )
                     ->
                       parentIndirection(pi={$generic_indirection.st})
                    ;

/**********************************************/

generic_indirection  :
//^(
//                        GENERIC_INDIRECTION formal_generic_name
//                       )
//                      ->
//                       genericIndirection(gi={$formal_generic_name.st})
//                      |
                      ^(
                        GENERIC_INDIRECTION indirection_element
                       )
                      ->
                        genericIndirection(gi={$indirection_element.st})
                     ;
                     
named_indirection  :^(
                      NAMED_INDIRECTION class_name indirection_list
                     ) 
                    ->
                      namedIndirection(name={$class_name.st},il={$indirection_list.st})
                    |
                    ^(NAMED_INDIRECTION PARSE_ERROR)
                   ;
                   
indirection_list  :^(
                     INDIRECTION_LIST (il+=indirection_element)+
                    )
                   ->
                     indirectionList(il={$il})
                  ;
                  
indirection_element  : ^(
                         INDIRECTION_ELEMENT t='...'
                        )
                       ->
                         indirectionElement(ie={$t.text})
                      | 
                       ^(
                         INDIRECTION_ELEMENT named_indirection
                        )
                       ->
                         indirectionElement(ie={$named_indirection.st})
                      | 
                       ^(
                       	 INDIRECTION_ELEMENT class_name
                       	)
                       ->
                         indirectionElement(ie={$class_name.st})
                     ;

                     
type_mark  :^(
              TYPE_MARK t=':'
             )
            ->
              typeMark(tm={$t.text})
            |
            ^(
              TYPE_MARK t=':{'
             )
            ->
              typeMark(tm={$t.text})
            | 
            ^(
              TYPE_MARK shared_mark
             )
            ->
              typeMark(tm={$shared_mark.st})
           ;
           
shared_mark  :^(
                SHARED_MARK multiplicity
               )
              ->
                sharedMark(mult={$multiplicity.st})
             ;

/**********************************************/

child  :^(
          CHILD static_ref
         )
        ->
          child(c={$static_ref.st})
       ;
       
parent  :^(
           PARENT static_ref
          )
         ->
           parent(p={$static_ref.st})
        ;
        
client  :^(
           CLIENT static_ref
          )
         ->
           client(c={$static_ref.st})
        ;
        
supplier  :^(
             SUPPLIER static_ref
            )
           ->
             supplier(s={$static_ref.st})
          ;
          
static_ref  :^(
               STATIC_REF (cp+=cluster_prefix)? static_component_name
              )
             ->
               staticRef(cp={$cp},name={$static_component_name.st})
            ;
            
cluster_prefix  :^(
                   CLUSTER_PREFIX (cn+=cluster_name)+
                  )
                 ->
                   clusterPrefix(cns={$cn})
                ;
  
static_component_name  :^(
                          STATIC_COMPONENT_NAME IDENTIFIER
                         )
                        ->
                          staticComponentName(name={$IDENTIFIER.text})
                       ;
                       
multiplicity  :^(
                 MULTIPLICITY INTEGER
                )
               ->
                 multiplicity(i={$INTEGER.text})
              ;
              
semantic_label  :^(
                   SEMANTIC_LABEL MANIFEST_STRING
                  )
                 ->
                   semanticLabel(l={$MANIFEST_STRING.text})
                ;

/**********************************************  
 ***   Class Interface Description          ***
 **********************************************/

class_interface  :^(
                    CLASS_INTERFACE
                    (o+=indexing)?
                    (o+=parent_class_list)?
                    features
                    (inv+=class_invariant)?
                   )
                  ->
                    classInterface(other={$o},features={$features.st},inv={$inv})
                 ;
                    
class_invariant  :^(
                    CLASS_INVARIANT assertion
                   )
                  ->
                    classInvariant(ass={$assertion.st})
                 ;
                 
parent_class_list  :^(
                      PARENT_CLASS_LIST (pcl+=class_type)+
                     )
                    ->
                      parentClassList(pcl={$pcl})
                    |
                    ^(PARENT_CLASS_LIST PARSE_ERROR )
                   ;
                   
features  :^(
             FEATURES (fc+=feature_clause)+
            )
           ->
             features(fcl={$fc})
          ;
          
/**********************************************/

feature_clause  :^(
                   FEATURE_CLAUSE
                   (se+=selective_export)? 
                   (COMMENT)? 
                   feature_specifications 
                  )
                 ->
                   featureClause(se={$se},fspecs={$feature_specifications.st})
                ;
                
feature_specifications  :^(
                           FEATURE_SPECIFICATIONS
                           (fcl+=feature_specification)+
                          ) 
                         ->
                           featureSpecifications(fcl={$fcl})
                        ;
                        
feature_specification  :^(
                          FEATURE_SPECIFICATION
                          (key+='deferred')? (key+='effective')? (key+='redefined')?
                          feature_name_list (a+=has_type)?
                          (a+=rename_clause)?
                          (COMMENT)?
                          (o+=feature_arguments)?
                          (o+=contract_clause)? 
                         )
                        ->
                          featureSpecification(key={$key},fnl={$feature_name_list.st},aft={$a},other={$o})
                       ;

has_type  : ^(HAS_TYPE type_mark type)
            ->
              hasType(tm={$type_mark.st},type={$type.st})
          ;

/**********************************************/

contract_clause  :^(
                    CONTRACT_CLAUSE contracting_conditions
                   )
                  ->
                    contractClause(cc={$contracting_conditions.st}) 
                 ;
             
contracting_conditions  :^(
                           CONTRACTING_CONDITIONS (cc+=precondition)? (cc+=postcondition)?
                          )
                         -> 
                           contractingConditions(cc={$cc})
                        ;
        
precondition  :^(
                 PRECONDITION assertion
                )
               ->
                 precondition(ass={$assertion.st})
              ;
              
postcondition  :^(
                  POSTCONDITION assertion
                 )
                ->
                  postcondition(ass={$assertion.st})
               ;

/**********************************************/

selective_export  :^(
                     SELECTIVE_EXPORT class_name_list
                    )
                   ->
                     selectiveExport(cnl={$class_name_list.st})
                  ;
                  
feature_name_list  :^(
                      FEATURE_NAME_LIST (fnl+=feature_name)+
                     )
                    ->
                      featureNameList(fnl={$fnl})
                   ;
                   
feature_name  :^(
                 FEATURE_NAME IDENTIFIER
                )
               ->
                 featureName(name={$IDENTIFIER.text})
               | 
               ^(
                 FEATURE_NAME prefix
                )
               ->
                 featureName(name={$prefix.st})
               | 
               ^(
                 FEATURE_NAME infix
                )
               ->
                 featureName(name={$infix.st})
              ;
              
rename_clause  :^(
                  RENAME_CLAUSE renaming
                 )
                ->
                  renameClause(re={$renaming.st})
               ;
               
renaming  :^(
             RENAMING class_name feature_name
            )
           ->
             renaming(cname={$class_name.st},fname={$feature_name.st})
          ;
          
feature_arguments  :^(
                      FEATURE_ARGUMENTS (fal+=feature_argument)+ 
                     )
                    ->
                      featureArguments(fal={$fal})
                   ;
                   
feature_argument  :^(
                     FEATURE_ARGUMENT (il+=identifier_list)? type
                    )
                   ->
                     featureArgument(il={$il},type={$type.st})
                  ;
                  
identifier_list  :^(
                    IDENTIFIER_LIST (il+=IDENTIFIER)+
                   )
                  ->
                    identifierList(il={$il})
                 ;
              
prefix  :^(
           PREFIX prefix_operator
          ) 
         ->
           prefix(op={$prefix_operator.st})
        ;
        
infix  :^(
          INFIX infix_operator
         )
        ->
          infix(op={$infix_operator.st})
       ;
       
prefix_operator  :^(
                    PREFIX_OPERATOR unary
                   )
                  ->
                    prefixOperator(un={$unary.st})
                 ;                

infix_operator  :^(
                   INFIX_OPERATOR binary
                  )
                 ->
                   infixOperator(bin={$binary.st})
                ;

/**********************************************/

formal_generics  :^(
                    FORMAL_GENERICS formal_generic_list
                   )
                  ->
                    formalGenerics(fgl={$formal_generic_list.st})
                 ;
                 
formal_generic_list  :^(
                        FORMAL_GENERIC_LIST (fgl+=formal_generic)+
                       )
                      ->
                        formalGenericList(fgl={$fgl})
                     ;
                     
formal_generic  :^(
                   FORMAL_GENERIC formal_generic_name (t+=class_type)?
                  )
                 ->
                   formalGeneric(name={$formal_generic_name.st},type={$t})
                ;
                
formal_generic_name  :^(
                        FORMAL_GENERIC_NAME IDENTIFIER
                       )
                      ->
                        formalGenericName(name={$IDENTIFIER.text})
                     ;
                     
class_type  :^(
               CLASS_TYPE class_name (ag+=actual_generics)? 
              )
             ->
               classType(name={$class_name.st},gen={$ag})
            ;
            
actual_generics  :^(
                    ACTUAL_GENERICS type_list
                   ) 
                  ->
                    actualGenerics(tl={$type_list.st})
                 ;
                 
type_list  :^(
              TYPE_LIST (tl+=type)+
             )
            ->
              typeList(tl={$tl})
           ;

type  :^(
         TYPE IDENTIFIER (ag+=actual_generics)?
        )
       ->
         type(id={$IDENTIFIER.text},gen={$ag})
      ;

/**********************************************  
 ***   Formal Assertions                    ***
 **********************************************/

assertion  :^(
              ASSERTION (acl+=assertion_clause)+
             )
            ->
              assertion(acl={$acl})
           ;
           
assertion_clause  :^(
                     ASSERTION_CLAUSE boolean_expression
                    )
                   ->
                     assertionClause(exp={$boolean_expression.st})
                  ;
                 
boolean_expression  :^(
                       BOOLEAN_EXPRESSION expression
                      )
                     ->
                       booleanExpression(exp={$expression.st})
                    ;
            
quantification  :^(
                   QUANTIFICATION
                   quantifier  
                   range_expression 
                   (restr+=restriction)? 
                   proposition 
                  )
                 ->
                   quantification(q={$quantifier.st},re={$range_expression.st},restr={$restr},prop={$proposition.st})
                ;
                
quantifier  :^(
               QUANTIFIER t='for_all'
              )
             ->
               quantifier(t={$t.text})
             |
             ^(
               QUANTIFIER t='exists'
              )
             ->
               quantifier(t={$t.text})
            ;
            
range_expression  :^(
                     RANGE_EXPRESSION (vrl+=variable_range)+
                    )
                   ->
                     rangeExpression(vrl={$vrl})
                  ;
                  
restriction  :^(
                RESTRICTION boolean_expression
               )
              -> 
                restriction(exp={$boolean_expression.st})
             ;
             
proposition  :^(
                PROPOSITION boolean_expression
               )
              ->
                poposition(exp={$boolean_expression.st})
             ;
             
variable_range  :^(
                   VARIABLE_RANGE member_range
                  )
                 ->
                   variableRange(r={$member_range.st})
                 |
                 ^(
                   VARIABLE_RANGE type_range
                  )
                 ->
                   variableRange(r={$type_range.st})
                ;
                
member_range  :^(
                 MEMBER_RANGE identifier_list expression
                )
               ->
                 memberRange(il={$identifier_list.st},exp={$expression.st})
              ;
              
type_range  :^(
               TYPE_RANGE identifier_list type
              )
             ->
               typeRange(il={$identifier_list.st},type={$type.st})
            ;

/**********************************************/

//call  :^(
//         CALL
//         (exp+=expression)? call_chain
//        )
//       ->
//         call(exp={$exp},cc={$call_chain.st})
//      ;
                         
call_chain  :^(
               CALL_CHAIN (ucl+=unqualified_call)+
              )
             ->
               callChain(ucl={$ucl})
            ;
            
unqualified_call  :^(
                     UNQUALIFIED_CALL IDENTIFIER (aa+=actual_arguments)?
                    )
                   -> 
                     unqualifiedCall(id={$IDENTIFIER.text},aa={$aa})
                  ;
                  
actual_arguments  : ACTUAL_ARGUMENTS 
                   ->
                     actualArguments()
                   |
                    ^(
                      ACTUAL_ARGUMENTS expression_list
                     )
                   ->
                     actualArguments(el={$expression_list.st})
                  ;
              
expression_list  :^(
                    EXPRESSION_LIST (el+=expression)+
                   )
                  ->
                    expressionList(el={$el})
                 ;

/**********************************************/
                
enumerated_set  :^(
                   ENUMERATED_SET enumeration_list
                  )
                 ->
                   enumeratedSet(el={$enumeration_list.st})
                ;
                
enumeration_list  :^(
                     ENUMERATION_LIST (el+=enumeration_element)+
                    )
                   ->
                     enumerationList(el={$el})
                  ;
         
enumeration_element  :^(
                        ENUMERATION_ELEMENT expression
                       )
                      ->
                        enumeration_element(ee={$expression.st})
                      | 
                      ^(
                        ENUMERATION_ELEMENT interval
                       )
                      ->
                        enumeration_element(ee={$interval.st})
                     ;
                     
interval  :^(
             INTERVAL integer_interval
            ) 
           ->
             interval(i={$integer_interval.st})
           | 
           ^(
             INTERVAL character_interval
            ) 
           ->
             interval(i={$character_interval.st})
          ;
          
integer_interval  :^(
                     INTEGER_INTERVAL i1=integer_constant i2=integer_constant
                    )
                   ->
                     integerInterval(i1={$i1.text},i2={$i2.text})
                  ;
                  
character_interval  :^(
                       CHARACTER_INTERVAL c1=CHARACTER_CONSTANT c2=CHARACTER_CONSTANT
                      )
                     -> 
                       character_interval(c1={$c1.text},c2={$c2.text})
                    ;
/**********************************************/

constant  :^(
             CONSTANT manifest_constant
            )
           ->
             constant(c={$manifest_constant.st})
           |
           ^(
             CONSTANT t='Current'
            )
           ->
             constant(c={$t.text})
           |
           ^(
             CONSTANT t='Void'
            )
           ->
             constant(c={$t.text})
          ;

manifest_constant  : ^(
                       MANIFEST_CONSTANT boolean_constant
                      )
                     ->
                       manifest_constant(mc={$boolean_constant.text})
                     | 
                     ^(
                       MANIFEST_CONSTANT CHARACTER_CONSTANT
                      )
                     ->
                       manifest_constant(mc={$CHARACTER_CONSTANT.text})
                     | 
                     ^(
                       MANIFEST_CONSTANT integer_constant
                      )
                     ->
                       manifest_constant(mc={$integer_constant.st})
                     | 
                     ^(
                       MANIFEST_CONSTANT real_constant
                      )
                     ->
                       manifest_constant(mc={$real_constant.st})
                     | 
                     ^(
                       MANIFEST_CONSTANT MANIFEST_STRING
                      )
                     ->
                       manifest_constant(mc={$MANIFEST_STRING.text})
                     | 
                     ^(
                     	 MANIFEST_CONSTANT enumerated_set
                     	)
                     ->
                       manifest_constant(mc={$enumerated_set.st})
                   ;
                   
sign  :^(
         SIGN add_sub_op
        )
       ->
         sign(s={$add_sub_op.st})
      ;
      
boolean_constant  :^(
                     BOOLEAN_CONSTANT t='true'
                    )
                   ->
                     booleanConstant(bc={$t.text})
                   |
                   ^(
                     BOOLEAN_CONSTANT t='false'
                    )
                   ->
                     booleanConstant(bc={$t.text})
                  ;
                    
integer_constant  :^(
                     INTEGER_CONSTANT
                     (s+=sign)? INTEGER
                    )
                   ->
                     integerConstant(sign={$s},i={$INTEGER.text})
                  ;
                  
real_constant  :^(
                  REAL_CONSTANT
                  (s+=sign)? REAL
                 )
                ->
                  realConstant(sign={$s},r={$REAL.text})
               ;

/**********************************************  
 ***   Dynamic Diagrams                     ***
 **********************************************/

dynamic_diagram  :^(
                    DYNAMIC_DIAGRAM
                    (exid+=extended_id)? (COMMENT)?
                    (db+=dynamic_block)?
                   )
                  ->
                    dynamicDiagram(exid={$exid},dynblock={$db})
                 ;
                 
dynamic_block  :^(
                  DYNAMIC_BLOCK
                  (dcl+=dynamic_component)+
                 )
                ->
                  dynamicBlock(dcl={$dcl})
               ;
               
dynamic_component  : ^(
                       DYNAMIC_COMPONENT scenario_description
                      )
                     ->
                       dynamicComponent(dc={$scenario_description.st})
                     |
                     ^(
                       DYNAMIC_COMPONENT object_group
                      )
                     ->
                       dynamicComponent(dc={$object_group.st})
                     |
                     ^(
                       DYNAMIC_COMPONENT object_stack
                      )
                     ->
                       dynamicComponent(dc={$object_stack.st})
                     | 
                     ^(
                       DYNAMIC_COMPONENT object
                      )
                     ->
                       dynamicComponent(dc={$object.st})
                     | 
                     ^(
                       DYNAMIC_COMPONENT message_relation
                      )
                     ->
                       dynamicComponent(dc={$message_relation.st})
                   ; 

/**********************************************/

scenario_description  :^(
                         SCENARIO_DESCRIPTION 
                         scenario_name (COMMENT)?
                         labelled_actions 
                        )
                       ->
                         scenarioDescription(name={$scenario_name.st},la={$labelled_actions.st})
                      ;
                      
labelled_actions  :^(
                     LABELLED_ACTIONS (lal+=labelled_action)+
                    )
                   ->
                     labelledActions(lal={$lal})
                  ;
                  
labelled_action  :^(
                    LABELLED_ACTION action_label action_description
                   )
                  ->
                    labelledAction(l={$action_label.st},ad={$action_description.st})
                 ;
                 
action_label  :^(
                 ACTION_LABEL MANIFEST_STRING
                )
               ->
                 actionLabel(al={$MANIFEST_STRING.text})
              ;
              
action_description  :^(
                       ACTION_DESCRIPTION manifest_textblock
                      )
                     ->
                       actionDescription(ad={$manifest_textblock.st})
                    ;
                    
scenario_name  :^(
                  SCENARIO_NAME manifest_textblock
                 )
                ->
                  scenarioName(name={$manifest_textblock.st})
               ;

/**********************************************/

object_group  :^(
                 OBJECT_GROUP (n+='nameless')? group_name (COMMENT)? (gc+=group_components)? 
                )
               ->
                 objectGroup(n={$n},name={$group_name.st},gc={$gc})
              ;
              
group_components  :^(
                     GROUP_COMPONENTS dynamic_block
                    ) 
                   ->
                     groupComponents(db={$dynamic_block.st})
                  ;
                  
object_stack  :^(
                 OBJECT_STACK object_name (COMMENT)?
                )
               ->
                 objectStack(name={$object_name.st})
              ;
              
object  :^(
           OBJECT object_name (COMMENT)?
          )
         ->
           object(name={$object_name.st})
        ;

/**********************************************/

message_relation  :^(
                     MESSAGE_RELATION caller receiver (ml+=message_label)?
                    )
                   ->
                     messageRelation(caller={$caller.st},receiver={$receiver.st},label={$ml})
                  ;
                  
caller  :^(
           RECEIVER dynamic_ref
          )
         ->
           caller(c={$dynamic_ref.st})
        ;
        
receiver  :^(
             RECEIVER dynamic_ref
            )
           ->
             receiver(r={$dynamic_ref.st})
          ;
          
dynamic_ref  :^(
                DYNAMIC_REF (eil+=extended_id)+
               )
              ->
                dynamicRef(eil={$eil})
             ;

dynamic_component_name  :^(
                           DYNAMIC_COMPONENT_NAME IDENTIFIER (ei+=extended_id)?
                          )
                         ->
                           dynamicComponentName(a={$IDENTIFIER.text},b={$ei})
                         |
                         ^(
                           DYNAMIC_COMPONENT_NAME INTEGER
                          )
                         ->
                           dynamicComponentName(a={$INTEGER.text})
                        ;

object_name  :^(
                OBJECT_NAME class_name (ei+=extended_id)?
               )
              ->
                objectName(a={$class_name.st},b={$ei})
             ;
             
group_name  :^(
               GROUP_NAME extended_id
              ) 
             ->
               groupName(name={$extended_id.st})
            ;
            
message_label  :^(
                  MESSAGE_LABEL MANIFEST_STRING
                 )
                ->
                  messageLabel(l={$MANIFEST_STRING.text})
               ;

/**********************************************  
 ***   Notational Tuning                    ***
 **********************************************/
notational_tuning  :^(
                      NOTATIONAL_TUNING change_string_marks
                     )
                    ->
                      notationalTuning(nt={$change_string_marks.st})
                    |
                    ^(
                      NOTATIONAL_TUNING change_concatenator
                     )
                    ->
                      notationalTuning(nt={$change_concatenator.st})
                    | 
                    ^(
                      NOTATIONAL_TUNING change_prefix
                     )
                    ->
                      notationalTuning(nt={$change_prefix.st})
                   ;
                   
change_string_marks  :^(
                        CHANGE_STRING_MARKS m1=MANIFEST_STRING m2=MANIFEST_STRING
                       )
                      ->
                        changeStringMarks(m1={$m1.text},m2={$m2.text})
                     ;
                     
change_concatenator  :^(
                        CHANGE_CONCATENATOR MANIFEST_STRING
                       )
                      ->
                        changeConcatenator(cc={$MANIFEST_STRING.text})
                     ;
                     
change_prefix  :^(
                  CHANGE_PREFIX MANIFEST_STRING
                 )
                ->
                  changePrefix(cp={$MANIFEST_STRING.text})
               ;
    
/**********************************************  
 ***   Expressions                          ***
 **********************************************/

expression  :^(
               EXPRESSION equivalence_expression
              )
             ->
               expressionAsIs(exp={$equivalence_expression.st})
             | 
             ^(
               EXPRESSION quantification
              )
             ->
               expressionAsIs(exp={$quantification.st})  
            ;

equivalence_expression	:  ^('<->' e1=equivalence_expression e2=equivalence_expression) -> equivalence_expression(e1={$e1.st},e2={$e2.st})
													| implies_expression -> expressionAsIs(exp={$implies_expression.st})
                        ;

//Right associative
implies_expression  :  ^('->' e1=implies_expression e2=implies_expression) -> impliesExpression(e1={$e1.st},e2={$e2.st})
                      | and_or_xor_expression -> expressionAsIs(exp={$and_or_xor_expression.st})
                    ;

and_or_xor_expression  :  ^(and_or_xor_op e1=and_or_xor_expression e2=and_or_xor_expression) -> andOrXorExpression(op={$and_or_xor_op.st},e1={$e1.st},e2={$e2.st})
												 | comparison_expression -> expressionAsIs(exp={$comparison_expression.st})
                       ;

comparison_expression  :  ^(comparison_op  e1=comparison_expression e2=comparison_expression) -> comparisonExpression(op={$comparison_op.st},e1={$e1.st},e2={$e2.st})
												 | add_sub_expression -> expressionAsIs(exp={$add_sub_expression.st})
                       ;

add_sub_expression  :  ^(add_sub_op e1=add_sub_expression e2=add_sub_expression) -> addSubExpression(op={$add_sub_op.st},e1={$e1.st},e2={$e2.st})
											| mul_div_expression -> expressionAsIs(exp={$mul_div_expression.st})
                    ;

mul_div_expression  :  ^(mul_div_op e1=mul_div_expression e2=mul_div_expression) -> mulDivExpression(op={$mul_div_op.st},e1={$e1.st},e2={$e2.st})
											| mod_pow_expression -> expressionAsIs(exp={$mod_pow_expression.st})
                    ;

//Right-associative
mod_pow_expression  :  ^(mod_pow_op e1=mod_pow_expression e2=mod_pow_expression) -> mod_pow_expression(op={$mod_pow_op.st},e1={$e1.st},e2={$e2.st})
                     | lowest_expression -> expressionAsIs(exp={$lowest_expression.st})
                    ;

lowest_expression  :  constant -> expressionAsIs(exp={$constant.st})
										|	unary t=lowest_expression -> unaryExpression(unary={$unary.st},exp={$t.st})
      					    | '(' expression ')' ('.' cc+=call_chain)? -> parenthesisExpression(exp={$expression.st},cc={$cc})
      					    | call_chain -> expressionAsIs(exp={$call_chain.st})
        					 ;


/*############################################*  
 ###   Lexer...                             ###
 ##############################################
 *############################################*/


manifest_textblock  :   MANIFEST_STRING -> manifestTextBlock(s={stripIfNecessary($MANIFEST_STRING.text)})
											|	ms=MANIFEST_TEXTBLOCK_START
												{ String t = $ms.text; }  
												(m=MANIFEST_TEXTBLOCK_MIDDLE { t+=$m.text; } )*
												me=MANIFEST_TEXTBLOCK_END 
												{ t+=$me.text; }
											->
											  manifestTextBlock(s={stripIfNecessary(t)})
                    ;


/**********************************************  
 ***   Operatives                           ***
 **********************************************/

add_sub_op  :  '+' -> plus()
             | '-' -> minus()
            ;

and_or_xor_op  :  'and' -> and()
                | 'or'  -> or()
                | 'xor' -> xor()
               ; 

unary   :   other_unary -> unary(u={$other_unary.st})
          | add_sub_op -> unary(ou={$add_sub_op.st})
        ;

other_unary  :  'delta' -> delta()
           		| 'old'   -> old()
           	 	| 'not'   -> not()
           	 ;
               
binary  :   add_sub_op     -> asIs(x={$add_sub_op.st})
          | mul_div_op     -> asIs(x={$mul_div_op.st})
          | comparison_op  -> asIs(x={$comparison_op.st})
          | mod_pow_op     -> asIs(x={$mod_pow_op.st})
          | and_or_xor_op  -> asIs(x={$and_or_xor_op.st})
          | '->'           -> implies() 
          | '<->'          -> equivalent()
          ;

comparison_op  :    '<'              -> lessThan() 
                  | '>'              -> greaterThan()
                  | '<='             -> lessThanOrEqualTo()
                  | '>='             -> greaterThanOrEqualTo()
                  | '='              -> equals()
                  | '/='             -> notEquals()
                  | 'member_of'      -> memberOf()
                  | NOT_MEMBER_OF    -> notMemberOf()
                  | ':'              -> typeChar()
                  ;

       
mul_div_op  :  '*'  -> multiply()
             | '/'  -> divide()
             | '//' -> integerDivide()
            ;

mod_pow_op : MOD_POW_OP -> asIs(x={$MOD_POW_OP.text}) ;               
//mod_pow_op  :  '\\\\' -> modulo() 
//             | '^' -> power()
//             ;
