/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */

grammar BON;
options {
  output=AST;
  ASTLabelType=CommonTree;
  superClass=AbstractBONParser;
}
tokens {
  PROG;
  CLASS_CHART;
  CLASS_DICTIONARY;
  DICTIONARY_ENTRY;
  SYSTEM_CHART;
  EXPLANATION;
  INDEXING;
  PART;
  DESCRIPTION;
  CLUSTER_ENTRIES;
  CLUSTER_ENTRY;
  SYSTEM_NAME;
  INDEX_LIST;
  INDEX_CLAUSE;
  INDEX_TERM_LIST;
  INDEX_STRING;
  CLUSTER_CHART;
  CLASS_ENTRIES;
  CLASS_ENTRY;
  CLUSTER_NAME;
  QUERY_LIST;
  COMMAND_LIST;
  CONSTRAINT_LIST;
  CLASS_NAME_LIST;
  CLASS_OR_CLUSTER_NAME_LIST;
  CLASS_NAME;
  EVENT_CHART;
  EVENT_ENTRIES;
  EVENT_ENTRY;
  SCENARIO_CHART;
  SCENARIO_ENTRIES;
  SCENARIO_ENTRY;
  CREATION_CHART;
  CREATION_ENTRIES;
  CREATION_ENTRY;
  STATIC_DIAGRAM;
  EXTENDED_ID;
  STATIC_BLOCK;
  STATIC_COMPONENT;
  CLUSTER;
  CLUSTER_COMPONENTS;
  CLASS;
  STATIC_RELATION;
  INHERITANCE_RELATION;
  CLIENT_RELATION;
  CLIENT_ENTITIES;
  INDIRECTION_ELEMENT;
  CLIENT_ENTITY_EXPRESSION;
  CLIENT_ENTITY_LIST;
  CLIENT_ENTITY;
  SUPPLIER_INDIRECTION;
  INDIRECTION_FEATURE_PART;
  INDIRECTION_FEATURE_LIST;
  PARENT_INDIRECTION;
  GENERIC_INDIRECTION;
  NAMED_INDIRECTION;
  INDIRECTION_LIST;
  TYPE_MARK;
  SHARED_MARK;
  CHILD;
  PARENT;
  CLIENT;
  SUPPLIER;
  STATIC_REF;
  CLUSTER_PREFIX;
  STATIC_COMPONENT_NAME;
  MULTIPLICITY;
  SEMANTIC_LABEL;
  CLASS_INTERFACE;
  CLASS_INVARIANT;
  PARENT_CLASS_LIST;
  FEATURES;
  FEATURE_CLAUSE;
  FEATURE_SPECIFICATIONS;
  FEATURE_SPECIFICATION;
  CONTRACT_CLAUSE;
  CONTRACTING_CONDITIONS;
  PRECONDITION;
  POSTCONDITION;
  SELECTIVE_EXPORT;
  FEATURE_NAME_LIST;
  FEATURE_NAME;
  RENAME_CLAUSE;
  RENAMING;
  FEATURE_ARGUMENTS;
  FEATURE_ARGUMENT;
  IDENTIFIER_LIST;
  PREFIX;
  INFIX;
  PREFIX_OPERATOR;
  INFIX_OPERATOR;
  FORMAL_GENERICS;
  FORMAL_GENERIC_LIST;
  FORMAL_GENERIC;
  FORMAL_GENERIC_NAME;
  CLASS_TYPE;
  ACTUAL_GENERICS;
  TYPE_LIST;
  TYPE;
  ASSERTION;
  ASSERTION_CLAUSE;
  BOOLEAN_EXPRESSION;
  QUANTIFICATION;
  QUANTIFIER;
  RANGE_EXPRESSION;
  RESTRICTION;
  PROPOSITION;
  VARIABLE_RANGE;
  MEMBER_RANGE;
  TYPE_RANGE;
  CALL;
  CALL_CHAIN;
  UNQUALIFIED_CALL;
  ACTUAL_ARGUMENTS;
  EXPRESSION_LIST;
  ENUMERATED_SET;
  ENUMERATION_LIST;
  ENUMERATION_ELEMENT;
  INTERVAL;
  INTEGER_INTERVAL;
  CHARACTER_INTERVAL;
  CONSTANT;
  MANIFEST_CONSTANT;
  SIGN;
  BOOLEAN_CONSTANT;
  INTEGER_CONSTANT;
  REAL_CONSTANT;
  DYNAMIC_DIAGRAM;
  DYNAMIC_BLOCK;
  DYNAMIC_COMPONENT;
  SCENARIO_DESCRIPTION;
  LABELLED_ACTIONS;
  LABELLED_ACTION;
  ACTION_LABEL;
  ACTION_DESCRIPTION;
  SCENARIO_NAME;
  OBJECT_GROUP;
  GROUP_COMPONENTS;
  OBJECT_STACK;
  OBJECT;
  MESSAGE_RELATION;
  RECEIVER;
  DYNAMIC_REF;
  DYNAMIC_COMPONENT_NAME;
  OBJECT_NAME;
  GROUP_NAME;
  MESSAGE_LABEL;
  NOTATIONAL_TUNING;
  CHANGE_STRING_MARKS;
  CHANGE_CONCATENATOR;
  MANFIEST_STRING;
  CHANGE_PREFIX;
  LOWEST;
  SET_EXPRESSION;
  EXPRESSION;
  NOT_MEMBER_OF;
//  CHARACTER_CONSTANT;
  INHERITS;
  QUERIES;
  COMMANDS;
  CONSTRAINTS;
  HAS_TYPE;
  PARSE_ERROR;
  CLUSTER_NAME_LIST;
}

@header {
  package ie.ucd.bon.parser; 
  
  import ie.ucd.bon.parser.errors.MissingElementParseError;
  import java.util.LinkedList;
  import ie.ucd.bon.ast.*;
  import ie.ucd.bon.typechecker.informal.*;
  import ie.ucd.bon.typechecker.*;
}

@lexer::header {
/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser;
}

@members {
//Currently nothing, everything in BONAbstractParser	
}

/**********************************************  
 ##############################################
 ###   Parser...                            ###
 ##############################################
 **********************************************/

prog returns [BONSourceFile bonSource] :
         bs=bon_specification EOF
         { $bonSource = BonsourceFile.mk($bs.spec_els, null, getSLoc($bs.start, $bs.stop)); }
       ->
         ^( PROG bon_specification )
       |
         indexing bon_specification EOF
         { $bonSource = BonsourceFile.mk($bs.spec_els, $indexing.indexing, getSLoc($bs.start, $bs.stop)); }
       ->
         ^( PROG indexing bon_specification )
       |
         indexing? e=EOF 
         { addParseProblem(new MissingElementParseError(getSourceLocation($e), "at least one specification entry", "in source file", true)); }
       ->
         ^( PROG PARSE_ERROR )
;

/**********************************************  
 ***   BON Specification                    ***
 **********************************************/

bon_specification returns [List<SpecificationElement> spec_els] :
  { $spec_els = new LinkedList<SpecificationElement>(); }
  ( se=specification_element
    { $spec_els.add($se.se); }
  )+ 
;

specification_element returns [SpecificationElement se] :
    ic=informal_chart
    { $se = $ic.ic; }
  | cd=class_dictionary
    { $se = $cd.cd; }
  | sd=static_diagram
    { $se = $sd.sd; }
  | dd=dynamic_diagram
    { $se = $dd.dd; }
  | nt=notational_tuning
    { $se = $nt.nt; } 
;

/**********************************************  
 ***   Informal charts                      ***
 **********************************************/

informal_chart returns [InformalChart ic] :
    system_chart
    { $ic = $system_chart.sc; }
  | cluster_chart
    { $ic = $cluster_chart.cc; }
  | class_chart
    { $ic = $class_chart.cc; }
  | event_chart
    { $ic = $event_chart.ec; }
  | scenario_chart
    { $ic = $scenario_chart.sc; }
  | creation_chart 
    { $ic = $creation_chart.cc; }
;
			
class_dictionary returns [ClassDictionary cd] :  
  d='dictionary' system_name 
  (indexing)?
  (explanation)? 
  (part)? 
  (dictionary_entry)+ 
  'end'
                   ->
                   ^(
                     CLASS_DICTIONARY[$d] system_name 
                     (indexing)?
                     (explanation)? 
                     (part)? 
                     (dictionary_entry)+ 
                    )
                   |
                     d='dictionary' system_name 
                     (indexing)?
                     (explanation)? 
                     (part)? 
                     'end'
                     { addParseProblem(new MissingElementParseError(getSourceLocation($d), "dictionary entries", "in system dictionary", false)); }
                   -> 
                   ^( CLASS_DICTIONARY  PARSE_ERROR )
                  ;
			
dictionary_entry returns [DictionaryEntry de] :  
  c='class' class_name 
  'cluster' cluster_name_list 
  description 
  { $de = DictionaryEntry.mk($class_name.text, $cluster_name_list.clusters, $description.text, getSLoc($c.start, $description.stop)); }
                   ->
                   ^(
                     DICTIONARY_ENTRY[$c] class_name
                     cluster_name_list description 
                    )
                  ;

/**********************************************/

system_chart returns [SystemChart sc] :
  s='system_chart' system_name 
  { ClusterChartDefinition system = new ClusterChartDefinition($system_name.text, getSLoc($s, $system_name.stop), true);
  getTI().informal().setSystem(system);
  getContext().enterSystemChart(system); }
  (indexing)?
  (explanation)? 
  (part)? 
  (cluster_entries)? 
  'end'
  { getContext().leaveSystemChart(); }
               ->
               ^(
                 SYSTEM_CHART[$s] system_name
                 (indexing)?
                 (explanation)? 
                 (part)? 
                 (cluster_entries)? 
                )
              ;

explanation returns [String explanation] :
  e='explanation' manifest_textblock
  { getITI().setExplanation($manifest_textblock.text); }
  { $explanation = $e.text; }
              ->
              ^(
                EXPLANATION[$e] manifest_textblock
               )
              |
               e='explanation' { addParseProblem(new MissingElementParseError(getSourceLocation($e), "explanation text", "after 'explanation'", false)); }
              ->
              ^( EXPLANATION[$e] PARSE_ERROR )
             ;

indexing returns [Indexing indexing] :  
           i='indexing' index_list
           { $indexing = Indexing.mk($index_list.list); getTI().indexing($indexing); }
           ->
           ^(
             INDEXING[$i] index_list
            ) 
           |
             i='indexing' { addParseProblem(new MissingElementParseError(getSourceLocation($i), "indexing entries", "after 'indexing'", false)); }
           ->
           ^( INDEXING[$i] PARSE_ERROR )
          ;

part returns [String part] :
    p='part' m=MANIFEST_STRING
    { $part = $m.text; }
       ->
       ^(
         PART[$p] MANIFEST_STRING
        )
  |
    p='part' 
    { addParseProblem(new MissingElementParseError(getSourceLocation($p), "part text", "after 'part'", false)); }
    { $part = ""; }
       ->
         ^( PART PARSE_ERROR ) 
      ;

description returns [String description] :
  d='description' m=manifest_textblock 
  { getTI().setDescription($m.text); }
  { $description = $m.text; }
  
              ->
              ^(
                DESCRIPTION[$d] manifest_textblock
               )  
             ;

cluster_entries returns [List<ClusterEntry> entries] :
  { $entries = new LinkedList<ClusterEntry>(); }
  (cluster_entry { $entries.add($cluster_entry.ce); } )+
   
                  ->
                  ^(
                    CLUSTER_ENTRIES (cluster_entry)+ 
                   )
                 ;
                 
cluster_entry returns [ClusterEntry ce] :
  c='cluster' cluster_name description
  { getTI().informal().addClusterEntry($cluster_name.text); }
  { $ce = ClusterEntry.mk($cluster_name.text, $description.text, getSLoc($c.start, $description.stop)); } 
                ->
                ^(
                  CLUSTER_ENTRY[$c] cluster_name description
                 )
               ;
               
system_name returns [String name] :
  i=IDENTIFIER
  { $name = $i.text; } 
              ->
              ^(
                SYSTEM_NAME[$i] IDENTIFIER
               )
             ;

/**********************************************/

index_list returns [List<IndexClause> list] :  
               { $list = new LinkedList<IndexClause>(); }
               i1=index_clause 
               { $list.add($i1.clause); }
               (  (';' i2=index_clause)
                  { $list.add($i2.clause); }
                | i=index_clause { addParseProblem(new MissingElementParseError(getSourceLocation($i.start), "semi-colon", "before additional index clause", false)); }
                  { $list.add($i.clause); }
               )* 
               ';'? //Final semi-colon optional
             -> 
             ^(
               INDEX_LIST[$i1.start] index_clause+
              )
            ;
            
index_clause returns [IndexClause clause] :  
               i=IDENTIFIER ':' index_term_list 
               { $clause = IndexClause.mk($i.text, $index_term_list.strings, getSLoc($i.start, $index_term_list.stop)); }
               ->
               ^(
                 INDEX_CLAUSE[$i] IDENTIFIER index_term_list
                )
               |
                 i=IDENTIFIER ':' { addParseProblem(new MissingElementParseError(getSourceLocation($i), "index term(s)", "in index clause", true)); }
               ->
                 ^(INDEX_CLAUSE PARSE_ERROR)
              ;
                
index_term_list returns [List<String> strings] :
                  { $strings = new LinkedList<String>(); }
                  i1=index_string 
                  { $strings.add($i1.text); }
                  (',' i=index_string
                  { $strings.add($i.text); }
                  )* 
                  -> 
                  ^(
                    INDEX_TERM_LIST[$i1.start] index_string+
                   )
                 ;
                 
index_string returns [String s] :
  m=MANIFEST_STRING
  { $s = $m.text; }    
               ->
               ^(
                 INDEX_STRING[$m] MANIFEST_STRING
                )
              ;

/**********************************************/

cluster_chart returns [ClusterChart cc] :
  c='cluster_chart' cluster_name 
  { ClusterChartDefinition cluster = new ClusterChartDefinition($cluster_name.text, getSLoc($c, $cluster_name.stop), false);
  getTI().informal().addCluster(cluster);
  getContext().enterClusterChart(cluster); }
  (indexing)? 
  (explanation)? 
  (part)? 
  (class_entries)? 
  (cluster_entries)? 
  'end'
  { getContext().leaveClusterChart(); }
                ->
                ^(
                  CLUSTER_CHART[$c] cluster_name 
                  (indexing)? 
                  (explanation)? 
                  (part)? 
                  (class_entries)? 
                  (cluster_entries)? 
                 )
               ;
               
class_entries returns [List<ClassEntry> classes] :
  { $classes = new LinkedList<ClassEntry>(); }
  (class_entry { $classes.add($class_entry.entry); } )+ 
                ->
                ^(
                  CLASS_ENTRIES (class_entry)+ 
                 )
               ;
               
class_entry returns [ClassEntry entry] :
  c='class' class_name { getContext().enterClassEntry($class_name.text); }
  description
  { getTI().informal().addClassEntry($class_name.text); getContext().leaveClassEntry(); }
  { $entry = ClassEntry.mk($class_name.text, $description.text, getSLoc($c.start, $description.stop)); }
              ->
              ^(
                CLASS_ENTRY[$c] class_name description
               )
             ;
             
cluster_name  :  i=IDENTIFIER 
               ->
               ^(
                 CLUSTER_NAME[$i] IDENTIFIER
                )
              ;

/**********************************************/

class_chart returns [ClassChart cc] :
  c='class_chart' class_name 
  { ClassChartDefinition classX = new ClassChartDefinition($class_name.text, getSLoc($c, $class_name.stop));
  getTI().informal().addClass(classX);
  getContext().enterClassChart(classX); }
  (indexing)? 
  (explanation)? 
  (part)? 
  (inherits)?
  (queries)? 
  (commands)? 
  (constraints)? 
  'end'
  { getContext().leaveClassChart(); }
              ->
              ^( 
                CLASS_CHART[$c] class_name
                (indexing)? 
                (explanation)? 
                (part)? 
                (inherits)?
                (queries)? 
                (commands)? 
                (constraints)?
               )
             ;
             
inherits returns [List<String> inherits] :
  i='inherit' { getContext().enterInheritsClause(); } 
  class_name_list
  { getContext().leaveInheritsClause(); }
  { $inherits = $class_name_list.list; }
          -> ^(INHERITS[$i] class_name_list)
           | i='inherit' { addParseProblem(new MissingElementParseError(getSourceLocation($i), "class name(s)", "in inherits clause", true)); }
          -> ^( INHERITS PARSE_ERROR )
            
          ;

queries returns [List<String> queries] :
  q='query' query_list  
  { $queries = $query_list.queries; }
 -> ^(QUERIES[$q] query_list)
         ;
         
commands returns [List<String> commands] :
  c='command' command_list
  { $commands = $command_list.commands; }
  -> ^(COMMANDS[$c] command_list)
          ;

constraints returns [List<String> constraints] :
  c='constraint' constraint_list
  { $constraints = $constraint_list.string; }
  -> ^(CONSTRAINTS[$c] constraint_list)
             ;


query_list returns [List<String> queries] :
  { $queries = new LinkedList<String>(); }
  m1=manifest_textblock 
  { getTI().informal().addQuery($m1.text); }
  { $queries.add($m1.text); }
  (  (',' m=manifest_textblock 
      { getTI().informal().addQuery($m.text); }
      { $queries.add($m.text); } 
     )      
   | m=manifest_textblock 
     { getTI().informal().addQuery($m.text); addParseProblem(new MissingElementParseError(getSourceLocation($m.start), "comma", "before additional query item", false)); }
     { $queries.add($m.text); } 
  )* 
  ','?             
             -> 
             ^(
               QUERY_LIST[$m1.start] manifest_textblock+
              )
            ;
            
command_list returns [List<String> commands] :
  { $commands = new LinkedList<String>(); }
  m1=manifest_textblock 
  { getTI().informal().addCommand($m1.text); }
  { $commands.add($m1.text); }
  (  (',' m=manifest_textblock 
      { getTI().informal().addCommand($m.text); }
      { $commands.add($m.text); } 
     )
   | m=manifest_textblock 
     { getTI().informal().addCommand($m.text); addParseProblem(new MissingElementParseError(getSourceLocation($m.start), "comma", "before additional command item", false)); }
     { $commands.add($m.text); }
  )* 
  ','?
               ->
               ^(
                 COMMAND_LIST[$m1.start] manifest_textblock+
                )
              ;
              
constraint_list returns [List<String> constraints] :
  { $constraints = new LinkedList<String>(); }
  m1=manifest_textblock 
  { getTI().informal().addConstraint($m1.text); }
  { $constraints.add($m1.text); }
  (  (',' m=manifest_textblock 
      { getTI().informal().addConstraint($m.text); }
      { $constraints.add($m.text); }
     )
   | m=manifest_textblock 
     { getTI().informal().addConstraint($m.text); addParseProblem(new MissingElementParseError(getSourceLocation($m.start), "comma", "before additional constraint item", false)); }
     { $constraints.add($m.text); }
  )*
  ','?
                  -> 
                  ^(
                    CONSTRAINT_LIST[$m1.start] manifest_textblock+
                   )
                 ;

class_name_list returns [List<String> list] :
  { $list = new LinkedList<String>(); }
  c1=class_name 
  { getTI().classNameListEntry($c1.text, getSLoc($c1.stop)); }
  { $list.add($c1.text); }
  (  ( ',' c=class_name 
       { getTI().classNameListEntry($c.text, getSLoc($c.start)); }
       { $list.add($c.text); } 
     )
   | ( c=class_name 
       { getTI().classNameListEntry($c.text, getSLoc($c.start)); addParseProblem(new MissingElementParseError(getSourceLocation($c.start), "comma", "before additional class name", false)); }
       { $list.add($c.text); }										       
     )
  )*
                  ->
                  ^(
                    CLASS_NAME_LIST[$c1.start] class_name+
                   )
                 ;
                 
cluster_name_list returns [List<String> list] :
  { $list = new LinkedList<String>(); }
  c1=cluster_name
  (  ( ',' c=cluster_name
       { $list.add($c.text); } 
     )
   | ( c=cluster_name 
       { addParseProblem(new MissingElementParseError(getSourceLocation($c.start), "comma", "before additional class name", false)); }
       { $list.add($c.text); }                           
     )
  )*                  
                  ->
                  ^(
                    CLUSTER_NAME_LIST[$c1.start] cluster_name+
                   )
                 ;

// TODO not done.
class_or_cluster_name_list returns [List<String> list] :
  (class_name ',' )* 
  '(' cluster_name ')' 
  ( ',' ( class_name | '(' cluster_name ')' ) )*
                             ->
                               ^( CLASS_OR_CLUSTER_NAME_LIST (class_name)* (cluster_name)+ )
                             |
                               class_name_list
                             ->
                               ^( CLASS_OR_CLUSTER_NAME_LIST class_name_list ) 
                            ;

                 
class_name returns [String name] :
  i=IDENTIFIER
  { $name = $i.text; } 
             ->
             ^(
               CLASS_NAME[$i] IDENTIFIER
              )
            ;

/**********************************************/

event_chart returns [EventChart ec] :
  e='event_chart' system_name 
  ('incoming' | 'outgoing')?
  (indexing)?
  (explanation)?
  (part)?
  (event_entries)?
  'end'
              ->
              ^(
                EVENT_CHART[$e]
                system_name 
                ('incoming')? ('outgoing')?
                (indexing)?
                (explanation)?
                (part)?
                (event_entries)?
               )
             ;
             
event_entries returns [List<EventEntry> entries] :
  { $entries = new LinkedList<EventEntry>(); }
  (event_entry { $entries.add($event_entry.entry); } )+ 
                ->
                ^(
                  EVENT_ENTRIES
                  (event_entry)+
                 )
               ;
               
event_entry returns [EventEntry event]
@init { boolean mok=false; boolean cok=false; List<String> ccnl = null; String m = null; Token stop=null; } :
  e='event'
  (  ( m=manifest_textblock 
      {mok=true; m=$m.text;} 
     )
   |  
   { addParseProblem(new MissingElementParseError(getSourceLocation($e), "event name", "in event entry clause", true)); }
  ) 
  i='involves'
  (  (ccnl=class_or_cluster_name_list 
      { cok=true; ccnl = $ccnl.list; }
      { stop = $ccnl.stop; } 
     )
   |  
     { addParseProblem(new MissingElementParseError(getSourceLocation($i), "class name list", "in involves clause of event entry", true)); }
     { stop = $i.stop; }
  )
  { if (mok && cok) $event = EventEntry.mk(m, ccnl, getSLoc($e.start,stop)); }
              ->
                {!mok}? ^( EVENT_ENTRY PARSE_ERROR )
              ->
                {!cok}? ^( EVENT_ENTRY PARSE_ERROR )
              ->
              ^(
                EVENT_ENTRY[$e]
                manifest_textblock
                class_or_cluster_name_list
               )
             ;

/**********************************************/

scenario_chart returns [ScenarioChart sc] :
  s='scenario_chart' system_name
  (indexing)?
  (explanation)?
  (part)?
  (scenario_entries)?
  'end'
                 ->
                 ^(
                   SCENARIO_CHART[$s]
                   system_name
                   (indexing)?
                   (explanation)?
                   (part)?
                   (scenario_entries)?
                  )
                ;
                
scenario_entries returns [List<ScenarioEntry> entries] :
  { $entries = new LinkedList<ScenarioEntry>(); }
  (scenario_entry { $entries.add($scenario_entry.entry); } )+ 
                   ->
                   ^(
                     SCENARIO_ENTRIES
                     (scenario_entry)+ 
                    )                     
                  ;
                  
scenario_entry returns [ScenarioEntry entry] :
  s='scenario' m=MANIFEST_STRING d=description
  { $entry =  ScenarioEntry.mk($m.text, $d.description getSLoc($s.start,$d.stop)); }
                 ->
                 ^(
                   SCENARIO_ENTRY[$s]
                   MANIFEST_STRING description 
                  )
                ;

/**********************************************/

creation_chart returns [CreationChart cc] :
  c='creation_chart' system_name
  (indexing)?
  (explanation)?
  (part)?
  (creation_entries)?
  'end' 
                 ->
                 ^(
                   CREATION_CHART[$c]
                   system_name
                   (indexing)?
                   (explanation)?
                   (part)?
                   (creation_entries)?
                  )
                ;
                
creation_entries returns [List<CreationEntry> entries] :
  { $entries = new LinkedList<CreationEntry>(); }
  (creation_entry { $entries.add($creation_entry.entry); } )+
                   ->
                   ^(
                     CREATION_ENTRIES
                     (creation_entry)+
                    )
                  ;
                  
creation_entry returns [CreationEntry entry] :
  c='creator' class_name 
  'creates' ccnl=class_or_cluster_name_list
  { $entry = CreationEntry.mk($class_name.name, $ccnl.list, getSLoc($c.start,$ccnl.stop)); } 
                 ->
                 ^(
                   CREATION_ENTRY[$c]
                   class_name 
                   class_or_cluster_name_list 
                  )
                ;

/**********************************************  
 ***   Static Diagrams                      ***
 **********************************************/
 
static_diagram returns [StaticDiagram sd] 
@init { String eid = null; String comment = null; } 
:
  s='static_diagram' 
  (extended_id { eid=$extended_id.eid; } )? 
  (c=COMMENT { comment=$c.text; } )? 
  'component' 
  sb=static_block 
  e='end'
  { $sd = StaticDiagram.mk($sb.components, eid, comment, getSLoc($s.start,$e.end)); }                
                 ->
                 ^(
                   STATIC_DIAGRAM[$s]
                   (extended_id)? (COMMENT)? 
                   static_block 
                  )
                ;
                
extended_id returns [String eid] :  
   i=IDENTIFIER
   { $eid = $i.text; } 
              ->
              ^(
                EXTENDED_ID[$i] IDENTIFIER
               )
 | i=INTEGER
   { $eid = $i.text; } 
              ->
              ^(
                EXTENDED_ID[$i] INTEGER
               )
             ;
             
static_block returns [List<StaticComponent> components] :
  { $components = new LinkedList<StaticComponent>(); }
  (sc=static_component { $components.add($sc.component); })*
               ->
               ^(
                 STATIC_BLOCK (static_component)*
                )
              ;

//NB renamed "class" rule to "classX" as class is a reserved keyword in Java              
static_component returns [StaticComponent component] :
   c1=cluster
   { $component = $c1.cluster; } 
                    ->
                    ^(
                      STATIC_COMPONENT[$c1.start] cluster
                     )
 | c2=classX 
   { $component = $c2.classX; }
                    ->
                    ^(
                      STATIC_COMPONENT[$c2.start] classX
                     )
 | s=static_relation
   { $component = $s.relation; } 
                    ->
                    ^(
                      STATIC_COMPONENT[$s.start] static_relation
                     )
                  ;

/**********************************************/

cluster returns [Cluster cluster] 
@init { boolean reused = false; }
:
  c='cluster' cluster_name 
  ('reused' { reused = true; } )? 
  (COMMENT)? 
  { getTI().addCluster($cluster_name.text, getSLoc($c, $cluster_name.stop)); }   
  ( { getContext().enterCluster($cluster_name.text); }
    cluster_components
    { getContext().leaveCluster(); }
  )?
          ->
          ^(
            CLUSTER[$c] cluster_name
            ('reused')? (COMMENT)? 
            (cluster_components)?
           )
         ;
         
cluster_components returns [List<StaticComponent> components] :  
  c='component' static_block 'end'
  { $components = $static_block.components; }
                     -> 
                     ^(
                       CLUSTER_COMPONENTS[$c] static_block
                      ) 
                    ;
                    
classX returns [Clazz clazz] :
  (  ( 'root' c='class' c1=class_name 			{ getTI().addClass($c1.text, getSLoc($c,$c1.stop), "root"); getContext().enterClass($c1.text); }       ) 
						| ( 'deferred' c='class' c2=class_name   { getTI().addClass($c2.text, getSLoc($c,$c2.stop), "deferred"); getContext().enterClass($c2.text); }  )
						| ( 'effective' c='class' c3=class_name  { getTI().addClass($c3.text, getSLoc($c,$c3.stop), "effective"); getContext().enterClass($c3.text); } )
						| ( c='class' c4=class_name              { getTI().addClass($c4.text, getSLoc($c,$c4.stop), null); getContext().enterClass($c4.text); }        )
					 )             
           (formal_generics)?
           ('reused' { getTI().setClassReused(); } )? 
           ('persistent' { getTI().setClassPersistent(); })?   
           ('interfaced' { getTI().setClassInterfaced(); })? 
           (COMMENT)?
           (class_interface)? 
           { getContext().leaveClass(); }
         ->
         ^(
           CLASS[$c]
           ('root')? ('deferred')? ('effective')? 
           class_name (formal_generics)?
           ('reused')? ('persistent')?  ('interfaced')? (COMMENT)?
           (class_interface)? 
          )
        ;
            
static_relation returns [StaticRelation relation] :
   ir=inheritance_relation
   { $relation = $ir.relation; }
                  ->
                  ^(
                    STATIC_RELATION[$ir.start] inheritance_relation
                   )
 | cr=client_relation
   { $relation = $cr.relation; }
                  ->
                  ^(
                    STATIC_RELATION[$cr.start] client_relation
                   )                   
                 ;

/**********************************************/

inheritance_relation  :  c=child 'inherit' ('{' multiplicity '}')? 
                         parent (semantic_label)? 
                         { getTI().addParent($c.type,$parent.type,getSLoc($c.start,$parent.stop)); }
                       ->
                       ^(
                         INHERITANCE_RELATION[$c.start]
                         child (multiplicity)? 
                         parent (semantic_label)? 
                        )
                      ;
                    
client_relation  :  c=client 'client'
										{ ie.ucd.bon.typechecker.ClientRelation cr = new ie.ucd.bon.typechecker.ClientRelation($c.text); 
										  getContext().enterClientRelation(cr); } 
                    (client_entities)? 
                    ( type_mark 
                      { getTI().typeMark($type_mark.text); }
                      |
                      { getTI().typeMark(""); }
                    )
                    supplier 
                    { getContext().getClientRelation().setSupplier($supplier.text); }
                    (semantic_label)?
                    { getTI().addClientRelation(); } 
                  ->
                  ^(
                    CLIENT_RELATION[$c.start]
                    client (client_entities)? (type_mark)? 
                    supplier (semantic_label)? 
                   )
                 ;
                 
client_entities  :  a='{' client_entity_expression '}'
                  -> 
                  ^(
                    CLIENT_ENTITIES[$a]
                    client_entity_expression
                   )
                 ;
                 
client_entity_expression  :  cel=client_entity_list 
                           ->
                           ^(
                             CLIENT_ENTITY_EXPRESSION[$cel.start] client_entity_list
                            )
                           | m=multiplicity 
                           ->
                           ^(
                             CLIENT_ENTITY_EXPRESSION[$m.start] multiplicity
                            )
                          ;
                          
client_entity_list  :  ce=client_entity (',' client_entity)* 
                     -> 
                     ^(
                       CLIENT_ENTITY_LIST[$ce.start] (client_entity)+
                      )
                    ;
                    
//Conflict here is:
// feature_name can be a IDENTIFIER, and supplier_indirection can also be an IDENTIFIER
//TODO
//client_entity  :    feature_name 
client_entity  :    prefix
                  ->
                  ^(
                    CLIENT_ENTITY prefix
                   )
                  | infix
                  ->
                  ^(
                    CLIENT_ENTITY infix
                   )
                  | supplier_indirection 
                  ->
                  ^(
                    CLIENT_ENTITY supplier_indirection
                   )
                  | parent_indirection 
                  ->
                  ^(
                    CLIENT_ENTITY parent_indirection
                   )
               ;
               
supplier_indirection  :  (indirection_feature_part ':')? generic_indirection 
                       ->
                       ^(
                         SUPPLIER_INDIRECTION (indirection_feature_part)? generic_indirection 
                        )
                      ;
                      
indirection_feature_part  :  feature_name 
                           ->
                           ^(
                             INDIRECTION_FEATURE_PART feature_name
                            )
                           | indirection_feature_list 
                           ->
                           ^(
                             INDIRECTION_FEATURE_PART indirection_feature_list
                            )
                          ;	
                          
indirection_feature_list  :  '(' feature_name_list ')' 
                           ->
                           ^(
                             INDIRECTION_FEATURE_LIST feature_name_list
                            )
                          ;
                          
parent_indirection  :  '->' generic_indirection
                     ->
                     ^(
                       PARENT_INDIRECTION generic_indirection
                      )
                    ;

/**********************************************/

generic_indirection  :
//                        formal_generic_name 
//                      ->
//                      ^(
//                        GENERIC_INDIRECTION formal_generic_name
//                       )
                       //NB - changed the below... both are IDENTIFIERs
//                      | 
                      indirection_element
                      ->
                      ^(
                        GENERIC_INDIRECTION indirection_element
                       )
                     ;
                     
named_indirection :  class_name '[' indirection_list ']'
                    ->
                    ^(
                      NAMED_INDIRECTION class_name indirection_list
                     )
                    |
                     s='[' indirection_list ']'  { addParseProblem(new MissingElementParseError(getSLoc($s), "class name", "before indirection list", true)); }
                    ->
                      ^(NAMED_INDIRECTION PARSE_ERROR) 
                   ;
                   
indirection_list  :  indirection_element (',' indirection_element)* 
                   -> 
                   ^(
                     INDIRECTION_LIST indirection_element+
                    )
                  ;
                  
indirection_element  :   '...'
                       ->
                       ^(
                         INDIRECTION_ELEMENT '...'
                        )
                      | named_indirection 
                       ->
                       ^(
                         INDIRECTION_ELEMENT named_indirection
                        )
                      | class_name
                       ->
                       ^(
                       	 INDIRECTION_ELEMENT class_name
                       	)
                     ;

                     
type_mark  :  ':' 
            ->
            ^(
              TYPE_MARK ':'
             )
            | ':{' 
            ->
            ^(
              TYPE_MARK ':{'
             )
            | shared_mark             
            ->
            ^(
              TYPE_MARK shared_mark
             )
           ;
           
shared_mark  :  ':' '(' multiplicity ')'
              ->
              ^(
                SHARED_MARK multiplicity
               )
             ;

/**********************************************/

child returns [BONType type] :
         s=static_ref
         { $type = $s.type; } 
        ->
        ^(
          CHILD static_ref
         )
       ;
       
parent returns [BONType type] :
         s=static_ref
         { $type = $s.type; }         
         ->
         ^(
           PARENT static_ref
          )
        ;
        
client returns [BONType type] :
           s=static_ref
           { $type = $s.type; } 
         ->
         ^(
           CLIENT static_ref
          )
        ;
        
supplier returns [BONType type] :
           s=static_ref
           { $type = $s.type; }
           ->
           ^(
             SUPPLIER static_ref
            )
          ;
          
static_ref returns [BONType type] :  
               s=static_component_name
               { $type = $s.type; }
             ->
             ^(
               STATIC_REF[$s.start] static_component_name
              )
             | 
               c=cluster_prefix s=static_component_name
               { $type = $s.type; } 
             ->
             ^(
               STATIC_REF[$c.start] cluster_prefix static_component_name
              )
            ;
            
cluster_prefix  :  c1=cluster_name '.' (cluster_name '.')*
                 ->
                 ^(
                   CLUSTER_PREFIX[$c1.start] (cluster_name)+
                  )
                ;
  
//TODO - class_name and cluster_name are both just IDENTIFIERs.              
//static_component_name  :  class_name | cluster_name 
static_component_name returns [BONType type] :
                        i=IDENTIFIER
                        { $type = BONType.mk($i.text, null, $i.text); }
                        ->
                        ^(
                          STATIC_COMPONENT_NAME[$i] IDENTIFIER
                         )
                       ;
                       
multiplicity  :  i=INTEGER 
               ->
               ^(
                 MULTIPLICITY[$i] INTEGER
                )
              ;
              
semantic_label  :  m=MANIFEST_STRING
                 ->
                 ^(
                   SEMANTIC_LABEL[$m] MANIFEST_STRING
                  )
                ;

/**********************************************  
 ***   Class Interface Description          ***
 **********************************************/

class_interface  :  (indexing)?
                    (parent_class_list)?
                    features
                    (class_invariant)?
                    'end'
                  ->
                  ^(
                    CLASS_INTERFACE
                    (indexing)?
                    (parent_class_list)?
                    (features)?
                    (class_invariant)?
                   )
                 ;
                    
class_invariant  :  'invariant' assertion 
                    { getTI().addInvariant($assertion.text,getSLoc($assertion.start,$assertion.stop)); }
                  ->
                  ^(
                    CLASS_INVARIANT assertion
                   )                
                 ;
                 
parent_class_list  :  'inherit' c1=class_type 
                      { getTI().addParent($c1.type,getSLoc($c1.start,$c1.stop)); } 
                      (';' c=class_type 
                       { getTI().addParent($c.type,getSLoc($c.start,$c.stop)); } 
                      )* 
                      ';'? 
                    -> 
                    ^(
                      PARENT_CLASS_LIST (class_type)+
                     )
                    |
                       i='inherit' { addParseProblem(new MissingElementParseError(getSourceLocation($i), "class name(s)", "in inherits clause", true)); }
                    ->
                    ^(PARENT_CLASS_LIST PARSE_ERROR )
                   ;
                   
features  :  (feature_clause)+
           -> 
           ^(
             FEATURES (feature_clause)+
            )
          ;
          
/**********************************************/

feature_clause  :  f='feature' 
                   { getContext().enterFeatureClause(getSLoc($f)); }
                   (selective_export)? 
                   (COMMENT)? 
                   feature_specifications 
                   { getContext().leaveFeatureClause(); }
                 ->
                 ^(
                   FEATURE_CLAUSE
                   (selective_export)? 
                   (COMMENT)? 
                   feature_specifications 
                  )
                ;
                
feature_specifications  :  (feature_specification)+
                         ->
                         ^(
                           FEATURE_SPECIFICATIONS
                           (feature_specification)+
                          ) 
                        ;
                        
feature_specification  :  ( ( 'deferred'  { getContext().enterFeatureSpecification(); } feature_name_list { getTI().featureSpecDeferred(); }  ) 
                          | ( 'effective' { getContext().enterFeatureSpecification(); } feature_name_list { getTI().featureSpecEffective(); } )
                          | ( 'redefined' { getContext().enterFeatureSpecification(); } feature_name_list { getTI().featureSpecRedefined(); } )
                          | ( { getContext().enterFeatureSpecification(); } feature_name_list                                                 )
                          )
                          (has_type)?
                          (rename_clause)?
                          (COMMENT)?
                          (feature_arguments)?
                          (contract_clause)? 
                          { getContext().leaveFeatureSpecification(); }
                        ->
                        ^(
                          FEATURE_SPECIFICATION
                          ('deferred')? ('effective')? ('redefined')?
                          feature_name_list (has_type)?
                          (rename_clause)?
                          (COMMENT)?
                          (feature_arguments)?
                          (contract_clause)? 
                         )
                       ;
                       
has_type  :  type_mark type { getTI().hasType($type_mark.text, $type.text); }
           ->
           ^(HAS_TYPE type_mark type)
          ;

/**********************************************/

contract_clause  :  contracting_conditions 'end'
                  ->
                  ^(
                    CONTRACT_CLAUSE contracting_conditions
                   ) 
                 ;

//NB. Rewritten from precondition | postcondition | pre_and_post                 
contracting_conditions  :  ((precondition (postcondition)?) | postcondition)
                         -> 
                         ^(
                           CONTRACTING_CONDITIONS (precondition)? (postcondition)?
                          )
                        ;
                
//pre_and_post  :  precondition postcondition 
//              ;
        
precondition  :  'require' assertion 
                 { getTI().setPrecondition($assertion.text,getSLoc($assertion.start,$assertion.stop)); }
               ->
               ^(
                 PRECONDITION assertion
                )
              ;
              
postcondition  :  'ensure' assertion 
                  { getTI().setPostcondition($assertion.text,getSLoc($assertion.start,$assertion.stop)); }
                ->
                ^(
                  POSTCONDITION assertion
                 )
               ;

/**********************************************/

selective_export  :  '{' 
                     { getContext().enterSelectiveExport(); } 
                     class_name_list 
                     { getContext().leaveSelectiveExport(); }   
                     '}' 
                   ->
                   ^(
                     SELECTIVE_EXPORT class_name_list
                    )
                  ;
                  
feature_name_list  :  f1=feature_name { getTI().featureNameListEntry($f1.text,getSLoc($f1.start,$f1.stop)); } 
                      (',' f=feature_name { getTI().featureNameListEntry($f.text,getSLoc($f.start,$f1.stop)); } )*
                    -> 
                    ^(
                      FEATURE_NAME_LIST (feature_name)+
                     )
                   ;
                   
feature_name  :  IDENTIFIER 
               ->
               ^(
                 FEATURE_NAME IDENTIFIER
                )
               | prefix 
               ->
               ^(
                 FEATURE_NAME prefix
                )
               | infix 
               ->
               ^(
                 FEATURE_NAME infix
                )
              ;
              
rename_clause  :  '{' renaming '}'
                ->
                ^(
                  RENAME_CLAUSE renaming
                 )
               ;
               
renaming  :  s='^' class_name '.' feature_name 
             { getTI().renaming($class_name.text,$feature_name.text,getSLoc($s,$feature_name.stop)); }
           ->
           ^(
             RENAMING class_name feature_name
            )
          ;
          
feature_arguments  :  (feature_argument)+ 
                    ->
                    ^(
                      FEATURE_ARGUMENTS (feature_argument)+ 
                     )
                   ;
                   
feature_argument  :  '->' 
                     (  
                        ( identifier_list ':' t1=type { getTI().featureArg($identifier_list.text,$t1.text); } ) 
                      | ( t2=type                     { getTI().featureArg(null,$t2.text); }                  ) 
                     )
                   ->
                   ^(
                     FEATURE_ARGUMENT (identifier_list)? type
                    )
                  ;
                  
identifier_list  :  IDENTIFIER (',' IDENTIFIER)*
                  ->
                  ^(
                    IDENTIFIER_LIST (IDENTIFIER)+
                   )
                 ;

//TODO - are these necessary if we do not allow free operators?                 
prefix  :  'prefix' '"' prefix_operator '"'
         ->
         ^(
           PREFIX prefix_operator
          ) 
        ;
        
infix  :  'infix' '"' infix_operator '"' 
        ->
        ^(
          INFIX infix_operator
         )
       ;
       
//TODO - Add free_operator back?
prefix_operator  :  unary
                  ->
                  ^(
                    PREFIX_OPERATOR unary
                   )
                 ;
//prefix_operator  :  UNARY | free_operator                  

infix_operator  :  binary
                 ->
                 ^(
                   INFIX_OPERATOR binary
                  )
//infix_operator  :  binary | free_operator 
                ;

/**********************************************/

formal_generics  :  '[' formal_generic_list ']'
                  ->
                  ^(
                    FORMAL_GENERICS formal_generic_list
                   )
                 ;
                 
formal_generic_list  :  formal_generic (',' formal_generic)* 
                      -> 
                      ^(
                        FORMAL_GENERIC_LIST (formal_generic)+
                       )
                     ;
                     
formal_generic  :   f=formal_generic_name 								   { getTI().formalGeneric($f.text, null, getSLoc($f.start,$f.stop)); }
								 ->
								 ^(
								 	 FORMAL_GENERIC formal_generic_name
								  )
									| f=formal_generic_name '->' ct=class_type { getTI().formalGeneric($f.text, $ct.text, getSLoc($f.start,$f.stop)); }
                 -> 
                 ^(
                   FORMAL_GENERIC formal_generic_name class_type
                  )
                ;
                
formal_generic_name  :  i=IDENTIFIER 
                      -> 
                      ^(
                        FORMAL_GENERIC_NAME[$i] IDENTIFIER
                       )
                     ;
                     
class_type returns [BONType type] :  
             c=class_name 
             ( actual_generics
                 { $type = BONType.mk($c.text, $actual_generics.types, $c.text.concat($actual_generics.text)); }
               |
               { $type = BONType.mk($c.text, null, $c.text); } 
             ) 
             ->
             ^(
               CLASS_TYPE[$c.start] class_name (actual_generics)? 
              )
            ;
            
actual_generics returns [List<BONType> types] :  
                  '[' type_list ']'
                  { $types = $type_list.types; }
                  ->
                  ^(
                    ACTUAL_GENERICS type_list
                   ) 
                 ;
                 
type_list returns [List<BONType> types]  :
           t1=type
           { $types = new LinkedList<BONType>(); $types.add($t1.type); } 
           (',' t=type
           { $types.add($t.type); }
           )* 
            ->
            ^(
              TYPE_LIST (type)+
             )
           ;

//TODO - Conflict - class_type is essentially IDENTIFIER (actual_generics)?
//And formal_generic_name is IDENTIFIER          
//type  :  class_type | formal_generic_name 
type returns [BONType type] :  
       IDENTIFIER 
       (
        ( actual_generics 
          { $type = BONType.mk($IDENTIFIER.text, $actual_generics.types, $IDENTIFIER.text.concat($actual_generics.text)); }
        ) 
        |
        { $type = BONType.mk($IDENTIFIER.text, null, $IDENTIFIER.text); }
       ) 
       
       ->
       ^(
         TYPE IDENTIFIER (actual_generics)?
        )
;

/**********************************************  
 ***   Formal Assertions                    ***
 **********************************************/
//TODO correct this all for use with the new expression grammar

assertion  :  assertion_clause (';' assertion_clause)* ';'? //Final semi-colon is optional
            -> 
            ^(
              ASSERTION (assertion_clause)+
             )
           ;
           
assertion_clause  :  boolean_expression 
                   ->
                   ^(
                     ASSERTION_CLAUSE boolean_expression
                    )
//                   | COMMENT 
//                   ->
//                   ^(
//                     ASSERTION_CLAUSE COMMENT
//                    )
//TODO - Disallowing until revisiting this part of the grammar, as allowing comments here seems to make no sense
                  ;

//TODO - replace expression here?                  
boolean_expression  :  expression 
                     ->
                     ^(
                       BOOLEAN_EXPRESSION expression
                      )
                    ;
            
quantification  :  q=quantifier 
                   range_expression 
                   (restriction)? 
                   proposition 
                 ->
                 ^(
                   QUANTIFICATION[$q.start]
                   quantifier  
                   range_expression 
                   (restriction)? 
                   proposition 
                  )
                ;
                
quantifier  :  f='for_all' 
             ->
             ^(
               QUANTIFIER[$f] 'for_all'
              )
             | e='exists'
             ->
             ^(
               QUANTIFIER[$e] 'exists'
              )
            ;
            
range_expression  :  vr=variable_range (';' variable_range)* ';'? 
                   ->
                   ^(
                     RANGE_EXPRESSION[$vr.start] (variable_range)+
                    )
                  ;
                  
restriction  :  st='such_that' boolean_expression 
              ->
              ^(
                RESTRICTION[$st] boolean_expression
               )
             ;
             
proposition  :  ih='it_holds' boolean_expression 
              ->
              ^(
                PROPOSITION[$ih] boolean_expression
               )
             ;
             
variable_range  :  member_range 
                 ->
                 ^(
                   VARIABLE_RANGE member_range
                  )
                 | type_range 
                 ->
                 ^(
                   VARIABLE_RANGE type_range
                  )
                ;
                
member_range  :  identifier_list 'member_of' expression 
               -> 
               ^(
                 MEMBER_RANGE identifier_list expression
                )
              ;
              
type_range  :  identifier_list ':' type 
             ->
             ^(
               TYPE_RANGE identifier_list type
              )
            ;

/**********************************************/

//Not used...
//call  :  ('(' expression ')' '.')? call_chain 
//       -> 
//       ^(
//         CALL
//         (expression)? call_chain
//        )
//      ;
                               
call_chain  :  unqualified_call ('.' unqualified_call)* 
             -> 
             ^(
               CALL_CHAIN (unqualified_call)+
              )
            ;
            
unqualified_call  :  IDENTIFIER (actual_arguments)? 
                   ->
                   ^(
                     UNQUALIFIED_CALL IDENTIFIER (actual_arguments)?
                    )
                  ;
                  
actual_arguments  :  '(' expression_list? ')' 
                   ->
                   ^(
                     ACTUAL_ARGUMENTS expression_list?
                    )
                  ;
              
expression_list  :  expression (',' expression)* 
                  -> 
                  ^(
                    EXPRESSION_LIST (expression)+
                   )
                 ;
  
//Obsolete               
//operator_expression  :    parenthesized 
//                        | unary_expression 
//                        | binary_expression 
//                     ;
                                        
//parenthesized  :  '('! expression ')'!
//               ;


/**********************************************/

//enumerated sets are allowed as an expression
//set_expression  :  enumerated_set 
//                 ->
//                 ^(
//                   SET_EXPRESSION enumerated_set
//                  )
//                 | expression 
//                 ->
//                 ^(
//                   SET_EXPRESSION expression
//                  )
//                ;
                
enumerated_set  :  '{' enumeration_list '}'
                 ->
                 ^(
                   ENUMERATED_SET enumeration_list
                  )
                ;
                
enumeration_list  :  enumeration_element (',' enumeration_element)* 
                   -> 
                   ^(
                     ENUMERATION_LIST (enumeration_element)+
                    )
                  ;
         
enumeration_element  :  expression 
                      ->
                      ^(
                        ENUMERATION_ELEMENT expression
                       )
                      | interval 
                      ->
                      ^(
                        ENUMERATION_ELEMENT interval
                       )
                     ;
                     
interval  :  integer_interval
           ->
           ^(
             INTERVAL integer_interval
            ) 
           | character_interval 
           ->
           ^(
             INTERVAL character_interval
            ) 
          ;
          
integer_interval  :  integer_constant '..' integer_constant 
                   ->
                   ^(
                     INTEGER_INTERVAL integer_constant integer_constant
                    )
                  ;
                  
character_interval  :  CHARACTER_CONSTANT '..' CHARACTER_CONSTANT 
                     ->
                     ^(
                       CHARACTER_INTERVAL CHARACTER_CONSTANT CHARACTER_CONSTANT
                      )
                    ;
/**********************************************/

constant  :  mc=manifest_constant 
           ->
           ^(
             CONSTANT[$mc.start] manifest_constant
            )
           | c='Current' 
           ->
           ^(
             CONSTANT[$c] 'Current'
            )
           | v='Void'            
           ->
           ^(
             CONSTANT[$v] 'Void'
            )
          ;

manifest_constant  :   bc=boolean_constant 
                     ->
                     ^(
                       MANIFEST_CONSTANT[$bc.start] boolean_constant
                      )
                     | cc=CHARACTER_CONSTANT 
                     ->
                     ^(
                       MANIFEST_CONSTANT[$cc] CHARACTER_CONSTANT
                      )
                     | ic=integer_constant 
                     ->
                     ^(
                       MANIFEST_CONSTANT[$ic.start] integer_constant
                      )
                     | rc=real_constant 
                     ->
                     ^(
                       MANIFEST_CONSTANT[$rc.start] real_constant
                      )
                     | ms=MANIFEST_STRING 
                     ->
                     ^(
                       MANIFEST_CONSTANT[$ms] MANIFEST_STRING
                      )
                     | es=enumerated_set
                     ->
                     ^(
                     	 MANIFEST_CONSTANT[$es.start] enumerated_set
                     	)
                   ;
                   
sign  :  add_sub_op
       ->
       ^(
         SIGN add_sub_op
        )
      ;
      
boolean_constant  :  'true' 
                   ->
                   ^(
                     BOOLEAN_CONSTANT 'true'
                    )
                   | 'false' 
                   ->
                   ^(
                     BOOLEAN_CONSTANT 'false'
                    )
                  ;


//Changed to lexer rule, as we greedily take any character preceded and followed by a '                  
CHARACTER_CONSTANT  :  '\'' . '\'' 
                    ;


                    
integer_constant  :  (sign)? i=INTEGER 
                   ->
                   ^(
                     INTEGER_CONSTANT[$i]
                     (sign)? INTEGER
                    )
                  ;
                  
real_constant  :  (sign)? r=REAL 
                ->
                ^(
                  REAL_CONSTANT[$r]
                  (sign)? REAL
                 )
               ;

/**********************************************  
 ***   Dynamic Diagrams                     ***
 **********************************************/

dynamic_diagram  :  'dynamic_diagram' (extended_id)? (COMMENT)?
                    'component' (dynamic_block)? 'end'
                  ->
                  ^(
                    DYNAMIC_DIAGRAM
                    (extended_id)? (COMMENT)?
                    (dynamic_block)?
                   )
                 ;
                 
dynamic_block  :  (dynamic_component)+ 
                ->
                ^(
                  DYNAMIC_BLOCK
                  (dynamic_component)+
                 )
               ;
               
dynamic_component  :   scenario_description
                     -> 
                     ^(
                       DYNAMIC_COMPONENT scenario_description
                      )
                     | object_group 
                     -> 
                     ^(
                       DYNAMIC_COMPONENT object_group
                      )
                     | object_stack
                     -> 
                     ^(
                       DYNAMIC_COMPONENT object_stack
                      )
                     | object
                     -> 
                     ^(
                       DYNAMIC_COMPONENT object
                      )
                     | message_relation 
                     -> 
                     ^(
                       DYNAMIC_COMPONENT message_relation
                      )
                   ; 

/**********************************************/

scenario_description  :  'scenario' scenario_name (COMMENT)?
                         'action' labelled_actions 'end'
                       ->
                       ^(
                         SCENARIO_DESCRIPTION 
                         scenario_name (COMMENT)?
                         labelled_actions 
                        )
                      ;
                      
labelled_actions  :  (labelled_action)+ 
                   ->
                   ^(
                     LABELLED_ACTIONS (labelled_action)+
                    )
                  ;
                  
labelled_action  :  action_label action_description 
                  ->
                  ^(
                    LABELLED_ACTION action_label action_description
                   )
                 ;
                 
action_label  :  MANIFEST_STRING 
               ->
               ^(
                 ACTION_LABEL MANIFEST_STRING
                )
              ;
              
action_description  :  manifest_textblock 
                     ->
                     ^(
                       ACTION_DESCRIPTION manifest_textblock
                      )
                    ;
                    
scenario_name  :  manifest_textblock 
                ->
                ^(
                  SCENARIO_NAME MANIFEST_STRING
                 )
               ;

/**********************************************/

object_group  :  ('nameless')? 'object_group' group_name (COMMENT)? 
                 (group_components)? 
               ->
               ^(
                 OBJECT_GROUP ('nameless')? group_name (COMMENT)? (group_components)? 
                )
              ;
              
group_components  :  'component' dynamic_block 'end'
                   ->
                   ^(
                     GROUP_COMPONENTS dynamic_block
                    ) 
                  ;
                  
object_stack  :  'object_stack' object_name (COMMENT)?
               ->
               ^(
                 OBJECT_STACK object_name (COMMENT)?
                )
              ;
              
object  :  'object' object_name (COMMENT)? 
         ->
         ^(
           OBJECT object_name (COMMENT)?
          )
        ;

/**********************************************/

message_relation  :  caller 'calls' receiver (message_label)? 
                   ->
                   ^(
                     MESSAGE_RELATION caller receiver (message_label)?
                    )
                  ;
                  
caller  :  dynamic_ref 
         ->
         ^(
           RECEIVER dynamic_ref
          )
        ;
        
receiver  :  dynamic_ref 
           ->
           ^(
             RECEIVER dynamic_ref
            )
          ;
          
//TODO - the below change fixes a conflict, and allows the same grammar
//...but we lose some information here as to what the dynamic ref is.
//Can this be fixed at a later point when going over the AST?
//dynamic_ref  :  (group_prefix)* dynamic_component_name 
dynamic_ref  :  extended_id ('.' extended_id)*
              ->
              ^(
                DYNAMIC_REF (extended_id)+
               )
             ;
       
//group_prefix  :  group_name '.'
//              ;

//TODO - similarly this rule matches the same grammar, but will we need to know
// which we're actually matching?
//dynamic_component_name  :   object_name | group_name
dynamic_component_name  :  (IDENTIFIER ('.' extended_id)?) 
                         ->
                         ^(
                           DYNAMIC_COMPONENT_NAME IDENTIFIER (extended_id)?
                          )
                         | INTEGER
                         ->
                         ^(
                           DYNAMIC_COMPONENT_NAME INTEGER
                          )
                        ;

object_name  :  class_name ('.' extended_id)? 
              ->
              ^(
                OBJECT_NAME class_name (extended_id)?
               )
             ;
             
group_name  :  extended_id
             ->
             ^(
               GROUP_NAME extended_id
              ) 
            ;
            
message_label  :  MANIFEST_STRING 
                ->
                ^(
                  MESSAGE_LABEL MANIFEST_STRING
                 )
               ;

/**********************************************  
 ***   Notational Tuning                    ***
 **********************************************/
//TODO - do we want any of this section currently?
notational_tuning  :  change_string_marks 
                    ->
                    ^(
                      NOTATIONAL_TUNING change_string_marks
                     )
                    | change_concatenator
                    ->
                    ^(
                      NOTATIONAL_TUNING change_concatenator
                     )
                    | change_prefix 
                    ->
                    ^(
                      NOTATIONAL_TUNING change_prefix
                     )
                   ;

change_string_marks  :  'string_marks' MANIFEST_STRING MANIFEST_STRING 
                      ->
                      ^(
                        CHANGE_STRING_MARKS MANIFEST_STRING MANIFEST_STRING
                       )
                     ;
                     
change_concatenator  :  'concatenator' MANIFEST_STRING 
                      ->
                      ^(
                        CHANGE_CONCATENATOR MANIFEST_STRING
                       )
                     ;
                     
change_prefix  :  'keyword_prefix' MANIFEST_STRING 
                ->
                ^(
                  CHANGE_PREFIX MANIFEST_STRING
                 )
               ;
    
/**********************************************  
 ***   Expressions                          ***
 **********************************************/

expression  :  e=equivalence_expression  
             ->
             ^(
               EXPRESSION[$e.start] equivalence_expression
              )
             | q=quantification
             ->
             ^(
               EXPRESSION[$q.start] quantification
              )  
            ;

equivalence_expression	:  implies_expression ('<->'^ implies_expression)* 
                        ;

//Right associative
implies_expression  :  and_or_xor_expression ('->'^ implies_expression)?
                    ;

and_or_xor_expression  :  comparison_expression (and_or_xor_op^ comparison_expression)* 
                       ;

comparison_expression  :  add_sub_expression (comparison_op^  add_sub_expression)* 
                       ;

add_sub_expression  :  mul_div_expression (add_sub_op^ mul_div_expression)* 
                    ;

mul_div_expression  :  mod_pow_expression (mul_div_op^ mod_pow_expression)* 
                    ;

//Right-associative
mod_pow_expression  :  lowest_expression (mod_pow_op^ mod_pow_expression)? 
                    ;

lowest_expression  :  (constant)=> constant
										|	unary lowest_expression
      					    | '(' expression ')' ('.' call_chain)?
      					    | call_chain
        					 ;


/*############################################*  
 ###   Lexer...                             ###
 ##############################################
 *############################################*/

//FREE_OPERATOR  :  ~('"'|' '|'\n'|'\r'|'\t') ;

/**********************************************  
 ***   Strings                              ***
 **********************************************/

//fragment
//CONTINUED_STRING :  '\\' NEWLINE (options {greedy=false;} : ~('"'|'\\') )*
//                    ;


MANIFEST_STRING : '"' 
                  (options {greedy=false;} : ~('\n'|'\r'|'"'|'\\') )*  
                  '"'
                ;

//MANIFEST_TEXTBLOCK :   '"' 
//                       (options {greedy=false;} : ~('\n'|'\r'|'"'|'\\') )* 
//                       ('\\' NEWLINE (options {greedy=false;} : ~('"'|'\\') )* )*
//                       '"'                       
//                   ;

MANIFEST_TEXTBLOCK_START  : '"' (options {greedy=false;} : ~('\n'|'\r'|'"'|'\\') )+ '\\' (' '|'\t')* NEWLINE
           								;

MANIFEST_TEXTBLOCK_MIDDLE  : '\\' (options {greedy=false;} : ~('"'|'\\') )+ '\\' (' '|'\t')* NEWLINE
            							 ;

MANIFEST_TEXTBLOCK_END  : '\\' (options {greedy=false;} : ~('"'|'\\') )+ '"'
         								;


manifest_textblock  :   MANIFEST_STRING 
					  | MANIFEST_TEXTBLOCK_START MANIFEST_TEXTBLOCK_MIDDLE* MANIFEST_TEXTBLOCK_END
                    ;

COMMENT  :  LINE_COMMENT+ { $channel=HIDDEN; }
         ;

fragment 
LINE_COMMENT  :  COMMENT_START (options {greedy=false;} : .)* NEWLINE 
              ;

fragment
COMMENT_START  : '--'
               ;

fragment
NEWLINE  :  '\r'? '\n' 
         ;

/**********************************************  
 ***   Numbers                              ***
 **********************************************/

INTEGER  :  (DIGIT)+ 
         ;
         
REAL  :  DIGIT+ '.' DIGIT+ 
      ;
      
fragment 
DIGIT  :  '0'..'9' 
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
               
binary  :   add_sub_op | mul_div_op | comparison_op 
          | mod_pow_op | and_or_xor_op 
          | '->' | '<->' ;

comparison_op  :    '<'
                  | '>'
                  | '<='
                  | '>='
                  | '='
                  | '/='
                  | 'member_of'
                  | 'not' 'member_of'
                  ->
                  	NOT_MEMBER_OF
                  | ':'                  
                  ;

       
mul_div_op  :    '*'
             | '/'
             | '\\' 
             | '//'
            ;
               
mod_pow_op  :  '\\\\' 
             | '^' 
             ;

               
/**********************************************  
 ***   Identifiers                          ***
 **********************************************/
/* From the book:
   the identifier construct is defined as a sequence of alphanumeric -
   characters including underscore. an identifier must begin with an
   alphanumeric character and must not end with an underscore (whose
   purpose really is to mimic word separation). letter case is not
   significant, but using consistent style rules is important. */
       
IDENTIFIER  : ALPHA (ALPHANUMERIC_OR_UNDERSCORE* ALPHANUMERIC)? 
            ;



fragment 
ALPHANUMERIC_OR_UNDERSCORE  : ALPHANUMERIC | UNDERSCORE 
                            ;
                                     
fragment 
UNDERSCORE  :  '_' 
            ;
                    
fragment 
ALPHANUMERIC  :  ALPHA | DIGIT 
              ;
                       
fragment 
ALPHA  : LOWER | UPPER 
       ;
                
fragment 
LOWER  : 'a'..'z' 
       ;
                
fragment 
UPPER  : 'A'..'Z' 
       ;

/**********************************************  
 ***   Whitespace                           ***
 **********************************************/
 
WHITESPACE  :  (' '|'\n'|'\r'|'\t')+ {$channel=HIDDEN;}
            ;
