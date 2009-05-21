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

prog returns [BonSourceFile bonSource] :
         bs=bon_specification EOF
         { $bonSource = BonSourceFile.mk($bs.spec_els, null, getSLoc($bs.start, $bs.stop)); }
       ->
         ^( PROG bon_specification )
       |
         indexing bon_specification EOF
         { $bonSource = BonSourceFile.mk($bs.spec_els, $indexing.indexing, getSLoc($bs.start, $bs.stop)); }
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
//  | nt=notational_tuning
//    { $se = $nt.nt; } 
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
			
class_dictionary returns [ClassDictionary cd] 
@init { Indexing index = null; String expl = null; String p = null; 
        List<DictionaryEntry> entries = new LinkedList<DictionaryEntry>(); }
:  
  d='dictionary' 
  system_name 
  (indexing { index = $indexing.indexing; } )?
  (explanation { expl = $explanation.explanation; } )? 
  (part { p = $part.part; } )? 
  (de=dictionary_entry
   { entries.add($de.entry); }
  )+ 
  e='end'
  { $cd = ClassDictionary.mk($system_name.name, entries, index, expl, p, getSLoc($d,$e)); }
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
			
dictionary_entry returns [DictionaryEntry entry] :  
  c='class' class_name 
  'cluster' cluster_name_list 
  description 
  { $entry = DictionaryEntry.mk($class_name.text, $cluster_name_list.list, $description.text, getSLoc($c, $description.stop)); }
                   ->
                   ^(
                     DICTIONARY_ENTRY[$c] class_name
                     cluster_name_list description 
                    )
                  ;

/**********************************************/

system_chart returns [SystemChart sc] 
@init { Indexing index = null; String expl = null; String p = null; 
        List<ClusterEntry> entries = null; }
:
  s='system_chart' 
  system_name 
  { ie.ucd.bon.typechecker.informal.ClusterChartDefinition system = new ie.ucd.bon.typechecker.informal.ClusterChartDefinition($system_name.text, getSLoc($s, $system_name.stop), true);
  getTI().informal().setSystem(system);
  getContext().enterSystemChart(system); }
  (indexing { index = $indexing.indexing; } )?
  (explanation { expl = $explanation.explanation; } )? 
  (part { p = $part.part; } )? 
  (  ce=cluster_entries 
     { entries = $ce.entries; } 
   | { entries = Constants.NO_CLUSTER_ENTRIES; }
  ) 
  e='end'
  { getContext().leaveSystemChart(); }
  { $sc = SystemChart.mk($system_name.name, entries, index, expl, p, getSLoc($s,$e)); }
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
   { getTI().indexing($indexing); }
   { $indexing = Indexing.mk($index_list.list, getSLoc($i,$index_list.stop)); } 
           ->
           ^(
             INDEXING[$i] index_list
            ) 
 |
   i='indexing' 
   { addParseProblem(new MissingElementParseError(getSourceLocation($i), "indexing entries", "after 'indexing'", false)); }
   { $indexing = Indexing.mk(Constants.NO_INDEX_CLAUSES, getSLoc($i)); }
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
  { $ce = ClusterEntry.mk($cluster_name.text, $description.text, getSLoc($c, $description.stop)); } 
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
               { $clause = IndexClause.mk($i.text, $index_term_list.strings, getSLoc($i, $index_term_list.stop)); }
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
  { ie.ucd.bon.typechecker.informal.ClusterChartDefinition cluster = new ie.ucd.bon.typechecker.informal.ClusterChartDefinition($cluster_name.text, getSLoc($c, $cluster_name.stop), false);
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
  { $entry = ClassEntry.mk($class_name.text, $description.text, getSLoc($c, $description.stop)); }
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
  { ie.ucd.bon.typechecker.informal.ClassChartDefinition classX = new ie.ucd.bon.typechecker.informal.ClassChartDefinition($class_name.text, getSLoc($c, $class_name.stop));
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
  { $constraints = $constraint_list.constraints; }
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
               
event_entry returns [EventEntry entry]
@init { boolean mok=false; boolean cok=false; List<String> ccnl = null; String name = null; Token stop=null; } :
  e='event'
  (  ( m=manifest_textblock 
      {mok=true; name=$m.text;} 
     )
   |  
   { addParseProblem(new MissingElementParseError(getSourceLocation($e), "event name", "in event entry clause", true)); }
  ) 
  i='involves'
  (  (ccns=class_or_cluster_name_list 
      { cok=true; ccnl = $ccns.list; }
      { stop = $ccns.stop; } 
     )
   |  
     { addParseProblem(new MissingElementParseError(getSourceLocation($i), "class name list", "in involves clause of event entry", true)); }
     { stop = $i; }
  )
  { if (mok && cok) $entry = EventEntry.mk(name, ccnl, getSLoc($e,stop)); }
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
  { $entry =  ScenarioEntry.mk($m.text, $d.description, getSLoc($s,$d.stop)); }
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
  { $entry = CreationEntry.mk($class_name.name, $ccnl.list, getSLoc($c,$ccnl.stop)); } 
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
  { $sd = StaticDiagram.mk($sb.components, eid, comment, getSLoc($s,$e)); }                
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
             
static_component returns [StaticComponent component] :
   c1=cluster
   { $component = $c1.cluster; } 
                    ->
                    ^(
                      STATIC_COMPONENT[$c1.start] cluster
                     )
 | c2=clazz 
   { $component = $c2.clazz; }
                    ->
                    ^(
                      STATIC_COMPONENT[$c2.start] clazz
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
                    
clazz returns [Clazz clazz] :
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

inheritance_relation returns [InheritanceRelation relation] 
@init { Multiplicity multiplicity = null; String semanticLabel = null; }
:
  c=child 'inherit' 
  ('{' multiplicity '}'
   { multiplicity = Multiplicity.mk($multiplicity.num); }
  )? 
  p=parent 
  ( semantic_label
   { semanticLabel = $semantic_label.label; } 
  )? 
  { getTI().addParent($c.type,$parent.type,getSLoc($c.start,$parent.stop)); }
  { $relation = InheritanceRelation.mk($c.type, $p.type, multiplicity, semanticLabel); }
                       ->
                       ^(
                         INHERITANCE_RELATION[$c.start]
                         child (multiplicity)? 
                         parent (semantic_label)? 
                        )
                      ;
                    
client_relation returns [ClientRelation relation] 
@init { ClientEntityExpression entities = null; TypeMark mark = null; String semanticLabel = null; Token end = null; }
:
  c=client 'client'
  { ie.ucd.bon.typechecker.ClientRelation cr = new ie.ucd.bon.typechecker.ClientRelation($c.text); 
  getContext().enterClientRelation(cr); } 
  (client_entities { entities = $client_entities.entities; } )? 
  ( type_mark 
   { getTI().typeMark($type_mark.mark); }
   { mark = $type_mark.mark; }
   |
   { getTI().typeMark(Constants.NO_TYPE_MARK); }
   { mark = Constants.NO_TYPE_MARK; }
  )
  s=supplier 
  { end = $supplier.stop; }
  { getContext().getClientRelation().setSupplier($supplier.text); }
  (semantic_label { semanticLabel = $semantic_label.label; end = $semantic_label.stop; } )?
  { getTI().addClientRelation(); } 
  { $relation = ClientRelation.mk($c.type,$s.type,entities,mark,semanticLabel,getSLoc($c.start,end)); }
                  ->
                  ^(
                    CLIENT_RELATION[$c.start]
                    client (client_entities)? (type_mark)? 
                    supplier (semantic_label)? 
                   )
                 ;
                 
client_entities returns [ClientEntityExpression entities] :
  a='{' cee=client_entity_expression b='}'
  { $entities = $cee.entities; }
                  -> 
                  ^(
                    CLIENT_ENTITIES[$a]
                    client_entity_expression
                   )
                 ;
                 
client_entity_expression returns [ClientEntityExpression entities] :
   cel=client_entity_list
   { $entities = ClientEntityList.mk($cel.entities,getSLoc($cel.start,$cel.stop)); } 
                           ->
                           ^(
                             CLIENT_ENTITY_EXPRESSION[$cel.start] client_entity_list
                            )
 | m=multiplicity
   { $entities = Multiplicity.mk($m.num, getSLoc($m.start,$m.stop)); } 
                           ->
                           ^(
                             CLIENT_ENTITY_EXPRESSION[$m.start] multiplicity
                            )
                          ;
                          
client_entity_list returns [List<ClientEntity> entities] :
  { $entities = new LinkedList<ClientEntity>(); }
  ce=client_entity
  { $entities.add($ce.entity); }
  (',' c=client_entity
   { $entities.add($c.entity); }
  )* 
                     -> 
                     ^(
                       CLIENT_ENTITY_LIST[$ce.start] (client_entity)+
                      )
                    ;
                    
//Conflict here is:
// feature_name can be an IDENTIFIER, and supplier_indirection can also be an IDENTIFIER
//TODO
//client_entity  :    feature_name 
client_entity returns [ClientEntity entity] :
   prefix
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

                     
type_mark returns [TypeMark mark] :
   m=':'
   { $mark = TypeMark.mk(TypeMark.Mark.HASTYPE, null, getSLoc($m)); } 
            ->
            ^(
              TYPE_MARK ':'
             )
 | m=':{'
   { $mark = TypeMark.mk(TypeMark.Mark.AGGREGATE, null, getSLoc($m)); } 
            ->
            ^(
              TYPE_MARK ':{'
             )
 | sm=shared_mark
   { $mark = $sm.mark; }             
            ->
            ^(
              TYPE_MARK shared_mark
             )
           ;
           
shared_mark returns [TypeMark mark] :
  a=':' '(' m=multiplicity b=')'
  { $mark = TypeMark.mk(TypeMark.Mark.SHAREDMARK, m.num, getSLoc($a, $b)); }
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
                       
multiplicity returns [Integer num] :
  i=INTEGER
  { $num = new Integer($i.text); } 
               ->
               ^(
                 MULTIPLICITY[$i] INTEGER
                )
              ;
              
semantic_label returns [String label] :
  m=MANIFEST_STRING
  { $label = $m.text; }
                 ->
                 ^(
                   SEMANTIC_LABEL[$m] MANIFEST_STRING
                  )
                ;

/**********************************************  
 ***   Class Interface Description          ***
 **********************************************/

class_interface returns [ClassInterface ci] 
@init { Indexing indexing = null; List<BONType> parents = null; List<Expression> invariant = null; Token start = null; }
:
  (indexing { indexing = $indexing.indexing; start = $indexing.start; } )?
  (pcl=parent_class_list { parents = $pcl.parents; if (start == null) start = $pcl.start; } )?
  features
  { if (start == null) start = $features.start; }
  (inv=class_invariant { invariant = $inv.invariant; } )?
  e='end'
  { $ci = ClassInterface.mk($features.features, parents, invariant, indexing, getSLoc(start, $e)); }
                  ->
                  ^(
                    CLASS_INTERFACE
                    (indexing)?
                    (parent_class_list)?
                    (features)?
                    (class_invariant)?
                   )
                 ;
                    
class_invariant returns [List<Expression> invariant] :
  'invariant' assertion 
  { getTI().addInvariant($assertion.text,getSLoc($assertion.start,$assertion.stop)); }
  { $invariant = $assertion.clauses; }
                  ->
                  ^(
                    CLASS_INVARIANT assertion
                   )                
                 ;
                 
parent_class_list returns [List<BONType> parents] :
  { $parents = new LinkedList<BONType>(); }
  'inherit' c1=class_type 
  { getTI().addParent($c1.type,getSLoc($c1.start,$c1.stop)); }
  { $parents.add($c1.type); } 
  (';' c=class_type 
   { getTI().addParent($c.type,getSLoc($c.start,$c.stop)); }
   { $parents.add($c.type); } 
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
                   
features returns [List<Feature> features] :
  { $features = new LinkedList<Feature>(); }
  (feature_clause { $features.add($feature_clause.feature); } )+
           -> 
           ^(
             FEATURES (feature_clause)+
            )
          ;
          
/**********************************************/

feature_clause returns [Feature feature] 
@init { String comment = null; List<String> selectiveExport = null; }
:
  f='feature' 
  { getContext().enterFeatureClause(getSLoc($f)); }
  (se=selective_export { selectiveExport = $se.exports; } )? 
  (c=COMMENT { comment = $c.text; } )? 
  fs=feature_specifications 
  { getContext().leaveFeatureClause(); }
  { $feature = Feature.mk($fs.specs, selectiveExport, comment, getSLoc($f,$fs.stop)); }
                 ->
                 ^(
                   FEATURE_CLAUSE
                   (selective_export)? 
                   (COMMENT)? 
                   feature_specifications 
                  )
                ;
                
feature_specifications returns [List<FeatureSpecification> specs] :
  { $specs = new LinkedList<FeatureSpecification>(); }
  (fs=feature_specification { $specs.add($fs.spec); } )+
                         ->
                         ^(
                           FEATURE_SPECIFICATIONS
                           (feature_specification)+
                          ) 
                        ;
                        
feature_specification returns [FeatureSpecification spec] 
@init { FeatureSpecification.Modifier modifier = FeatureSpecification.Modifier.NONE; 
        List<FeatureArgument> args = null; HasType hasType = null; 
        RenameClause renaming = null; String comment = null; ContractClause contracts = null;}
:
  (  'deferred'  { modifier = FeatureSpecification.Modifier.DEFERRED; } 
   | 'effective' { modifier = FeatureSpecification.Modifier.EFFECTIVE; }
   | 'redefined' { modifier = FeatureSpecification.Modifier.REDEFINED; }
   |             { modifier = FeatureSpecification.Modifier.NONE; }
  )
  { getContext().enterFeatureSpecification(); }
  fnl=feature_name_list
  { getTI().featureSpecModifier(modifier); }
  (has_type { hasType = $has_type.htype; } )?
  (rc=rename_clause { renaming = $rc.rename; } )?
  (c=COMMENT { comment = $c.text; } )?
  (  fa=feature_arguments
     { args = $fa.args; }
   | { args = Constants.NO_ARGS; }
  )
  (  cc=contract_clause 
     { contracts = $cc.contracts; } 
   | { contracts = Constants.EMPTY_CONTRACT; }
  ) 
  { getContext().leaveFeatureSpecification(); }
  { $spec = FeatureSpecification.mk(modifier, $fnl.list, args, contracts, hasType, renaming, comment); }
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
                       
has_type returns [HasType htype] :
  type_mark type 
  { getTI().hasType($type_mark.mark, $type.text); }
  { $htype = HasType.mk($type_mark.mark, $type.type, getSLoc($type_mark.start,$type.stop)); }
           ->
           ^(HAS_TYPE type_mark type)
          ;

/**********************************************/

contract_clause returns [ContractClause contracts] :
  cc=contracting_conditions 'end'
  { $contracts = $cc.contracts; }
                  ->
                  ^(
                    CONTRACT_CLAUSE contracting_conditions
                   ) 
                 ;

//NB. Rewritten from precondition | postcondition | pre_and_post                 
contracting_conditions returns [ContractClause contracts] 
@init { List<Expression> postC = null; }
:
  (  (pre=precondition (post=postcondition { postC = $post.assertions; } )?)
     { if (postC == null) $contracts = ContractClause.mk($pre.assertions, Constants.NO_ASSERTIONS, getSLoc($pre.start,$post.stop)); 
       else $contracts = ContractClause.mk($pre.assertions, postC, getSLoc($pre.start,$post.stop)); }  
   | post=postcondition
     { $contracts = ContractClause.mk(Constants.NO_ASSERTIONS, $post.assertions, getSLoc($pre.start,$post.stop)); }
  )
  
                         -> 
                         ^(
                           CONTRACTING_CONDITIONS (precondition)? (postcondition)?
                          )
                        ;

precondition returns [List<Expression> assertions] :
  'require' assertion 
  { getTI().setPrecondition($assertion.text,getSLoc($assertion.start,$assertion.stop)); }
  { $assertions = $assertion.clauses; }
               ->
               ^(
                 PRECONDITION assertion
                )
              ;
              
postcondition returns [List<Expression> assertions] :
  'ensure' assertion 
  { getTI().setPostcondition($assertion.text,getSLoc($assertion.start,$assertion.stop)); }
  { $assertions = $assertion.clauses; }
                ->
                ^(
                  POSTCONDITION assertion
                 )
               ;

/**********************************************/

selective_export returns [List<String> exports] :
  '{' 
  { getContext().enterSelectiveExport(); } 
  cnl=class_name_list 
  { getContext().leaveSelectiveExport(); }   
  '}'
  { $exports = $cnl.list; }  
                   ->
                   ^(
                     SELECTIVE_EXPORT class_name_list
                    )
                  ;
                  
feature_name_list returns [List<String> list] :
  { $list = new LinkedList<String>(); }
  f1=feature_name 
  { getTI().featureNameListEntry($f1.text,getSLoc($f1.start,$f1.stop)); }
  { $list.add($f1.name); }
  (',' f=feature_name 
   { getTI().featureNameListEntry($f.text,getSLoc($f.start,$f1.stop)); }
   { $list.add($f.name); } 
  )*
                    -> 
                    ^(
                      FEATURE_NAME_LIST (feature_name)+
                     )
                   ;
                   
feature_name returns [String name] :
   i=IDENTIFIER
   { $name = $i.text; }
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
              
rename_clause returns [RenameClause rename] :
  '{' renaming '}'
  { $rename = $renaming.renaming; }
                ->
                ^(
                  RENAME_CLAUSE renaming
                 )
               ;
               
renaming returns [RenameClause renaming] :
  s='^' class_name '.' feature_name 
  { getTI().renaming($class_name.text,$feature_name.text,getSLoc($s,$feature_name.stop)); }
  { $renaming = RenameClause.mk($class_name.name, $feature_name.name, getSLoc($s,$feature_name.stop)); }
           ->
           ^(
             RENAMING class_name feature_name
            )
          ;
          
feature_arguments returns [List<FeatureArgument> args] :
  { $args = new LinkedList<FeatureArgument>(); }
  (feature_argument { $args.addAll($feature_argument.args); } )+ 
                    ->
                    ^(
                      FEATURE_ARGUMENTS (feature_argument)+ 
                     )
                   ;
                   
feature_argument returns [List<FeatureArgument> args] :
  '->' 
  (  
     ( identifier_list ':' t1=type 
       { getTI().featureArg($identifier_list.text,$t1.text); }
       { List<String> ids = $identifier_list.list; $args = new ArrayList<FeatureArgument>(ids.size()); for (String id : $identifier_list.list) $args.add(FeatureArgument.mk(id, $t1.type, getSLoc($identifier_list.start, $t1.stop))); }   
     ) 
   | ( t2=type
       { getTI().featureArg(null,$t2.text); }
       { $args = new ArrayList<FeatureArgument>(1); $args.add(FeatureArgument.mk(null, $t2.type, getSLoc($t2.start,$t2.stop))); }
     ) 
  )
                   ->
                   ^(
                     FEATURE_ARGUMENT (identifier_list)? type
                    )
                  ;
                  
identifier_list returns [List<String> list] :
  { $list = new LinkedList<String>(); }
  i1=IDENTIFIER
  { $list.add($i1.text); } 
  (',' i=IDENTIFIER { $list.add($i.text); } )*
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
                     
formal_generic returns [FormalGeneric generic] :
   f=formal_generic_name
   { getTI().formalGeneric($f.text, null, getSLoc($f.start,$f.stop)); }
   { $generic = FormalGeneric.mk($f.name, null, getSLoc($f.start,$f.stop)); }
								 ->
								 ^(
								 	 FORMAL_GENERIC formal_generic_name
								  )
 | f=formal_generic_name '->' ct=class_type 
   { getTI().formalGeneric($f.text, $ct.text, getSLoc($f.start,$f.stop)); }
   { $generic = FormalGeneric.mk($f.name, $ct.type, getSLoc($f.start, $ct.stop)); }
                 -> 
                 ^(
                   FORMAL_GENERIC formal_generic_name class_type
                  )
                ;
                
formal_generic_name returns [String name] :
  i=IDENTIFIER
  { $name = $i.text; } 
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

assertion returns [List<Expression> clauses] :
  { $clauses = new LinkedList<Expression>(); }
  a1=assertion_clause
  { $clauses.add($a1.clause); }
  (';' a=assertion_clause  
   { $clauses.add($a.clause); }
  )* 
  ';'?
  
            -> 
            ^(
              ASSERTION (assertion_clause)+
             )
           ;
           
assertion_clause returns [Expression clause] :
  be=boolean_expression
  { $clause = $be.exp; }
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
boolean_expression returns [Expression exp] :
  expression
  { $exp = $expression.exp; } 
                     ->
                     ^(
                       BOOLEAN_EXPRESSION expression
                      )
                    ;
            
quantification returns [Quantification quantification] 
@init { Expression restrict = null; }
:
  q=quantifier 
  rexp=range_expression 
  (r=restriction { restrict = $r.exp; } )? 
  p=proposition
  { $quantification = Quantification.mk($q.q, $rexp.ranges, restrict, $p.exp, getSLoc($q.start,$p.stop)); } 
                 ->
                 ^(
                   QUANTIFICATION[$q.start]
                   quantifier  
                   range_expression 
                   (restriction)? 
                   proposition 
                  )
                ;
                
quantifier returns [Quantification.Quantifier q] :
   f='for_all' 
   { $q = Quantification.Quantifier.FORALL; }
             ->
             ^(
               QUANTIFIER[$f] 'for_all'
              )
 | e='exists'
   { $q = Quantification.Quantifier.EXISTS; }
             ->
             ^(
               QUANTIFIER[$e] 'exists'
              )
            ;
            
range_expression returns [List<VariableRange> ranges] :
  { $ranges = new LinkedList<VariableRange>(); }
  vr1=variable_range 
  { $ranges.add($vr.range); }
  (';' vr=variable_range
   { $ranges.add($vr.range); }
  )* 
  ';'? 
                   ->
                   ^(
                     RANGE_EXPRESSION[$vr1.start] (variable_range)+
                    )
                  ;
                  
restriction returns [Expression exp] :
  st='such_that' be=boolean_expression
  { $exp =  $be.exp; }
              ->
              ^(
                RESTRICTION[$st] boolean_expression
               )
             ;
             
proposition returns [Expression exp] :
  ih='it_holds' be=boolean_expression
  { $exp = $be.exp; } 
              ->
              ^(
                PROPOSITION[$ih] boolean_expression
               )
             ;
             
variable_range returns [VariableRange range] :
   mr=member_range
   { $range = $mr.range; }
                 ->
                 ^(
                   VARIABLE_RANGE member_range
                  )
 | tr=type_range 
   { $range = $tr.range; } 
                 ->
                 ^(
                   VARIABLE_RANGE type_range
                  )
                ;
                
member_range returns [MemberRange range] :
  il=identifier_list 'member_of' e=expression
  { $range = MemberRange.mk($il.list, $e.exp, getSLoc($il.start,$e.stop)); } 
               -> 
               ^(
                 MEMBER_RANGE identifier_list expression
                )
              ;
              
type_range returns [TypeRange range] :
  il=identifier_list ':' t=type
  { $range = TypeRange.mk($il.list, $t.type, getSLoc($il.start,$t.stop)); } 
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

dynamic_diagram returns [DynamicDiagram dd] 
@init { String id = null; String comment = null; List<DynamicComponent> components = null; }
:
  s='dynamic_diagram' 
  (eid=extended_id { id = $eid.eid; } )? 
  (c=COMMENT { comment = $c.text; } )?
  'component' 
  ( db=dynamic_block
    { components = $db.components; }
   | { components = Constants.NO_COMPONENTS; }
  ) 
  e='end'
  { $dd = DynamicDiagram.mk(components, id, comment, getSLoc($s,$e)); }
                  ->
                  ^(
                    DYNAMIC_DIAGRAM
                    (extended_id)? (COMMENT)?
                    (dynamic_block)?
                   )
                 ;
                 
dynamic_block returns [List<DynamicComponent> components] :
  { $components = new LinkedList<DynamicComponent>(); }
  (dc=dynamic_component { $components.add($dc.component); } )+ 
                ->
                ^(
                  DYNAMIC_BLOCK
                  (dynamic_component)+
                 )
               ;
               
dynamic_component returns [DynamicComponent component] :
   scenario_description
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

scenario_description returns [ScenarioDescription description] 
@init { String comment = null; }
:
  s='scenario' scenario_name 
  (c=COMMENT { comment = $c.text; } )?
  'action' 
  la=labelled_actions 
  e='end'
  { $description = ScenarioDescription.mk($scenario_name.name, $la.actions, comment, getSLoc($s,$c)); }
                       ->
                       ^(
                         SCENARIO_DESCRIPTION 
                         scenario_name (COMMENT)?
                         labelled_actions 
                        )
                      ;
                      
labelled_actions returns [List<LabelledAction> actions] :
  { $actions = new LinkedList<LabelledAction>(); }
  (la=labelled_action { $actions.add($la.action); } )+ 
                   ->
                   ^(
                     LABELLED_ACTIONS (labelled_action)+
                    )
                  ;
                  
labelled_action returns [LabelledAction action] :
  al=action_label ad=action_description
  { $action = LabelledAction.mk($al.label, $ad.description, getSLoc($al.start,$ad.stop)); } 
                  ->
                  ^(
                    LABELLED_ACTION action_label action_description
                   )
                 ;
                 
action_label returns [String label] :
  m=MANIFEST_STRING
  { $label = $m.text; }
               ->
               ^(
                 ACTION_LABEL MANIFEST_STRING
                )
              ;
              
action_description returns [String description] :
  m=manifest_textblock
  { $description = $m.text; }
                     ->
                     ^(
                       ACTION_DESCRIPTION manifest_textblock
                      )
                    ;
                    
scenario_name returns [String name] :
  m=manifest_textblock
  { $name = $m.text; }
                ->
                ^(
                  SCENARIO_NAME MANIFEST_STRING
                 )
               ;

/**********************************************/

object_group returns [ObjectGroup group] 
@init { String comment = null; List<DynamicComponent> components = null; 
        ObjectGroup.Nameless nameless = ObjectGroup.Nameless.NOTNAMELESS; 
        Token start = null; Token end = null; }
:
  (  n='nameless'
     { nameless = ObjectGroup.Nameless.NAMELESS; start = $n; }
   | { nameless = ObjectGroup.Nameless.NOTNAMELESS; }
  ) 
  s='object_group' { if (start==null) start=$s; }
  group_name 
  { end = $group_name.stop; }
  (c=COMMENT { comment = $c.text; end = $c; } )? 
  (  gc=group_components
     { components = $gc.components; }
   | { components = Constants.NO_COMPONENTS; }
  )
  { $group = ObjectGroup.mk(nameless, $group_name.text, components, comment, getSLoc(start,end)); }
               ->
               ^(
                 OBJECT_GROUP ('nameless')? group_name (COMMENT)? (group_components)? 
                )
              ;
              
group_components returns [List<DynamicComponent> components] :
  'component' dynamic_block 'end'
  { $components = $dynamic_block.components; }
                   ->
                   ^(
                     GROUP_COMPONENTS dynamic_block
                    ) 
                  ;
                  
object_stack returns [ObjectStack stack] 
@init { String comment = null; Token end = null; }
:
  s='object_stack' 
  n=object_name
  { end = $n.stop; } 
  (c=COMMENT { comment = $c.text; end = $c; } )?
  { $stack = ObjectStack.mk($n.name, comment, getSLoc($s,end)); }
               ->
               ^(
                 OBJECT_STACK object_name (COMMENT)?
                )
              ;
              
object returns [ObjectInstance object] 
@init { String comment = null; Token end = null; }
:  
  s='object' 
  n=object_name
  { end = $n.stop; } 
  (c=COMMENT { comment = $c.text; end = $c; } )?
  { $object = ObjectInstance.mk($n.name, comment, getSLoc($s,end)); } 
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

object_name returns [ObjectName name] 
@init { String id = null; Token end = null; }
:
  n=class_name 
  { end = $n.stop; }
  ('.' e=extended_id { id = $e.eid; end=$e.stop; } )?
  { $name = ObjectName.mk($n.name, id, getSLoc($n.start,end)); } 
              ->
              ^(
                OBJECT_NAME class_name (extended_id)?
               )
             ;
             
group_name returns [String name] :
  e=extended_id
  { $name = $e.eid; }
             ->
             ^(
               GROUP_NAME extended_id
              ) 
            ;
            
message_label returns [String label] :
  m=MANIFEST_STRING
  { $label = $m.text; }   
                ->
                ^(
                  MESSAGE_LABEL MANIFEST_STRING
                 )
               ;

/**********************************************  
 ***   Notational Tuning                    ***
 **********************************************/
//TODO - do we want any of this section currently?
notational_tuning :  change_string_marks 
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

expression returns [Expression exp] :
   e=equivalence_expression
   { $exp = $e.exp; }  
             ->
             ^(
               EXPRESSION[$e.start] equivalence_expression
              )
 | q=quantification
   { $exp = $q.quantification; }
             ->
             ^(
               EXPRESSION[$q.start] quantification
              )  
            ;

equivalence_expression returns [Expression exp] :
  l=implies_expression
  { $exp = $l.exp; } 
  ('<->'^ r=implies_expression
   { $exp = BinaryExp.mk(BinaryExp.Op.EQUIV, $exp, $r.exp, getSLoc($exp.getLocation(),$r.exp.getLocation())); }
  )*
;

//Right associative
implies_expression returns [Expression exp] :
  l=and_or_xor_expression
  { $exp = $l.exp; } 
  ('->' r=implies_expression
   { $exp = BinaryExp.mk(BinaryExp.Op.IMPLIES, $exp, $r.exp, getSLoc($exp.getLocation(),$r.exp.getLocation())); }
  )?
;

and_or_xor_expression returns [Expression exp] :
  l=comparison_expression 
  (op=and_or_xor_op comparison_expression)* 
;

comparison_expression returns [Expression exp] :
  l=add_sub_expression 
  (op=comparison_op  add_sub_expression)* 
;

add_sub_expression returns [Expression exp] :
  l=mul_div_expression 
  (op=add_sub_op mul_div_expression)* 
;

mul_div_expression returns [Expression exp] :
  l=mod_pow_expression 
  (op=mul_div_op mod_pow_expression)* 
;

//Right-associative
mod_pow_expression returns [Expression exp] :
  l=lowest_expression 
  (op=mod_pow_op mod_pow_expression)? 
;

lowest_expression returns [Expression exp] :
  (constant)=> constant
										|	unary lowest_expression
      					    | '(' expression ')' ('.' call_chain)?
      					    | call_chain
        					 ;

/**********************************************  
 ***   Operatives                           ***
 **********************************************/

add_sub_op returns [BinaryExp.Op op] :
   '+' { $op = BinaryExp.Op.ADD; } 
 | '-' { $op = BinaryExp.Op.SUB; }
;

add_sub_op_unary returns [UnaryExp.Op op] :
   '+' { $op = UnaryExp.Op.ADD; } 
 | '-' { $op = UnaryExp.Op.SUB; }
;

and_or_xor_op returns [BinaryExp.Op op] :
   'and' { $op = BinaryExp.Op.AND; }
 | 'or'  { $op = BinaryExp.Op.OR; }
 | 'xor' { $op = BinaryExp.Op.XOR; }
; 

unary returns [UnaryExp.Op op]  :
   other_unary       { $op = $other_unary.op; } 
 | add_sub_op_unary  { $op = $add_sub_op_unary.op; }
;

other_unary returns [UnaryExp.Op op]  :
   'delta' { $op = UnaryExp.Op.DELTA; } 
 | 'old'   { $op = UnaryExp.Op.OLD; }
 | 'not'   { $op = UnaryExp.Op.NOT; }
;
               
binary  :   add_sub_op | mul_div_op | comparison_op 
          | mod_pow_op | and_or_xor_op 
          | '->' | '<->' ;

comparison_op returns [BinaryExp.Op op] :
   '<'  { $op = BinaryExp.Op.LT; }
 | '>'  { $op = BinaryExp.Op.GT; }
 | '<=' { $op = BinaryExp.Op.LE; }
 | '>=' { $op = BinaryExp.Op.GE; }
 | '='  { $op = BinaryExp.Op.EQ; }
 | '/=' { $op = BinaryExp.Op.NEQ; }
 | 'member_of' { $op = BinaryExp.Op.MEMBEROF; }
 | 'not' 'member_of' { $op = BinaryExp.Op.NOTMEMBEROF; }
                  ->
                  	NOT_MEMBER_OF
 | ':'  { $op = BinaryExp.Op.HASTYPE; }
;

       
mul_div_op returns [BinaryExp.Op op] :
   '*'  { $op = BinaryExp.Op.MUL; }
 | '/'  { $op = BinaryExp.Op.DIV; }
 | '//' { $op = BinaryExp.Op.INTDIV; }
;
               
mod_pow_op returns [BinaryExp.Op op] :
   '\\\\' { $op = BinaryExp.Op.MOD; } 
 | '^'    { $op = BinaryExp.Op.POW; }
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
