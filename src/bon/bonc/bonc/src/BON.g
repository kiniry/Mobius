/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */

grammar BON;
options {
  ASTLabelType=CommonTree;
  superClass=AbstractBONParser;
}

@header {
  package ie.ucd.bon.parser; 
  
  import ie.ucd.bon.parser.errors.MissingElementParseError;
  import ie.ucd.bon.ast.*;
  import java.io.File;
}

@lexer::header {
/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser;
}

@members {
  //Nothing
}

/**********************************************  
 ##############################################
 ###   Parser...                            ###
 ##############################################
 **********************************************/

prog returns [BonSourceFile bonSource] :
         bs=bon_specification EOF
         { if(isOk()) $bonSource = BonSourceFile.mk($bs.spec_els, null, getSLoc($bs.start, $bs.stop)); }
       |
         i=indexing bs=bon_specification EOF
         { if(isOk()) $bonSource = BonSourceFile.mk($bs.spec_els, $indexing.indexing, getSLoc($i.start, $bs.stop)); }
       |
         e=EOF 
         { addParseProblem(new MissingElementParseError(getSourceLocation($e), "at least one specification entry", "in source file", true)); }
         { $bonSource = BonSourceFile.mk(Constants.NO_SPEC_ELEMS, null, getSLoc($e)); }
       | 
         indexing e=EOF 
         { addParseProblem(new MissingElementParseError(getSourceLocation($e), "at least one specification entry", "in source file", true)); }
         { if(isOk()) $bonSource = BonSourceFile.mk(Constants.NO_SPEC_ELEMS, $indexing.indexing, getSLoc($indexing.start,$indexing.stop)); }
;

/**********************************************  
 ***   BON Specification                    ***
 **********************************************/

bon_specification returns [List<SpecificationElement> spec_els] :
  { $spec_els = createList(); }
  ( se=specification_element
    { if(isOk()) $spec_els.add($se.se); }
  )+ 
;

specification_element returns [SpecificationElement se] :
    ic=informal_chart
    { if(isOk()) $se = $ic.ic; }
  | cd=class_dictionary
    { if(isOk()) $se = $cd.cd; }
  | sd=static_diagram
    { if(isOk()) $se = $sd.sd; }
  | dd=dynamic_diagram
    { if(isOk()) $se = $dd.dd; }
//  | nt=notational_tuning
//    { if(isOk()) $se = $nt.nt; } 
;

/**********************************************  
 ***   Informal charts                      ***
 **********************************************/

informal_chart returns [InformalChart ic] :
    system_chart
    { if(isOk()) $ic = $system_chart.sc; }
  | cluster_chart
    { if(isOk()) $ic = $cluster_chart.cc; }
  | class_chart
    { if(isOk()) $ic = $class_chart.cc; }
  | event_chart
    { if(isOk()) $ic = $event_chart.ec; }
  | scenario_chart
    { if(isOk()) $ic = $scenario_chart.sc; }
  | creation_chart 
    { if(isOk()) $ic = $creation_chart.cc; }
;
			
class_dictionary returns [ClassDictionary cd] 
@init { Indexing index = null; String expl = null; String p = null; 
        List<DictionaryEntry> entries = createList(); }
:  
  d='dictionary' 
  system_name 
  (indexing { if(isOk()) index = $indexing.indexing; } )?
  (explanation { if(isOk()) expl = $explanation.explanation; } )? 
  (part { if(isOk()) p = $part.part; } )? 
  (de=dictionary_entry
   { if(isOk()) entries.add($de.entry); }
  )+ 
  e='end'
  { if(isOk()) $cd = ClassDictionary.mk($system_name.name, entries, index, expl, p, getSLoc($d,$e)); }
;
			
dictionary_entry returns [DictionaryEntry entry] :  
  c='class' class_name 
  'cluster' cluster_name_list 
  description 
  { if(isOk()) $entry = DictionaryEntry.mk($class_name.text, $cluster_name_list.list, $description.text, getSLoc($c, $description.stop)); }
;

/**********************************************/

system_chart returns [ClusterChart sc] 
@init { Indexing index = null; String expl = null; String p = null; 
        List<ClusterEntry> entries = null; }
:
  s='system_chart' 
  system_name 
  (indexing { if(isOk()) index = $indexing.indexing; } )?
  (explanation { if(isOk()) expl = $explanation.explanation; } )? 
  (part { if(isOk()) p = $part.part; } )? 
  (  ce=cluster_entries 
     { if(isOk()) entries = $ce.entries; } 
   | { if(isOk()) entries = emptyList(); }
  ) 
  e='end'
  { if(isOk()) $sc = ClusterChart.mk($system_name.name, true, Constants.NO_CLASS_ENTRIES, entries, index, expl, p, getSLoc($s,$e)); }
;

explanation returns [String explanation] :
  e='explanation' m=manifest_textblock
  { if(isOk()) $explanation = $m.text; }
 |
  e='explanation' 
  { addParseProblem(new MissingElementParseError(getSourceLocation($e), "explanation text", "after 'explanation'", false)); }
;

indexing returns [Indexing indexing] :  
   i='indexing' index_list
   { if(isOk()) $indexing = Indexing.mk($index_list.list, getSLoc($i,$index_list.stop)); } 
 |
   i='indexing' 
   { addParseProblem(new MissingElementParseError(getSourceLocation($i), "indexing entries", "after 'indexing'", false)); }
   { $indexing = Indexing.mk(Constants.NO_INDEX_CLAUSES, getSLoc($i)); }
;

part returns [String part] :
    p='part' m=MANIFEST_STRING
    { if(isOk()) $part = $m.text; }
  |
    p='part' 
    { addParseProblem(new MissingElementParseError(getSourceLocation($p), "part text", "after 'part'", false)); }
    { if(isOk()) $part = ""; }
;

description returns [String description] :
  d='description' m=manifest_textblock 
  { if(isOk()) $description = $m.text; }
;

cluster_entries returns [List<ClusterEntry> entries] :
  { $entries = createList(); }
  (cluster_entry { if(isOk()) $entries.add($cluster_entry.ce); } )+
;
                 
cluster_entry returns [ClusterEntry ce] :
  c='cluster' cluster_name description
  { if(isOk()) $ce = ClusterEntry.mk($cluster_name.text, $description.description, getSLoc($c, $description.stop)); } 
;
               
system_name returns [String name] :
  i=IDENTIFIER
  { if(isOk()) $name = $i.text; } 
;

/**********************************************/

index_list returns [List<IndexClause> list] :  
               { $list = createList(); }
               i1=index_clause 
               { if(isOk()) $list.add($i1.clause); }
               (  (';' i2=index_clause)
                  { if(isOk()) $list.add($i2.clause); }
                | i=index_clause { addParseProblem(new MissingElementParseError(getSourceLocation($i.start), "semi-colon", "before additional index clause", false)); }
                  { if(isOk()) $list.add($i.clause); }
               )* 
               ';'? //Final semi-colon optional
;
            
index_clause returns [IndexClause clause] :  
  i=IDENTIFIER ':' index_term_list 
  { if(isOk()) $clause = IndexClause.mk($i.text, $index_term_list.strings, getSLoc($i, $index_term_list.stop)); }
 |
  i=IDENTIFIER ':' 
  { addParseProblem(new MissingElementParseError(getSourceLocation($i), "index term(s)", "in index clause", true)); }
;
                
index_term_list returns [List<String> strings] :
  { $strings = createList(); }
  i1=index_string 
  { if(isOk()) $strings.add($i1.text); }
  (',' i=index_string
   { if(isOk()) $strings.add($i.text); }
  )* 
;
                 
index_string returns [String s] :
  m=manifest_textblock
  { if(isOk()) $s = $m.text; }    
;

/**********************************************/

cluster_chart returns [ClusterChart cc] 
@init { List<ClassEntry> classes = null; List<ClusterEntry> clusters = null; 
        Indexing indexing = null; String explanation = null; String part = null;  }
:
  c='cluster_chart' cluster_name 
  (i=indexing { if(isOk()) indexing = $i.indexing; } )? 
  (explanation { if(isOk()) explanation = $explanation.explanation; } )? 
  (part { if(isOk()) part = $part.part; } )? 
  (  ce=class_entries { if(isOk()) classes = $ce.entries; }
   | { if(isOk()) classes = emptyList(); } 
  ) 
  (  cle=cluster_entries { clusters = $cle.entries; } 
   | { if(isOk()) clusters = emptyList(); }
  ) 
  e='end'
  { if(isOk()) $cc = ClusterChart.mk($cluster_name.name, false, classes, clusters, indexing, explanation, part, getSLoc($c,$e)); }
;
               
class_entries returns [List<ClassEntry> entries] :
  { $entries = createList(); }
  (class_entry { if(isOk()) $entries.add($class_entry.entry); } )+ 
;
               
class_entry returns [ClassEntry entry] :
  c='class' class_name
  description
  { if(isOk()) $entry = ClassEntry.mk($class_name.text, $description.description, getSLoc($c, $description.stop)); }
;
             
cluster_name returns [String name] :
  i=IDENTIFIER
  { if(isOk()) $name = $i.text; } 
;

/**********************************************/

class_chart returns [ClassChart cc] 
@init { Indexing indexing = null; String explanation = null; String part = null;
        List<ClassName> inherits = emptyList(); List<String> commands = emptyList(); List<String> queries = emptyList(); 
        List<String> constraints = emptyList();  }
:
  c='class_chart' class_name 
  (i=indexing { if(isOk()) indexing = $i.indexing; } )? 
  (explanation { if(isOk()) explanation = $explanation.explanation; } )? 
  (part { if(isOk()) part = $part.part; } )? 
  (  inherits
     { if(isOk()) inherits = $inherits.inherits; }
  )?
  (  queries
     { if(isOk()) queries = $queries.queries; }
  )?
  (  commands
     { if(isOk()) commands = $commands.commands; }
  )?
  (  constraints
     { if(isOk()) constraints = $constraints.constraints; }
  )?
  e='end'
  { if(isOk()) $cc = ClassChart.mk($class_name.name, inherits, queries, commands, constraints, indexing, explanation, part, getSLoc($c,$e)); }
;
             
inherits returns [List<ClassName> inherits] :
  i='inherit' 
  class_name_list
  { if(isOk()) $inherits = $class_name_list.list; }
 | 
  i='inherit' 
  { addParseProblem(new MissingElementParseError(getSourceLocation($i), "class name(s)", "in inherits clause", true)); }
;

queries returns [List<String> queries] :
  'query' query_list  
  { if(isOk()) $queries = $query_list.queries; }
;
         
commands returns [List<String> commands] :
  'command' command_list
  { if(isOk()) $commands = $command_list.commands; }
;

constraints returns [List<String> constraints] :
  'constraint' constraint_list
  { if(isOk()) $constraints = $constraint_list.constraints; }
;


query_list returns [List<String> queries] :
  { $queries = createList(); }
  m1=manifest_textblock 
  { if(isOk()) $queries.add($m1.text); }
  (  (',' m=manifest_textblock 
      { if(isOk()) $queries.add($m.text); } 
     )      
   | m=manifest_textblock 
     { addParseProblem(new MissingElementParseError(getSourceLocation($m.start), "comma", "before additional query item", false)); }
     { if(isOk()) $queries.add($m.text); } 
  )* 
  ','?             
;
            
command_list returns [List<String> commands] :
  { $commands = createList(); }
  m1=manifest_textblock 
  { if(isOk()) $commands.add($m1.text); }
  (  (',' m=manifest_textblock 
      { if(isOk()) $commands.add($m.text); } 
     )
   | m=manifest_textblock 
     { addParseProblem(new MissingElementParseError(getSourceLocation($m.start), "comma", "before additional command item", false)); }
     { if(isOk()) $commands.add($m.text); }
  )* 
  ','?
;
              
constraint_list returns [List<String> constraints] :
  { $constraints = createList(); }
  m1=manifest_textblock 
  { if(isOk()) $constraints.add($m1.text); }
  (  (',' m=manifest_textblock )
   | m=manifest_textblock 
     { addParseProblem(new MissingElementParseError(getSourceLocation($m.start), "comma", "before additional constraint item", false)); }
     { if(isOk()) $constraints.add($m.text); }
  )*
  ','?
;

class_name_list returns [List<ClassName> list] :
  { $list = createList(); }
  c1=class_name 
  { if(isOk()) $list.add($c1.name); }
  (  ( ',' c=class_name 
       { if(isOk()) $list.add($c.name); } 
     )
   | ( c=class_name 
       { if(isOk()) $list.add($c.name); }	
       //TODO warn missing comma									       
     )
  )*
;
                 
cluster_name_list returns [List<String> list] :
  { $list = createList(); }
  c1=cluster_name
  { if(isOk()) $list.add($c1.text); }
  (  ( ',' c=cluster_name
       { if(isOk()) $list.add($c.text); } 
     )
   | ( c=cluster_name 
       { addParseProblem(new MissingElementParseError(getSourceLocation($c.start), "comma", "before additional class name", false)); }
       { if(isOk()) $list.add($c.text); }                           
     )
  )*                  
;

class_or_cluster_name_list returns [List<String> list] :
  { $list = createList(); }
  c1=class_or_bracketed_cluster_name
  { if(isOk()) $list.add($c1.name); }
  ( ',' c=class_or_bracketed_cluster_name
    { if(isOk()) $list.add($c.name); } 
  )*
;

class_or_bracketed_cluster_name returns [String name] :
   class_name
   { if(isOk()) $name = $class_name.name.getName(); }
 | 
   '(' cluster_name ')'
   { if(isOk()) $name = $cluster_name.name; }
;

class_name returns [ClassName name] :
  i=IDENTIFIER
  { if(isOk()) $name = ClassName.mk($i.text, getSLoc($i)); } 
;

/**********************************************/

event_chart returns [EventChart ec] 
@init { boolean incoming = false; boolean outgoing = false; Indexing indexing = null;
        String explanation = null; String part = null; List<EventEntry> eventEntries = null; }
:
  e='event_chart' system_name 
  (  'incoming' { incoming = true; } 
   | 'outgoing' { outgoing = true; }
  )?
  (indexing { if(isOk()) indexing = $indexing.indexing; })?
  (explanation { if(isOk()) explanation = $explanation.explanation; } )?
  (part { if(isOk()) part = $part.part; } )?
  ( ee=event_entries
    { if(isOk()) eventEntries = $ee.entries; }
   |
    { eventEntries = createList(); }
  )
  end='end'
  { if(isOk()) $ec = EventChart.mk($system_name.name, incoming, outgoing, eventEntries, indexing, explanation, part, getSLoc($e,$end)); }
;
             
event_entries returns [List<EventEntry> entries] :
  { $entries = createList(); }
  (event_entry { if(isOk()) $entries.add($event_entry.entry); } )+ 
;
               
event_entry returns [EventEntry entry]
@init { boolean mok=false; boolean cok=false; List<String> ccnl = null; String description = null; Token stop=null; } :
  e='event'
  (  ( m=manifest_textblock 
      {mok=true; if(isOk()) description=$m.text;} 
     )
   |  
   { addParseProblem(new MissingElementParseError(getSourceLocation($e), "event name", "in event entry clause", true)); }
  ) 
  i='involves'
  (  (ccns=class_or_cluster_name_list 
      { cok=true; if(isOk()) ccnl = $ccns.list; }
      { stop = $ccns.stop; } 
     )
   |  
     { addParseProblem(new MissingElementParseError(getSourceLocation($i), "class name list", "in involves clause of event entry", true)); }
     { stop = $i; }
  )
  { if (mok && cok && isOk()) $entry = EventEntry.mk(description, ccnl, getSLoc($e,stop)); }
;

/**********************************************/

scenario_chart returns [ScenarioChart sc] 
@init { Indexing indexing = null; String explanation = null; String part = null; List<ScenarioEntry> entries = null; }
:
  s='scenario_chart' system_name
  (indexing { if(isOk()) indexing = $indexing.indexing; } )?
  (explanation { if(isOk()) explanation = $explanation.explanation; } )?
  (part { if(isOk()) part = $part.part; } )?
  ( scenario_entries { if(isOk()) entries = $scenario_entries.entries; }
   | { if(isOk()) entries = emptyList(); }
    )
  e='end'
  { if(isOk()) $sc = ScenarioChart.mk($system_name.name, entries, indexing, explanation, part, getSLoc($s,$e)); }
;
                
scenario_entries returns [List<ScenarioEntry> entries] :
  { $entries = createList(); }
  (scenario_entry { if(isOk()) $entries.add($scenario_entry.entry); } )+ 
;
                  
scenario_entry returns [ScenarioEntry entry] :
  s='scenario' m=MANIFEST_STRING d=description
  { if(isOk()) $entry =  ScenarioEntry.mk($m.text, $d.description, getSLoc($s,$d.stop)); }
;

/**********************************************/

creation_chart returns [CreationChart cc]
@init { List<CreationEntry> entries = null; Indexing indexing = null; String explanation = null; String part = null; }
:
  start='creation_chart' system_name
  (indexing { if(isOk()) indexing = $indexing.indexing; } )?
  (explanation { if(isOk()) explanation = $explanation.explanation; } )?
  (part { if(isOk()) part = $part.part; } )?
  ( creation_entries { if(isOk()) entries = $creation_entries.entries; }
   | { entries = emptyList(); } )
  end='end' 
  { if(isOk()) $cc = CreationChart.mk($system_name.name, entries, indexing, explanation, part,getSLoc($start,$end)); }
;
                
creation_entries returns [List<CreationEntry> entries] :
  { $entries = createList(); }
  (creation_entry { if(isOk()) $entries.add($creation_entry.entry); } )+
;
                  
creation_entry returns [CreationEntry entry] :
  c='creator' class_name 
  'creates' ccnl=class_or_cluster_name_list
  { if(isOk()) $entry = CreationEntry.mk($class_name.name, $ccnl.list, getSLoc($c,$ccnl.stop)); } 
;

/**********************************************  
 ***   Static Diagrams                      ***
 **********************************************/
 
static_diagram returns [StaticDiagram sd] 
@init { String eid = null; String comment = null; } 
:
  s='static_diagram' 
  (extended_id { if(isOk()) eid=$extended_id.eid; } )?
  comment { comment = $comment.comment; } 
  'component' 
  sb=static_block 
  e='end'
  { if(isOk()) $sd = StaticDiagram.mk($sb.components, eid, comment, getSLoc($s,$e)); }                
;
                
extended_id returns [String eid] :  
   i=IDENTIFIER
   { if(isOk()) $eid = $i.text; } 
 | i=INTEGER
   { if(isOk()) $eid = $i.text; } 
;
             
static_block returns [List<StaticComponent> components] :
  { $components = createList(); }
  (sc=static_component { if(isOk()) $components.add($sc.component); })*
;
             
static_component returns [StaticComponent component] :
   c1=cluster
   { if(isOk()) $component = $c1.cluster; } 
 | c2=clazz 
   { if(isOk()) $component = $c2.clazz; }
 | s=static_relation
   { if(isOk()) $component = $s.relation; } 
;

/**********************************************/

cluster returns [Cluster cluster] 
@init { boolean reused = false; String comment = null; List<StaticComponent> components = null; Token end = null; }
:
  c='cluster' cluster_name { end = $cluster_name.stop; }
  (r='reused' { if(isOk()) reused = true; end = $r; } )? 
  comment { comment = $comment.comment; }   
  (  cc=cluster_components 
     { if(isOk()) components = $cc.components; end = $cc.stop;}
   |
     { components = emptyList(); } 
  )
  { if(isOk()) $cluster = Cluster.mk($cluster_name.name, components, reused, comment, getSLoc($c,end)); }
;
         
cluster_components returns [List<StaticComponent> components] :  
  'component' static_block 'end'
  { if(isOk()) $components = $static_block.components; }
;
                    
clazz returns [Clazz clazz] 
@init { Clazz.Mod mod = null; List<FormalGeneric> generics = null; Token start = null; Token end = null;
        boolean reused = false; boolean persistent = false; boolean interfaced = false; 
        String comment = null; ClassInterface classInterface = null; }
:
  (   r='root'      { mod = Clazz.Mod.ROOT; start = $r; }
    | d='deferred'  { mod = Clazz.Mod.DEFERRED; start = $d; }
    | e='effective' { mod = Clazz.Mod.EFFECTIVE; start = $e; }
    |               { mod = Clazz.Mod.NONE; }
  )
  c='class' 
  { if (start == null) start = $c; }
  cn=class_name
  { end = $cn.stop; }
  (  fg=formal_generics { if(isOk()) generics = $fg.generics; end = $fg.stop; } 
   | { generics = emptyList(); } 
  )
  (ru='reused' { reused = true; end = $ru; } )? 
  (p='persistent' { persistent = true; end = $p; })?   
  (i='interfaced' { interfaced = true; end = $i; })?
  comment { comment = $comment.comment; }
  
  (ci=class_interface { if(isOk()) classInterface = $ci.ci; end = $ci.stop; } )?
  
  { if(isOk()) $clazz = Clazz.mk($cn.name, generics, mod, classInterface, reused, persistent, interfaced, comment, getSLoc(start,end)); }
;

comment returns [String comment] :
  { $comment = lookForCommentBefore(); } 
;
            
static_relation returns [StaticRelation relation] :
   ir=inheritance_relation
   { if(isOk()) $relation = $ir.relation; }
 | cr=client_relation
   { if(isOk()) $relation = $cr.relation; }
;

/**********************************************/

inheritance_relation returns [InheritanceRelation relation] 
@init { Multiplicity multiplicity = null; String semanticLabel = null; Token end = null; }
:
  c=child 'inherit' 
  (a='{' multiplicity b='}'
   { if(isOk()) multiplicity = Multiplicity.mk($multiplicity.num, getSLoc($a,$b)); }
  )? 
  p=parent 
  { end = $p.stop; }
  ( semantic_label
   { if(isOk()) semanticLabel = $semantic_label.label; end = $semantic_label.stop; } 
  )? 
  { if(isOk()) $relation = InheritanceRelation.mk($c.ref, $p.ref, multiplicity, semanticLabel, getSLoc($c.start, end)); }
;
                    
client_relation returns [ClientRelation relation] 
@init { ClientEntityExpression entities = null; TypeMark mark = null; String semanticLabel = null; Token end = null; }
:
  c=client 'client'
  (client_entities { if(isOk()) entities = $client_entities.entities; } )? 
  ( type_mark 
   { if(isOk()) mark = $type_mark.mark; }
   |
   { mark = Constants.NO_TYPE_MARK; }
  )
  s=supplier 
  { end = $supplier.stop; }
  (semantic_label { if(isOk()) semanticLabel = $semantic_label.label; end = $semantic_label.stop; } )?
  { if(isOk()) $relation = ClientRelation.mk($c.ref,$s.ref,entities,mark,semanticLabel,getSLoc($c.start,end)); }
;
                 
client_entities returns [ClientEntityExpression entities] :
  '{' cee=client_entity_expression '}'
  { if(isOk()) $entities = $cee.entities; }
;
                 
client_entity_expression returns [ClientEntityExpression entities] :
   cel=client_entity_list
   { if(isOk()) $entities = ClientEntityList.mk($cel.entities,getSLoc($cel.start,$cel.stop)); } 
 | m=multiplicity
   { if(isOk()) $entities = Multiplicity.mk($m.num, getSLoc($m.start,$m.stop)); } 
;
                          
client_entity_list returns [List<ClientEntity> entities] :
  { $entities = createList(); }
  ce=client_entity
  { if(isOk()) $entities.add($ce.entity); }
  (',' c=client_entity
   { if(isOk()) $entities.add($c.entity); }
  )* 
;
                    
//Conflict here is:
// feature_name can be an IDENTIFIER, and supplier_indirection can also be an IDENTIFIER
//TODO
//client_entity  :    feature_name 
client_entity returns [ClientEntity entity] :
   prefix
 | infix
 | supplier_indirection
   { if(isOk()) $entity = $supplier_indirection.indirection; } 
 | parent_indirection 
   { if(isOk()) $entity = $parent_indirection.indirection; }
;
               
supplier_indirection returns [SupplierIndirection indirection] 
@init{IndirectionFeaturePart part = null; Token start = null; }
:  
  (ifp=indirection_feature_part { start = $ifp.start; } ':')? 
  gi=generic_indirection 
  { if (start==null) start=$gi.start; }
  { if(isOk()) indirection = SupplierIndirection.mk(part, $gi.indirection,getSLoc(start,$gi.stop)); }  
;
                      
indirection_feature_part returns [IndirectionFeaturePart part] :
   feature_name 
   { if(isOk()) $part = $feature_name.name; }
 | indirection_feature_list 
   { if(isOk()) $part = $indirection_feature_list.list; }
;	
                          
indirection_feature_list returns [IndirectionFeatureList list] :
  s='(' fnl=feature_name_list e=')'
  { if(isOk()) $list = IndirectionFeatureList.mk($fnl.list,getSLoc($s,$e)); } 
;
                          
parent_indirection returns [ParentIndirection indirection] :  
  '->' gi=generic_indirection
  { if(isOk()) $indirection = ParentIndirection.mk($gi.indirection,getSLoc($gi.start,$gi.stop)); }
;

/**********************************************/

generic_indirection returns [GenericIndirection indirection] :
//  formal_generic_name 
                       //NB - changed the below... both are IDENTIFIERs
// | 
    ie=indirection_element
    { if(isOk()) $indirection = GenericIndirection.mk($ie.el,getSLoc($ie.start,$ie.stop)); }
;
                     
named_indirection returns [NamedIndirection indirection] :
   cn=class_name '[' il=indirection_list e=']'
   { if(isOk()) $indirection = NamedIndirection.mk($cn.name, $il.list, getSLoc($cn.start,$e)); }
 |
   s='[' indirection_list ']'  
   { addParseProblem(new MissingElementParseError(getSLoc($s), "class name", "before indirection list", true)); }
;
                   
indirection_list returns [List<IndirectionElement> list] :
  { $list = createList(); }
  i1=indirection_element
  { if(isOk()) $list.add($i1.el); } 
  (',' i=indirection_element
       { if(isOk()) $list.add($i.el); }
  )* 
;
                  
indirection_element returns [IndirectionElement el] :   
   t='...'
   { if(isOk()) $el = CompactedIndirectionElementImpl.mk(getSLoc($t)); }
 | named_indirection 
   { if(isOk()) $el = $named_indirection.indirection; }
 | class_name
   { if(isOk()) $el = $class_name.name; }
;

                     
type_mark returns [TypeMark mark] :
   m=':'
   { if(isOk()) $mark = TypeMark.mk(TypeMark.Mark.HASTYPE, null, getSLoc($m)); } 
 | m=':{'
   { if(isOk()) $mark = TypeMark.mk(TypeMark.Mark.AGGREGATE, null, getSLoc($m)); } 
 | sm=shared_mark
   { if(isOk()) $mark = $sm.mark; }             
;
           
shared_mark returns [TypeMark mark] :
  a=':' '(' m=multiplicity b=')'
  { if(isOk()) $mark = TypeMark.mk(TypeMark.Mark.SHAREDMARK, m.num, getSLoc($a, $b)); }
;

/**********************************************/

child returns [StaticRef ref] :
  s=static_ref
  { if(isOk()) $ref = $s.ref; }
;
       
parent returns [StaticRef ref] :
  s=static_ref
  { if(isOk()) $ref = $s.ref; }         
;
        
client returns [StaticRef ref] :
  s=static_ref
  { if(isOk()) $ref = $s.ref; } 
;
        
supplier returns [StaticRef ref] :
  s=static_ref
  { if(isOk()) $ref = $s.ref; }
;
          
static_ref returns [StaticRef ref] :  
   s=static_component_name
   { List<StaticRefPart> empty = emptyList(); if(isOk()) $ref = StaticRef.mk(empty, $s.ref, getSLoc($s.start,$s.stop)); }
 | 
   cp=cluster_prefix s=static_component_name
   { if(isOk()) $ref = StaticRef.mk($cp.prefix, $s.ref, getSLoc($cp.start,$s.stop)); } 
;
            
cluster_prefix returns [List<StaticRefPart> prefix] :
  { $prefix = createList(); }
  c1=cluster_name 
  { if(isOk()) $prefix.add(StaticRefPart.mk($c1.name, getSLoc($c1.start,$c1.stop))); }
  '.' 
  ( c=cluster_name '.'
    { if(isOk()) $prefix.add(StaticRefPart.mk($c.name, getSLoc($c.start,$c.stop))); }
  )*
;
  
//TODO - class_name and cluster_name are both just IDENTIFIERs.              
//static_component_name  :  class_name | cluster_name 
static_component_name returns [StaticRefPart ref] :
  i=IDENTIFIER
  { if(isOk()) $ref = StaticRefPart.mk($i.text, getSLoc($i)); }
;
                       
multiplicity returns [Integer num] :
  i=INTEGER
  { if(isOk()) $num = new Integer($i.text); } 
;
              
semantic_label returns [String label] :
  m=MANIFEST_STRING
  { if(isOk()) $label = $m.text; }
;

/**********************************************  
 ***   Class Interface Description          ***
 **********************************************/

class_interface returns [ClassInterface ci] :
    cisi=class_interface_start_indexing {if(isOk()) $ci=$cisi.ci;}
  | cisp=class_interface_start_inherit {if(isOk()) $ci=$cisp.ci;}
  | cisf=class_interface_start_features {if(isOk()) $ci=$cisf.ci;}
  | cisv=class_interface_start_invariant {if(isOk()) $ci=$cisv.ci;}
;

class_interface_start_indexing returns [ClassInterface ci]
@init { Indexing indexing = null; List<Type> parents = emptyList(); 
        List<Expression> invariant = emptyList(); Token start = null; 
        List<Feature> features = emptyList(); }
:
  indexing { if(isOk()) indexing = $indexing.indexing; start = $indexing.start; } 
  (  pcl=parent_class_list { if(isOk()) parents = $pcl.parents; if (start == null) start = $pcl.start; } )?
  (   features { if(isOk()) features = $features.features; } )?
  (  inv=class_invariant { if(isOk()) invariant = $inv.invariant; } )?
  e='end'
  { if(isOk()) $ci = ClassInterface.mk(features, parents, invariant, indexing, getSLoc(start, $e)); }
;

class_interface_start_inherit returns [ClassInterface ci]
@init { Indexing indexing = null; List<Type> parents = emptyList(); 
        List<Expression> invariant = emptyList(); Token start = null; 
        List<Feature> features = emptyList(); }
:
  pcl=parent_class_list { start = $pcl.start; }
  (   features { if(isOk()) features = $features.features; } )?
  (  inv=class_invariant { if(isOk()) invariant = $inv.invariant; } )?
  e='end'
  { if(isOk()) $ci = ClassInterface.mk(features, $pcl.parents, invariant, indexing, getSLoc(start, $e)); }
;

class_interface_start_features returns [ClassInterface ci]
@init { Indexing indexing = null; List<Type> parents = emptyList(); 
        List<Expression> invariant = emptyList(); Token start = null; }
:
  features { start = $features.start; }
  (  inv=class_invariant { if(isOk()) invariant = $inv.invariant; } )?
  e='end'
  { if(isOk()) $ci = ClassInterface.mk($features.features, parents, invariant, indexing, getSLoc(start, $e)); }
;

class_interface_start_invariant returns [ClassInterface ci]
@init { Indexing indexing = null; List<Type> parents = emptyList(); 
        Token start = null; List<Feature> features = emptyList(); }
:
  inv=class_invariant { start = $inv.start; }
  e='end'
  { if(isOk()) $ci = ClassInterface.mk(features, parents, $inv.invariant, indexing, getSLoc(start, $e)); }
;

class_invariant returns [List<Expression> invariant] :
  'invariant' assertion 
  { if(isOk()) $invariant = $assertion.clauses; }
;
                 
parent_class_list returns [List<Type> parents] :
  { $parents = createList(); }
  'inherit' c1=class_type 
  { if(isOk()) $parents.add($c1.type); } 
  (';' c=class_type 
   { if(isOk()) $parents.add($c.type); } 
  )* 
  ';'? 
 |
  i='inherit' 
  { addParseProblem(new MissingElementParseError(getSourceLocation($i), "class name(s)", "in inherits clause", true)); }
;
                   
features returns [List<Feature> features] :
  { $features = createList(); }
  (feature_clause { if(isOk()) $features.add($feature_clause.feature); } )+
;
          
/**********************************************/

feature_clause returns [Feature feature] 
@init { String comment = null; List<ClassName> selectiveExport = null; }
:
  f='feature' 
  (  se=selective_export { if(isOk()) selectiveExport = $se.exports; } 
   | { selectiveExport = emptyList(); }
  ) 
  comment { comment = $comment.comment; }
  fs=feature_specifications 
  { if(isOk()) $feature = Feature.mk($fs.specs, selectiveExport, comment, getSLoc($f,$fs.stop)); }
;
                
feature_specifications returns [List<FeatureSpecification> specs] :
  { $specs = createList(); }
  (fs=feature_specification { if(isOk()) $specs.add($fs.spec); } )+
;
                        
feature_specification returns [FeatureSpecification spec] 
@init { FeatureSpecification.Modifier modifier = FeatureSpecification.Modifier.NONE; 
        List<FeatureArgument> args = null; HasType hasType = null; Token start = null; Token end = null;
        RenameClause renaming = null; String comment = null; ContractClause contracts = null;}
:
  (  d='deferred'  { modifier = FeatureSpecification.Modifier.DEFERRED; start = $d; } 
   | e='effective' { modifier = FeatureSpecification.Modifier.EFFECTIVE; start = $e; }
   | r='redefined' { modifier = FeatureSpecification.Modifier.REDEFINED; start = $r; }
   |             { modifier = FeatureSpecification.Modifier.NONE; }
  )
  fnl=feature_name_list
  { end=$fnl.stop; if (start==null) start=$fnl.start; }
  (has_type { if(isOk()) hasType = $has_type.htype; end=$has_type.stop; } )?
  (rc=rename_clause { if(isOk()) renaming = $rc.rename; end=$rc.stop; } )?
  comment { comment = $comment.comment; }
  (  fa=feature_arguments
     { if(isOk()) args = $fa.args; end=$fa.stop; }
   | { args = emptyList(); }
  )
  (  cc=contract_clause 
     { if(isOk()) contracts = $cc.contracts; end=$cc.stop; } 
   | { contracts = Constants.EMPTY_CONTRACT; }
  ) 
  { if(isOk()) $spec = FeatureSpecification.mk(modifier, $fnl.list, args, contracts, hasType, renaming, comment, getSLoc(start,end)); }
;
                       
has_type returns [HasType htype] :
  type_mark 
  (  type 
     { if(isOk()) $htype = HasType.mk($type_mark.mark, $type.type, getSLoc($type_mark.start,$type.stop)); }
   | v='Void'
     { if(isOk()) $htype = HasType.mk($type_mark.mark, BONType.voidType(getSLoc($v)), getSLoc($v)); }
  )
;

/**********************************************/

contract_clause returns [ContractClause contracts] :
  cc=contracting_conditions 'end'
  { if(isOk()) $contracts = $cc.contracts; }
;

//NB. Rewritten from precondition | postcondition | pre_and_post                 
contracting_conditions returns [ContractClause contracts] 
@init { List<Expression> postC = null; }
:
  (  (pre=precondition (post=postcondition { if(isOk()) postC = $post.assertions; } )?)
     { if (postC == null && isOk()) $contracts = ContractClause.mk($pre.assertions, Constants.NO_EXPRESSIONS, getSLoc($pre.start,$pre.stop)); 
       else if (isOk()) $contracts = ContractClause.mk($pre.assertions, postC, getSLoc($pre.start,$post.stop)); }  
   | post=postcondition
     { if(isOk()) $contracts = ContractClause.mk(Constants.NO_EXPRESSIONS, $post.assertions, getSLoc($post.start,$post.stop)); }
  )
;

precondition returns [List<Expression> assertions] :
  'require' assertion 
  { if(isOk()) $assertions = $assertion.clauses; }
;
              
postcondition returns [List<Expression> assertions] :
  'ensure' assertion 
  { if(isOk()) $assertions = $assertion.clauses; }
;

/**********************************************/

selective_export returns [List<ClassName> exports] :
  '{' cnl=class_name_list '}'
  { if(isOk()) $exports = $cnl.list; }  
;
                  
feature_name_list returns [List<FeatureName> list] :
  { $list = createList(); }
  f1=feature_name 
  { if(isOk()) $list.add($f1.name); }
  (',' f=feature_name 
   { if(isOk()) $list.add($f.name); } 
  )*
;
                   
feature_name returns [FeatureName name] :
   i=IDENTIFIER
   { if(isOk()) $name = FeatureName.mk($i.text, getSLoc($i)); }
 | prefix 
 | infix 
;
              
rename_clause returns [RenameClause rename] :
  '{' renaming '}'
  { if(isOk()) $rename = $renaming.renaming; }
;
               
renaming returns [RenameClause renaming] :
  s='^' class_name '.' feature_name 
  { if(isOk()) $renaming = RenameClause.mk($class_name.name, $feature_name.name, getSLoc($s,$feature_name.stop)); }
;
          
feature_arguments returns [List<FeatureArgument> args] :
  { $args = createList(); }
  (feature_argument { if(isOk()) $args.addAll($feature_argument.args); } )+ 
;
                   
feature_argument returns [List<FeatureArgument> args] :
  ( '->' | '<-' ) 
  (  
     ( identifier_list ':' t1=type 
       { if(isOk()) { List<String> ids = $identifier_list.list; $args = new ArrayList<FeatureArgument>(ids.size()); for (String id : $identifier_list.list) $args.add(FeatureArgument.mk(id, $t1.type, getSLoc($identifier_list.start, $t1.stop))); } }   
     ) 
   | ( t2=type
       { if(isOk()) { $args = new ArrayList<FeatureArgument>(1); $args.add(FeatureArgument.mk(null, $t2.type, getSLoc($t2.start,$t2.stop))); } }
     ) 
  )
;
                  
identifier_list returns [List<String> list] :
  { $list = createList(); }
  i1=IDENTIFIER
  { if(isOk()) $list.add($i1.text); } 
  (',' i=IDENTIFIER { if(isOk()) $list.add($i.text); } )*
;

//TODO - are these necessary if we do not allow free operators?                 
prefix  :  'prefix' '"' prefix_operator '"'
;
        
infix  :  'infix' '"' infix_operator '"' 
;
       
//TODO - Add free_operator back?
prefix_operator  :  unary
;
//prefix_operator  :  UNARY | free_operator                  

infix_operator  :  
  binary
//  infix_operator  :  binary | free_operator 
;

/**********************************************/

formal_generics returns [List<FormalGeneric> generics] :
  '[' fgl=formal_generic_list ']'
  { if(isOk()) $generics = $fgl.list; } 
;
                 
formal_generic_list returns [List<FormalGeneric> list] :
  { $list = createList(); }
  fg1=formal_generic
  { if(isOk()) $list.add($fg1.generic); }
  (',' fg=formal_generic
   { if(isOk()) $list.add($fg.generic); }
  )* 
;
                     
formal_generic returns [FormalGeneric generic] :
   f=formal_generic_name
   { if(isOk()) $generic = FormalGeneric.mk($f.name, null, getSLoc($f.start,$f.stop)); }
 | f=formal_generic_name '->' ct=class_type 
   { if(isOk()) $generic = FormalGeneric.mk($f.name, $ct.type, getSLoc($f.start, $ct.stop)); }
;
                
formal_generic_name returns [String name] :
  i=IDENTIFIER
  { if(isOk()) $name = $i.text; } 
;
                     
class_type returns [Type type] :  
  c=class_name 
  (  actual_generics
     { if(isOk()) $type = BONType.mk($c.text, $actual_generics.types, $c.text.concat($actual_generics.text), getSLoc($c.start, $actual_generics.stop)); }
    |
     { if(isOk()) $type = BONType.mk($c.text, Constants.EMPTY_TYPE_LIST, $c.text, getSLoc($c.start,$c.stop)); } 
  ) 
;
            
actual_generics returns [List<Type> types] :  
                  '[' type_list ']'
                  { if(isOk()) $types = $type_list.types; }
;
                 
type_list returns [List<Type> types]  :
           t1=type
           { $types = createList(); if(isOk()) $types.add($t1.type); } 
           (',' t=type
           { if(isOk()) $types.add($t.type); }
           )* 
;

//TODO - Conflict - class_type is essentially IDENTIFIER (actual_generics)?
//And formal_generic_name is IDENTIFIER          
//type  :  class_type | formal_generic_name 
type returns [Type type] :  
       i=IDENTIFIER 
       (
        ( actual_generics 
          { String fullText = $actual_generics.text==null? $IDENTIFIER.text : $IDENTIFIER.text.concat($actual_generics.text);
            if(isOk()) $type = BONType.mk($IDENTIFIER.text, $actual_generics.types, fullText, getSLoc($i,$actual_generics.stop)); }
        ) 
        |
        { if(isOk()) $type = BONType.mk($IDENTIFIER.text, Constants.EMPTY_TYPE_LIST, $IDENTIFIER.text,getSLoc($i)); }
       ) 
;

/**********************************************  
 ***   Formal Assertions                    ***
 **********************************************/
//TODO correct this all for use with the new expression grammar

assertion returns [List<Expression> clauses] :
  { $clauses = createList(); }
  a1=assertion_clause
  { if(isOk()) $clauses.add($a1.clause); }
  (';' a=assertion_clause  
   { if(isOk()) $clauses.add($a.clause); }
  )* 
  ';'?
;
           
assertion_clause returns [Expression clause] :
  be=boolean_expression
  { if(isOk()) $clause = $be.exp; }
// | COMMENT 
//TODO - Disallowing until revisiting this part of the grammar, as allowing comments here seems to make no sense
;

//TODO - replace expression here?                  
boolean_expression returns [Expression exp] :
  expression
  { if(isOk()) $exp = $expression.exp; } 
;
            
quantification returns [Quantification quantification] 
@init { Expression restrict = null; }
:
  q=quantifier 
  rexp=range_expression 
  (r=restriction { if(isOk()) restrict = $r.exp; } )? 
  p=proposition
  { if(isOk()) $quantification = Quantification.mk($q.q, $rexp.ranges, restrict, $p.exp, getSLoc($q.start,$p.stop)); } 
;
                
quantifier returns [Quantification.Quantifier q] :
   f='for_all' 
   { if(isOk()) $q = Quantification.Quantifier.FORALL; }
 | e='exists'
   { if(isOk()) $q = Quantification.Quantifier.EXISTS; }
;
            
range_expression returns [List<VariableRange> ranges] :
  { $ranges = createList(); }
  vr1=variable_range 
  { if(isOk()) $ranges.add($vr.range); }
  (';' vr=variable_range
   { if(isOk()) $ranges.add($vr.range); }
  )* 
  ';'? 
;
                  
restriction returns [Expression exp] :
  st='such_that' be=boolean_expression
  { if(isOk()) $exp =  $be.exp; }
;
             
proposition returns [Expression exp] :
  ih='it_holds' be=boolean_expression
  { if(isOk()) $exp = $be.exp; } 
;
             
variable_range returns [VariableRange range] :
   mr=member_range
   { if(isOk()) $range = $mr.range; }
 | tr=type_range 
   { if(isOk()) $range = $tr.range; } 
;
                
member_range returns [MemberRange range] :
  il=identifier_list 'member_of' e=expression
  { if(isOk()) $range = MemberRange.mk($il.list, $e.exp, getSLoc($il.start,$e.stop)); } 
;
              
type_range returns [TypeRange range] :
  il=identifier_list ':' t=type
  { if(isOk()) $range = TypeRange.mk($il.list, $t.type, getSLoc($il.start,$t.stop)); } 
;

/**********************************************/
                               
call_chain returns [List<UnqualifiedCall> calls] :
  { if(isOk()) $calls = createList(); }
  uc1=unqualified_call
  { if(isOk()) $calls.add($uc1.call); }
  ('.' uc=unqualified_call { if(isOk()) $calls.add($uc.call); } )* 
;
            
unqualified_call returns [UnqualifiedCall call] 
@init { List<Expression> args = null; Token end = null;}
:
  i=IDENTIFIER 
  { end = $i; }
  (  aa=actual_arguments
     { if(isOk()) args = $aa.args; end = $aa.stop; }
   | { args = emptyList(); }
  )
  { if(isOk()) $call = UnqualifiedCall.mk($i.text, args, getSLoc($i,end)); } 
;

actual_arguments returns [List<Expression> args] 
:
  '(' 
  (  el=expression_list
     { if(isOk()) $args = $el.list; } 
   | { $args = emptyList(); }
  )
  ')' 
;
              
expression_list returns [List<Expression> list] :
  { $list = createList(); }
  e1=expression 
  { if(isOk()) $list.add($e1.exp); }
  (',' e=expression { if(isOk()) $list.add($e.exp); } )* 
;

/**********************************************/

//enumerated sets are allowed as an expression
//set_expression  :  enumerated_set 
//                 ->
//                 | expression 
//                ;
                
enumerated_set returns [List<EnumerationElement> list] :
  '{' el=enumeration_list '}'
  { if(isOk()) $list = $el.list; } 
;
                
enumeration_list returns [List<EnumerationElement> list] :
  { $list = createList(); }
  el1=enumeration_element
  { if(isOk()) $list.add($el1.el); } 
  (',' el=enumeration_element { if(isOk()) $list.add($el.el); } )*
;
         
enumeration_element returns [EnumerationElement el] :
   e=expression
   { if(isOk()) $el = $e.exp; }  
 | i=interval
   { if(isOk()) $el = $i.interval; }  
;
                     
interval returns [Interval interval]  :
   ii=integer_interval
   { if(isOk()) $interval = $ii.interval; }
 | ci=character_interval
   { if(isOk()) $interval = $ci.interval; } 
;
          
integer_interval returns [IntegerInterval interval] :
  i1=integer_constant '..' i2=integer_constant
  { if(isOk()) $interval = IntegerInterval.mk($i1.value,$i2.value,getSLoc($i1.start,$i2.stop)); } 
;
                  
character_interval returns [CharacterInterval interval] :  
  c1=character_constant '..' c2=character_constant 
  { if(isOk()) $interval = CharacterInterval.mk($c1.value,$c2.value,getSLoc($c1.start,$c2.stop)); }
;

/**********************************************/

constant returns [Constant constant] :
   mc=manifest_constant
   { $constant = $mc.constant; } 
 | c='Current'
   { $constant = KeywordConstant.mk(KeywordConstant.Constant.CURRENT, getSLoc($c)); } 
 | v='Void'
   { $constant = KeywordConstant.mk(KeywordConstant.Constant.VOID, getSLoc($v)); }            
 | v='Result'
   { $constant = KeywordConstant.mk(KeywordConstant.Constant.RESULT, getSLoc($v)); }
;

manifest_constant returns [ManifestConstant constant] :
   bc=boolean_constant
   { $constant = BooleanConstant.mk($bc.value,getSLoc($bc.start,$bc.stop)); } 
 | cc=character_constant
   { $constant = CharacterConstant.mk($cc.value,getSLoc($cc.start,$cc.stop)); } 
 | ic=integer_constant 
   { $constant = IntegerConstant.mk($ic.value,getSLoc($ic.start,$ic.stop)); }
 | rc=real_constant 
   { $constant = RealConstant.mk($rc.value,getSLoc($rc.start,$rc.stop)); }
 | ms=MANIFEST_STRING 
   { $constant = StringConstant.mk($ms.text,getSLoc($ms)); }
 | es=enumerated_set
   { $constant = SetConstant.mk($es.list, getSLoc($es.start,$es.stop)); }
;
                   
sign returns [BinaryExp.Op op] :
  add_sub_op
  { if(isOk()) $op = $add_sub_op.op; }
;
      
boolean_constant returns [Boolean value] :
   'true'
   { $value = true; } 
 | 'false' 
   { $value = false; }
;


//Changed to lexer rule, as we greedily take any character preceded and followed by a '                  
character_constant returns [Character value] :
	cc=CHARACTER_CONSTANT
  { $value = $cc.text.charAt(1); } 
;

CHARACTER_CONSTANT :  '\'' v=. '\''; 


                    
integer_constant returns [Integer value]  
@init { boolean negative = false; }
:
  (sign { if ($sign.op == BinaryExp.Op.SUB) negative = true; })? 
  i=INTEGER
  { $value = new Integer($i.text); if (negative) $value = -$value; } 
;
                  
real_constant returns [Double value] 
@init { boolean negative = false; }
:
  (sign { if ($sign.op == BinaryExp.Op.SUB) negative = true; })?  
  r=REAL 
  { $value = new Double($r.text); if (negative) $value = -$value; }
;

/**********************************************  
 ***   Dynamic Diagrams                     ***
 **********************************************/

dynamic_diagram returns [DynamicDiagram dd] 
@init { String id = null; String comment = null; List<DynamicComponent> components = null; }
:
  s='dynamic_diagram' 
  (eid=extended_id { if(isOk()) id = $eid.eid; } )? 
  comment { comment = $comment.comment; }
  'component' 
  ( db=dynamic_block
    { if(isOk()) components = $db.components; }
   | { components = emptyList(); }
  ) 
  e='end'
  { if(isOk()) $dd = DynamicDiagram.mk(components, id, comment, getSLoc($s,$e)); }
;
                 
dynamic_block returns [List<DynamicComponent> components] :
  { $components = createList(); }
  (dc=dynamic_component { if(isOk()) $components.add($dc.component); } )+ 
;
               
dynamic_component returns [DynamicComponent component] :
   scenario_description
 | object_group 
 | object_stack
 | object
 | message_relation 
; 

/**********************************************/

scenario_description returns [ScenarioDescription description] 
@init { String comment = null; }
:
  s='scenario' scenario_name 
  comment { comment = $comment.comment; }
  'action' 
  la=labelled_actions 
  e='end'
  { if(isOk()) $description = ScenarioDescription.mk($scenario_name.name, $la.actions, comment, getSLoc($s,$e)); }
;
                      
labelled_actions returns [List<LabelledAction> actions] :
  { $actions = createList(); }
  (la=labelled_action { if(isOk()) $actions.add($la.action); } )+ 
;
                  
labelled_action returns [LabelledAction action] :
  al=action_label ad=action_description
  { if(isOk()) $action = LabelledAction.mk($al.label, $ad.description, getSLoc($al.start,$ad.stop)); } 
;
                 
action_label returns [String label] :
  m=MANIFEST_STRING
  { if(isOk()) $label = $m.text; }
;
              
action_description returns [String description] :
  m=manifest_textblock
  { if(isOk()) $description = $m.text; }
;
                    
scenario_name returns [String name] :
  m=manifest_textblock
  { if(isOk()) $name = $m.text; }
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
  comment { comment = $comment.comment; }
  (  gc=group_components
     { if(isOk()) components = $gc.components; }
   | { components = emptyList(); }
  )
  { if(isOk()) $group = ObjectGroup.mk(nameless, $group_name.text, components, comment, getSLoc(start,end)); }
;
              
group_components returns [List<DynamicComponent> components] :
  'component' dynamic_block 'end'
  { if(isOk()) $components = $dynamic_block.components; }
;
                  
object_stack returns [ObjectStack stack] 
@init { String comment = null; Token end = null; }
:
  s='object_stack' 
  n=object_name
  { end = $n.stop; } 
  comment { comment = $comment.comment; }
  { if(isOk()) $stack = ObjectStack.mk($n.name, comment, getSLoc($s,end)); }
;
              
object returns [ObjectInstance object] 
@init { String comment = null; Token end = null; }
:  
  s='object' 
  n=object_name
  { end = $n.stop; } 
  comment { comment = $comment.comment; }
  { if(isOk()) $object = ObjectInstance.mk($n.name, comment, getSLoc($s,end)); } 
;

/**********************************************/

message_relation  :  caller 'calls' receiver (message_label)? 
;
                  
caller  :  dynamic_ref 
;
        
receiver  :  dynamic_ref 
;
          
//TODO - the below change fixes a conflict, and allows the same grammar
//...but we lose some information here as to what the dynamic ref is.
//Can this be fixed at a later point when going over the AST?
//dynamic_ref  :  (group_prefix)* dynamic_component_name 
dynamic_ref  :  extended_id ('.' extended_id)*
;
       
//group_prefix  :  group_name '.'
//              ;

//TODO - similarly this rule matches the same grammar, but will we need to know
// which we're actually matching?
//dynamic_component_name  :   object_name | group_name
dynamic_component_name  :  
   (IDENTIFIER ('.' extended_id)?) 
 | INTEGER
;

object_name returns [ObjectName name] 
@init { String id = null; Token end = null; }
:
  n=class_name 
  { end = $n.stop; }
  ('.' e=extended_id { id = $e.eid; end=$e.stop; } )?
  { if(isOk()) $name = ObjectName.mk($n.name, id, getSLoc($n.start,end)); } 
;
             
group_name returns [String name] :
  e=extended_id
  { if(isOk()) $name = $e.eid; }
;
            
message_label returns [String label] :
  m=MANIFEST_STRING
  { if(isOk()) $label = $m.text; }   
;

/**********************************************  
 ***   Notational Tuning                    ***
 **********************************************/
//TODO - do we want any of this section currently?
notational_tuning :  
   change_string_marks 
 | change_concatenator
 | change_prefix 
;

change_string_marks  :  
  'string_marks' MANIFEST_STRING MANIFEST_STRING 
;
                     
change_concatenator  :
  'concatenator' MANIFEST_STRING 
;
                     
change_prefix  :
  'keyword_prefix' MANIFEST_STRING 
;
    
/**********************************************  
 ***   Expressions                          ***
 **********************************************/

expression returns [Expression exp] :
   e=equivalence_expression
   { if(isOk()) $exp = $e.exp; }  
 | q=quantification
   { if(isOk()) $exp = $q.quantification; }
;

equivalence_expression returns [Expression exp] :
  l=implies_expression
  { if(isOk()) $exp = $l.exp; } 
  ('<->' r=implies_expression
   { if ($r.exp == null) throw new RecognitionException();
     if(isOk()) $exp = BinaryExp.mk(BinaryExp.Op.EQUIV, $exp, $r.exp, getSLoc($exp.getLocation(),$r.exp.getLocation())); }
  )*
;

//Right associative
implies_expression returns [Expression exp] :
  l=and_or_xor_expression
  { if(isOk()) $exp = $l.exp; } 
  ('->' r=implies_expression
   { if ($r.exp == null) throw new RecognitionException();
     if(isOk()) $exp = BinaryExp.mk(BinaryExp.Op.IMPLIES, $exp, $r.exp, getSLoc($exp.getLocation(),$r.exp.getLocation())); }
  )?
;

and_or_xor_expression returns [Expression exp] :
  l=comparison_expression
  { if(isOk()) $exp = $l.exp; } 
  ( op=and_or_xor_op r=comparison_expression
   { if ($r.exp == null) throw new RecognitionException();
     if(isOk()) $exp = BinaryExp.mk($op.op, $exp, $r.exp, getSLoc($exp.getLocation(),$r.exp.getLocation())); }
  )* 
;

comparison_expression returns [Expression exp] :
  l=add_sub_expression
  { if(isOk()) $exp = $l.exp; } 
  (op=comparison_op  r=add_sub_expression
   { if ($r.exp == null) throw new RecognitionException();
     if(isOk()) $exp = BinaryExp.mk($op.op, $exp, $r.exp, getSLoc($exp.getLocation(),$r.exp.getLocation())); 
   }
  )* 
;

add_sub_expression returns [Expression exp] :
  l=mul_div_expression
  { if(isOk()) $exp = $l.exp; } 
  (op=add_sub_op r=mul_div_expression
   { if ($r.exp == null) throw new RecognitionException();
     if(isOk()) $exp = BinaryExp.mk($op.op, $exp, $r.exp, getSLoc($exp.getLocation(),$r.exp.getLocation())); }
  )* 
;

mul_div_expression returns [Expression exp] :
  l=mod_pow_expression
  { if(isOk()) $exp = $l.exp; } 
  (op=mul_div_op r=mod_pow_expression
   { if ($r.exp == null) throw new RecognitionException();
     if(isOk()) $exp = BinaryExp.mk($op.op, $exp, $r.exp, getSLoc($exp.getLocation(),$r.exp.getLocation())); }
  )* 
;

//Right-associative
mod_pow_expression returns [Expression exp] :
  l=lowest_expression
  { if(isOk()) $exp = $l.exp; } 
  (op=mod_pow_op r=mod_pow_expression
   { if ($r.exp == null) throw new RecognitionException();
     if(isOk()) $exp = BinaryExp.mk($op.op, $exp, $r.exp, getSLoc($exp.getLocation(),$r.exp.getLocation())); }
  )? 
;

lowest_expression returns [Expression exp] :
    (constant)=> constant
    ( ('.' cc=call_chain
       { if(isOk()) $exp = CallExp.mk($constant.constant, $cc.calls, getSLoc($constant.start,$cc.stop)); }
      )
     | //Just a constant
      { if(isOk()) $exp = $constant.constant; }  
    )    
 |	unary le=lowest_expression
    { if(isOk()) $exp = UnaryExp.mk($unary.op, $le.exp, getSLoc($unary.start,$le.stop)); }
 | s='(' e=expression ')'  
   ( ('.' cc=call_chain
      { if(isOk()) $exp = CallExp.mk($e.exp, $cc.calls, getSLoc($s,$cc.stop)); }
     )
    | { if(isOk()) $exp = $e.exp; } //Parenthesized expression
   )
 | cc=call_chain
   { if(isOk()) $exp =  CallExp.mk(null, $cc.calls, getSLoc($cc.start,$cc.stop)); }
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


manifest_textblock  
:   
  { //TODO warn when not MANIFEST_STRING where we desire a single block. 
  }
   MANIFEST_STRING 
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
