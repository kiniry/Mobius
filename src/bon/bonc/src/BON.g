/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
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
       |
         i=indexing bs=bon_specification EOF
         { $bonSource = BonSourceFile.mk($bs.spec_els, $indexing.indexing, getSLoc($i.start, $bs.stop)); }
       |
         e=EOF 
         { addParseProblem(new MissingElementParseError(getSourceLocation($e), "at least one specification entry", "in source file", true)); }
         { $bonSource = BonSourceFile.mk(Constants.NO_SPEC_ELEMS, null, getSLoc($e)); }
       | 
         indexing e=EOF 
         { addParseProblem(new MissingElementParseError(getSourceLocation($e), "at least one specification entry", "in source file", true)); }
         { $bonSource = BonSourceFile.mk(Constants.NO_SPEC_ELEMS, $i.indexing, getSLoc($i.start,$i.stop)); }
;

/**********************************************  
 ***   BON Specification                    ***
 **********************************************/

bon_specification returns [List<SpecificationElement> spec_els] :
  { $spec_els = createList(); }
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
        List<DictionaryEntry> entries = createList(); }
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
;
			
dictionary_entry returns [DictionaryEntry entry] :  
  c='class' class_name 
  'cluster' cluster_name_list 
  description 
  { $entry = DictionaryEntry.mk($class_name.text, $cluster_name_list.list, $description.text, getSLoc($c, $description.stop)); }
;

/**********************************************/

system_chart returns [ClusterChart sc] 
@init { Indexing index = null; String expl = null; String p = null; 
        List<ClusterEntry> entries = null; }
:
  s='system_chart' 
  system_name 
  (indexing { index = $indexing.indexing; } )?
  (explanation { expl = $explanation.explanation; } )? 
  (part { p = $part.part; } )? 
  (  ce=cluster_entries 
     { entries = $ce.entries; } 
   | { entries = emptyList(); }
  ) 
  e='end'
  { $sc = ClusterChart.mk($system_name.name, true, Constants.NO_CLASS_ENTRIES, entries, index, expl, p, getSLoc($s,$e)); }
;

explanation returns [String explanation] :
  e='explanation' manifest_textblock
  { $explanation = $e.text; }
 |
  e='explanation' 
  { addParseProblem(new MissingElementParseError(getSourceLocation($e), "explanation text", "after 'explanation'", false)); }
;

indexing returns [Indexing indexing] :  
   i='indexing' index_list
   { $indexing = Indexing.mk($index_list.list, getSLoc($i,$index_list.stop)); } 
 |
   i='indexing' 
   { addParseProblem(new MissingElementParseError(getSourceLocation($i), "indexing entries", "after 'indexing'", false)); }
   { $indexing = Indexing.mk(Constants.NO_INDEX_CLAUSES, getSLoc($i)); }
;

part returns [String part] :
    p='part' m=MANIFEST_STRING
    { $part = $m.text; }
  |
    p='part' 
    { addParseProblem(new MissingElementParseError(getSourceLocation($p), "part text", "after 'part'", false)); }
    { $part = ""; }
;

description returns [String description] :
  d='description' m=manifest_textblock 
  { $description = $m.text; }
;

cluster_entries returns [List<ClusterEntry> entries] :
  { $entries = createList(); }
  (cluster_entry { $entries.add($cluster_entry.ce); } )+
;
                 
cluster_entry returns [ClusterEntry ce] :
  c='cluster' cluster_name description
  { $ce = ClusterEntry.mk($cluster_name.text, $description.text, getSLoc($c, $description.stop)); } 
;
               
system_name returns [String name] :
  i=IDENTIFIER
  { $name = $i.text; } 
;

/**********************************************/

index_list returns [List<IndexClause> list] :  
               { $list = createList(); }
               i1=index_clause 
               { $list.add($i1.clause); }
               (  (';' i2=index_clause)
                  { $list.add($i2.clause); }
                | i=index_clause { addParseProblem(new MissingElementParseError(getSourceLocation($i.start), "semi-colon", "before additional index clause", false)); }
                  { $list.add($i.clause); }
               )* 
               ';'? //Final semi-colon optional
;
            
index_clause returns [IndexClause clause] :  
  i=IDENTIFIER ':' index_term_list 
  { $clause = IndexClause.mk($i.text, $index_term_list.strings, getSLoc($i, $index_term_list.stop)); }
 |
  i=IDENTIFIER ':' 
  { addParseProblem(new MissingElementParseError(getSourceLocation($i), "index term(s)", "in index clause", true)); }
;
                
index_term_list returns [List<String> strings] :
  { $strings = createList(); }
  i1=index_string 
  { $strings.add($i1.text); }
  (',' i=index_string
   { $strings.add($i.text); }
  )* 
;
                 
index_string returns [String s] :
  m=MANIFEST_STRING
  { $s = $m.text; }    
;

/**********************************************/

cluster_chart returns [ClusterChart cc] 
@init { List<ClassEntry> classes = null; List<ClusterEntry> clusters = null; 
        Indexing indexing = null; String explanation = null; String part = null;  }
:
  c='cluster_chart' cluster_name 
  (i=indexing { indexing = $i.indexing; } )? 
  (explanation { explanation = $explanation.explanation; } )? 
  (part { part = $part.part; } )? 
  (  ce=class_entries { classes = $ce.entries; }
   | { classes = emptyList(); } 
  ) 
  (  cle=cluster_entries { clusters = $cle.entries; } 
   | { clusters = emptyList(); }
  ) 
  e='end'
  { $cc = ClusterChart.mk($cluster_name.name, false, classes, clusters, indexing, explanation, part, getSLoc($c,$e)); }
;
               
class_entries returns [List<ClassEntry> entries] :
  { $entries = createList(); }
  (class_entry { $entries.add($class_entry.entry); } )+ 
;
               
class_entry returns [ClassEntry entry] :
  c='class' class_name
  description
  { $entry = ClassEntry.mk($class_name.text, $description.text, getSLoc($c, $description.stop)); }
;
             
cluster_name returns [String name] :
  i=IDENTIFIER
  { $name = $i.text; } 
;

/**********************************************/

class_chart returns [ClassChart cc] 
@init { Indexing indexing = null; String explanation = null; String part = null;
        List<String> inherits = null; List<String> commands = null; List<String> queries = null; 
        List<String> constraints = null;  }
:
  c='class_chart' class_name 
  (i=indexing { indexing = $i.indexing; } )? 
  (explanation { explanation = $explanation.explanation; } )? 
  (part { part = $part.part; } )? 
  (  inherits
     { inherits = $inherits.inherits; }
   | { inherits = emptyList(); } 
  )
  (  queries
     { queries = $queries.queries; }
   | { queries = emptyList(); }
  )
  (  commands
     { commands = $commands.commands; }
   | { commands = emptyList(); }
  ) 
  (  constraints
     { constraints = $constraints.constraints; }
   | { constraints = emptyList(); }
  ) 
  e='end'
  { $cc = ClassChart.mk($class_name.name, inherits, queries, commands, constraints, indexing, explanation, part, getSLoc($c,$e)); }
;
             
inherits returns [List<String> inherits] :
  i='inherit' 
  class_name_list
  { $inherits = $class_name_list.list; }
 | 
  i='inherit' 
  { addParseProblem(new MissingElementParseError(getSourceLocation($i), "class name(s)", "in inherits clause", true)); }
;

queries returns [List<String> queries] :
  q='query' query_list  
  { $queries = $query_list.queries; }
;
         
commands returns [List<String> commands] :
  c='command' command_list
  { $commands = $command_list.commands; }
;

constraints returns [List<String> constraints] :
  c='constraint' constraint_list
  { $constraints = $constraint_list.constraints; }
;


query_list returns [List<String> queries] :
  { $queries = createList(); }
  m1=manifest_textblock 
  { $queries.add($m1.text); }
  (  (',' m=manifest_textblock 
      { $queries.add($m.text); } 
     )      
   | m=manifest_textblock 
     { addParseProblem(new MissingElementParseError(getSourceLocation($m.start), "comma", "before additional query item", false)); }
     { $queries.add($m.text); } 
  )* 
  ','?             
;
            
command_list returns [List<String> commands] :
  { $commands = createList(); }
  m1=manifest_textblock 
  { $commands.add($m1.text); }
  (  (',' m=manifest_textblock 
      { $commands.add($m.text); } 
     )
   | m=manifest_textblock 
     { addParseProblem(new MissingElementParseError(getSourceLocation($m.start), "comma", "before additional command item", false)); }
     { $commands.add($m.text); }
  )* 
  ','?
;
              
constraint_list returns [List<String> constraints] :
  { $constraints = createList(); }
  m1=manifest_textblock 
  { $constraints.add($m1.text); }
  (  (',' m=manifest_textblock )
   | m=manifest_textblock 
     { addParseProblem(new MissingElementParseError(getSourceLocation($m.start), "comma", "before additional constraint item", false)); }
     { $constraints.add($m.text); }
  )*
  ','?
;

class_name_list returns [List<String> list] :
  { $list = createList(); }
  c1=class_name 
  { $list.add($c1.text); }
  (  ( ',' c=class_name 
       { $list.add($c.text); } 
     )
   | ( c=class_name 
       { $list.add($c.text); }										       
     )
  )*
;
                 
cluster_name_list returns [List<String> list] :
  { $list = createList(); }
  c1=cluster_name
  (  ( ',' c=cluster_name
       { $list.add($c.text); } 
     )
   | ( c=cluster_name 
       { addParseProblem(new MissingElementParseError(getSourceLocation($c.start), "comma", "before additional class name", false)); }
       { $list.add($c.text); }                           
     )
  )*                  
;

class_or_cluster_name_list returns [List<String> list] :
  { $list = createList(); }
  c1=class_or_bracketed_cluster_name
  { $list.add($c1.name); }
  ( ',' c=class_or_bracketed_cluster_name
    { $list.add($c.name); } 
  )*
;

class_or_bracketed_cluster_name returns [String name] :
   class_name
   { $name = $class_name.name; }
 | 
   '(' cluster_name ')'
   { $name = $cluster_name.name; }
;

class_name returns [String name] :
  i=IDENTIFIER
  { $name = $i.text; } 
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
;
             
event_entries returns [List<EventEntry> entries] :
  { $entries = createList(); }
  (event_entry { $entries.add($event_entry.entry); } )+ 
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
;

/**********************************************/

scenario_chart returns [ScenarioChart sc] :
  s='scenario_chart' system_name
  (indexing)?
  (explanation)?
  (part)?
  (scenario_entries)?
  'end'
;
                
scenario_entries returns [List<ScenarioEntry> entries] :
  { $entries = createList(); }
  (scenario_entry { $entries.add($scenario_entry.entry); } )+ 
;
                  
scenario_entry returns [ScenarioEntry entry] :
  s='scenario' m=MANIFEST_STRING d=description
  { $entry =  ScenarioEntry.mk($m.text, $d.description, getSLoc($s,$d.stop)); }
;

/**********************************************/

creation_chart returns [CreationChart cc] :
  c='creation_chart' system_name
  (indexing)?
  (explanation)?
  (part)?
  (creation_entries)?
  'end' 
;
                
creation_entries returns [List<CreationEntry> entries] :
  { $entries = createList(); }
  (creation_entry { $entries.add($creation_entry.entry); } )+
;
                  
creation_entry returns [CreationEntry entry] :
  c='creator' class_name 
  'creates' ccnl=class_or_cluster_name_list
  { $entry = CreationEntry.mk($class_name.name, $ccnl.list, getSLoc($c,$ccnl.stop)); } 
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
;
                
extended_id returns [String eid] :  
   i=IDENTIFIER
   { $eid = $i.text; } 
 | i=INTEGER
   { $eid = $i.text; } 
;
             
static_block returns [List<StaticComponent> components] :
  { $components = createList(); }
  (sc=static_component { $components.add($sc.component); })*
;
             
static_component returns [StaticComponent component] :
   c1=cluster
   { $component = $c1.cluster; } 
 | c2=clazz 
   { $component = $c2.clazz; }
 | s=static_relation
   { $component = $s.relation; } 
;

/**********************************************/

cluster returns [Cluster cluster] 
@init { boolean reused = false; String comment = null; List<StaticComponent> components = null; Token end = null; }
:
  c='cluster' cluster_name { end = $cluster_name.stop; }
  (r='reused' { reused = true; end = $r; } )? 
  (co=COMMENT { comment = $co.text; end = $co;} )?    
  (  cc=cluster_components 
     { components = $cc.components; end = $cc.stop;}
   |
     { components = emptyList(); } 
  )
  { $cluster = Cluster.mk($cluster_name.name, components, reused, comment, getSLoc($c,end)); }
;
         
cluster_components returns [List<StaticComponent> components] :  
  c='component' static_block 'end'
  { $components = $static_block.components; }
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
  (  fg=formal_generics { generics = $fg.generics; end = $fg.stop; } 
   | { generics = emptyList(); } 
  )
  (ru='reused' { reused = true; end = $ru; } )? 
  (p='persistent' { persistent = true; end = $p; })?   
  (i='interfaced' { interfaced = true; end = $i; })? 
  (co=COMMENT { comment = $co.text; end = $co; } )?
  (ci=class_interface { classInterface = $ci.ci; end = $ci.stop; } )? 
  { $clazz = Clazz.mk($cn.name, generics, mod, classInterface, reused, persistent, interfaced, comment, getSLoc(start,end)); }
;
            
static_relation returns [StaticRelation relation] :
   ir=inheritance_relation
   { $relation = $ir.relation; }
 | cr=client_relation
   { $relation = $cr.relation; }
;

/**********************************************/

inheritance_relation returns [InheritanceRelation relation] 
@init { Multiplicity multiplicity = null; String semanticLabel = null; Token end = null; }
:
  c=child 'inherit' 
  (a='{' multiplicity b='}'
   { multiplicity = Multiplicity.mk($multiplicity.num, getSLoc($a,$b)); }
  )? 
  p=parent 
  { end = $p.stop; }
  ( semantic_label
   { semanticLabel = $semantic_label.label; end = $semantic_label.stop; } 
  )? 
  { $relation = InheritanceRelation.mk($c.type, $p.type, multiplicity, semanticLabel, getSLoc($c.start, end)); }
;
                    
client_relation returns [ClientRelation relation] 
@init { ClientEntityExpression entities = null; TypeMark mark = null; String semanticLabel = null; Token end = null; }
:
  c=client 'client'
  (client_entities { entities = $client_entities.entities; } )? 
  ( type_mark 
   { mark = $type_mark.mark; }
   |
   { mark = Constants.NO_TYPE_MARK; }
  )
  s=supplier 
  { end = $supplier.stop; }
  (semantic_label { semanticLabel = $semantic_label.label; end = $semantic_label.stop; } )?
  { $relation = ClientRelation.mk($c.type,$s.type,entities,mark,semanticLabel,getSLoc($c.start,end)); }
;
                 
client_entities returns [ClientEntityExpression entities] :
  a='{' cee=client_entity_expression b='}'
  { $entities = $cee.entities; }
;
                 
client_entity_expression returns [ClientEntityExpression entities] :
   cel=client_entity_list
   { $entities = ClientEntityList.mk($cel.entities,getSLoc($cel.start,$cel.stop)); } 
 | m=multiplicity
   { $entities = Multiplicity.mk($m.num, getSLoc($m.start,$m.stop)); } 
;
                          
client_entity_list returns [List<ClientEntity> entities] :
  { $entities = createList(); }
  ce=client_entity
  { $entities.add($ce.entity); }
  (',' c=client_entity
   { $entities.add($c.entity); }
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
 | parent_indirection 
;
               
supplier_indirection  :  
  (indirection_feature_part ':')? generic_indirection 
;
                      
indirection_feature_part  :
   feature_name 
 | indirection_feature_list 
;	
                          
indirection_feature_list  :
  '(' feature_name_list ')' 
;
                          
parent_indirection  :  
  '->' generic_indirection
;

/**********************************************/

generic_indirection  :
//  formal_generic_name 
                       //NB - changed the below... both are IDENTIFIERs
// | 
    indirection_element
;
                     
named_indirection :
   class_name '[' indirection_list ']'
 |
   s='[' indirection_list ']'  
   { addParseProblem(new MissingElementParseError(getSLoc($s), "class name", "before indirection list", true)); }
;
                   
indirection_list  :
  indirection_element (',' indirection_element)* 
;
                  
indirection_element  :   
   '...'
 | named_indirection 
 | class_name
;

                     
type_mark returns [TypeMark mark] :
   m=':'
   { $mark = TypeMark.mk(TypeMark.Mark.HASTYPE, null, getSLoc($m)); } 
 | m=':{'
   { $mark = TypeMark.mk(TypeMark.Mark.AGGREGATE, null, getSLoc($m)); } 
 | sm=shared_mark
   { $mark = $sm.mark; }             
;
           
shared_mark returns [TypeMark mark] :
  a=':' '(' m=multiplicity b=')'
  { $mark = TypeMark.mk(TypeMark.Mark.SHAREDMARK, m.num, getSLoc($a, $b)); }
;

/**********************************************/

child returns [BONType type] :
  s=static_ref
  { $type = $s.type; }
;
       
parent returns [BONType type] :
  s=static_ref
  { $type = $s.type; }         
;
        
client returns [BONType type] :
  s=static_ref
  { $type = $s.type; } 
;
        
supplier returns [BONType type] :
  s=static_ref
  { $type = $s.type; }
;
          
static_ref returns [BONType type] :  
   s=static_component_name
   { $type = $s.type; }
 | 
   c=cluster_prefix s=static_component_name
   { $type = $s.type; } 
;
            
cluster_prefix  :
  c1=cluster_name '.' (cluster_name '.')*
;
  
//TODO - class_name and cluster_name are both just IDENTIFIERs.              
//static_component_name  :  class_name | cluster_name 
static_component_name returns [BONType type] :
  i=IDENTIFIER
  { $type = BONType.mk($i.text, null, $i.text, getSLoc($i)); }
;
                       
multiplicity returns [Integer num] :
  i=INTEGER
  { $num = new Integer($i.text); } 
;
              
semantic_label returns [String label] :
  m=MANIFEST_STRING
  { $label = $m.text; }
;

/**********************************************  
 ***   Class Interface Description          ***
 **********************************************/

class_interface returns [ClassInterface ci] 
@init { Indexing indexing = null; List<BONType> parents = null; List<Expression> invariant = null; Token start = null; }
:
  (indexing { indexing = $indexing.indexing; start = $indexing.start; } )?
  (  pcl=parent_class_list { parents = $pcl.parents; if (start == null) start = $pcl.start; } 
   | { parents = emptyList(); }
  )
  features
  { if (start == null) start = $features.start; }
  (  inv=class_invariant { invariant = $inv.invariant; } 
   | { invariant = emptyList(); }
  )
  e='end'
  { $ci = ClassInterface.mk($features.features, parents, invariant, indexing, getSLoc(start, $e)); }
;
                    
class_invariant returns [List<Expression> invariant] :
  'invariant' assertion 
  { $invariant = $assertion.clauses; }
;
                 
parent_class_list returns [List<BONType> parents] :
  { $parents = createList(); }
  'inherit' c1=class_type 
  { $parents.add($c1.type); } 
  (';' c=class_type 
   { $parents.add($c.type); } 
  )* 
  ';'? 
 |
  i='inherit' 
  { addParseProblem(new MissingElementParseError(getSourceLocation($i), "class name(s)", "in inherits clause", true)); }
;
                   
features returns [List<Feature> features] :
  { $features = createList(); }
  (feature_clause { $features.add($feature_clause.feature); } )+
;
          
/**********************************************/

feature_clause returns [Feature feature] 
@init { String comment = null; List<String> selectiveExport = null; }
:
  f='feature' 
  (  se=selective_export { selectiveExport = $se.exports; } 
   | { selectiveExport = emptyList(); }
  ) 
  (c=COMMENT { comment = $c.text; } )? 
  fs=feature_specifications 
  { $feature = Feature.mk($fs.specs, selectiveExport, comment, getSLoc($f,$fs.stop)); }
;
                
feature_specifications returns [List<FeatureSpecification> specs] :
  { $specs = createList(); }
  (fs=feature_specification { $specs.add($fs.spec); } )+
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
  (has_type { hasType = $has_type.htype; end=$has_type.stop; } )?
  (rc=rename_clause { renaming = $rc.rename; end=$rc.stop; } )?
  (c=COMMENT { comment = $c.text; end=$c; } )?
  (  fa=feature_arguments
     { args = $fa.args; end=$fa.stop; }
   | { args = emptyList(); }
  )
  (  cc=contract_clause 
     { contracts = $cc.contracts; end=$cc.stop; } 
   | { contracts = Constants.EMPTY_CONTRACT; }
  ) 
  { $spec = FeatureSpecification.mk(modifier, $fnl.list, args, contracts, hasType, renaming, comment, getSLoc(start,end)); }
;
                       
has_type returns [HasType htype] :
  type_mark type 
  { $htype = HasType.mk($type_mark.mark, $type.type, getSLoc($type_mark.start,$type.stop)); }
;

/**********************************************/

contract_clause returns [ContractClause contracts] :
  cc=contracting_conditions 'end'
  { $contracts = $cc.contracts; }
;

//NB. Rewritten from precondition | postcondition | pre_and_post                 
contracting_conditions returns [ContractClause contracts] 
@init { List<Expression> postC = null; }
:
  (  (pre=precondition (post=postcondition { postC = $post.assertions; } )?)
     { if (postC == null) $contracts = ContractClause.mk($pre.assertions, Constants.NO_EXPRESSIONS, getSLoc($pre.start,$pre.stop)); 
       else $contracts = ContractClause.mk($pre.assertions, postC, getSLoc($pre.start,$post.stop)); }  
   | post=postcondition
     { $contracts = ContractClause.mk(Constants.NO_EXPRESSIONS, $post.assertions, getSLoc($post.start,$post.stop)); }
  )
;

precondition returns [List<Expression> assertions] :
  'require' assertion 
  { $assertions = $assertion.clauses; }
;
              
postcondition returns [List<Expression> assertions] :
  'ensure' assertion 
  { $assertions = $assertion.clauses; }
;

/**********************************************/

selective_export returns [List<String> exports] :
  '{' cnl=class_name_list '}'
  { $exports = $cnl.list; }  
;
                  
feature_name_list returns [List<String> list] :
  { $list = createList(); }
  f1=feature_name 
  { $list.add($f1.name); }
  (',' f=feature_name 
   { $list.add($f.name); } 
  )*
;
                   
feature_name returns [String name] :
   i=IDENTIFIER
   { $name = $i.text; }
 | prefix 
 | infix 
;
              
rename_clause returns [RenameClause rename] :
  '{' renaming '}'
  { $rename = $renaming.renaming; }
;
               
renaming returns [RenameClause renaming] :
  s='^' class_name '.' feature_name 
  { $renaming = RenameClause.mk($class_name.name, $feature_name.name, getSLoc($s,$feature_name.stop)); }
;
          
feature_arguments returns [List<FeatureArgument> args] :
  { $args = createList(); }
  (feature_argument { $args.addAll($feature_argument.args); } )+ 
;
                   
feature_argument returns [List<FeatureArgument> args] :
  '->' 
  (  
     ( identifier_list ':' t1=type 
       { List<String> ids = $identifier_list.list; $args = new ArrayList<FeatureArgument>(ids.size()); for (String id : $identifier_list.list) $args.add(FeatureArgument.mk(id, $t1.type, getSLoc($identifier_list.start, $t1.stop))); }   
     ) 
   | ( t2=type
       { $args = new ArrayList<FeatureArgument>(1); $args.add(FeatureArgument.mk(null, $t2.type, getSLoc($t2.start,$t2.stop))); }
     ) 
  )
;
                  
identifier_list returns [List<String> list] :
  { $list = createList(); }
  i1=IDENTIFIER
  { $list.add($i1.text); } 
  (',' i=IDENTIFIER { $list.add($i.text); } )*
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
  { $generics = $fgl.list; } 
;
                 
formal_generic_list returns [List<FormalGeneric> list] :
  { $list = createList(); }
  fg1=formal_generic
  { $list.add($fg1.generic); }
  (',' fg=formal_generic
   { $list.add($fg.generic); }
  )* 
;
                     
formal_generic returns [FormalGeneric generic] :
   f=formal_generic_name
   { $generic = FormalGeneric.mk($f.name, null, getSLoc($f.start,$f.stop)); }
 | f=formal_generic_name '->' ct=class_type 
   { $generic = FormalGeneric.mk($f.name, $ct.type, getSLoc($f.start, $ct.stop)); }
;
                
formal_generic_name returns [String name] :
  i=IDENTIFIER
  { $name = $i.text; } 
;
                     
class_type returns [BONType type] :  
  c=class_name 
  (  actual_generics
     { $type = BONType.mk($c.text, $actual_generics.types, $c.text.concat($actual_generics.text), getSLoc($c.start, $actual_generics.stop)); }
    |
     { $type = BONType.mk($c.text, null, $c.text, getSLoc($c.start,$c.stop)); } 
  ) 
;
            
actual_generics returns [List<BONType> types] :  
                  '[' type_list ']'
                  { $types = $type_list.types; }
;
                 
type_list returns [List<BONType> types]  :
           t1=type
           { $types = createList(); $types.add($t1.type); } 
           (',' t=type
           { $types.add($t.type); }
           )* 
;

//TODO - Conflict - class_type is essentially IDENTIFIER (actual_generics)?
//And formal_generic_name is IDENTIFIER          
//type  :  class_type | formal_generic_name 
type returns [BONType type] :  
       i=IDENTIFIER 
       (
        ( actual_generics 
          { $type = BONType.mk($IDENTIFIER.text, $actual_generics.types, $IDENTIFIER.text.concat($actual_generics.text), getSLoc($i,$actual_generics.stop)); }
        ) 
        |
        { $type = BONType.mk($IDENTIFIER.text, null, $IDENTIFIER.text,getSLoc($i)); }
       ) 
;

/**********************************************  
 ***   Formal Assertions                    ***
 **********************************************/
//TODO correct this all for use with the new expression grammar

assertion returns [List<Expression> clauses] :
  { $clauses = createList(); }
  a1=assertion_clause
  { $clauses.add($a1.clause); }
  (';' a=assertion_clause  
   { $clauses.add($a.clause); }
  )* 
  ';'?
;
           
assertion_clause returns [Expression clause] :
  be=boolean_expression
  { $clause = $be.exp; }
// | COMMENT 
//TODO - Disallowing until revisiting this part of the grammar, as allowing comments here seems to make no sense
;

//TODO - replace expression here?                  
boolean_expression returns [Expression exp] :
  expression
  { $exp = $expression.exp; } 
;
            
quantification returns [Quantification quantification] 
@init { Expression restrict = null; }
:
  q=quantifier 
  rexp=range_expression 
  (r=restriction { restrict = $r.exp; } )? 
  p=proposition
  { $quantification = Quantification.mk($q.q, $rexp.ranges, restrict, $p.exp, getSLoc($q.start,$p.stop)); } 
;
                
quantifier returns [Quantification.Quantifier q] :
   f='for_all' 
   { $q = Quantification.Quantifier.FORALL; }
 | e='exists'
   { $q = Quantification.Quantifier.EXISTS; }
;
            
range_expression returns [List<VariableRange> ranges] :
  { $ranges = createList(); }
  vr1=variable_range 
  { $ranges.add($vr.range); }
  (';' vr=variable_range
   { $ranges.add($vr.range); }
  )* 
  ';'? 
;
                  
restriction returns [Expression exp] :
  st='such_that' be=boolean_expression
  { $exp =  $be.exp; }
;
             
proposition returns [Expression exp] :
  ih='it_holds' be=boolean_expression
  { $exp = $be.exp; } 
;
             
variable_range returns [VariableRange range] :
   mr=member_range
   { $range = $mr.range; }
 | tr=type_range 
   { $range = $tr.range; } 
;
                
member_range returns [MemberRange range] :
  il=identifier_list 'member_of' e=expression
  { $range = MemberRange.mk($il.list, $e.exp, getSLoc($il.start,$e.stop)); } 
;
              
type_range returns [TypeRange range] :
  il=identifier_list ':' t=type
  { $range = TypeRange.mk($il.list, $t.type, getSLoc($il.start,$t.stop)); } 
;

/**********************************************/

//Not used...
//call  :  ('(' expression ')' '.')? call_chain 
//      ;
                               
call_chain returns [List<UnqualifiedCall> calls] :
  { $calls = createList(); }
  uc1=unqualified_call
  { $calls.add($uc1.call); }
  ('.' uc=unqualified_call { $calls.add($uc.call); } )* 
;
            
unqualified_call returns [UnqualifiedCall call] 
@init { List<Expression> args = null; Token end = null;}
:
  i=IDENTIFIER 
  { end = $i; }
  (  aa=actual_arguments
     { args = $aa.args; end = $aa.stop; }
   | { args = emptyList(); }
  )
  { $call = UnqualifiedCall.mk($i.text, args, getSLoc($i,end)); } 
;
                  
actual_arguments returns [List<Expression> args] 
:
  '(' 
  (  el=expression_list
     { $args = $el.list; } 
   | { $args = emptyList(); }
  )
  ')' 
;
              
expression_list returns [List<Expression> list] :
  { $list = createList(); }
  e1=expression 
  { $list.add($e1.exp); }
  (',' e=expression { $list.add($e.exp); } )* 
;

/**********************************************/

//enumerated sets are allowed as an expression
//set_expression  :  enumerated_set 
//                 ->
//                 | expression 
//                ;
                
enumerated_set returns [List<EnumerationElement> list] :
  '{' el=enumeration_list '}'
  { $list = $el.list; } 
;
                
enumeration_list returns [List<EnumerationElement> list] :
  { $list = createList(); }
  el1=enumeration_element
  { $list.add($el1.el); } 
  (',' el=enumeration_element { $list.add($el.el); } )*
;
         
enumeration_element returns [EnumerationElement el] :
   e=expression
   { $el = $e.exp; }  
 | i=interval
   { $el = $i.interval; }  
;
                     
interval returns [Interval interval]  :
   ii=integer_interval
   { $interval = $ii.interval; }
 | ci=character_interval
   { $interval = $ci.interval; } 
;
          
integer_interval returns [IntegerInterval interval] :
  i1=integer_constant '..' i2=integer_constant
  { $interval = IntegerInterval.mk($i1.value,$i2.value,getSLoc($i1.start,$i2.stop)); } 
;
                  
character_interval returns [CharacterInterval interval] :  
  c1=character_constant '..' c2=character_constant 
  { $interval = CharacterInterval.mk($c1.value,$c2.value,getSLoc($c1.start,$c2.stop)); }
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
  { $op = $add_sub_op.op; }
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
  (eid=extended_id { id = $eid.eid; } )? 
  (c=COMMENT { comment = $c.text; } )?
  'component' 
  ( db=dynamic_block
    { components = $db.components; }
   | { components = emptyList(); }
  ) 
  e='end'
  { $dd = DynamicDiagram.mk(components, id, comment, getSLoc($s,$e)); }
;
                 
dynamic_block returns [List<DynamicComponent> components] :
  { $components = createList(); }
  (dc=dynamic_component { $components.add($dc.component); } )+ 
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
  (c=COMMENT { comment = $c.text; } )?
  'action' 
  la=labelled_actions 
  e='end'
  { $description = ScenarioDescription.mk($scenario_name.name, $la.actions, comment, getSLoc($s,$c)); }
;
                      
labelled_actions returns [List<LabelledAction> actions] :
  { $actions = createList(); }
  (la=labelled_action { $actions.add($la.action); } )+ 
;
                  
labelled_action returns [LabelledAction action] :
  al=action_label ad=action_description
  { $action = LabelledAction.mk($al.label, $ad.description, getSLoc($al.start,$ad.stop)); } 
;
                 
action_label returns [String label] :
  m=MANIFEST_STRING
  { $label = $m.text; }
;
              
action_description returns [String description] :
  m=manifest_textblock
  { $description = $m.text; }
;
                    
scenario_name returns [String name] :
  m=manifest_textblock
  { $name = $m.text; }
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
   | { components = emptyList(); }
  )
  { $group = ObjectGroup.mk(nameless, $group_name.text, components, comment, getSLoc(start,end)); }
;
              
group_components returns [List<DynamicComponent> components] :
  'component' dynamic_block 'end'
  { $components = $dynamic_block.components; }
;
                  
object_stack returns [ObjectStack stack] 
@init { String comment = null; Token end = null; }
:
  s='object_stack' 
  n=object_name
  { end = $n.stop; } 
  (c=COMMENT { comment = $c.text; end = $c; } )?
  { $stack = ObjectStack.mk($n.name, comment, getSLoc($s,end)); }
;
              
object returns [ObjectInstance object] 
@init { String comment = null; Token end = null; }
:  
  s='object' 
  n=object_name
  { end = $n.stop; } 
  (c=COMMENT { comment = $c.text; end = $c; } )?
  { $object = ObjectInstance.mk($n.name, comment, getSLoc($s,end)); } 
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
  { $name = ObjectName.mk($n.name, id, getSLoc($n.start,end)); } 
;
             
group_name returns [String name] :
  e=extended_id
  { $name = $e.eid; }
;
            
message_label returns [String label] :
  m=MANIFEST_STRING
  { $label = $m.text; }   
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
   { $exp = $e.exp; }  
 | q=quantification
   { $exp = $q.quantification; }
;

equivalence_expression returns [Expression exp] :
  l=implies_expression
  { $exp = $l.exp; } 
  ('<->' r=implies_expression
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
  { $exp = $l.exp; } 
  (op=and_or_xor_op r=comparison_expression
   { $exp = BinaryExp.mk($op.op, $exp, $r.exp, getSLoc($exp.getLocation(),$r.exp.getLocation())); }
  )* 
;

comparison_expression returns [Expression exp] :
  l=add_sub_expression
  { $exp = $l.exp; } 
  (op=comparison_op  r=add_sub_expression
   { $exp = BinaryExp.mk($op.op, $exp, $r.exp, getSLoc($exp.getLocation(),$r.exp.getLocation())); }
  )* 
;

add_sub_expression returns [Expression exp] :
  l=mul_div_expression
  { $exp = $l.exp; } 
  (op=add_sub_op r=mul_div_expression
   { $exp = BinaryExp.mk($op.op, $exp, $r.exp, getSLoc($exp.getLocation(),$r.exp.getLocation())); }
  )* 
;

mul_div_expression returns [Expression exp] :
  l=mod_pow_expression
  { $exp = $l.exp; } 
  (op=mul_div_op r=mod_pow_expression
   { $exp = BinaryExp.mk($op.op, $exp, $r.exp, getSLoc($exp.getLocation(),$r.exp.getLocation())); }
  )* 
;

//Right-associative
mod_pow_expression returns [Expression exp] :
  l=lowest_expression
  { $exp = $l.exp; } 
  (op=mod_pow_op r=mod_pow_expression
   { $exp = BinaryExp.mk($op.op, $exp, $r.exp, getSLoc($exp.getLocation(),$r.exp.getLocation())); }
  )? 
;

lowest_expression returns [Expression exp] :
    (constant)=> constant
    { $exp = $constant.constant; }
 |	unary le=lowest_expression
    { $exp = UnaryExp.mk($unary.op, $le.exp, getSLoc($unary.start,$le.stop)); }
 | s='(' e=expression ')'  
   ( ('.' cc=call_chain
      { $exp = CallExp.mk($e.exp, $cc.calls, getSLoc($s,$cc.stop)); }
     )
    | { $exp = $e.exp; } //Parenthesized expression
   )
 | cc=call_chain
   { $exp =  CallExp.mk(null, $cc.calls, getSLoc($cc.start,$cc.stop)); }
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
