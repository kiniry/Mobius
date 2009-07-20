
grammar Coq;

options {
   backtrack=true;
}

@header {
package mobius.logic.lang.coq.parser; 

import mobius.logic.lang.coq.ast.*;
import java.util.LinkedList;
import java.util.Iterator;
}

@lexer::header {
package mobius.logic.lang.coq.parser; 
}


@members {
 // No members
 private Formula getApplication(Formula t) {
   if (t.getNext() == null) {
     return t;
   } 
   else return Application.mk(null, t);
 }
   // really no
     private Formula reverse(Formula first) {
       LinkedList<Formula> l = new LinkedList<Formula>();
       while (first != null) {
         l.addFirst(first);
         first = first.getNext();
       }
       Iterator<Formula> iter = l.iterator();
       Formula f = iter.next();
       first =f;
       while (iter.hasNext()) {
         f.setNext(iter.next());
         f = f.getNext();
       }
       f.setNext(null);
       return first;
     }
}

/**********************************************  
 ##############################################
 ###   Parser...                            ###
 ##############################################
 **********************************************/

prog returns [CoqAst ast]: 
      command_list EOF 
      {$ast = $command_list.ast;};

command_list returns [CoqAst ast]: 
             vernacular tail=command_list
             {$ast = $vernacular.ast;
              $ast.add($tail.ast);}
             |;
  			 
vernacular returns [CoqAst ast]: 
             require {$ast = $require.ast;}
           | open_scope {$ast = $open_scope.ast;}
           | coercion {$ast = $coercion.ast;}
           | lemma {$ast = $lemma.ast;}
           | axiom {$ast = $axiom.ast;}
           | tactic {$ast = $tactic.ast;}
           | hint {$ast = $hint.ast;}
           | definition {$ast = $definition.ast;}
           | inductive {$ast = $inductive.ast;}
           | coqdoc {$ast = $coqdoc.ast;}
           ;

coqdoc returns [CoqAst ast]:
        c=DOC {if ($c.getText().charAt(0) == '*') 
                      $ast = Doc.mk($c.getText().substring(1));
                   else $ast = Comment.mk($c.getText());
        };

coercion returns [CoqAst ast]:
          COERCION fun=NAME COLON t1=NAME SHIFT t2=NAME DOT
          {$ast = Coercion.mk(fun.getText(), t1.getText(), t2.getText());};

require returns [CoqAst ast]: 
        REQUIRE req_type STRING_CONSTANT DOT
           {$ast = Require.mk($STRING_CONSTANT.text, $req_type.t);}
      | REQUIRE req_type NAME DOT
           {$ast = Require.mk($NAME.text, $req_type.t);}
      ;
      
open_scope returns [CoqAst ast]: 
        OPEN SCOPE NAME DOT
        {$ast = OpenScope.mk($NAME.text);}
        ;

axiom returns [CoqAst ast]: 
       ax_wrd NAME type_decl DOT
       {$ast = Axiom.mk($ax_wrd.t, $NAME.text, $type_decl.ast);}
     ;
lemma returns [CoqAst ast]: 
       LEMMA NAME COLON formula DOT proof DOT
       {$ast = Lemma.mk($NAME.text, $formula.f, $proof.txt);}  
     ;

hint returns [CoqAst ast]: 
      HINT IMMEDIATE NAME name_list DOT
      {$name_list.list.addFirst($NAME.getText());
       $ast = Hint.mk(HintType.Immediate, 
                      $name_list.list,
                      "");}
    | HINT RESOLVE NAME name_list DOT
      {$name_list.list.addFirst($NAME.getText());
       $ast = Hint.mk(HintType.Resolve, 
                      $name_list.list,
                      "");}
    | HINT REWRITE n=NAME name_list COLON lib=NAME DOT
      {$name_list.list.addFirst($n.getText());
       $ast = Hint.mk(HintType.Rewrite, 
                      $name_list.list,
                      $lib.text);}
    | HINT REWRITE IMPLIES n=NAME name_list COLON lib=NAME DOT
      {$name_list.list.addFirst($n.getText());
       $ast = Hint.mk(HintType.RewriteBk, 
                      $name_list.list,
                      $lib.text);}
    ;
    
definition returns [CoqAst ast]: 
            DEFINITION NAME type_decl? (DEF formula)? DOT (proof DOT)?
            {$ast = Definition.mk($NAME.text, $type_decl.ast, $formula.f, $proof.text);}
          ;
   
inductive returns [CoqAst ast]: 
            INDUCTIVE NAME type_decl DEF inductive_constr DOT
            {$ast = Inductive.mk($NAME.text, $type_decl.ast, $inductive_constr.list);}
          ;
inductive_constr returns [ConstrList list]: 
            PIPE NAME type_decl l=inductive_constr 
             {$list = $l.list; 
              $list.setFirst(Constructor.mk($list.getFirst(), $NAME.text, $type_decl.ast));
              if($list.getLast() == null) $list.setLast($list.getFirst());
              }
          | {$list = ConstrList.mk(null, null);};


         
type_decl returns [Formula ast]: 
             COLON formula
             {$ast = $formula.f; }
           ;
ax_wrd returns [AxiomType t]: 
        VARIABLE {$t = AxiomType.Variable;} 
      | AXIOM {$t = AxiomType.Axiom;};

req_type returns [ReqType t]: 
       IMPORT {$t = ReqType.Import;} 
     | EXPORT {$t = ReqType.Import;};

          

expr returns [Formula f]: 
             LPAR formula RPAR {$f = $formula.f;}
           | NAME  {$f = Term.mk(null, $NAME.text);}
           | INTEGER {$f = Term.mk(null, $INTEGER.text);}
           | TILD tail=expr  {$f = Application.mk(null, Term.mk($tail.f, "~"));}
           ;
           
expr_list returns [Formula f]: ( tail=expr 
                                   {$tail.f.setNext($f); $f = $tail.f;}
                                )+ 
                             ;
                             
                             
formula returns [Formula f]: 
      first=formula0  IMPLIES tail=formula
           {$f = BinaryTerm.mk(null, Term.mk(null, "->"), $first.f, $tail.f);} 
                          
      | formula0 {$f = $formula0.f;} ;
    
formula0 returns [Formula f]:  
      first=formula1 {$f = $first.f;} 
      (o=op1 tail=formula1 {$f = BinaryTerm.mk(null, $o.t, $f, $tail.f);})*
      ;
      
      
formula1 returns [Formula f]:  
      first=formula2 {$f = $first.f;} 
      (o=op2 tail=formula2 {$f = BinaryTerm.mk(null, $o.t, $f, $tail.f);})* 
      ;
      
      
formula2 returns [Formula f]:  
      first=expr_list {if ($first.f.getNext() != null) {
                            
              	            $f = Application.mk(null, reverse($first.f)); 
              	       }
              	       else
                           $f = $first.f;}
    | FORALL var_decl COMMA tail=formula {$f = Forall.mk(null, $var_decl.list, $tail.f);}
    | FUN var_decl '=>' tail=formula {$f = Fun.mk(null, $var_decl.list, $tail.f);}
    | LCURLY var_decl PIPE tail=formula RCURLY {$f = Exists.mk(null, $var_decl.list.getFirst(), $tail.f);}
    
      ;
      
op: op1 | op2 | IMPLIES;


op1 returns [Term t]:
                    
                    OR  {$t = Term.mk(null, "\\/");}
                   | AND {$t = Term.mk(null, "/\\");} 
                   ;
op2 returns [Term t]: STAR {$t = Term.mk(null, "*");}
                   | COMP_OP {$t = Term.mk(null, $COMP_OP.text);}
                   | ARIT_OP {$t = Term.mk(null, $ARIT_OP.text);}

                   ;
var_decl returns [VariableList list]: 
          LPAR name_list type_decl RPAR decl=var_decl
                    {$list = $decl.list; 
                     for (String var: $name_list.list) {
	                     $list.setFirst(Variable.mk($list.getFirst(), 
	                                                var, $type_decl.ast));
	                 }
	                }
        | name_list type_decl?
                    {$list = VariableList.mk(null, null, null);
                     for (String var: $name_list.list) {
	                     $list.setFirst(Variable.mk($list.getFirst(), 
	                                                var, $type_decl.ast));
	                     if ($list.getTail() == null) {
	                        $list.setTail($list.getFirst());
	                     }
	                 }
	                }
        ;

name_list returns [LinkedList<String> list]: 
        NAME l=name_list 
		{$l.list.addFirst($NAME.text);
		 $list = $l.list;}
      | {$list = new LinkedList<String>();};




tac_expr: tac_expr_smp
        | 'autorewrite' WITH tac_expr_smp
        | 'unfold' tac_name_comma_list tac_hyp_list
        | 'rewrite' tac_name_comma_list tac_hyp_list
        | tac_let
        | tac_set
        ;
        
tac_expr_smp: LPAR tac_list RPAR
        | '[' tac_list PIPE tac_list ']'
        | REPEAT tac_expr
        | 'constr' COLON expr
        | 'try' tac_expr
        | tac_assert
        | tac_match
        | 'autorewrite' WITH tac_expr
        | 'unfold' tac_name_comma_list tac_hyp_list
        | 'rewrite' tac_name_comma_list tac_hyp_list
        | NAME expr*
        ;
tac_name_comma_list: NAME (COMMA NAME)*;

tac_hyp_list: IN STAR
            | IN NAME
            |;
tac_list returns [String tac]: tac_expr (SEMICOLON tac_expr)* {$tac = $text;};
      
tac_let: LET NAME DEF (formula | tac_expr_smp | 
                         'fresh' STRING_CONSTANT) IN tac_list;
                         
                         
tac_set: SET LPAR NAME DEF (formula | tac_expr_smp | 
                         'fresh' STRING_CONSTANT) RPAR IN (NAME+ | STAR);
                         
tac_assert: ASSERT LPAR NAME DEF formula RPAR
          | ASSERT LPAR NAME COLON formula RPAR
          | ASSERT LPAR formula RPAR
          | ASSERT NAME;
tac_match: MATCH ('type' 'of')? NAME WITH tac_match_clause_list END;

tac_match_clause_list: PIPE? tac_match_clause (PIPE tac_match_clause)*;

tac_match_clause: '[' tac_match_goal ']' '=>' tac_list
                | tac_match_formula '=>' tac_list; 
                
tac_match_goal: tac_match_hyp? '|-' tac_match_formula ;
tac_match_hyp: NAME COLON tac_match_formula (COMMA NAME COLON tac_match_formula)*
               | UNDERSCORE;
tac_match_expr:  LPAR tac_match_formula RPAR
               | QUESTION? (NAME | UNDERSCORE);
 
tac_match_formula:        
    | tac_match_expr+ (op tac_match_formula)*
    | TILD tac_match_formula
    ;
    
 tactic returns [CoqAst ast]: 
       LTAC NAME name_list DEF tac_list DOT
       {$ast = Tactic.mk($NAME.text, $name_list.text, $tac_list.tac);}
     ;
     
     
proof returns [String txt]: PROOF DOT proof_content QED 
          {$txt = $text;}; 
proof_content: (tac_list DOT)*;



/**********************************************  
 ##############################################
 ###   Lexer...                             ###
 ##############################################
 **********************************************/ 

WHITESPACE  :  (' '|'\n'|'\r'|'\t')+  {$channel=HIDDEN;} 
            ;

LPAR: '('  ;
RPAR: ')' ;
LCURLY: '{';
RCURLY: '}';

SEMICOLON: ';';

// Operators:

SHIFT: '>->' ;
COMMA: ',';
DOT: '.';
COLON: ':';
DEF: ':=';
UNDERSCORE: '_' ;

COMP_OP: '=' 
       | '!=' 
       | '>' 
       | '<' 
       | '<='
       | '>='
       | '<>'
       | '?='
       ;
ARIT_OP: '+'
       | '-' 
       | '/' 
       ;
STAR: '*';
IMPLIES: '->';

LET: 'let';
SET: 'set';
IN: 'in';
REQUIRE: 'Require';
IMPORT: 'Import' ;
EXPORT: 'Export' ;
OPEN: 'Open' ;
SCOPE: 'Scope' ;
VARIABLE: 'Variable' ;
AXIOM: 'Axiom';
COERCION: 'Coercion' ;

LTAC: 'Ltac';

FORALL: 'forall';

HINT: 'Hint';
IMMEDIATE: 'Immediate';
REWRITE: 'Rewrite';
LEMMA: 'Lemma';
PROOF: 'Proof';
QED: 'Qed';
PIPE: '|';

OR: '\\/';
AND: '/\\';
ASSERT: 'assert';
MATCH: 'match';
WITH: 'with';
END: 'end';
RESOLVE: 'Resolve';
DEFINITION: 'Definition';
REPEAT: 'repeat';
FUN: 'fun';
QUESTION:'?';
INDUCTIVE:'Inductive';
TILD: '~';
EOF:'<EOF>' ;


STRING_CONSTANT : '"' .* '"';

DOC: '(**' .* '*)'{setText($text.substring(3, $text.length() - 2));};
COMMENT: '(*' .* '*)' {$channel=HIDDEN;};
                  

//Identifier name
NAME  : ALPHA ( ALPHANUMERIC | UNDERSCORE | ('-' (ALPHANUMERIC | UNDERSCORE)) | '\'')*
      ;
        



                    
fragment 
ALPHANUMERIC  :  ALPHA | DIGIT 
              ;
               
INTEGER  :  (DIGIT)+ 
         ;
         
REAL  :  DIGIT+ '.' DIGIT+ 
      ;
      
fragment 
DIGIT  :  '0'..'9' 
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
