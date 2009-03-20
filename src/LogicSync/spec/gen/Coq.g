
grammar Coq;
options {
  backtrack=true;
}

@header {
package mobius.logic.lang.coq.parser; 

import mobius.logic.lang.coq.ast.*;
import java.util.LinkedList;
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
          // | tactic {$ast = $tactic.ast;}
           | hint {$ast = $hint.ast;}
           | definition {$ast = $definition.ast;}
           | inductive {$ast = $inductive.ast;}
           | coqdoc {$ast = $coqdoc.ast;}
           ;

coqdoc returns [CoqAst ast]:
        c=COMMENT {if ($c.getText().charAt(0) == '*') 
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
       LEMMA NAME COLON formula DOT //proof DOT
       {$ast = Lemma.mk($NAME.text, $formula.f, null/*$proof.txt*/);}  
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
            DEFINITION NAME type_decl? (DEF formula)? DOT //(proof DOT)?
            {$ast = Definition.mk($NAME.text, $type_decl.ast, $formula.f, null /*$proof.txt */);}
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
             LPAR formula RPAR {$f = Application.mk(null, $formula.f);}
           | NAME  {$f = Term.mk(null, $NAME.text);}
           | INTEGER {$f = Term.mk(null, $INTEGER.text);}
           | TILD tail=expr  {$f = Term.mk($tail.f, "~");}
           ;
           
expr_list returns [Formula f]:
           expr l=expr_list {$f = $expr.f;
                             $f.setNext($l.f);}
         | expr {$f = $expr.f;}
         ;
formula returns [Formula f]:
      binary_formula0 {$f = $binary_formula0.f;}
    | not_binary {$f = $not_binary.f;}
    ;

binary_formula0 returns [Formula f]: 
      first=binary_formula1 {$f = $first.f;} 
      (o=op tail=not_binary {$f = BinaryTerm.mk(null, $o.t, $f, $tail.f);})*
    ;
    
binary_formula1 returns [Formula f]: 
      first=expr_list {$f = $first.f;} 
      (o=op tail=not_binary {$f = BinaryTerm.mk(null, $o.t, $f, $tail.f);})*
    ;
not_binary returns [Formula f]: 
     FORALL var_decl COMMA tail=formula {$f = Forall.mk(null, $var_decl.list, $tail.f);}
    | FUN var_decl '=>' tail=formula {$f = Fun.mk(null, $var_decl.list, $tail.f);}
    | LCURLY var_decl PIPE tail=formula RCURLY {$f = Exists.mk(null, $var_decl.list.getFirst(), $tail.f);}
    | expr_list {$f = $expr_list.f;}
    ;
    
op returns [Term t]: logop {$t = $logop.t;}
                   
                   ;

aritop returns [Term t]: 
                     COMP_OP {$t = Term.mk(null, $COMP_OP.text);}
                   | ARIT_OP{$t = Term.mk(null, $ARIT_OP.text);}
                   ;

logop returns [Term t]: IMPLIES {$t = Term.mk(null, "->");}
                   | OR  {$t = Term.mk(null, "\\/");}
                   | AND {$t = Term.mk(null, "/\\");}
                   | aritop {$t = $aritop.t;}
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
      | {$list = new LinkedList();};





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
       | '*' 
       ;

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

/* fragment
WHITECOM:
 WHITESPACE* COMMENT WHITESPACE* {System.out.println($COMMENT.text);};
*/
COMMENT: '(*' .* '*)'{setText($text.substring(2, $text.length() - 2));};

                  

//Identifier name
NAME  : ALPHA ( ALPHANUMERIC | UNDERSCORE | '-' | '\'')*
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
