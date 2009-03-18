
grammar Coq;
options{
  backtrack=true;
}

@header {
package mobius.logic.lang.coq.parser; 

import mobius.logic.lang.coq.ast.*;
}

@lexer::header {
package mobius.logic.lang.coq.parser; 
}

@lexer::members {
  boolean curliesInJavaMode = false;
}

@members {
 // No members
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
       {$ast = Axiom.mk($NAME.text);}
     ;
lemma returns [CoqAst ast]: 
       LEMMA NAME COLON formula DOT proof DOT
       {$ast = Lemma.mk($NAME.text);}  
     ;
tactic returns [CoqAst ast]: 
       LTAC NAME name_list DEF tac_list DOT
       {$ast = Tactic.mk($NAME.text);}
     ;
hint returns [CoqAst ast]: 
      HINT IMMEDIATE NAME name_list DOT
      {$ast = Hint.mk(HintType.Immediate, 
                      $NAME.getText() + " " + $name_list.text,
                      "");}
    | HINT RESOLVE NAME name_list DOT
      {$ast = Hint.mk(HintType.Resolve, 
                      $NAME.getText() + " " + $name_list.text,
                      "");}
    | HINT REWRITE n=NAME name_list COLON lib=NAME DOT
      {$ast = Hint.mk(HintType.Rewrite, 
                      $n.getText() + " " + $name_list.text,
                      $lib.text);}
    | HINT REWRITE IMPLIES n=NAME name_list COLON lib=NAME DOT
      {$ast = Hint.mk(HintType.RewriteBk, 
                      $n.getText() + " " + $name_list.text,
                      $lib.text);}
    ;
    
definition returns [CoqAst ast]: 
            DEFINITION NAME type_decl? DEF formula DOT
            {$ast = Definition.mk($NAME.text);}
          | DEFINITION NAME type_decl DOT proof DOT
            {$ast = Definition.mk($NAME.text);}
          ;
   
inductive returns [CoqAst ast]: 
            INDUCTIVE NAME type_decl DEF inductive_constr+ DOT
            {$ast = Inductive.mk($NAME.text);}
          ;
inductive_constr: PIPE NAME type_decl;

proof: PROOF DOT proof_content QED; 
proof_content: (tac_list DOT)*;
         
type_decl: COLON formula;
ax_wrd: VARIABLE | AXIOM;

req_type returns [ReqType t]: 
       IMPORT {$t = ReqType.Import;} 
     | EXPORT {$t = ReqType.Import;};

tac_expr: LPAR tac_list RPAR
        | '[' tac_list PIPE tac_list ']'
        | REPEAT tac_expr
        | 'constr' COLON expr
        | 'try' tac_expr
        | tac_assert
        | tac_match
        | tac_let
        | tac_set
        | 'autorewrite' WITH tac_expr
        | 'unfold' NAME (',' NAME)* ('in' ('*' | NAME))?
        | 'rewrite' NAME (',' NAME)* ('in' ('*' | NAME))?
        | NAME expr*
        ;
     
tac_list: tac_expr (SEMICOLON tac_expr)*;
      
tac_let: 'let' NAME DEF (formula | tac_expr | 
                         'fresh' STRING_CONSTANT) 'in' tac_list;
tac_set: 'set' LPAR NAME DEF (formula | tac_expr | 
                         'fresh' STRING_CONSTANT) RPAR 'in' (NAME+ | '*');
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
    | tac_match_expr IMPLIES tac_match_formula
    | tac_match_expr comparison_op tac_match_formula
    | tac_match_expr arit_op tac_match_formula
    | tac_match_expr OR tac_match_formula
    | tac_match_expr AND tac_match_formula
    | TILD tac_match_formula
    | FUN var_decl '=>' tac_match_formula
    | LCURLY var_decl PIPE tac_match_formula RCURLY
    | tac_match_expr tac_match_formula
    ;
          

expr: LPAR formula RPAR 
           | NAME expr*
           | INTEGER;
           
formula: expr IMPLIES formula
    | expr comparison_op formula
    | expr arit_op formula
    | expr OR formula
    | expr AND formula
    | TILD formula
    | FORALL var_decl COMMA formula
    | FUN var_decl '=>' formula
    | LCURLY var_decl PIPE formula RCURLY
    | expr
    ;
    

     
var_decl: LPAR name_list type_decl RPAR var_decl
        | name_list type_decl
        | name_list;

name_list returns [String text]: 
        NAME l=name_list 
		{$text = $NAME.text + " " + $l.text;}
      | {$text = "";};


/**********************************************/

comparison_op  :    '='
                  | '!='
                  | '>'
                  | '<'
                  | '<='
                  | '>='
                  | '<>'
                  | '?='
               ;
arit_op: '+'
       | '-'
       | '/'
       | '*'
       ;

/**********************************************  
 ##############################################
 ###   Lexer...                             ###
 ##############################################
 **********************************************/ 

LPAR: '(';
RPAR: ')';
LCURLY: '{';
RCURLY: '}';

REQUIRE: 'Require';
IMPORT: 'Import';
EXPORT: 'Export';
OPEN: 'Open';
SCOPE: 'Scope';
VARIABLE: 'Variable';
AXIOM: 'Axiom';
COERCION: 'Coercion';
SHIFT: '>->';
DOT: '.';
COLON: ':';
DEF: ':=';
LTAC: 'Ltac';
SEMICOLON: ';';
IMPLIES: '->';
COMMA: ',';
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
EOF:'<EOF>';

STRING_CONSTANT : '"' .* '"';
COMMENT: '(*' .* '*)' {setText($text.substring(2, $text.length() - 2));};

/**********************************************/

//  : DIGIT  ( ALPHANUMERIC | UNDERSCORE | DASH )*
//                   ;

//Identifier name
NAME  : ALPHA ( ALPHANUMERIC | UNDERSCORE | DASH | '\'')*
      ;
        
UNDERSCORE  :  '_' 
            ;

DASH  :  '-'
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

/**********************************************  
 ***   Whitespace                           ***
 **********************************************/
 
WHITESPACE  :  (' '|'\n'|'\r'|'\t')+ {$channel=HIDDEN;}
            ;
