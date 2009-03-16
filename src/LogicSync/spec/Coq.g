
grammar Coq;
options{
  backtrack=true;
}

@header {
package mobius.logic.lang.coq.parser; 
  
}

@lexer::header {
package mobius.logic.lang.coq.parser; 
}

@lexer::members {
  boolean curliesInJavaMode = false;
}

@members {
  // Nothing now.
}

/**********************************************  
 ##############################################
 ###   Parser...                            ###
 ##############################################
 **********************************************/

prog  : command_list EOF         
      ;
command_list : (vernacular)*
  			 ;
  			 
vernacular : require
           | open_scope
           | tactic
           | axiom
           | hint
           | lemma
           | definition
           | inductive
           | coercion
           ;

coercion : COERCION NAME COLON NAME SHIFT NAME DOT;

require : REQUIRE req_type STRING_CONSTANT DOT
        {System.out.println($STRING_CONSTANT.text);}
        | REQUIRE req_type NAME DOT
        {System.out.println($NAME.text);}
        ;
open_scope: OPEN SCOPE NAME DOT
        {System.out.println($NAME.text);}
        ;

axiom: ax_wrd NAME type_decl DOT
       {System.out.println($NAME.text);}
     ;
lemma: LEMMA NAME COLON formula DOT proof DOT;
tactic: LTAC NAME name_list DEF tac_list DOT
       {System.out.println("Tactic: " + $NAME.text);}
       ;
hint: HINT IMMEDIATE NAME name_list DOT
    | HINT RESOLVE NAME name_list DOT
    | HINT REWRITE (IMPLIES)? NAME name_list COLON NAME DOT;
    
definition: DEFINITION NAME type_decl? DEF formula DOT
          | DEFINITION NAME type_decl DOT proof DOT;
   
inductive: INDUCTIVE NAME type_decl DEF inductive_constr+ DOT;
inductive_constr: PIPE NAME type_decl;

proof: PROOF DOT proof_content QED; 
proof_content: (tac_list DOT)*;
         
type_decl: COLON formula;
ax_wrd: VARIABLE | AXIOM;
req_type : IMPORT | EXPORT;

tac_expr: LPAR tac_list RPAR
        | '[' tac_list PIPE tac_list ']'
        | REPEAT tac_expr
        | 'try' tac_expr
        | tac_assert
        | tac_match
        | tac_let
        | 'autorewrite' WITH tac_expr
        | 'unfold' NAME (',' NAME)* ('in' ('*' | NAME))?
        | 'rewrite' NAME (',' NAME)* ('in' ('*' | NAME))?
        | NAME expr*
        ;
     
tac_list: tac_expr (SEMICOLON tac_expr)*;
      
tac_let: 'let' NAME DEF (formula | 'fresh' STRING_CONSTANT) 'in' tac_list;
tac_assert: ASSERT LPAR NAME DEF formula RPAR
          | ASSERT LPAR NAME COLON formula RPAR
          | ASSERT LPAR formula RPAR;
tac_match: MATCH NAME WITH tac_match_clause+ END;

tac_match_clause: PIPE '[' tac_match_goal ']' '=>' tac_list
                | PIPE tac_match_formula '=>' tac_list; 
                
tac_match_goal: tac_match_hyp '|-' tac_match_formula ;
tac_match_hyp: NAME COLON tac_match_formula (COMMA NAME COLON tac_match_formula)*
               | UNDERSCORE;
tac_match_expr: 
              LPAR tac_match_formula RPAR
              | QUESTION? NAME (QUESTION? NAME)*
              | UNDERSCORE;
 
tac_match_formula: tac_match_expr IMPLIES tac_match_formula
    | tac_match_expr comparison_op tac_match_formula
    | tac_match_expr arit_op tac_match_formula
    | tac_match_expr OR tac_match_formula
    | tac_match_expr AND tac_match_formula
    | TILD tac_match_formula
    | FUN var_decl '=>' tac_match_formula
    | LCURLY var_decl PIPE tac_match_formula RCURLY
    | tac_match_expr
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

name_list: (NAME)*;
      


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

STRING_CONSTANT : '"' .* '"' 
  { /* FIXME */ setText($text.substring(1, $text.length() - 1));};  
COMMENT  :  '(*' .* '*)' { $channel=HIDDEN; }
                    ;


/**********************************************/

//  : DIGIT  ( ALPHANUMERIC | UNDERSCORE | DASH )*
//                   ;

//Identifier name
NAME  : ALPHA ( ALPHANUMERIC | UNDERSCORE | DASH )*
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
