
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
command_list : vernacular command_list
             | ;
vernacular : require
           | open_scope
           | tactic
           | axiom
           | hint
           | lemma
           ;

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
lemma: LEMMA NAME COLON expr DOT proof DOT;
tactic: LTAC NAME name_list DEF tac_list DOT
       {System.out.println("Tactic: " + $NAME.text);}
       ;
hint: HINT IMMEDIATE NAME name_list DOT
    | HINT REWRITE NAME name_list COLON NAME DOT;
    
    
proof: PROOF DOT proof_content QED; 
proof_content: tac_list DOT proof_content
             |;
         
type_decl: COLON expr;
ax_wrd: VARIABLE | AXIOM;
req_type : IMPORT | EXPORT;

tac_list: tac_expr SEMICOLON tac_list
        | tac_expr;
        
tac_expr: '[' tac_list PIPE tac_list ']'
        | tac_assert
        | NAME expr;
      
tac_assert: ASSERT LPAR NAME DEF expr RPAR
          | ASSERT LPAR NAME COLON expr RPAR
          | ASSERT LPAR expr RPAR;
          
expr: LPAR expr RPAR
    | name_list IMPLIES expr
    | name_list comparison_op expr
    | FORALL var_decl COMMA expr
    | name_list;
    

     
var_decl: LPAR name_list type_decl RPAR var_decl
        | name_list type_decl
        | name_list;

name_list: NAME name_list
         |;
      


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


/**********************************************  
 ##############################################
 ###   Lexer...                             ###
 ##############################################
 **********************************************/ 

REQUIRE: 'Require';
IMPORT: 'Import';
EXPORT: 'Export';
OPEN: 'Open';
SCOPE: 'Scope';
VARIABLE: 'Variable';
AXIOM: 'Axiom';
DOT: '.';
COLON: ':';
DEF: ':=';
LTAC: 'Ltac';
SEMICOLON: ';';
IMPLIES: '->';
COMMA: ',';
FORALL: 'forall';
LPAR: '(';
RPAR: ')';
HINT: 'Hint';
IMMEDIATE: 'Immediate';
REWRITE: 'Rewrite';
LEMMA: 'Lemma';
PROOF: 'Proof';
QED: 'Qed';
PIPE: '|';
ASSERT: 'assert';

STRING_CONSTANT : '"' .* '"' 
  { /* FIXME */ setText($text.substring(1, $text.length() - 1));};  
COMMENT  :  '(*' .* '*)' { $channel=HIDDEN; }
                    ;





fragment
NEWLINE  :  '\r'? '\n' 
         ;

/**********************************************/

//  : DIGIT  ( ALPHANUMERIC | UNDERSCORE | DASH )*
//                   ;

//Identifier name
NAME  : ALPHA ( ALPHANUMERIC | UNDERSCORE | DASH )*
      ;
                                    
fragment 
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
