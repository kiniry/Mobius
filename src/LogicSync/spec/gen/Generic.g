grammar Generic;


@header {
package mobius.logic.lang.generic.parser; 

import mobius.logic.lang.generic.ast.*;
}

@lexer::header {
package mobius.logic.lang.generic.parser; 
}

@members {
 // No members
}

prog: clause_list EOF;

clause_list: clause clause_list
           |;
clause: DOC
      | ATOM COLON expr
      | ATOM
      ;
      
expr: ATOM
    | LPAR expr expr_list RPAR
    | LPAR FORALL atom_list COMMA expr expr_list RPAR
    ;
expr_list: expr expr_list
         |;

atom_list: ATOM atom_list
         | ATOM
         ;
    



//Lexer part

WHITESPACE  :  (' '|'\n'|'\r'|'\t')+  {$channel=HIDDEN;} 
            ;

LPAR: '('  ;
RPAR: ')' ;
DOC: '[' .* ']'{setText($text.substring(2, $text.length() - 2));};
COLON: ':';
FORALL: 'forall';
COMMA: ',';

COMMENT: '{' .* '}'{$channel=HIDDEN;};
//Identifier
ATOM : ( ALPHANUMERIC | UNDERSCORE | DASH | '\'')*;      
fragment
UNDERSCORE:  '_' ;
fragment
DASH:  '-';

STAR: '*';
SLASH: '/';
                    
fragment 
ALPHANUMERIC :  ALPHA | DIGIT ;
      
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
