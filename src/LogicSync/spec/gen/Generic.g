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
    | LPAR atom_list RPAR
    ;

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

COMMENT: '{' .* '}'{$channel=HIDDEN;};
//Identifier
ATOM : ( ALPHANUMERIC | UNDERSCORE | DASH | '\'')*;      
UNDERSCORE:  '_' ;
DASH:  '-';
STAR: '*';
SLASH: '/';
                    
fragment 
ALPHANUMERIC :  ALPHA | DIGIT ;
               
INTEGER  :  (DIGIT)+ ;
         
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
