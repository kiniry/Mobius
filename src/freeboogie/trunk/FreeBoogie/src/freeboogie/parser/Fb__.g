lexer grammar Fb;
@header {
  package freeboogie.parser;
}

T9 : 'type' ;
T10 : 'const' ;
T11 : 'function' ;
T12 : 'axiom' ;
T13 : 'var' ;
T14 : 'procedure' ;
T15 : 'implementation' ;
T16 : ';' ;
T17 : ',' ;
T18 : ':' ;
T19 : '(' ;
T20 : ')' ;
T21 : 'returns' ;
T22 : 'free' ;
T23 : 'requires' ;
T24 : 'modifies' ;
T25 : 'ensures' ;
T26 : '{' ;
T27 : '}' ;
T28 : 'goto' ;
T29 : 'return' ;
T30 : ':=' ;
T31 : 'assert' ;
T32 : 'assume' ;
T33 : 'havoc' ;
T34 : 'call' ;
T35 : '[' ;
T36 : ']' ;
T37 : '<==>' ;
T38 : '==>' ;
T39 : '-' ;
T40 : '!' ;
T41 : '&&' ;
T42 : '||' ;
T43 : '==' ;
T44 : '!=' ;
T45 : '<' ;
T46 : '<=' ;
T47 : '>=' ;
T48 : '>' ;
T49 : '<:' ;
T50 : '+' ;
T51 : '*' ;
T52 : '/' ;
T53 : '%' ;
T54 : 'false' ;
T55 : 'true' ;
T56 : 'null' ;
T57 : 'old' ;
T58 : 'cast' ;
T59 : '::' ;
T60 : 'forall' ;
T61 : 'exists' ;
T62 : 'bool' ;
T63 : 'int' ;
T64 : 'ref' ;
T65 : 'name' ;
T66 : 'any' ;
T67 : 'where' ;

// $ANTLR src "Fb.g" 325
ID:
  ('a'..'z'|'A'..'Z'|'\''|'~'|'#'|'$'|'.'|'?'|'_'|'^') 
  ('a'..'z'|'A'..'Z'|'\''|'~'|'#'|'$'|'.'|'?'|'_'|'^'|'`'|'0'..'9')*
;
	
// $ANTLR src "Fb.g" 330
INT     : 	'0'..'9'+ ;
// $ANTLR src "Fb.g" 331
WS      : 	(' '|'\t'|'\n'|'\r')+ {$channel=HIDDEN;};
// $ANTLR src "Fb.g" 332
COMMENT
    :   '/*' ( options {greedy=false;} : . )* '*/' {$channel=HIDDEN;}
    ;

// $ANTLR src "Fb.g" 336
LINE_COMMENT
    : '//' ~('\n'|'\r')* '\r'? '\n' {$channel=HIDDEN;}
    ;
