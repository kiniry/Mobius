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
T18 : 'unique' ;
T19 : ':' ;
T20 : '(' ;
T21 : ')' ;
T22 : 'returns' ;
T23 : 'free' ;
T24 : 'requires' ;
T25 : 'modifies' ;
T26 : 'ensures' ;
T27 : '{' ;
T28 : '}' ;
T29 : 'goto' ;
T30 : 'return' ;
T31 : ':=' ;
T32 : 'assert' ;
T33 : 'assume' ;
T34 : 'havoc' ;
T35 : 'call' ;
T36 : '[' ;
T37 : ']' ;
T38 : '<==>' ;
T39 : '==>' ;
T40 : '-' ;
T41 : '!' ;
T42 : '&&' ;
T43 : '||' ;
T44 : '==' ;
T45 : '!=' ;
T46 : '<' ;
T47 : '<=' ;
T48 : '>=' ;
T49 : '>' ;
T50 : '<:' ;
T51 : '+' ;
T52 : '*' ;
T53 : '/' ;
T54 : '%' ;
T55 : 'false' ;
T56 : 'true' ;
T57 : 'null' ;
T58 : 'old' ;
T59 : 'cast' ;
T60 : '::' ;
T61 : 'forall' ;
T62 : 'exists' ;
T63 : 'bool' ;
T64 : 'int' ;
T65 : 'ref' ;
T66 : 'name' ;
T67 : 'any' ;
T68 : 'where' ;

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
