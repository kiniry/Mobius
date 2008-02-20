lexer grammar Tester;
@header {
  package ie.ucd.bon.tests;
}

T13 : '@Test-Location:' ;
T14 : '@Test-name:' ;
T15 : '@Prog-args:' ;
T16 : ',' ;
T17 : '@Location' ;
T18 : '{' ;
T19 : '}' ;
T20 : '@Input' ;
T21 : '@Output' ;
T22 : '<' ;
T23 : '#File:' ;
T24 : '>' ;
T25 : '/' ;
T26 : '.' ;
T27 : '-' ;
T28 : '_' ;
T29 : '..' ;

// $ANTLR src "Tester.g" 85
TESTNAME : '"' (options {greedy=false;} : ~('\n'|'\r'|'"') )* '"'
         ;
         
//testname : string
//         ; 

//Note that file allows any string also
// $ANTLR src "Tester.g" 122
ALPHANUMERIC  : ALPHA | DIGIT
              ;

// $ANTLR src "Tester.g" 125
fragment
ALPHA  : 'A'..'Z' | 'a'..'z'
       ;

// $ANTLR src "Tester.g" 129
fragment
DIGIT  : '0'..'9'
       ;

// $ANTLR src "Tester.g" 133
COMMENT  :  LINE_COMMENT+ { $channel=HIDDEN; }
         ;

// $ANTLR src "Tester.g" 136
fragment 
LINE_COMMENT  :  COMMENT_START (options {greedy=false;} : .)* NEWLINE 
              ;

// $ANTLR src "Tester.g" 140
fragment
COMMENT_START  : '--'
               ;

// $ANTLR src "Tester.g" 144
fragment
NEWLINE  :  '\r'? '\n' 
         ;

// $ANTLR src "Tester.g" 148
WHITESPACE  :  (' '|'\n'|'\r'|'\t')+ {$channel=HIDDEN;}
            ;


