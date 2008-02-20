lexer grammar BON;
@header {
  package ie.ucd.bon.parser;
}

T186 : 'dictionary' ;
T187 : 'end' ;
T188 : 'class' ;
T189 : 'cluster' ;
T190 : 'system_chart' ;
T191 : 'explanation' ;
T192 : 'indexing' ;
T193 : 'part' ;
T194 : 'description' ;
T195 : ';' ;
T196 : ':' ;
T197 : ',' ;
T198 : 'cluster_chart' ;
T199 : 'class_chart' ;
T200 : 'inherit' ;
T201 : 'query' ;
T202 : 'command' ;
T203 : 'constraint' ;
T204 : 'event_chart' ;
T205 : 'incoming' ;
T206 : 'outgoing' ;
T207 : 'event' ;
T208 : 'involves' ;
T209 : 'scenario_chart' ;
T210 : 'scenario' ;
T211 : 'creation_chart' ;
T212 : 'creator' ;
T213 : 'creates' ;
T214 : 'static_diagram' ;
T215 : 'component' ;
T216 : 'reused' ;
T217 : 'root' ;
T218 : 'deferred' ;
T219 : 'effective' ;
T220 : 'persistent' ;
T221 : 'interfaced' ;
T222 : '{' ;
T223 : '}' ;
T224 : 'client' ;
T225 : '(' ;
T226 : ')' ;
T227 : '->' ;
T228 : '[' ;
T229 : ']' ;
T230 : '...' ;
T231 : ':{' ;
T232 : '.' ;
T233 : 'invariant' ;
T234 : 'feature' ;
T235 : 'redefined' ;
T236 : 'require' ;
T237 : 'ensure' ;
T238 : '^' ;
T239 : 'prefix' ;
T240 : '"' ;
T241 : 'infix' ;
T242 : 'for_all' ;
T243 : 'exists' ;
T244 : 'such_that' ;
T245 : 'it_holds' ;
T246 : 'member_of' ;
T247 : '..' ;
T248 : 'Current' ;
T249 : 'Void' ;
T250 : 'true' ;
T251 : 'false' ;
T252 : 'dynamic_diagram' ;
T253 : 'action' ;
T254 : 'nameless' ;
T255 : 'object_group' ;
T256 : 'object_stack' ;
T257 : 'object' ;
T258 : 'calls' ;
T259 : 'string_marks' ;
T260 : 'concatenator' ;
T261 : 'keyword_prefix' ;
T262 : '<->' ;
T263 : '+' ;
T264 : '-' ;
T265 : 'and' ;
T266 : 'or' ;
T267 : 'xor' ;
T268 : 'delta' ;
T269 : 'old' ;
T270 : 'not' ;
T271 : '<' ;
T272 : '>' ;
T273 : '<=' ;
T274 : '>=' ;
T275 : '=' ;
T276 : '/=' ;
T277 : '*' ;
T278 : '/' ;
T279 : '\\' ;

// $ANTLR src "BON.g" 1622
CHARACTER_CONSTANT  :  '\'' . '\'' 
                    ;


                    
// $ANTLR src "BON.g" 1938
/**********************************************  
 ***   Strings                              ***
 **********************************************/

//fragment
//CONTINUED_STRING :  '\\' NEWLINE (options {greedy=false;} : ~('"'|'\\') )*
//                    ;


MANIFEST_STRING : '"' 
                  (options {greedy=false;} : ~('\n'|'\r'|'"'|'\\') )*  
                  '"'
                ;

//MANIFEST_TEXTBLOCK :   '"' 
//                       (options {greedy=false;} : ~('\n'|'\r'|'"'|'\\') )* 
//                       ('\\' NEWLINE (options {greedy=false;} : ~('"'|'\\') )* )*
//                       '"'                       
//                   ;

// $ANTLR src "BON.g" 1958
MANIFEST_TEXTBLOCK_START  : '"' (options {greedy=false;} : ~('\n'|'\r'|'"'|'\\') )+ '\\' (' '|'\t')* NEWLINE
           								;

// $ANTLR src "BON.g" 1961
MANIFEST_TEXTBLOCK_MIDDLE  : '\\' (options {greedy=false;} : ~('"'|'\\') )+ '\\' (' '|'\t')* NEWLINE
            							 ;

// $ANTLR src "BON.g" 1964
MANIFEST_TEXTBLOCK_END  : '\\' (options {greedy=false;} : ~('"'|'\\') )+ '"'
         								;


// $ANTLR src "BON.g" 1972
COMMENT  :  LINE_COMMENT+ { $channel=HIDDEN; }
         ;

// $ANTLR src "BON.g" 1975
fragment 
LINE_COMMENT  :  COMMENT_START (options {greedy=false;} : .)* NEWLINE 
              ;

// $ANTLR src "BON.g" 1979
fragment
COMMENT_START  : '--'
               ;

// $ANTLR src "BON.g" 1983
fragment
NEWLINE  :  '\r'? '\n' 
         ;

// $ANTLR src "BON.g" 1987
/**********************************************  
 ***   Numbers                              ***
 **********************************************/

INTEGER  :  (DIGIT)+ 
         ;
         
// $ANTLR src "BON.g" 1994
REAL  :  DIGIT+ '.' DIGIT+ 
      ;
      
// $ANTLR src "BON.g" 1997
fragment 
DIGIT  :  '0'..'9' 
       ;

// $ANTLR src "BON.g" 2055
MOD_POW_OP  :  '\\\\' 
             | '^' 
             ;

               
// $ANTLR src "BON.g" 2060
/**********************************************  
 ***   Identifiers                          ***
 **********************************************/
/* From the book:
   the identifier construct is defined as a sequence of alphanumeric -
   characters including underscore. an identifier must begin with an
   alphanumeric character and must not end with an underscore (whose
   purpose really is to mimic word separation). letter case is not
   significant, but using consistent style rules is important. */
       
IDENTIFIER  : ALPHA (ALPHANUMERIC_OR_UNDERSCORE* ALPHANUMERIC)? 
            ;



// $ANTLR src "BON.g" 2075
fragment 
ALPHANUMERIC_OR_UNDERSCORE  : ALPHANUMERIC | UNDERSCORE 
                            ;
                                     
// $ANTLR src "BON.g" 2079
fragment 
UNDERSCORE  :  '_' 
            ;
                    
// $ANTLR src "BON.g" 2083
fragment 
ALPHANUMERIC  :  ALPHA | DIGIT 
              ;
                       
// $ANTLR src "BON.g" 2087
fragment 
ALPHA  : LOWER | UPPER 
       ;
                
// $ANTLR src "BON.g" 2091
fragment 
LOWER  : 'a'..'z' 
       ;
                
// $ANTLR src "BON.g" 2095
fragment 
UPPER  : 'A'..'Z' 
       ;

// $ANTLR src "BON.g" 2099
/**********************************************  
 ***   Whitespace                           ***
 **********************************************/
 
WHITESPACE  :  (' '|'\n'|'\r'|'\t')+ {$channel=HIDDEN;}
            ;
