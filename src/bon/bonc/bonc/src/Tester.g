/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
 
grammar Tester;

options {
  superClass=AbstractTesterParser;
}

@members {
    private TestCase currentTestCase;
    private String testsDir;
    private String testLocation;
    private String currentDir;
    private int testNumber = 1;

  private String fileString(String fileName) {
    if (currentDir == null) {
      return testsDir + testLocation + fileName;
    } else {
      return testsDir + testLocation + currentDir + fileName;
    }
  }
  
  public void setTestsDir(String dir) {
  	testsDir = dir;
  }
}

@header {
  package ie.ucd.bon.tests;
  
  import ie.ucd.bon.tests.testcase.TestCase;
  import ie.ucd.bon.tests.testcase.TestOutput;  
}

@lexer::header {
/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.tests;
}

@lexer::members {
  boolean curliesMode = false;
}

testGrammar : testLocation
              ( test )+
            ;

testLocation : '@Test-Location:' directory { testLocation = $directory.text; }
             ;
            
test : { currentTestCase = new TestCase(testNumber++); }
       ('@Test-name:' TESTNAME { currentTestCase.setTestName($TESTNAME.text); } )?
       (PROG_ARGS b=UNCHECKED_CODE_BLOCK { currentTestCase.setProgramArguments($b.text); } )?
       LOCATION			 
       '{' directory '}'
       { currentTestCase.setLocation(testsDir + testLocation + $directory.text); }
       '@Input'  
       '{' inputs '}' 
       ( '@Output' 
         '{' outputs? '}' )?
       { addTestCase(currentTestCase); }
     ;
      
inputs : (f1=file      { currentTestCase.addInputFile($f1.text); } )?
         (',' f=file  { currentTestCase.addInputFile($f.text);  }  )*
       ;
       
outputs : output (',' output)*
        ;

output : '<'
         { TestOutput output = new TestOutput(); } 
         error            { output.setErrorType($error.text); }
         (',' (   ( extraparam  { output.addExtraParam($extraparam.text); } )
                | ( '#File:' file   { output.addExtraParam(fileString($file.text)); } )
              )
         )* 
         '>'
         { currentTestCase.addOutput(output); }
       ;

error : javastring
      ;

TESTNAME : '"' (options {greedy=false;} : ~('\n'|'\r'|'"') )* '"'
         ;
         
//testname : string
//         ; 

//Note that file allows any string also
extraparam :   file
             | TESTNAME
           ;

directory : file '/'
          ;

file : filestring ('/' filestring)*
     ;

linenumber : integer
           ;

charposition : integer
             ;

javastring  : string ('.' string)*
            ;

string  : ALPHANUMERIC+
        ;
        
progArg  :  '-' '-'? filestring
         ;

filestring  :   ALPHANUMERIC ( ALPHANUMERIC | '-' | '_' | '.' )*
              | '.'
              | '..'
            ;

integer  : DIGIT+
         ;

PROG_ARGS  : '@Prog-args:' { curliesMode = true; } ;
LOCATION  : '@Location' { curliesMode = false; } ;
UNCHECKED_CODE_BLOCK  :
{curliesMode}?=>
  UNCHECKED_CODE { setText($text.substring(1, $text.length()-1).trim()); }
;
   
fragment                  
UNCHECKED_CODE :
  '{' 
  ( options {greedy=false; k=2;}
  : UNCHECKED_CODE
  | .
  )*
  '}'
;

ALPHANUMERIC  : ALPHA | DIGIT
              ;

fragment
ALPHA  : 'A'..'Z' | 'a'..'z'
       ;

fragment
DIGIT  : '0'..'9'
       ;

COMMENT  :  LINE_COMMENT+ { $channel=HIDDEN; }
         ;

fragment 
LINE_COMMENT  :  COMMENT_START (options {greedy=false;} : .)* NEWLINE 
              ;

fragment
COMMENT_START  : '//'
               ;

fragment
NEWLINE  :  '\r'? '\n' 
         ;

WHITESPACE  :  (' '|'\n'|'\r'|'\t')+ {$channel=HIDDEN;}
            ;


