/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
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
  package ie.ucd.bon.tests;
}

testGrammar : testLocation
              ( test )+
            ;

testLocation : '@Test-Location:' directory { testLocation = $directory.text; }
             ;
            
test : { currentTestCase = new TestCase(testNumber++); }
       ('@Test-name:' TESTNAME { currentTestCase.setTestName($TESTNAME.text); } )?
       ('@Prog-args:' f1=filestring { currentTestCase.addProgramArgument($f1.text); } 
                      (',' f=filestring { currentTestCase.addProgramArgument($f.text); } )* )?
       '@Location'			 
       '{' directory '}'
       { currentTestCase.setLocation(testsDir + testLocation + $directory.text); }
       '@Input'  
       '{' inputs '}' 
       '@Output' 
       '{' outputs? '}'
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
        
filestring  :   ( ALPHANUMERIC | '-' | '_' )+
              | '.'
              | '..'
            ;

integer  : DIGIT+
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
COMMENT_START  : '--'
               ;

fragment
NEWLINE  :  '\r'? '\n' 
         ;

WHITESPACE  :  (' '|'\n'|'\r'|'\t')+ {$channel=HIDDEN;}
            ;


