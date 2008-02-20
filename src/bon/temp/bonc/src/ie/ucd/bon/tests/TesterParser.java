// $ANTLR 3.0.1 Tester.g 2008-02-20 14:22:08

  package ie.ucd.bon.tests;
  
  import ie.ucd.bon.tests.testcase.TestCase;
  import ie.ucd.bon.tests.testcase.TestOutput;  


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
public class TesterParser extends AbstractTesterParser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "TESTNAME", "ALPHANUMERIC", "DIGIT", "ALPHA", "LINE_COMMENT", "COMMENT", "COMMENT_START", "NEWLINE", "WHITESPACE", "'@Test-Location:'", "'@Test-name:'", "'@Prog-args:'", "','", "'@Location'", "'{'", "'}'", "'@Input'", "'@Output'", "'<'", "'#File:'", "'>'", "'/'", "'.'", "'-'", "'_'", "'..'"
    };
    public static final int NEWLINE=11;
    public static final int LINE_COMMENT=8;
    public static final int ALPHANUMERIC=5;
    public static final int TESTNAME=4;
    public static final int WHITESPACE=12;
    public static final int DIGIT=6;
    public static final int COMMENT=9;
    public static final int EOF=-1;
    public static final int COMMENT_START=10;
    public static final int ALPHA=7;

        public TesterParser(TokenStream input) {
            super(input);
        }
        

    public String[] getTokenNames() { return tokenNames; }
    public String getGrammarFileName() { return "Tester.g"; }


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



    // $ANTLR start testGrammar
    // Tester.g:43:1: testGrammar : testLocation ( test )+ ;
    public final void testGrammar() throws RecognitionException {
        try {
            // Tester.g:43:13: ( testLocation ( test )+ )
            // Tester.g:43:15: testLocation ( test )+
            {
            pushFollow(FOLLOW_testLocation_in_testGrammar47);
            testLocation();
            _fsp--;

            // Tester.g:44:15: ( test )+
            int cnt1=0;
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( ((LA1_0>=14 && LA1_0<=15)||LA1_0==17) ) {
                    alt1=1;
                }


                switch (alt1) {
            	case 1 :
            	    // Tester.g:44:17: test
            	    {
            	    pushFollow(FOLLOW_test_in_testGrammar65);
            	    test();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt1 >= 1 ) break loop1;
                        EarlyExitException eee =
                            new EarlyExitException(1, input);
                        throw eee;
                }
                cnt1++;
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end testGrammar


    // $ANTLR start testLocation
    // Tester.g:47:1: testLocation : '@Test-Location:' directory ;
    public final void testLocation() throws RecognitionException {
        directory_return directory1 = null;


        try {
            // Tester.g:47:14: ( '@Test-Location:' directory )
            // Tester.g:47:16: '@Test-Location:' directory
            {
            match(input,13,FOLLOW_13_in_testLocation89); 
            pushFollow(FOLLOW_directory_in_testLocation91);
            directory1=directory();
            _fsp--;

             testLocation = input.toString(directory1.start,directory1.stop); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end testLocation


    // $ANTLR start test
    // Tester.g:50:1: test : ( '@Test-name:' TESTNAME )? ( '@Prog-args:' f1= filestring ( ',' f= filestring )* )? '@Location' '{' directory '}' '@Input' '{' inputs '}' '@Output' '{' ( outputs )? '}' ;
    public final void test() throws RecognitionException {
        Token TESTNAME2=null;
        filestring_return f1 = null;

        filestring_return f = null;

        directory_return directory3 = null;


        try {
            // Tester.g:50:6: ( ( '@Test-name:' TESTNAME )? ( '@Prog-args:' f1= filestring ( ',' f= filestring )* )? '@Location' '{' directory '}' '@Input' '{' inputs '}' '@Output' '{' ( outputs )? '}' )
            // Tester.g:50:8: ( '@Test-name:' TESTNAME )? ( '@Prog-args:' f1= filestring ( ',' f= filestring )* )? '@Location' '{' directory '}' '@Input' '{' inputs '}' '@Output' '{' ( outputs )? '}'
            {
             currentTestCase = new TestCase(testNumber++); 
            // Tester.g:51:8: ( '@Test-name:' TESTNAME )?
            int alt2=2;
            int LA2_0 = input.LA(1);

            if ( (LA2_0==14) ) {
                alt2=1;
            }
            switch (alt2) {
                case 1 :
                    // Tester.g:51:9: '@Test-name:' TESTNAME
                    {
                    match(input,14,FOLLOW_14_in_test137); 
                    TESTNAME2=(Token)input.LT(1);
                    match(input,TESTNAME,FOLLOW_TESTNAME_in_test139); 
                     currentTestCase.setTestName(TESTNAME2.getText()); 

                    }
                    break;

            }

            // Tester.g:52:8: ( '@Prog-args:' f1= filestring ( ',' f= filestring )* )?
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( (LA4_0==15) ) {
                alt4=1;
            }
            switch (alt4) {
                case 1 :
                    // Tester.g:52:9: '@Prog-args:' f1= filestring ( ',' f= filestring )*
                    {
                    match(input,15,FOLLOW_15_in_test154); 
                    pushFollow(FOLLOW_filestring_in_test158);
                    f1=filestring();
                    _fsp--;

                     currentTestCase.addProgramArgument(input.toString(f1.start,f1.stop)); 
                    // Tester.g:53:23: ( ',' f= filestring )*
                    loop3:
                    do {
                        int alt3=2;
                        int LA3_0 = input.LA(1);

                        if ( (LA3_0==16) ) {
                            alt3=1;
                        }


                        switch (alt3) {
                    	case 1 :
                    	    // Tester.g:53:24: ',' f= filestring
                    	    {
                    	    match(input,16,FOLLOW_16_in_test186); 
                    	    pushFollow(FOLLOW_filestring_in_test190);
                    	    f=filestring();
                    	    _fsp--;

                    	     currentTestCase.addProgramArgument(input.toString(f.start,f.stop)); 

                    	    }
                    	    break;

                    	default :
                    	    break loop3;
                        }
                    } while (true);


                    }
                    break;

            }

            match(input,17,FOLLOW_17_in_test207); 
            match(input,18,FOLLOW_18_in_test220); 
            pushFollow(FOLLOW_directory_in_test222);
            directory3=directory();
            _fsp--;

            match(input,19,FOLLOW_19_in_test224); 
             currentTestCase.setLocation(testsDir + testLocation + input.toString(directory3.start,directory3.stop)); 
            match(input,20,FOLLOW_20_in_test242); 
            match(input,18,FOLLOW_18_in_test253); 
            pushFollow(FOLLOW_inputs_in_test255);
            inputs();
            _fsp--;

            match(input,19,FOLLOW_19_in_test257); 
            match(input,21,FOLLOW_21_in_test267); 
            match(input,18,FOLLOW_18_in_test277); 
            // Tester.g:60:12: ( outputs )?
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0==22) ) {
                alt5=1;
            }
            switch (alt5) {
                case 1 :
                    // Tester.g:60:12: outputs
                    {
                    pushFollow(FOLLOW_outputs_in_test279);
                    outputs();
                    _fsp--;


                    }
                    break;

            }

            match(input,19,FOLLOW_19_in_test282); 
             addTestCase(currentTestCase); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end test


    // $ANTLR start inputs
    // Tester.g:64:1: inputs : (f1= file )? ( ',' f= file )* ;
    public final void inputs() throws RecognitionException {
        file_return f1 = null;

        file_return f = null;


        try {
            // Tester.g:64:8: ( (f1= file )? ( ',' f= file )* )
            // Tester.g:64:10: (f1= file )? ( ',' f= file )*
            {
            // Tester.g:64:10: (f1= file )?
            int alt6=2;
            int LA6_0 = input.LA(1);

            if ( (LA6_0==ALPHANUMERIC||(LA6_0>=26 && LA6_0<=29)) ) {
                alt6=1;
            }
            switch (alt6) {
                case 1 :
                    // Tester.g:64:11: f1= file
                    {
                    pushFollow(FOLLOW_file_in_inputs314);
                    f1=file();
                    _fsp--;

                     currentTestCase.addInputFile(input.toString(f1.start,f1.stop)); 

                    }
                    break;

            }

            // Tester.g:65:10: ( ',' f= file )*
            loop7:
            do {
                int alt7=2;
                int LA7_0 = input.LA(1);

                if ( (LA7_0==16) ) {
                    alt7=1;
                }


                switch (alt7) {
            	case 1 :
            	    // Tester.g:65:11: ',' f= file
            	    {
            	    match(input,16,FOLLOW_16_in_inputs336); 
            	    pushFollow(FOLLOW_file_in_inputs340);
            	    f=file();
            	    _fsp--;

            	     currentTestCase.addInputFile(input.toString(f.start,f.stop));  

            	    }
            	    break;

            	default :
            	    break loop7;
                }
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end inputs


    // $ANTLR start outputs
    // Tester.g:68:1: outputs : output ( ',' output )* ;
    public final void outputs() throws RecognitionException {
        try {
            // Tester.g:68:9: ( output ( ',' output )* )
            // Tester.g:68:11: output ( ',' output )*
            {
            pushFollow(FOLLOW_output_in_outputs370);
            output();
            _fsp--;

            // Tester.g:68:18: ( ',' output )*
            loop8:
            do {
                int alt8=2;
                int LA8_0 = input.LA(1);

                if ( (LA8_0==16) ) {
                    alt8=1;
                }


                switch (alt8) {
            	case 1 :
            	    // Tester.g:68:19: ',' output
            	    {
            	    match(input,16,FOLLOW_16_in_outputs373); 
            	    pushFollow(FOLLOW_output_in_outputs375);
            	    output();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    break loop8;
                }
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end outputs


    // $ANTLR start output
    // Tester.g:71:1: output : '<' error ( ',' ( ( extraparam ) | ( '#File:' file ) ) )* '>' ;
    public final void output() throws RecognitionException {
        error_return error4 = null;

        extraparam_return extraparam5 = null;

        file_return file6 = null;


        try {
            // Tester.g:71:8: ( '<' error ( ',' ( ( extraparam ) | ( '#File:' file ) ) )* '>' )
            // Tester.g:71:10: '<' error ( ',' ( ( extraparam ) | ( '#File:' file ) ) )* '>'
            {
            match(input,22,FOLLOW_22_in_output394); 
             TestOutput output = new TestOutput(); 
            pushFollow(FOLLOW_error_in_output417);
            error4=error();
            _fsp--;

             output.setErrorType(input.toString(error4.start,error4.stop)); 
            // Tester.g:74:10: ( ',' ( ( extraparam ) | ( '#File:' file ) ) )*
            loop10:
            do {
                int alt10=2;
                int LA10_0 = input.LA(1);

                if ( (LA10_0==16) ) {
                    alt10=1;
                }


                switch (alt10) {
            	case 1 :
            	    // Tester.g:74:11: ',' ( ( extraparam ) | ( '#File:' file ) )
            	    {
            	    match(input,16,FOLLOW_16_in_output442); 
            	    // Tester.g:74:15: ( ( extraparam ) | ( '#File:' file ) )
            	    int alt9=2;
            	    int LA9_0 = input.LA(1);

            	    if ( ((LA9_0>=TESTNAME && LA9_0<=ALPHANUMERIC)||(LA9_0>=26 && LA9_0<=29)) ) {
            	        alt9=1;
            	    }
            	    else if ( (LA9_0==23) ) {
            	        alt9=2;
            	    }
            	    else {
            	        NoViableAltException nvae =
            	            new NoViableAltException("74:15: ( ( extraparam ) | ( '#File:' file ) )", 9, 0, input);

            	        throw nvae;
            	    }
            	    switch (alt9) {
            	        case 1 :
            	            // Tester.g:74:19: ( extraparam )
            	            {
            	            // Tester.g:74:19: ( extraparam )
            	            // Tester.g:74:21: extraparam
            	            {
            	            pushFollow(FOLLOW_extraparam_in_output450);
            	            extraparam5=extraparam();
            	            _fsp--;

            	             output.addExtraParam(input.toString(extraparam5.start,extraparam5.stop)); 

            	            }


            	            }
            	            break;
            	        case 2 :
            	            // Tester.g:75:19: ( '#File:' file )
            	            {
            	            // Tester.g:75:19: ( '#File:' file )
            	            // Tester.g:75:21: '#File:' file
            	            {
            	            match(input,23,FOLLOW_23_in_output477); 
            	            pushFollow(FOLLOW_file_in_output479);
            	            file6=file();
            	            _fsp--;

            	             output.addExtraParam(fileString(input.toString(file6.start,file6.stop))); 

            	            }


            	            }
            	            break;

            	    }


            	    }
            	    break;

            	default :
            	    break loop10;
                }
            } while (true);

            match(input,24,FOLLOW_24_in_output525); 
             currentTestCase.addOutput(output); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end output

    public static class error_return extends ParserRuleReturnScope {
    };

    // $ANTLR start error
    // Tester.g:82:1: error : javastring ;
    public final error_return error() throws RecognitionException {
        error_return retval = new error_return();
        retval.start = input.LT(1);

        try {
            // Tester.g:82:7: ( javastring )
            // Tester.g:82:9: javastring
            {
            pushFollow(FOLLOW_javastring_in_error552);
            javastring();
            _fsp--;


            }

            retval.stop = input.LT(-1);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end error

    public static class extraparam_return extends ParserRuleReturnScope {
    };

    // $ANTLR start extraparam
    // Tester.g:92:1: extraparam : ( file | TESTNAME );
    public final extraparam_return extraparam() throws RecognitionException {
        extraparam_return retval = new extraparam_return();
        retval.start = input.LT(1);

        try {
            // Tester.g:92:12: ( file | TESTNAME )
            int alt11=2;
            int LA11_0 = input.LA(1);

            if ( (LA11_0==ALPHANUMERIC||(LA11_0>=26 && LA11_0<=29)) ) {
                alt11=1;
            }
            else if ( (LA11_0==TESTNAME) ) {
                alt11=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("92:1: extraparam : ( file | TESTNAME );", 11, 0, input);

                throw nvae;
            }
            switch (alt11) {
                case 1 :
                    // Tester.g:92:16: file
                    {
                    pushFollow(FOLLOW_file_in_extraparam624);
                    file();
                    _fsp--;


                    }
                    break;
                case 2 :
                    // Tester.g:93:16: TESTNAME
                    {
                    match(input,TESTNAME,FOLLOW_TESTNAME_in_extraparam641); 

                    }
                    break;

            }
            retval.stop = input.LT(-1);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end extraparam

    public static class directory_return extends ParserRuleReturnScope {
    };

    // $ANTLR start directory
    // Tester.g:96:1: directory : file '/' ;
    public final directory_return directory() throws RecognitionException {
        directory_return retval = new directory_return();
        retval.start = input.LT(1);

        try {
            // Tester.g:96:11: ( file '/' )
            // Tester.g:96:13: file '/'
            {
            pushFollow(FOLLOW_file_in_directory661);
            file();
            _fsp--;

            match(input,25,FOLLOW_25_in_directory663); 

            }

            retval.stop = input.LT(-1);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end directory

    public static class file_return extends ParserRuleReturnScope {
    };

    // $ANTLR start file
    // Tester.g:99:1: file : filestring ( '/' filestring )* ;
    public final file_return file() throws RecognitionException {
        file_return retval = new file_return();
        retval.start = input.LT(1);

        try {
            // Tester.g:99:6: ( filestring ( '/' filestring )* )
            // Tester.g:99:8: filestring ( '/' filestring )*
            {
            pushFollow(FOLLOW_filestring_in_file682);
            filestring();
            _fsp--;

            // Tester.g:99:19: ( '/' filestring )*
            loop12:
            do {
                int alt12=2;
                int LA12_0 = input.LA(1);

                if ( (LA12_0==25) ) {
                    int LA12_2 = input.LA(2);

                    if ( (LA12_2==ALPHANUMERIC||(LA12_2>=26 && LA12_2<=29)) ) {
                        alt12=1;
                    }


                }


                switch (alt12) {
            	case 1 :
            	    // Tester.g:99:20: '/' filestring
            	    {
            	    match(input,25,FOLLOW_25_in_file685); 
            	    pushFollow(FOLLOW_filestring_in_file687);
            	    filestring();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    break loop12;
                }
            } while (true);


            }

            retval.stop = input.LT(-1);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end file


    // $ANTLR start linenumber
    // Tester.g:102:1: linenumber : integer ;
    public final void linenumber() throws RecognitionException {
        try {
            // Tester.g:102:12: ( integer )
            // Tester.g:102:14: integer
            {
            pushFollow(FOLLOW_integer_in_linenumber703);
            integer();
            _fsp--;


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end linenumber


    // $ANTLR start charposition
    // Tester.g:105:1: charposition : integer ;
    public final void charposition() throws RecognitionException {
        try {
            // Tester.g:105:14: ( integer )
            // Tester.g:105:16: integer
            {
            pushFollow(FOLLOW_integer_in_charposition723);
            integer();
            _fsp--;


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end charposition


    // $ANTLR start javastring
    // Tester.g:108:1: javastring : string ( '.' string )* ;
    public final void javastring() throws RecognitionException {
        try {
            // Tester.g:108:13: ( string ( '.' string )* )
            // Tester.g:108:15: string ( '.' string )*
            {
            pushFollow(FOLLOW_string_in_javastring746);
            string();
            _fsp--;

            // Tester.g:108:22: ( '.' string )*
            loop13:
            do {
                int alt13=2;
                int LA13_0 = input.LA(1);

                if ( (LA13_0==26) ) {
                    alt13=1;
                }


                switch (alt13) {
            	case 1 :
            	    // Tester.g:108:23: '.' string
            	    {
            	    match(input,26,FOLLOW_26_in_javastring749); 
            	    pushFollow(FOLLOW_string_in_javastring751);
            	    string();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    break loop13;
                }
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end javastring


    // $ANTLR start string
    // Tester.g:111:1: string : ( ALPHANUMERIC )+ ;
    public final void string() throws RecognitionException {
        try {
            // Tester.g:111:9: ( ( ALPHANUMERIC )+ )
            // Tester.g:111:11: ( ALPHANUMERIC )+
            {
            // Tester.g:111:11: ( ALPHANUMERIC )+
            int cnt14=0;
            loop14:
            do {
                int alt14=2;
                int LA14_0 = input.LA(1);

                if ( (LA14_0==ALPHANUMERIC) ) {
                    alt14=1;
                }


                switch (alt14) {
            	case 1 :
            	    // Tester.g:111:11: ALPHANUMERIC
            	    {
            	    match(input,ALPHANUMERIC,FOLLOW_ALPHANUMERIC_in_string775); 

            	    }
            	    break;

            	default :
            	    if ( cnt14 >= 1 ) break loop14;
                        EarlyExitException eee =
                            new EarlyExitException(14, input);
                        throw eee;
                }
                cnt14++;
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end string

    public static class filestring_return extends ParserRuleReturnScope {
    };

    // $ANTLR start filestring
    // Tester.g:114:1: filestring : ( ( ALPHANUMERIC | '-' | '_' )+ | '.' | '..' );
    public final filestring_return filestring() throws RecognitionException {
        filestring_return retval = new filestring_return();
        retval.start = input.LT(1);

        try {
            // Tester.g:114:13: ( ( ALPHANUMERIC | '-' | '_' )+ | '.' | '..' )
            int alt16=3;
            switch ( input.LA(1) ) {
            case ALPHANUMERIC:
            case 27:
            case 28:
                {
                alt16=1;
                }
                break;
            case 26:
                {
                alt16=2;
                }
                break;
            case 29:
                {
                alt16=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("114:1: filestring : ( ( ALPHANUMERIC | '-' | '_' )+ | '.' | '..' );", 16, 0, input);

                throw nvae;
            }

            switch (alt16) {
                case 1 :
                    // Tester.g:114:17: ( ALPHANUMERIC | '-' | '_' )+
                    {
                    // Tester.g:114:17: ( ALPHANUMERIC | '-' | '_' )+
                    int cnt15=0;
                    loop15:
                    do {
                        int alt15=2;
                        int LA15_0 = input.LA(1);

                        if ( (LA15_0==ALPHANUMERIC||(LA15_0>=27 && LA15_0<=28)) ) {
                            alt15=1;
                        }


                        switch (alt15) {
                    	case 1 :
                    	    // Tester.g:
                    	    {
                    	    if ( input.LA(1)==ALPHANUMERIC||(input.LA(1)>=27 && input.LA(1)<=28) ) {
                    	        input.consume();
                    	        errorRecovery=false;
                    	    }
                    	    else {
                    	        MismatchedSetException mse =
                    	            new MismatchedSetException(null,input);
                    	        recoverFromMismatchedSet(input,mse,FOLLOW_set_in_filestring804);    throw mse;
                    	    }


                    	    }
                    	    break;

                    	default :
                    	    if ( cnt15 >= 1 ) break loop15;
                                EarlyExitException eee =
                                    new EarlyExitException(15, input);
                                throw eee;
                        }
                        cnt15++;
                    } while (true);


                    }
                    break;
                case 2 :
                    // Tester.g:115:17: '.'
                    {
                    match(input,26,FOLLOW_26_in_filestring835); 

                    }
                    break;
                case 3 :
                    // Tester.g:116:17: '..'
                    {
                    match(input,29,FOLLOW_29_in_filestring853); 

                    }
                    break;

            }
            retval.stop = input.LT(-1);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end filestring


    // $ANTLR start integer
    // Tester.g:119:1: integer : ( DIGIT )+ ;
    public final void integer() throws RecognitionException {
        try {
            // Tester.g:119:10: ( ( DIGIT )+ )
            // Tester.g:119:12: ( DIGIT )+
            {
            // Tester.g:119:12: ( DIGIT )+
            int cnt17=0;
            loop17:
            do {
                int alt17=2;
                int LA17_0 = input.LA(1);

                if ( (LA17_0==DIGIT) ) {
                    alt17=1;
                }


                switch (alt17) {
            	case 1 :
            	    // Tester.g:119:12: DIGIT
            	    {
            	    match(input,DIGIT,FOLLOW_DIGIT_in_integer875); 

            	    }
            	    break;

            	default :
            	    if ( cnt17 >= 1 ) break loop17;
                        EarlyExitException eee =
                            new EarlyExitException(17, input);
                        throw eee;
                }
                cnt17++;
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end integer


 

    public static final BitSet FOLLOW_testLocation_in_testGrammar47 = new BitSet(new long[]{0x000000000002C000L});
    public static final BitSet FOLLOW_test_in_testGrammar65 = new BitSet(new long[]{0x000000000002C002L});
    public static final BitSet FOLLOW_13_in_testLocation89 = new BitSet(new long[]{0x000000003C000020L});
    public static final BitSet FOLLOW_directory_in_testLocation91 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_14_in_test137 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_TESTNAME_in_test139 = new BitSet(new long[]{0x0000000000028000L});
    public static final BitSet FOLLOW_15_in_test154 = new BitSet(new long[]{0x000000003C000020L});
    public static final BitSet FOLLOW_filestring_in_test158 = new BitSet(new long[]{0x0000000000030000L});
    public static final BitSet FOLLOW_16_in_test186 = new BitSet(new long[]{0x000000003C000020L});
    public static final BitSet FOLLOW_filestring_in_test190 = new BitSet(new long[]{0x0000000000030000L});
    public static final BitSet FOLLOW_17_in_test207 = new BitSet(new long[]{0x0000000000040000L});
    public static final BitSet FOLLOW_18_in_test220 = new BitSet(new long[]{0x000000003C000020L});
    public static final BitSet FOLLOW_directory_in_test222 = new BitSet(new long[]{0x0000000000080000L});
    public static final BitSet FOLLOW_19_in_test224 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_20_in_test242 = new BitSet(new long[]{0x0000000000040000L});
    public static final BitSet FOLLOW_18_in_test253 = new BitSet(new long[]{0x000000003C090020L});
    public static final BitSet FOLLOW_inputs_in_test255 = new BitSet(new long[]{0x0000000000080000L});
    public static final BitSet FOLLOW_19_in_test257 = new BitSet(new long[]{0x0000000000200000L});
    public static final BitSet FOLLOW_21_in_test267 = new BitSet(new long[]{0x0000000000040000L});
    public static final BitSet FOLLOW_18_in_test277 = new BitSet(new long[]{0x0000000000480000L});
    public static final BitSet FOLLOW_outputs_in_test279 = new BitSet(new long[]{0x0000000000080000L});
    public static final BitSet FOLLOW_19_in_test282 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_file_in_inputs314 = new BitSet(new long[]{0x0000000000010002L});
    public static final BitSet FOLLOW_16_in_inputs336 = new BitSet(new long[]{0x000000003C000020L});
    public static final BitSet FOLLOW_file_in_inputs340 = new BitSet(new long[]{0x0000000000010002L});
    public static final BitSet FOLLOW_output_in_outputs370 = new BitSet(new long[]{0x0000000000010002L});
    public static final BitSet FOLLOW_16_in_outputs373 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_output_in_outputs375 = new BitSet(new long[]{0x0000000000010002L});
    public static final BitSet FOLLOW_22_in_output394 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_error_in_output417 = new BitSet(new long[]{0x0000000001010000L});
    public static final BitSet FOLLOW_16_in_output442 = new BitSet(new long[]{0x000000003C800030L});
    public static final BitSet FOLLOW_extraparam_in_output450 = new BitSet(new long[]{0x0000000001010000L});
    public static final BitSet FOLLOW_23_in_output477 = new BitSet(new long[]{0x000000003C000020L});
    public static final BitSet FOLLOW_file_in_output479 = new BitSet(new long[]{0x0000000001010000L});
    public static final BitSet FOLLOW_24_in_output525 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_javastring_in_error552 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_file_in_extraparam624 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_TESTNAME_in_extraparam641 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_file_in_directory661 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_directory663 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_filestring_in_file682 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_25_in_file685 = new BitSet(new long[]{0x000000003C000020L});
    public static final BitSet FOLLOW_filestring_in_file687 = new BitSet(new long[]{0x0000000002000002L});
    public static final BitSet FOLLOW_integer_in_linenumber703 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_integer_in_charposition723 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_string_in_javastring746 = new BitSet(new long[]{0x0000000004000002L});
    public static final BitSet FOLLOW_26_in_javastring749 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_string_in_javastring751 = new BitSet(new long[]{0x0000000004000002L});
    public static final BitSet FOLLOW_ALPHANUMERIC_in_string775 = new BitSet(new long[]{0x0000000000000022L});
    public static final BitSet FOLLOW_set_in_filestring804 = new BitSet(new long[]{0x0000000018000022L});
    public static final BitSet FOLLOW_26_in_filestring835 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_29_in_filestring853 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_DIGIT_in_integer875 = new BitSet(new long[]{0x0000000000000042L});

}