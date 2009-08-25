// $ANTLR 3.1.3 Mar 18, 2009 10:09:25 Tester.g 2009-08-25 14:21:04

  package ie.ucd.bon.tests;
  
  import ie.ucd.bon.tests.testcase.TestCase;
  import ie.ucd.bon.tests.testcase.TestOutput;  


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
public class TesterParser extends AbstractTesterParser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "TESTNAME", "PROG_ARGS", "UNCHECKED_CODE_BLOCK", "LOCATION", "ALPHANUMERIC", "DIGIT", "UNCHECKED_CODE", "ALPHA", "LINE_COMMENT", "COMMENT", "COMMENT_START", "NEWLINE", "WHITESPACE", "'@Test-Location:'", "'@Test-name:'", "'{'", "'}'", "'@Input'", "'@Output'", "','", "'<'", "'#File:'", "'>'", "'/'", "'.'", "'-'", "'_'", "'..'"
    };
    public static final int T__29=29;
    public static final int T__28=28;
    public static final int T__27=27;
    public static final int T__26=26;
    public static final int LINE_COMMENT=12;
    public static final int T__25=25;
    public static final int T__24=24;
    public static final int T__23=23;
    public static final int UNCHECKED_CODE_BLOCK=6;
    public static final int T__22=22;
    public static final int T__21=21;
    public static final int T__20=20;
    public static final int WHITESPACE=16;
    public static final int PROG_ARGS=5;
    public static final int EOF=-1;
    public static final int COMMENT_START=14;
    public static final int ALPHA=11;
    public static final int UNCHECKED_CODE=10;
    public static final int T__19=19;
    public static final int T__30=30;
    public static final int T__31=31;
    public static final int NEWLINE=15;
    public static final int T__18=18;
    public static final int T__17=17;
    public static final int ALPHANUMERIC=8;
    public static final int TESTNAME=4;
    public static final int LOCATION=7;
    public static final int DIGIT=9;
    public static final int COMMENT=13;

    // delegates
    // delegators


        public TesterParser(TokenStream input) {
            this(input, new RecognizerSharedState());
        }
        public TesterParser(TokenStream input, RecognizerSharedState state) {
            super(input, state);
             
        }
        

    public String[] getTokenNames() { return TesterParser.tokenNames; }
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



    // $ANTLR start "testGrammar"
    // Tester.g:51:1: testGrammar : testLocation ( test )+ ;
    public final void testGrammar() throws RecognitionException {
        try {
            // Tester.g:51:13: ( testLocation ( test )+ )
            // Tester.g:51:15: testLocation ( test )+
            {
            pushFollow(FOLLOW_testLocation_in_testGrammar56);
            testLocation();

            state._fsp--;

            // Tester.g:52:15: ( test )+
            int cnt1=0;
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( (LA1_0==PROG_ARGS||LA1_0==LOCATION||LA1_0==18) ) {
                    alt1=1;
                }


                switch (alt1) {
            	case 1 :
            	    // Tester.g:52:17: test
            	    {
            	    pushFollow(FOLLOW_test_in_testGrammar74);
            	    test();

            	    state._fsp--;


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
    // $ANTLR end "testGrammar"


    // $ANTLR start "testLocation"
    // Tester.g:55:1: testLocation : '@Test-Location:' directory ;
    public final void testLocation() throws RecognitionException {
        TesterParser.directory_return directory1 = null;


        try {
            // Tester.g:55:14: ( '@Test-Location:' directory )
            // Tester.g:55:16: '@Test-Location:' directory
            {
            match(input,17,FOLLOW_17_in_testLocation98); 
            pushFollow(FOLLOW_directory_in_testLocation100);
            directory1=directory();

            state._fsp--;

             testLocation = (directory1!=null?input.toString(directory1.start,directory1.stop):null); 

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
    // $ANTLR end "testLocation"


    // $ANTLR start "test"
    // Tester.g:58:1: test : ( '@Test-name:' TESTNAME )? ( PROG_ARGS b= UNCHECKED_CODE_BLOCK )? LOCATION '{' directory '}' '@Input' '{' inputs '}' ( '@Output' '{' ( outputs )? '}' )? ;
    public final void test() throws RecognitionException {
        Token b=null;
        Token TESTNAME2=null;
        TesterParser.directory_return directory3 = null;


        try {
            // Tester.g:58:6: ( ( '@Test-name:' TESTNAME )? ( PROG_ARGS b= UNCHECKED_CODE_BLOCK )? LOCATION '{' directory '}' '@Input' '{' inputs '}' ( '@Output' '{' ( outputs )? '}' )? )
            // Tester.g:58:8: ( '@Test-name:' TESTNAME )? ( PROG_ARGS b= UNCHECKED_CODE_BLOCK )? LOCATION '{' directory '}' '@Input' '{' inputs '}' ( '@Output' '{' ( outputs )? '}' )?
            {
             currentTestCase = new TestCase(testNumber++); 
            // Tester.g:59:8: ( '@Test-name:' TESTNAME )?
            int alt2=2;
            int LA2_0 = input.LA(1);

            if ( (LA2_0==18) ) {
                alt2=1;
            }
            switch (alt2) {
                case 1 :
                    // Tester.g:59:9: '@Test-name:' TESTNAME
                    {
                    match(input,18,FOLLOW_18_in_test146); 
                    TESTNAME2=(Token)match(input,TESTNAME,FOLLOW_TESTNAME_in_test148); 
                     currentTestCase.setTestName((TESTNAME2!=null?TESTNAME2.getText():null)); 

                    }
                    break;

            }

            // Tester.g:60:8: ( PROG_ARGS b= UNCHECKED_CODE_BLOCK )?
            int alt3=2;
            int LA3_0 = input.LA(1);

            if ( (LA3_0==PROG_ARGS) ) {
                alt3=1;
            }
            switch (alt3) {
                case 1 :
                    // Tester.g:60:9: PROG_ARGS b= UNCHECKED_CODE_BLOCK
                    {
                    match(input,PROG_ARGS,FOLLOW_PROG_ARGS_in_test163); 
                    b=(Token)match(input,UNCHECKED_CODE_BLOCK,FOLLOW_UNCHECKED_CODE_BLOCK_in_test167); 
                     currentTestCase.setProgramArguments((b!=null?b.getText():null)); 

                    }
                    break;

            }

            match(input,LOCATION,FOLLOW_LOCATION_in_test181); 
            match(input,19,FOLLOW_19_in_test194); 
            pushFollow(FOLLOW_directory_in_test196);
            directory3=directory();

            state._fsp--;

            match(input,20,FOLLOW_20_in_test198); 
             currentTestCase.setLocation(testsDir + testLocation + (directory3!=null?input.toString(directory3.start,directory3.stop):null)); 
            match(input,21,FOLLOW_21_in_test216); 
            match(input,19,FOLLOW_19_in_test227); 
            pushFollow(FOLLOW_inputs_in_test229);
            inputs();

            state._fsp--;

            match(input,20,FOLLOW_20_in_test231); 
            // Tester.g:66:8: ( '@Output' '{' ( outputs )? '}' )?
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0==22) ) {
                alt5=1;
            }
            switch (alt5) {
                case 1 :
                    // Tester.g:66:10: '@Output' '{' ( outputs )? '}'
                    {
                    match(input,22,FOLLOW_22_in_test243); 
                    match(input,19,FOLLOW_19_in_test255); 
                    // Tester.g:67:14: ( outputs )?
                    int alt4=2;
                    int LA4_0 = input.LA(1);

                    if ( (LA4_0==24) ) {
                        alt4=1;
                    }
                    switch (alt4) {
                        case 1 :
                            // Tester.g:67:14: outputs
                            {
                            pushFollow(FOLLOW_outputs_in_test257);
                            outputs();

                            state._fsp--;


                            }
                            break;

                    }

                    match(input,20,FOLLOW_20_in_test260); 

                    }
                    break;

            }

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
    // $ANTLR end "test"


    // $ANTLR start "inputs"
    // Tester.g:71:1: inputs : (f1= file )? ( ',' f= file )* ;
    public final void inputs() throws RecognitionException {
        TesterParser.file_return f1 = null;

        TesterParser.file_return f = null;


        try {
            // Tester.g:71:8: ( (f1= file )? ( ',' f= file )* )
            // Tester.g:71:10: (f1= file )? ( ',' f= file )*
            {
            // Tester.g:71:10: (f1= file )?
            int alt6=2;
            int LA6_0 = input.LA(1);

            if ( (LA6_0==ALPHANUMERIC||LA6_0==28||LA6_0==31) ) {
                alt6=1;
            }
            switch (alt6) {
                case 1 :
                    // Tester.g:71:11: f1= file
                    {
                    pushFollow(FOLLOW_file_in_inputs295);
                    f1=file();

                    state._fsp--;

                     currentTestCase.addInputFile((f1!=null?input.toString(f1.start,f1.stop):null)); 

                    }
                    break;

            }

            // Tester.g:72:10: ( ',' f= file )*
            loop7:
            do {
                int alt7=2;
                int LA7_0 = input.LA(1);

                if ( (LA7_0==23) ) {
                    alt7=1;
                }


                switch (alt7) {
            	case 1 :
            	    // Tester.g:72:11: ',' f= file
            	    {
            	    match(input,23,FOLLOW_23_in_inputs317); 
            	    pushFollow(FOLLOW_file_in_inputs321);
            	    f=file();

            	    state._fsp--;

            	     currentTestCase.addInputFile((f!=null?input.toString(f.start,f.stop):null));  

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
    // $ANTLR end "inputs"


    // $ANTLR start "outputs"
    // Tester.g:75:1: outputs : output ( ',' output )* ;
    public final void outputs() throws RecognitionException {
        try {
            // Tester.g:75:9: ( output ( ',' output )* )
            // Tester.g:75:11: output ( ',' output )*
            {
            pushFollow(FOLLOW_output_in_outputs351);
            output();

            state._fsp--;

            // Tester.g:75:18: ( ',' output )*
            loop8:
            do {
                int alt8=2;
                int LA8_0 = input.LA(1);

                if ( (LA8_0==23) ) {
                    alt8=1;
                }


                switch (alt8) {
            	case 1 :
            	    // Tester.g:75:19: ',' output
            	    {
            	    match(input,23,FOLLOW_23_in_outputs354); 
            	    pushFollow(FOLLOW_output_in_outputs356);
            	    output();

            	    state._fsp--;


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
    // $ANTLR end "outputs"


    // $ANTLR start "output"
    // Tester.g:78:1: output : '<' error ( ',' ( ( extraparam ) | ( '#File:' file ) ) )* '>' ;
    public final void output() throws RecognitionException {
        TesterParser.error_return error4 = null;

        TesterParser.extraparam_return extraparam5 = null;

        TesterParser.file_return file6 = null;


        try {
            // Tester.g:78:8: ( '<' error ( ',' ( ( extraparam ) | ( '#File:' file ) ) )* '>' )
            // Tester.g:78:10: '<' error ( ',' ( ( extraparam ) | ( '#File:' file ) ) )* '>'
            {
            match(input,24,FOLLOW_24_in_output375); 
             TestOutput output = new TestOutput(); 
            pushFollow(FOLLOW_error_in_output398);
            error4=error();

            state._fsp--;

             output.setErrorType((error4!=null?input.toString(error4.start,error4.stop):null)); 
            // Tester.g:81:10: ( ',' ( ( extraparam ) | ( '#File:' file ) ) )*
            loop10:
            do {
                int alt10=2;
                int LA10_0 = input.LA(1);

                if ( (LA10_0==23) ) {
                    alt10=1;
                }


                switch (alt10) {
            	case 1 :
            	    // Tester.g:81:11: ',' ( ( extraparam ) | ( '#File:' file ) )
            	    {
            	    match(input,23,FOLLOW_23_in_output423); 
            	    // Tester.g:81:15: ( ( extraparam ) | ( '#File:' file ) )
            	    int alt9=2;
            	    int LA9_0 = input.LA(1);

            	    if ( (LA9_0==TESTNAME||LA9_0==ALPHANUMERIC||LA9_0==28||LA9_0==31) ) {
            	        alt9=1;
            	    }
            	    else if ( (LA9_0==25) ) {
            	        alt9=2;
            	    }
            	    else {
            	        NoViableAltException nvae =
            	            new NoViableAltException("", 9, 0, input);

            	        throw nvae;
            	    }
            	    switch (alt9) {
            	        case 1 :
            	            // Tester.g:81:19: ( extraparam )
            	            {
            	            // Tester.g:81:19: ( extraparam )
            	            // Tester.g:81:21: extraparam
            	            {
            	            pushFollow(FOLLOW_extraparam_in_output431);
            	            extraparam5=extraparam();

            	            state._fsp--;

            	             output.addExtraParam((extraparam5!=null?input.toString(extraparam5.start,extraparam5.stop):null)); 

            	            }


            	            }
            	            break;
            	        case 2 :
            	            // Tester.g:82:19: ( '#File:' file )
            	            {
            	            // Tester.g:82:19: ( '#File:' file )
            	            // Tester.g:82:21: '#File:' file
            	            {
            	            match(input,25,FOLLOW_25_in_output458); 
            	            pushFollow(FOLLOW_file_in_output460);
            	            file6=file();

            	            state._fsp--;

            	             output.addExtraParam(fileString((file6!=null?input.toString(file6.start,file6.stop):null))); 

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

            match(input,26,FOLLOW_26_in_output506); 
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
    // $ANTLR end "output"

    public static class error_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "error"
    // Tester.g:89:1: error : javastring ;
    public final TesterParser.error_return error() throws RecognitionException {
        TesterParser.error_return retval = new TesterParser.error_return();
        retval.start = input.LT(1);

        try {
            // Tester.g:89:7: ( javastring )
            // Tester.g:89:9: javastring
            {
            pushFollow(FOLLOW_javastring_in_error533);
            javastring();

            state._fsp--;


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
    // $ANTLR end "error"

    public static class extraparam_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "extraparam"
    // Tester.g:99:1: extraparam : ( file | TESTNAME );
    public final TesterParser.extraparam_return extraparam() throws RecognitionException {
        TesterParser.extraparam_return retval = new TesterParser.extraparam_return();
        retval.start = input.LT(1);

        try {
            // Tester.g:99:12: ( file | TESTNAME )
            int alt11=2;
            int LA11_0 = input.LA(1);

            if ( (LA11_0==ALPHANUMERIC||LA11_0==28||LA11_0==31) ) {
                alt11=1;
            }
            else if ( (LA11_0==TESTNAME) ) {
                alt11=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 11, 0, input);

                throw nvae;
            }
            switch (alt11) {
                case 1 :
                    // Tester.g:99:16: file
                    {
                    pushFollow(FOLLOW_file_in_extraparam605);
                    file();

                    state._fsp--;


                    }
                    break;
                case 2 :
                    // Tester.g:100:16: TESTNAME
                    {
                    match(input,TESTNAME,FOLLOW_TESTNAME_in_extraparam622); 

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
    // $ANTLR end "extraparam"

    public static class directory_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "directory"
    // Tester.g:103:1: directory : file '/' ;
    public final TesterParser.directory_return directory() throws RecognitionException {
        TesterParser.directory_return retval = new TesterParser.directory_return();
        retval.start = input.LT(1);

        try {
            // Tester.g:103:11: ( file '/' )
            // Tester.g:103:13: file '/'
            {
            pushFollow(FOLLOW_file_in_directory642);
            file();

            state._fsp--;

            match(input,27,FOLLOW_27_in_directory644); 

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
    // $ANTLR end "directory"

    public static class file_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "file"
    // Tester.g:106:1: file : filestring ( '/' filestring )* ;
    public final TesterParser.file_return file() throws RecognitionException {
        TesterParser.file_return retval = new TesterParser.file_return();
        retval.start = input.LT(1);

        try {
            // Tester.g:106:6: ( filestring ( '/' filestring )* )
            // Tester.g:106:8: filestring ( '/' filestring )*
            {
            pushFollow(FOLLOW_filestring_in_file663);
            filestring();

            state._fsp--;

            // Tester.g:106:19: ( '/' filestring )*
            loop12:
            do {
                int alt12=2;
                int LA12_0 = input.LA(1);

                if ( (LA12_0==27) ) {
                    int LA12_2 = input.LA(2);

                    if ( (LA12_2==ALPHANUMERIC||LA12_2==28||LA12_2==31) ) {
                        alt12=1;
                    }


                }


                switch (alt12) {
            	case 1 :
            	    // Tester.g:106:20: '/' filestring
            	    {
            	    match(input,27,FOLLOW_27_in_file666); 
            	    pushFollow(FOLLOW_filestring_in_file668);
            	    filestring();

            	    state._fsp--;


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
    // $ANTLR end "file"


    // $ANTLR start "linenumber"
    // Tester.g:109:1: linenumber : integer ;
    public final void linenumber() throws RecognitionException {
        try {
            // Tester.g:109:12: ( integer )
            // Tester.g:109:14: integer
            {
            pushFollow(FOLLOW_integer_in_linenumber684);
            integer();

            state._fsp--;


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
    // $ANTLR end "linenumber"


    // $ANTLR start "charposition"
    // Tester.g:112:1: charposition : integer ;
    public final void charposition() throws RecognitionException {
        try {
            // Tester.g:112:14: ( integer )
            // Tester.g:112:16: integer
            {
            pushFollow(FOLLOW_integer_in_charposition704);
            integer();

            state._fsp--;


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
    // $ANTLR end "charposition"


    // $ANTLR start "javastring"
    // Tester.g:115:1: javastring : string ( '.' string )* ;
    public final void javastring() throws RecognitionException {
        try {
            // Tester.g:115:13: ( string ( '.' string )* )
            // Tester.g:115:15: string ( '.' string )*
            {
            pushFollow(FOLLOW_string_in_javastring727);
            string();

            state._fsp--;

            // Tester.g:115:22: ( '.' string )*
            loop13:
            do {
                int alt13=2;
                int LA13_0 = input.LA(1);

                if ( (LA13_0==28) ) {
                    alt13=1;
                }


                switch (alt13) {
            	case 1 :
            	    // Tester.g:115:23: '.' string
            	    {
            	    match(input,28,FOLLOW_28_in_javastring730); 
            	    pushFollow(FOLLOW_string_in_javastring732);
            	    string();

            	    state._fsp--;


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
    // $ANTLR end "javastring"


    // $ANTLR start "string"
    // Tester.g:118:1: string : ( ALPHANUMERIC )+ ;
    public final void string() throws RecognitionException {
        try {
            // Tester.g:118:9: ( ( ALPHANUMERIC )+ )
            // Tester.g:118:11: ( ALPHANUMERIC )+
            {
            // Tester.g:118:11: ( ALPHANUMERIC )+
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
            	    // Tester.g:118:11: ALPHANUMERIC
            	    {
            	    match(input,ALPHANUMERIC,FOLLOW_ALPHANUMERIC_in_string756); 

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
    // $ANTLR end "string"


    // $ANTLR start "progArg"
    // Tester.g:121:1: progArg : '-' ( '-' )? filestring ;
    public final void progArg() throws RecognitionException {
        try {
            // Tester.g:121:10: ( '-' ( '-' )? filestring )
            // Tester.g:121:13: '-' ( '-' )? filestring
            {
            match(input,29,FOLLOW_29_in_progArg784); 
            // Tester.g:121:17: ( '-' )?
            int alt15=2;
            int LA15_0 = input.LA(1);

            if ( (LA15_0==29) ) {
                alt15=1;
            }
            switch (alt15) {
                case 1 :
                    // Tester.g:121:17: '-'
                    {
                    match(input,29,FOLLOW_29_in_progArg786); 

                    }
                    break;

            }

            pushFollow(FOLLOW_filestring_in_progArg789);
            filestring();

            state._fsp--;


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
    // $ANTLR end "progArg"


    // $ANTLR start "filestring"
    // Tester.g:124:1: filestring : ( ALPHANUMERIC ( ALPHANUMERIC | '-' | '_' | '.' )* | '.' | '..' );
    public final void filestring() throws RecognitionException {
        try {
            // Tester.g:124:13: ( ALPHANUMERIC ( ALPHANUMERIC | '-' | '_' | '.' )* | '.' | '..' )
            int alt17=3;
            switch ( input.LA(1) ) {
            case ALPHANUMERIC:
                {
                alt17=1;
                }
                break;
            case 28:
                {
                alt17=2;
                }
                break;
            case 31:
                {
                alt17=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 17, 0, input);

                throw nvae;
            }

            switch (alt17) {
                case 1 :
                    // Tester.g:124:17: ALPHANUMERIC ( ALPHANUMERIC | '-' | '_' | '.' )*
                    {
                    match(input,ALPHANUMERIC,FOLLOW_ALPHANUMERIC_in_filestring810); 
                    // Tester.g:124:30: ( ALPHANUMERIC | '-' | '_' | '.' )*
                    loop16:
                    do {
                        int alt16=2;
                        int LA16_0 = input.LA(1);

                        if ( (LA16_0==ALPHANUMERIC||(LA16_0>=28 && LA16_0<=30)) ) {
                            alt16=1;
                        }


                        switch (alt16) {
                    	case 1 :
                    	    // Tester.g:
                    	    {
                    	    if ( input.LA(1)==ALPHANUMERIC||(input.LA(1)>=28 && input.LA(1)<=30) ) {
                    	        input.consume();
                    	        state.errorRecovery=false;
                    	    }
                    	    else {
                    	        MismatchedSetException mse = new MismatchedSetException(null,input);
                    	        throw mse;
                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop16;
                        }
                    } while (true);


                    }
                    break;
                case 2 :
                    // Tester.g:125:17: '.'
                    {
                    match(input,28,FOLLOW_28_in_filestring847); 

                    }
                    break;
                case 3 :
                    // Tester.g:126:17: '..'
                    {
                    match(input,31,FOLLOW_31_in_filestring865); 

                    }
                    break;

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
    // $ANTLR end "filestring"


    // $ANTLR start "integer"
    // Tester.g:129:1: integer : ( DIGIT )+ ;
    public final void integer() throws RecognitionException {
        try {
            // Tester.g:129:10: ( ( DIGIT )+ )
            // Tester.g:129:12: ( DIGIT )+
            {
            // Tester.g:129:12: ( DIGIT )+
            int cnt18=0;
            loop18:
            do {
                int alt18=2;
                int LA18_0 = input.LA(1);

                if ( (LA18_0==DIGIT) ) {
                    alt18=1;
                }


                switch (alt18) {
            	case 1 :
            	    // Tester.g:129:12: DIGIT
            	    {
            	    match(input,DIGIT,FOLLOW_DIGIT_in_integer887); 

            	    }
            	    break;

            	default :
            	    if ( cnt18 >= 1 ) break loop18;
                        EarlyExitException eee =
                            new EarlyExitException(18, input);
                        throw eee;
                }
                cnt18++;
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
    // $ANTLR end "integer"

    // Delegated rules


 

    public static final BitSet FOLLOW_testLocation_in_testGrammar56 = new BitSet(new long[]{0x00000000000400A0L});
    public static final BitSet FOLLOW_test_in_testGrammar74 = new BitSet(new long[]{0x00000000000400A2L});
    public static final BitSet FOLLOW_17_in_testLocation98 = new BitSet(new long[]{0x0000000090000100L});
    public static final BitSet FOLLOW_directory_in_testLocation100 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_18_in_test146 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_TESTNAME_in_test148 = new BitSet(new long[]{0x00000000000000A0L});
    public static final BitSet FOLLOW_PROG_ARGS_in_test163 = new BitSet(new long[]{0x0000000000000040L});
    public static final BitSet FOLLOW_UNCHECKED_CODE_BLOCK_in_test167 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_LOCATION_in_test181 = new BitSet(new long[]{0x0000000000080000L});
    public static final BitSet FOLLOW_19_in_test194 = new BitSet(new long[]{0x0000000090000100L});
    public static final BitSet FOLLOW_directory_in_test196 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_20_in_test198 = new BitSet(new long[]{0x0000000000200000L});
    public static final BitSet FOLLOW_21_in_test216 = new BitSet(new long[]{0x0000000000080000L});
    public static final BitSet FOLLOW_19_in_test227 = new BitSet(new long[]{0x0000000090900100L});
    public static final BitSet FOLLOW_inputs_in_test229 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_20_in_test231 = new BitSet(new long[]{0x0000000000400002L});
    public static final BitSet FOLLOW_22_in_test243 = new BitSet(new long[]{0x0000000000080000L});
    public static final BitSet FOLLOW_19_in_test255 = new BitSet(new long[]{0x0000000001100000L});
    public static final BitSet FOLLOW_outputs_in_test257 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_20_in_test260 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_file_in_inputs295 = new BitSet(new long[]{0x0000000000800002L});
    public static final BitSet FOLLOW_23_in_inputs317 = new BitSet(new long[]{0x0000000090000100L});
    public static final BitSet FOLLOW_file_in_inputs321 = new BitSet(new long[]{0x0000000000800002L});
    public static final BitSet FOLLOW_output_in_outputs351 = new BitSet(new long[]{0x0000000000800002L});
    public static final BitSet FOLLOW_23_in_outputs354 = new BitSet(new long[]{0x0000000001000000L});
    public static final BitSet FOLLOW_output_in_outputs356 = new BitSet(new long[]{0x0000000000800002L});
    public static final BitSet FOLLOW_24_in_output375 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_error_in_output398 = new BitSet(new long[]{0x0000000004800000L});
    public static final BitSet FOLLOW_23_in_output423 = new BitSet(new long[]{0x0000000092000110L});
    public static final BitSet FOLLOW_extraparam_in_output431 = new BitSet(new long[]{0x0000000004800000L});
    public static final BitSet FOLLOW_25_in_output458 = new BitSet(new long[]{0x0000000090000100L});
    public static final BitSet FOLLOW_file_in_output460 = new BitSet(new long[]{0x0000000004800000L});
    public static final BitSet FOLLOW_26_in_output506 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_javastring_in_error533 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_file_in_extraparam605 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_TESTNAME_in_extraparam622 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_file_in_directory642 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_27_in_directory644 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_filestring_in_file663 = new BitSet(new long[]{0x0000000008000002L});
    public static final BitSet FOLLOW_27_in_file666 = new BitSet(new long[]{0x0000000090000100L});
    public static final BitSet FOLLOW_filestring_in_file668 = new BitSet(new long[]{0x0000000008000002L});
    public static final BitSet FOLLOW_integer_in_linenumber684 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_integer_in_charposition704 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_string_in_javastring727 = new BitSet(new long[]{0x0000000010000002L});
    public static final BitSet FOLLOW_28_in_javastring730 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_string_in_javastring732 = new BitSet(new long[]{0x0000000010000002L});
    public static final BitSet FOLLOW_ALPHANUMERIC_in_string756 = new BitSet(new long[]{0x0000000000000102L});
    public static final BitSet FOLLOW_29_in_progArg784 = new BitSet(new long[]{0x00000000B0000100L});
    public static final BitSet FOLLOW_29_in_progArg786 = new BitSet(new long[]{0x0000000090000100L});
    public static final BitSet FOLLOW_filestring_in_progArg789 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ALPHANUMERIC_in_filestring810 = new BitSet(new long[]{0x0000000070000102L});
    public static final BitSet FOLLOW_set_in_filestring812 = new BitSet(new long[]{0x0000000070000102L});
    public static final BitSet FOLLOW_28_in_filestring847 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_31_in_filestring865 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_DIGIT_in_integer887 = new BitSet(new long[]{0x0000000000000202L});

}