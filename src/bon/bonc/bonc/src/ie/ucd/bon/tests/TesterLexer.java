// $ANTLR 3.1.3 Mar 18, 2009 10:09:25 Tester.g 2009-08-25 14:21:05

/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.tests;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

public class TesterLexer extends Lexer {
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
    public static final int T__30=30;
    public static final int T__19=19;
    public static final int T__31=31;
    public static final int T__18=18;
    public static final int NEWLINE=15;
    public static final int T__17=17;
    public static final int ALPHANUMERIC=8;
    public static final int TESTNAME=4;
    public static final int LOCATION=7;
    public static final int DIGIT=9;
    public static final int COMMENT=13;

      boolean curliesMode = false;


    // delegates
    // delegators

    public TesterLexer() {;} 
    public TesterLexer(CharStream input) {
        this(input, new RecognizerSharedState());
    }
    public TesterLexer(CharStream input, RecognizerSharedState state) {
        super(input,state);

    }
    public String getGrammarFileName() { return "Tester.g"; }

    // $ANTLR start "T__17"
    public final void mT__17() throws RecognitionException {
        try {
            int _type = T__17;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:14:7: ( '@Test-Location:' )
            // Tester.g:14:9: '@Test-Location:'
            {
            match("@Test-Location:"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__17"

    // $ANTLR start "T__18"
    public final void mT__18() throws RecognitionException {
        try {
            int _type = T__18;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:15:7: ( '@Test-name:' )
            // Tester.g:15:9: '@Test-name:'
            {
            match("@Test-name:"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__18"

    // $ANTLR start "T__19"
    public final void mT__19() throws RecognitionException {
        try {
            int _type = T__19;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:16:7: ( '{' )
            // Tester.g:16:9: '{'
            {
            match('{'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__19"

    // $ANTLR start "T__20"
    public final void mT__20() throws RecognitionException {
        try {
            int _type = T__20;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:17:7: ( '}' )
            // Tester.g:17:9: '}'
            {
            match('}'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__20"

    // $ANTLR start "T__21"
    public final void mT__21() throws RecognitionException {
        try {
            int _type = T__21;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:18:7: ( '@Input' )
            // Tester.g:18:9: '@Input'
            {
            match("@Input"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__21"

    // $ANTLR start "T__22"
    public final void mT__22() throws RecognitionException {
        try {
            int _type = T__22;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:19:7: ( '@Output' )
            // Tester.g:19:9: '@Output'
            {
            match("@Output"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__22"

    // $ANTLR start "T__23"
    public final void mT__23() throws RecognitionException {
        try {
            int _type = T__23;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:20:7: ( ',' )
            // Tester.g:20:9: ','
            {
            match(','); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__23"

    // $ANTLR start "T__24"
    public final void mT__24() throws RecognitionException {
        try {
            int _type = T__24;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:21:7: ( '<' )
            // Tester.g:21:9: '<'
            {
            match('<'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__24"

    // $ANTLR start "T__25"
    public final void mT__25() throws RecognitionException {
        try {
            int _type = T__25;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:22:7: ( '#File:' )
            // Tester.g:22:9: '#File:'
            {
            match("#File:"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__25"

    // $ANTLR start "T__26"
    public final void mT__26() throws RecognitionException {
        try {
            int _type = T__26;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:23:7: ( '>' )
            // Tester.g:23:9: '>'
            {
            match('>'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__26"

    // $ANTLR start "T__27"
    public final void mT__27() throws RecognitionException {
        try {
            int _type = T__27;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:24:7: ( '/' )
            // Tester.g:24:9: '/'
            {
            match('/'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__27"

    // $ANTLR start "T__28"
    public final void mT__28() throws RecognitionException {
        try {
            int _type = T__28;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:25:7: ( '.' )
            // Tester.g:25:9: '.'
            {
            match('.'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__28"

    // $ANTLR start "T__29"
    public final void mT__29() throws RecognitionException {
        try {
            int _type = T__29;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:26:7: ( '-' )
            // Tester.g:26:9: '-'
            {
            match('-'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__29"

    // $ANTLR start "T__30"
    public final void mT__30() throws RecognitionException {
        try {
            int _type = T__30;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:27:7: ( '_' )
            // Tester.g:27:9: '_'
            {
            match('_'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__30"

    // $ANTLR start "T__31"
    public final void mT__31() throws RecognitionException {
        try {
            int _type = T__31;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:28:7: ( '..' )
            // Tester.g:28:9: '..'
            {
            match(".."); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__31"

    // $ANTLR start "TESTNAME"
    public final void mTESTNAME() throws RecognitionException {
        try {
            int _type = TESTNAME;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:92:10: ( '\"' ( options {greedy=false; } : ~ ( '\\n' | '\\r' | '\"' ) )* '\"' )
            // Tester.g:92:12: '\"' ( options {greedy=false; } : ~ ( '\\n' | '\\r' | '\"' ) )* '\"'
            {
            match('\"'); 
            // Tester.g:92:16: ( options {greedy=false; } : ~ ( '\\n' | '\\r' | '\"' ) )*
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( ((LA1_0>='\u0000' && LA1_0<='\t')||(LA1_0>='\u000B' && LA1_0<='\f')||(LA1_0>='\u000E' && LA1_0<='!')||(LA1_0>='#' && LA1_0<='\uFFFF')) ) {
                    alt1=1;
                }
                else if ( (LA1_0=='\"') ) {
                    alt1=2;
                }


                switch (alt1) {
            	case 1 :
            	    // Tester.g:92:43: ~ ( '\\n' | '\\r' | '\"' )
            	    {
            	    if ( (input.LA(1)>='\u0000' && input.LA(1)<='\t')||(input.LA(1)>='\u000B' && input.LA(1)<='\f')||(input.LA(1)>='\u000E' && input.LA(1)<='!')||(input.LA(1)>='#' && input.LA(1)<='\uFFFF') ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    break loop1;
                }
            } while (true);

            match('\"'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "TESTNAME"

    // $ANTLR start "PROG_ARGS"
    public final void mPROG_ARGS() throws RecognitionException {
        try {
            int _type = PROG_ARGS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:132:12: ( '@Prog-args:' )
            // Tester.g:132:14: '@Prog-args:'
            {
            match("@Prog-args:"); 

             curliesMode = true; 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "PROG_ARGS"

    // $ANTLR start "LOCATION"
    public final void mLOCATION() throws RecognitionException {
        try {
            int _type = LOCATION;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:133:11: ( '@Location' )
            // Tester.g:133:13: '@Location'
            {
            match("@Location"); 

             curliesMode = false; 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "LOCATION"

    // $ANTLR start "UNCHECKED_CODE_BLOCK"
    public final void mUNCHECKED_CODE_BLOCK() throws RecognitionException {
        try {
            int _type = UNCHECKED_CODE_BLOCK;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:134:23: ({...}? => UNCHECKED_CODE )
            // Tester.g:135:1: {...}? => UNCHECKED_CODE
            {
            if ( !((curliesMode)) ) {
                throw new FailedPredicateException(input, "UNCHECKED_CODE_BLOCK", "curliesMode");
            }
            mUNCHECKED_CODE(); 
             setText(getText().substring(1, getText().length()-1).trim()); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "UNCHECKED_CODE_BLOCK"

    // $ANTLR start "UNCHECKED_CODE"
    public final void mUNCHECKED_CODE() throws RecognitionException {
        try {
            // Tester.g:140:16: ( '{' ( options {greedy=false; k=2; } : UNCHECKED_CODE | . )* '}' )
            // Tester.g:141:3: '{' ( options {greedy=false; k=2; } : UNCHECKED_CODE | . )* '}'
            {
            match('{'); 
            // Tester.g:142:3: ( options {greedy=false; k=2; } : UNCHECKED_CODE | . )*
            loop2:
            do {
                int alt2=3;
                int LA2_0 = input.LA(1);

                if ( (LA2_0=='}') ) {
                    alt2=3;
                }
                else if ( (LA2_0=='{') ) {
                    alt2=1;
                }
                else if ( ((LA2_0>='\u0000' && LA2_0<='z')||LA2_0=='|'||(LA2_0>='~' && LA2_0<='\uFFFF')) ) {
                    alt2=2;
                }


                switch (alt2) {
            	case 1 :
            	    // Tester.g:143:5: UNCHECKED_CODE
            	    {
            	    mUNCHECKED_CODE(); 

            	    }
            	    break;
            	case 2 :
            	    // Tester.g:144:5: .
            	    {
            	    matchAny(); 

            	    }
            	    break;

            	default :
            	    break loop2;
                }
            } while (true);

            match('}'); 

            }

        }
        finally {
        }
    }
    // $ANTLR end "UNCHECKED_CODE"

    // $ANTLR start "ALPHANUMERIC"
    public final void mALPHANUMERIC() throws RecognitionException {
        try {
            int _type = ALPHANUMERIC;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:149:15: ( ALPHA | DIGIT )
            // Tester.g:
            {
            if ( (input.LA(1)>='0' && input.LA(1)<='9')||(input.LA(1)>='A' && input.LA(1)<='Z')||(input.LA(1)>='a' && input.LA(1)<='z') ) {
                input.consume();

            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;}


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ALPHANUMERIC"

    // $ANTLR start "ALPHA"
    public final void mALPHA() throws RecognitionException {
        try {
            // Tester.g:153:8: ( 'A' .. 'Z' | 'a' .. 'z' )
            // Tester.g:
            {
            if ( (input.LA(1)>='A' && input.LA(1)<='Z')||(input.LA(1)>='a' && input.LA(1)<='z') ) {
                input.consume();

            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;}


            }

        }
        finally {
        }
    }
    // $ANTLR end "ALPHA"

    // $ANTLR start "DIGIT"
    public final void mDIGIT() throws RecognitionException {
        try {
            // Tester.g:157:8: ( '0' .. '9' )
            // Tester.g:157:10: '0' .. '9'
            {
            matchRange('0','9'); 

            }

        }
        finally {
        }
    }
    // $ANTLR end "DIGIT"

    // $ANTLR start "COMMENT"
    public final void mCOMMENT() throws RecognitionException {
        try {
            int _type = COMMENT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:160:10: ( ( LINE_COMMENT )+ )
            // Tester.g:160:13: ( LINE_COMMENT )+
            {
            // Tester.g:160:13: ( LINE_COMMENT )+
            int cnt3=0;
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( (LA3_0=='/') ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // Tester.g:160:13: LINE_COMMENT
            	    {
            	    mLINE_COMMENT(); 

            	    }
            	    break;

            	default :
            	    if ( cnt3 >= 1 ) break loop3;
                        EarlyExitException eee =
                            new EarlyExitException(3, input);
                        throw eee;
                }
                cnt3++;
            } while (true);

             _channel=HIDDEN; 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "COMMENT"

    // $ANTLR start "LINE_COMMENT"
    public final void mLINE_COMMENT() throws RecognitionException {
        try {
            // Tester.g:164:15: ( COMMENT_START ( options {greedy=false; } : . )* NEWLINE )
            // Tester.g:164:18: COMMENT_START ( options {greedy=false; } : . )* NEWLINE
            {
            mCOMMENT_START(); 
            // Tester.g:164:32: ( options {greedy=false; } : . )*
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( (LA4_0=='\r') ) {
                    alt4=2;
                }
                else if ( (LA4_0=='\n') ) {
                    alt4=2;
                }
                else if ( ((LA4_0>='\u0000' && LA4_0<='\t')||(LA4_0>='\u000B' && LA4_0<='\f')||(LA4_0>='\u000E' && LA4_0<='\uFFFF')) ) {
                    alt4=1;
                }


                switch (alt4) {
            	case 1 :
            	    // Tester.g:164:59: .
            	    {
            	    matchAny(); 

            	    }
            	    break;

            	default :
            	    break loop4;
                }
            } while (true);

            mNEWLINE(); 

            }

        }
        finally {
        }
    }
    // $ANTLR end "LINE_COMMENT"

    // $ANTLR start "COMMENT_START"
    public final void mCOMMENT_START() throws RecognitionException {
        try {
            // Tester.g:168:16: ( '//' )
            // Tester.g:168:18: '//'
            {
            match("//"); 


            }

        }
        finally {
        }
    }
    // $ANTLR end "COMMENT_START"

    // $ANTLR start "NEWLINE"
    public final void mNEWLINE() throws RecognitionException {
        try {
            // Tester.g:172:10: ( ( '\\r' )? '\\n' )
            // Tester.g:172:13: ( '\\r' )? '\\n'
            {
            // Tester.g:172:13: ( '\\r' )?
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0=='\r') ) {
                alt5=1;
            }
            switch (alt5) {
                case 1 :
                    // Tester.g:172:13: '\\r'
                    {
                    match('\r'); 

                    }
                    break;

            }

            match('\n'); 

            }

        }
        finally {
        }
    }
    // $ANTLR end "NEWLINE"

    // $ANTLR start "WHITESPACE"
    public final void mWHITESPACE() throws RecognitionException {
        try {
            int _type = WHITESPACE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Tester.g:175:13: ( ( ' ' | '\\n' | '\\r' | '\\t' )+ )
            // Tester.g:175:16: ( ' ' | '\\n' | '\\r' | '\\t' )+
            {
            // Tester.g:175:16: ( ' ' | '\\n' | '\\r' | '\\t' )+
            int cnt6=0;
            loop6:
            do {
                int alt6=2;
                int LA6_0 = input.LA(1);

                if ( ((LA6_0>='\t' && LA6_0<='\n')||LA6_0=='\r'||LA6_0==' ') ) {
                    alt6=1;
                }


                switch (alt6) {
            	case 1 :
            	    // Tester.g:
            	    {
            	    if ( (input.LA(1)>='\t' && input.LA(1)<='\n')||input.LA(1)=='\r'||input.LA(1)==' ' ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    if ( cnt6 >= 1 ) break loop6;
                        EarlyExitException eee =
                            new EarlyExitException(6, input);
                        throw eee;
                }
                cnt6++;
            } while (true);

            _channel=HIDDEN;

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "WHITESPACE"

    public void mTokens() throws RecognitionException {
        // Tester.g:1:8: ( T__17 | T__18 | T__19 | T__20 | T__21 | T__22 | T__23 | T__24 | T__25 | T__26 | T__27 | T__28 | T__29 | T__30 | T__31 | TESTNAME | PROG_ARGS | LOCATION | UNCHECKED_CODE_BLOCK | ALPHANUMERIC | COMMENT | WHITESPACE )
        int alt7=22;
        alt7 = dfa7.predict(input);
        switch (alt7) {
            case 1 :
                // Tester.g:1:10: T__17
                {
                mT__17(); 

                }
                break;
            case 2 :
                // Tester.g:1:16: T__18
                {
                mT__18(); 

                }
                break;
            case 3 :
                // Tester.g:1:22: T__19
                {
                mT__19(); 

                }
                break;
            case 4 :
                // Tester.g:1:28: T__20
                {
                mT__20(); 

                }
                break;
            case 5 :
                // Tester.g:1:34: T__21
                {
                mT__21(); 

                }
                break;
            case 6 :
                // Tester.g:1:40: T__22
                {
                mT__22(); 

                }
                break;
            case 7 :
                // Tester.g:1:46: T__23
                {
                mT__23(); 

                }
                break;
            case 8 :
                // Tester.g:1:52: T__24
                {
                mT__24(); 

                }
                break;
            case 9 :
                // Tester.g:1:58: T__25
                {
                mT__25(); 

                }
                break;
            case 10 :
                // Tester.g:1:64: T__26
                {
                mT__26(); 

                }
                break;
            case 11 :
                // Tester.g:1:70: T__27
                {
                mT__27(); 

                }
                break;
            case 12 :
                // Tester.g:1:76: T__28
                {
                mT__28(); 

                }
                break;
            case 13 :
                // Tester.g:1:82: T__29
                {
                mT__29(); 

                }
                break;
            case 14 :
                // Tester.g:1:88: T__30
                {
                mT__30(); 

                }
                break;
            case 15 :
                // Tester.g:1:94: T__31
                {
                mT__31(); 

                }
                break;
            case 16 :
                // Tester.g:1:100: TESTNAME
                {
                mTESTNAME(); 

                }
                break;
            case 17 :
                // Tester.g:1:109: PROG_ARGS
                {
                mPROG_ARGS(); 

                }
                break;
            case 18 :
                // Tester.g:1:119: LOCATION
                {
                mLOCATION(); 

                }
                break;
            case 19 :
                // Tester.g:1:128: UNCHECKED_CODE_BLOCK
                {
                mUNCHECKED_CODE_BLOCK(); 

                }
                break;
            case 20 :
                // Tester.g:1:149: ALPHANUMERIC
                {
                mALPHANUMERIC(); 

                }
                break;
            case 21 :
                // Tester.g:1:162: COMMENT
                {
                mCOMMENT(); 

                }
                break;
            case 22 :
                // Tester.g:1:170: WHITESPACE
                {
                mWHITESPACE(); 

                }
                break;

        }

    }


    protected DFA7 dfa7 = new DFA7(this);
    static final String DFA7_eotS =
        "\2\uffff\1\24\5\uffff\1\27\1\31\26\uffff";
    static final String DFA7_eofS =
        "\40\uffff";
    static final String DFA7_minS =
        "\1\11\1\111\1\0\5\uffff\1\57\1\56\5\uffff\1\145\12\uffff\1\163\1"+
        "\164\1\55\1\114\2\uffff";
    static final String DFA7_maxS =
        "\1\175\1\124\1\uffff\5\uffff\1\57\1\56\5\uffff\1\145\12\uffff\1"+
        "\163\1\164\1\55\1\156\2\uffff";
    static final String DFA7_acceptS =
        "\3\uffff\1\4\1\7\1\10\1\11\1\12\2\uffff\1\15\1\16\1\20\1\24\1\26"+
        "\1\uffff\1\5\1\6\1\21\1\22\1\3\1\23\1\25\1\13\1\17\1\14\4\uffff"+
        "\1\1\1\2";
    static final String DFA7_specialS =
        "\2\uffff\1\0\35\uffff}>";
    static final String[] DFA7_transitionS = {
            "\2\16\2\uffff\1\16\22\uffff\1\16\1\uffff\1\14\1\6\10\uffff\1"+
            "\4\1\12\1\11\1\10\12\15\2\uffff\1\5\1\uffff\1\7\1\uffff\1\1"+
            "\32\15\4\uffff\1\13\1\uffff\32\15\1\2\1\uffff\1\3",
            "\1\20\2\uffff\1\23\2\uffff\1\21\1\22\3\uffff\1\17",
            "\0\25",
            "",
            "",
            "",
            "",
            "",
            "\1\26",
            "\1\30",
            "",
            "",
            "",
            "",
            "",
            "\1\32",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "\1\33",
            "\1\34",
            "\1\35",
            "\1\36\41\uffff\1\37",
            "",
            ""
    };

    static final short[] DFA7_eot = DFA.unpackEncodedString(DFA7_eotS);
    static final short[] DFA7_eof = DFA.unpackEncodedString(DFA7_eofS);
    static final char[] DFA7_min = DFA.unpackEncodedStringToUnsignedChars(DFA7_minS);
    static final char[] DFA7_max = DFA.unpackEncodedStringToUnsignedChars(DFA7_maxS);
    static final short[] DFA7_accept = DFA.unpackEncodedString(DFA7_acceptS);
    static final short[] DFA7_special = DFA.unpackEncodedString(DFA7_specialS);
    static final short[][] DFA7_transition;

    static {
        int numStates = DFA7_transitionS.length;
        DFA7_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA7_transition[i] = DFA.unpackEncodedString(DFA7_transitionS[i]);
        }
    }

    class DFA7 extends DFA {

        public DFA7(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 7;
            this.eot = DFA7_eot;
            this.eof = DFA7_eof;
            this.min = DFA7_min;
            this.max = DFA7_max;
            this.accept = DFA7_accept;
            this.special = DFA7_special;
            this.transition = DFA7_transition;
        }
        public String getDescription() {
            return "1:1: Tokens : ( T__17 | T__18 | T__19 | T__20 | T__21 | T__22 | T__23 | T__24 | T__25 | T__26 | T__27 | T__28 | T__29 | T__30 | T__31 | TESTNAME | PROG_ARGS | LOCATION | UNCHECKED_CODE_BLOCK | ALPHANUMERIC | COMMENT | WHITESPACE );";
        }
        public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
            IntStream input = _input;
        	int _s = s;
            switch ( s ) {
                    case 0 : 
                        int LA7_2 = input.LA(1);

                         
                        int index7_2 = input.index();
                        input.rewind();
                        s = -1;
                        if ( ((LA7_2>='\u0000' && LA7_2<='\uFFFF')) && ((curliesMode))) {s = 21;}

                        else s = 20;

                         
                        input.seek(index7_2);
                        if ( s>=0 ) return s;
                        break;
            }
            NoViableAltException nvae =
                new NoViableAltException(getDescription(), 7, _s, input);
            error(nvae);
            throw nvae;
        }
    }
 

}