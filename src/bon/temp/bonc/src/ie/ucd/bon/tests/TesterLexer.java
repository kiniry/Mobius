// $ANTLR 3.0.1 Tester.g 2008-02-20 14:22:08

  package ie.ucd.bon.tests;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

public class TesterLexer extends Lexer {
    public static final int LINE_COMMENT=8;
    public static final int WHITESPACE=12;
    public static final int T29=29;
    public static final int T28=28;
    public static final int T27=27;
    public static final int T26=26;
    public static final int T25=25;
    public static final int Tokens=30;
    public static final int T24=24;
    public static final int EOF=-1;
    public static final int T23=23;
    public static final int COMMENT_START=10;
    public static final int T22=22;
    public static final int T21=21;
    public static final int T20=20;
    public static final int ALPHA=7;
    public static final int NEWLINE=11;
    public static final int ALPHANUMERIC=5;
    public static final int TESTNAME=4;
    public static final int DIGIT=6;
    public static final int T13=13;
    public static final int T14=14;
    public static final int COMMENT=9;
    public static final int T15=15;
    public static final int T16=16;
    public static final int T17=17;
    public static final int T18=18;
    public static final int T19=19;
    public TesterLexer() {;} 
    public TesterLexer(CharStream input) {
        super(input);
    }
    public String getGrammarFileName() { return "Tester.g"; }

    // $ANTLR start T13
    public final void mT13() throws RecognitionException {
        try {
            int _type = T13;
            // Tester.g:6:5: ( '@Test-Location:' )
            // Tester.g:6:7: '@Test-Location:'
            {
            match("@Test-Location:"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T13

    // $ANTLR start T14
    public final void mT14() throws RecognitionException {
        try {
            int _type = T14;
            // Tester.g:7:5: ( '@Test-name:' )
            // Tester.g:7:7: '@Test-name:'
            {
            match("@Test-name:"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T14

    // $ANTLR start T15
    public final void mT15() throws RecognitionException {
        try {
            int _type = T15;
            // Tester.g:8:5: ( '@Prog-args:' )
            // Tester.g:8:7: '@Prog-args:'
            {
            match("@Prog-args:"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T15

    // $ANTLR start T16
    public final void mT16() throws RecognitionException {
        try {
            int _type = T16;
            // Tester.g:9:5: ( ',' )
            // Tester.g:9:7: ','
            {
            match(','); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T16

    // $ANTLR start T17
    public final void mT17() throws RecognitionException {
        try {
            int _type = T17;
            // Tester.g:10:5: ( '@Location' )
            // Tester.g:10:7: '@Location'
            {
            match("@Location"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T17

    // $ANTLR start T18
    public final void mT18() throws RecognitionException {
        try {
            int _type = T18;
            // Tester.g:11:5: ( '{' )
            // Tester.g:11:7: '{'
            {
            match('{'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T18

    // $ANTLR start T19
    public final void mT19() throws RecognitionException {
        try {
            int _type = T19;
            // Tester.g:12:5: ( '}' )
            // Tester.g:12:7: '}'
            {
            match('}'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T19

    // $ANTLR start T20
    public final void mT20() throws RecognitionException {
        try {
            int _type = T20;
            // Tester.g:13:5: ( '@Input' )
            // Tester.g:13:7: '@Input'
            {
            match("@Input"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T20

    // $ANTLR start T21
    public final void mT21() throws RecognitionException {
        try {
            int _type = T21;
            // Tester.g:14:5: ( '@Output' )
            // Tester.g:14:7: '@Output'
            {
            match("@Output"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T21

    // $ANTLR start T22
    public final void mT22() throws RecognitionException {
        try {
            int _type = T22;
            // Tester.g:15:5: ( '<' )
            // Tester.g:15:7: '<'
            {
            match('<'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T22

    // $ANTLR start T23
    public final void mT23() throws RecognitionException {
        try {
            int _type = T23;
            // Tester.g:16:5: ( '#File:' )
            // Tester.g:16:7: '#File:'
            {
            match("#File:"); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T23

    // $ANTLR start T24
    public final void mT24() throws RecognitionException {
        try {
            int _type = T24;
            // Tester.g:17:5: ( '>' )
            // Tester.g:17:7: '>'
            {
            match('>'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T24

    // $ANTLR start T25
    public final void mT25() throws RecognitionException {
        try {
            int _type = T25;
            // Tester.g:18:5: ( '/' )
            // Tester.g:18:7: '/'
            {
            match('/'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T25

    // $ANTLR start T26
    public final void mT26() throws RecognitionException {
        try {
            int _type = T26;
            // Tester.g:19:5: ( '.' )
            // Tester.g:19:7: '.'
            {
            match('.'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T26

    // $ANTLR start T27
    public final void mT27() throws RecognitionException {
        try {
            int _type = T27;
            // Tester.g:20:5: ( '-' )
            // Tester.g:20:7: '-'
            {
            match('-'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T27

    // $ANTLR start T28
    public final void mT28() throws RecognitionException {
        try {
            int _type = T28;
            // Tester.g:21:5: ( '_' )
            // Tester.g:21:7: '_'
            {
            match('_'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T28

    // $ANTLR start T29
    public final void mT29() throws RecognitionException {
        try {
            int _type = T29;
            // Tester.g:22:5: ( '..' )
            // Tester.g:22:7: '..'
            {
            match(".."); 


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end T29

    // $ANTLR start TESTNAME
    public final void mTESTNAME() throws RecognitionException {
        try {
            int _type = TESTNAME;
            // Tester.g:85:10: ( '\"' ( options {greedy=false; } : ~ ( '\\n' | '\\r' | '\"' ) )* '\"' )
            // Tester.g:85:12: '\"' ( options {greedy=false; } : ~ ( '\\n' | '\\r' | '\"' ) )* '\"'
            {
            match('\"'); 
            // Tester.g:85:16: ( options {greedy=false; } : ~ ( '\\n' | '\\r' | '\"' ) )*
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( (LA1_0=='\"') ) {
                    alt1=2;
                }
                else if ( ((LA1_0>='\u0000' && LA1_0<='\t')||(LA1_0>='\u000B' && LA1_0<='\f')||(LA1_0>='\u000E' && LA1_0<='!')||(LA1_0>='#' && LA1_0<='\uFFFE')) ) {
                    alt1=1;
                }


                switch (alt1) {
            	case 1 :
            	    // Tester.g:85:43: ~ ( '\\n' | '\\r' | '\"' )
            	    {
            	    if ( (input.LA(1)>='\u0000' && input.LA(1)<='\t')||(input.LA(1)>='\u000B' && input.LA(1)<='\f')||(input.LA(1)>='\u000E' && input.LA(1)<='!')||(input.LA(1)>='#' && input.LA(1)<='\uFFFE') ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse =
            	            new MismatchedSetException(null,input);
            	        recover(mse);    throw mse;
            	    }


            	    }
            	    break;

            	default :
            	    break loop1;
                }
            } while (true);

            match('\"'); 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end TESTNAME

    // $ANTLR start ALPHANUMERIC
    public final void mALPHANUMERIC() throws RecognitionException {
        try {
            int _type = ALPHANUMERIC;
            // Tester.g:122:15: ( ALPHA | DIGIT )
            // Tester.g:
            {
            if ( (input.LA(1)>='0' && input.LA(1)<='9')||(input.LA(1)>='A' && input.LA(1)<='Z')||(input.LA(1)>='a' && input.LA(1)<='z') ) {
                input.consume();

            }
            else {
                MismatchedSetException mse =
                    new MismatchedSetException(null,input);
                recover(mse);    throw mse;
            }


            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end ALPHANUMERIC

    // $ANTLR start ALPHA
    public final void mALPHA() throws RecognitionException {
        try {
            // Tester.g:126:8: ( 'A' .. 'Z' | 'a' .. 'z' )
            // Tester.g:
            {
            if ( (input.LA(1)>='A' && input.LA(1)<='Z')||(input.LA(1)>='a' && input.LA(1)<='z') ) {
                input.consume();

            }
            else {
                MismatchedSetException mse =
                    new MismatchedSetException(null,input);
                recover(mse);    throw mse;
            }


            }

        }
        finally {
        }
    }
    // $ANTLR end ALPHA

    // $ANTLR start DIGIT
    public final void mDIGIT() throws RecognitionException {
        try {
            // Tester.g:130:8: ( '0' .. '9' )
            // Tester.g:130:10: '0' .. '9'
            {
            matchRange('0','9'); 

            }

        }
        finally {
        }
    }
    // $ANTLR end DIGIT

    // $ANTLR start COMMENT
    public final void mCOMMENT() throws RecognitionException {
        try {
            int _type = COMMENT;
            // Tester.g:133:10: ( ( LINE_COMMENT )+ )
            // Tester.g:133:13: ( LINE_COMMENT )+
            {
            // Tester.g:133:13: ( LINE_COMMENT )+
            int cnt2=0;
            loop2:
            do {
                int alt2=2;
                int LA2_0 = input.LA(1);

                if ( (LA2_0=='-') ) {
                    alt2=1;
                }


                switch (alt2) {
            	case 1 :
            	    // Tester.g:133:13: LINE_COMMENT
            	    {
            	    mLINE_COMMENT(); 

            	    }
            	    break;

            	default :
            	    if ( cnt2 >= 1 ) break loop2;
                        EarlyExitException eee =
                            new EarlyExitException(2, input);
                        throw eee;
                }
                cnt2++;
            } while (true);

             channel=HIDDEN; 

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end COMMENT

    // $ANTLR start LINE_COMMENT
    public final void mLINE_COMMENT() throws RecognitionException {
        try {
            // Tester.g:137:15: ( COMMENT_START ( options {greedy=false; } : . )* NEWLINE )
            // Tester.g:137:18: COMMENT_START ( options {greedy=false; } : . )* NEWLINE
            {
            mCOMMENT_START(); 
            // Tester.g:137:32: ( options {greedy=false; } : . )*
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( (LA3_0=='\r') ) {
                    alt3=2;
                }
                else if ( (LA3_0=='\n') ) {
                    alt3=2;
                }
                else if ( ((LA3_0>='\u0000' && LA3_0<='\t')||(LA3_0>='\u000B' && LA3_0<='\f')||(LA3_0>='\u000E' && LA3_0<='\uFFFE')) ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // Tester.g:137:59: .
            	    {
            	    matchAny(); 

            	    }
            	    break;

            	default :
            	    break loop3;
                }
            } while (true);

            mNEWLINE(); 

            }

        }
        finally {
        }
    }
    // $ANTLR end LINE_COMMENT

    // $ANTLR start COMMENT_START
    public final void mCOMMENT_START() throws RecognitionException {
        try {
            // Tester.g:141:16: ( '--' )
            // Tester.g:141:18: '--'
            {
            match("--"); 


            }

        }
        finally {
        }
    }
    // $ANTLR end COMMENT_START

    // $ANTLR start NEWLINE
    public final void mNEWLINE() throws RecognitionException {
        try {
            // Tester.g:145:10: ( ( '\\r' )? '\\n' )
            // Tester.g:145:13: ( '\\r' )? '\\n'
            {
            // Tester.g:145:13: ( '\\r' )?
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( (LA4_0=='\r') ) {
                alt4=1;
            }
            switch (alt4) {
                case 1 :
                    // Tester.g:145:13: '\\r'
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
    // $ANTLR end NEWLINE

    // $ANTLR start WHITESPACE
    public final void mWHITESPACE() throws RecognitionException {
        try {
            int _type = WHITESPACE;
            // Tester.g:148:13: ( ( ' ' | '\\n' | '\\r' | '\\t' )+ )
            // Tester.g:148:16: ( ' ' | '\\n' | '\\r' | '\\t' )+
            {
            // Tester.g:148:16: ( ' ' | '\\n' | '\\r' | '\\t' )+
            int cnt5=0;
            loop5:
            do {
                int alt5=2;
                int LA5_0 = input.LA(1);

                if ( ((LA5_0>='\t' && LA5_0<='\n')||LA5_0=='\r'||LA5_0==' ') ) {
                    alt5=1;
                }


                switch (alt5) {
            	case 1 :
            	    // Tester.g:
            	    {
            	    if ( (input.LA(1)>='\t' && input.LA(1)<='\n')||input.LA(1)=='\r'||input.LA(1)==' ' ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse =
            	            new MismatchedSetException(null,input);
            	        recover(mse);    throw mse;
            	    }


            	    }
            	    break;

            	default :
            	    if ( cnt5 >= 1 ) break loop5;
                        EarlyExitException eee =
                            new EarlyExitException(5, input);
                        throw eee;
                }
                cnt5++;
            } while (true);

            channel=HIDDEN;

            }

            this.type = _type;
        }
        finally {
        }
    }
    // $ANTLR end WHITESPACE

    public void mTokens() throws RecognitionException {
        // Tester.g:1:8: ( T13 | T14 | T15 | T16 | T17 | T18 | T19 | T20 | T21 | T22 | T23 | T24 | T25 | T26 | T27 | T28 | T29 | TESTNAME | ALPHANUMERIC | COMMENT | WHITESPACE )
        int alt6=21;
        switch ( input.LA(1) ) {
        case '@':
            {
            switch ( input.LA(2) ) {
            case 'T':
                {
                int LA6_15 = input.LA(3);

                if ( (LA6_15=='e') ) {
                    int LA6_24 = input.LA(4);

                    if ( (LA6_24=='s') ) {
                        int LA6_25 = input.LA(5);

                        if ( (LA6_25=='t') ) {
                            int LA6_26 = input.LA(6);

                            if ( (LA6_26=='-') ) {
                                int LA6_27 = input.LA(7);

                                if ( (LA6_27=='L') ) {
                                    alt6=1;
                                }
                                else if ( (LA6_27=='n') ) {
                                    alt6=2;
                                }
                                else {
                                    NoViableAltException nvae =
                                        new NoViableAltException("1:1: Tokens : ( T13 | T14 | T15 | T16 | T17 | T18 | T19 | T20 | T21 | T22 | T23 | T24 | T25 | T26 | T27 | T28 | T29 | TESTNAME | ALPHANUMERIC | COMMENT | WHITESPACE );", 6, 27, input);

                                    throw nvae;
                                }
                            }
                            else {
                                NoViableAltException nvae =
                                    new NoViableAltException("1:1: Tokens : ( T13 | T14 | T15 | T16 | T17 | T18 | T19 | T20 | T21 | T22 | T23 | T24 | T25 | T26 | T27 | T28 | T29 | TESTNAME | ALPHANUMERIC | COMMENT | WHITESPACE );", 6, 26, input);

                                throw nvae;
                            }
                        }
                        else {
                            NoViableAltException nvae =
                                new NoViableAltException("1:1: Tokens : ( T13 | T14 | T15 | T16 | T17 | T18 | T19 | T20 | T21 | T22 | T23 | T24 | T25 | T26 | T27 | T28 | T29 | TESTNAME | ALPHANUMERIC | COMMENT | WHITESPACE );", 6, 25, input);

                            throw nvae;
                        }
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("1:1: Tokens : ( T13 | T14 | T15 | T16 | T17 | T18 | T19 | T20 | T21 | T22 | T23 | T24 | T25 | T26 | T27 | T28 | T29 | TESTNAME | ALPHANUMERIC | COMMENT | WHITESPACE );", 6, 24, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1:1: Tokens : ( T13 | T14 | T15 | T16 | T17 | T18 | T19 | T20 | T21 | T22 | T23 | T24 | T25 | T26 | T27 | T28 | T29 | TESTNAME | ALPHANUMERIC | COMMENT | WHITESPACE );", 6, 15, input);

                    throw nvae;
                }
                }
                break;
            case 'P':
                {
                alt6=3;
                }
                break;
            case 'L':
                {
                alt6=5;
                }
                break;
            case 'O':
                {
                alt6=9;
                }
                break;
            case 'I':
                {
                alt6=8;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("1:1: Tokens : ( T13 | T14 | T15 | T16 | T17 | T18 | T19 | T20 | T21 | T22 | T23 | T24 | T25 | T26 | T27 | T28 | T29 | TESTNAME | ALPHANUMERIC | COMMENT | WHITESPACE );", 6, 1, input);

                throw nvae;
            }

            }
            break;
        case ',':
            {
            alt6=4;
            }
            break;
        case '{':
            {
            alt6=6;
            }
            break;
        case '}':
            {
            alt6=7;
            }
            break;
        case '<':
            {
            alt6=10;
            }
            break;
        case '#':
            {
            alt6=11;
            }
            break;
        case '>':
            {
            alt6=12;
            }
            break;
        case '/':
            {
            alt6=13;
            }
            break;
        case '.':
            {
            int LA6_9 = input.LA(2);

            if ( (LA6_9=='.') ) {
                alt6=17;
            }
            else {
                alt6=14;}
            }
            break;
        case '-':
            {
            int LA6_10 = input.LA(2);

            if ( (LA6_10=='-') ) {
                alt6=20;
            }
            else {
                alt6=15;}
            }
            break;
        case '_':
            {
            alt6=16;
            }
            break;
        case '\"':
            {
            alt6=18;
            }
            break;
        case '0':
        case '1':
        case '2':
        case '3':
        case '4':
        case '5':
        case '6':
        case '7':
        case '8':
        case '9':
        case 'A':
        case 'B':
        case 'C':
        case 'D':
        case 'E':
        case 'F':
        case 'G':
        case 'H':
        case 'I':
        case 'J':
        case 'K':
        case 'L':
        case 'M':
        case 'N':
        case 'O':
        case 'P':
        case 'Q':
        case 'R':
        case 'S':
        case 'T':
        case 'U':
        case 'V':
        case 'W':
        case 'X':
        case 'Y':
        case 'Z':
        case 'a':
        case 'b':
        case 'c':
        case 'd':
        case 'e':
        case 'f':
        case 'g':
        case 'h':
        case 'i':
        case 'j':
        case 'k':
        case 'l':
        case 'm':
        case 'n':
        case 'o':
        case 'p':
        case 'q':
        case 'r':
        case 's':
        case 't':
        case 'u':
        case 'v':
        case 'w':
        case 'x':
        case 'y':
        case 'z':
            {
            alt6=19;
            }
            break;
        case '\t':
        case '\n':
        case '\r':
        case ' ':
            {
            alt6=21;
            }
            break;
        default:
            NoViableAltException nvae =
                new NoViableAltException("1:1: Tokens : ( T13 | T14 | T15 | T16 | T17 | T18 | T19 | T20 | T21 | T22 | T23 | T24 | T25 | T26 | T27 | T28 | T29 | TESTNAME | ALPHANUMERIC | COMMENT | WHITESPACE );", 6, 0, input);

            throw nvae;
        }

        switch (alt6) {
            case 1 :
                // Tester.g:1:10: T13
                {
                mT13(); 

                }
                break;
            case 2 :
                // Tester.g:1:14: T14
                {
                mT14(); 

                }
                break;
            case 3 :
                // Tester.g:1:18: T15
                {
                mT15(); 

                }
                break;
            case 4 :
                // Tester.g:1:22: T16
                {
                mT16(); 

                }
                break;
            case 5 :
                // Tester.g:1:26: T17
                {
                mT17(); 

                }
                break;
            case 6 :
                // Tester.g:1:30: T18
                {
                mT18(); 

                }
                break;
            case 7 :
                // Tester.g:1:34: T19
                {
                mT19(); 

                }
                break;
            case 8 :
                // Tester.g:1:38: T20
                {
                mT20(); 

                }
                break;
            case 9 :
                // Tester.g:1:42: T21
                {
                mT21(); 

                }
                break;
            case 10 :
                // Tester.g:1:46: T22
                {
                mT22(); 

                }
                break;
            case 11 :
                // Tester.g:1:50: T23
                {
                mT23(); 

                }
                break;
            case 12 :
                // Tester.g:1:54: T24
                {
                mT24(); 

                }
                break;
            case 13 :
                // Tester.g:1:58: T25
                {
                mT25(); 

                }
                break;
            case 14 :
                // Tester.g:1:62: T26
                {
                mT26(); 

                }
                break;
            case 15 :
                // Tester.g:1:66: T27
                {
                mT27(); 

                }
                break;
            case 16 :
                // Tester.g:1:70: T28
                {
                mT28(); 

                }
                break;
            case 17 :
                // Tester.g:1:74: T29
                {
                mT29(); 

                }
                break;
            case 18 :
                // Tester.g:1:78: TESTNAME
                {
                mTESTNAME(); 

                }
                break;
            case 19 :
                // Tester.g:1:87: ALPHANUMERIC
                {
                mALPHANUMERIC(); 

                }
                break;
            case 20 :
                // Tester.g:1:100: COMMENT
                {
                mCOMMENT(); 

                }
                break;
            case 21 :
                // Tester.g:1:108: WHITESPACE
                {
                mWHITESPACE(); 

                }
                break;

        }

    }


 

}