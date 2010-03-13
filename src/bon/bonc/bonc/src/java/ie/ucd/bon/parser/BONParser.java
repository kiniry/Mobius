// $ANTLR 3.1.3 Apr 15, 2009 15:48:38 /home/fintan/workspaces/bon/bonc/src/BON.g 2010-03-11 11:56:28

  package ie.ucd.bon.parser; 
  
  import ie.ucd.bon.parser.errors.MissingElementParseError;
  import ie.ucd.bon.ast.*;
  import java.io.File;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;
/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
public class BONParser extends AbstractBONParser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "MANIFEST_STRING", "IDENTIFIER", "INTEGER", "CHARACTER_CONSTANT", "REAL", "NEWLINE", "MANIFEST_TEXTBLOCK_START", "MANIFEST_TEXTBLOCK_MIDDLE", "MANIFEST_TEXTBLOCK_END", "LINE_COMMENT", "COMMENT", "COMMENT_START", "DIGIT", "ALPHA", "ALPHANUMERIC_OR_UNDERSCORE", "ALPHANUMERIC", "UNDERSCORE", "LOWER", "UPPER", "WHITESPACE", "'dictionary'", "'end'", "'class'", "'cluster'", "'system_chart'", "'explanation'", "'indexing'", "'part'", "'description'", "';'", "':'", "','", "'cluster_chart'", "'class_chart'", "'inherit'", "'query'", "'command'", "'constraint'", "'('", "')'", "'event_chart'", "'incoming'", "'outgoing'", "'event'", "'involves'", "'scenario_chart'", "'scenario'", "'creation_chart'", "'creator'", "'creates'", "'static_diagram'", "'component'", "'reused'", "'root'", "'deferred'", "'effective'", "'persistent'", "'interfaced'", "'{'", "'}'", "'client'", "'->'", "'['", "']'", "'...'", "':{'", "'.'", "'invariant'", "'feature'", "'redefined'", "'Void'", "'require'", "'ensure'", "'^'", "'<-'", "'prefix'", "'\"'", "'infix'", "'for_all'", "'exists'", "'such_that'", "'it_holds'", "'member_of'", "'..'", "'Current'", "'Result'", "'true'", "'false'", "'dynamic_diagram'", "'action'", "'nameless'", "'object_group'", "'object_stack'", "'object'", "'calls'", "'string_marks'", "'concatenator'", "'keyword_prefix'", "'<->'", "'+'", "'-'", "'and'", "'or'", "'xor'", "'delta'", "'old'", "'not'", "'<'", "'>'", "'<='", "'>='", "'='", "'/='", "'*'", "'/'", "'//'", "'\\\\\\\\'"
    };
    public static final int T__29=29;
    public static final int T__28=28;
    public static final int T__27=27;
    public static final int T__26=26;
    public static final int T__25=25;
    public static final int T__24=24;
    public static final int EOF=-1;
    public static final int T__93=93;
    public static final int T__94=94;
    public static final int T__91=91;
    public static final int T__92=92;
    public static final int T__90=90;
    public static final int MANIFEST_TEXTBLOCK_END=12;
    public static final int ALPHANUMERIC_OR_UNDERSCORE=18;
    public static final int COMMENT=14;
    public static final int T__99=99;
    public static final int T__98=98;
    public static final int T__97=97;
    public static final int T__96=96;
    public static final int T__95=95;
    public static final int T__80=80;
    public static final int T__81=81;
    public static final int T__82=82;
    public static final int T__83=83;
    public static final int LINE_COMMENT=13;
    public static final int WHITESPACE=23;
    public static final int UNDERSCORE=20;
    public static final int T__85=85;
    public static final int T__84=84;
    public static final int T__87=87;
    public static final int T__86=86;
    public static final int T__89=89;
    public static final int ALPHA=17;
    public static final int T__88=88;
    public static final int REAL=8;
    public static final int T__71=71;
    public static final int T__72=72;
    public static final int T__70=70;
    public static final int LOWER=21;
    public static final int T__76=76;
    public static final int T__75=75;
    public static final int T__74=74;
    public static final int T__73=73;
    public static final int UPPER=22;
    public static final int T__79=79;
    public static final int T__78=78;
    public static final int T__77=77;
    public static final int T__68=68;
    public static final int T__69=69;
    public static final int T__66=66;
    public static final int T__67=67;
    public static final int T__64=64;
    public static final int T__65=65;
    public static final int T__62=62;
    public static final int T__63=63;
    public static final int CHARACTER_CONSTANT=7;
    public static final int T__118=118;
    public static final int T__119=119;
    public static final int T__116=116;
    public static final int T__117=117;
    public static final int T__114=114;
    public static final int T__115=115;
    public static final int T__120=120;
    public static final int T__61=61;
    public static final int T__60=60;
    public static final int COMMENT_START=15;
    public static final int T__55=55;
    public static final int T__56=56;
    public static final int T__57=57;
    public static final int T__58=58;
    public static final int T__51=51;
    public static final int T__52=52;
    public static final int T__53=53;
    public static final int T__54=54;
    public static final int T__107=107;
    public static final int T__108=108;
    public static final int T__109=109;
    public static final int IDENTIFIER=5;
    public static final int ALPHANUMERIC=19;
    public static final int T__59=59;
    public static final int T__103=103;
    public static final int MANIFEST_TEXTBLOCK_START=10;
    public static final int T__104=104;
    public static final int T__105=105;
    public static final int T__106=106;
    public static final int T__111=111;
    public static final int T__110=110;
    public static final int T__113=113;
    public static final int T__112=112;
    public static final int DIGIT=16;
    public static final int T__50=50;
    public static final int INTEGER=6;
    public static final int T__42=42;
    public static final int T__43=43;
    public static final int T__40=40;
    public static final int T__41=41;
    public static final int T__46=46;
    public static final int T__47=47;
    public static final int T__44=44;
    public static final int T__45=45;
    public static final int T__48=48;
    public static final int T__49=49;
    public static final int T__102=102;
    public static final int T__101=101;
    public static final int T__100=100;
    public static final int MANIFEST_STRING=4;
    public static final int T__30=30;
    public static final int T__31=31;
    public static final int T__32=32;
    public static final int T__33=33;
    public static final int T__34=34;
    public static final int NEWLINE=9;
    public static final int T__35=35;
    public static final int T__36=36;
    public static final int T__37=37;
    public static final int T__38=38;
    public static final int T__39=39;
    public static final int MANIFEST_TEXTBLOCK_MIDDLE=11;

    // delegates
    // delegators


        public BONParser(TokenStream input) {
            this(input, new RecognizerSharedState());
        }
        public BONParser(TokenStream input, RecognizerSharedState state) {
            super(input, state);
             
        }
        

    public String[] getTokenNames() { return BONParser.tokenNames; }
    public String getGrammarFileName() { return "/home/fintan/workspaces/bon/bonc/src/BON.g"; }


      //Nothing



    // $ANTLR start "prog"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:32:1: prog returns [BonSourceFile bonSource] : (bs= bon_specification EOF | i= indexing bs= bon_specification EOF | e= EOF | indexing e= EOF );
    public final BonSourceFile prog() throws RecognitionException {
        BonSourceFile bonSource = null;

        Token e=null;
        BONParser.bon_specification_return bs = null;

        BONParser.indexing_return i = null;

        BONParser.indexing_return indexing1 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:38:40: (bs= bon_specification EOF | i= indexing bs= bon_specification EOF | e= EOF | indexing e= EOF )
            int alt1=4;
            alt1 = dfa1.predict(input);
            switch (alt1) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:39:10: bs= bon_specification EOF
                    {
                    pushFollow(FOLLOW_bon_specification_in_prog70);
                    bs=bon_specification();

                    state._fsp--;
                    if (state.failed) return bonSource;
                    match(input,EOF,FOLLOW_EOF_in_prog72); if (state.failed) return bonSource;
                    if ( state.backtracking==0 ) {
                       if(isOk()) bonSource = BonSourceFile.mk((bs!=null?bs.spec_els:null), null, getSLoc((bs!=null?((Token)bs.start):null), (bs!=null?((Token)bs.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:42:10: i= indexing bs= bon_specification EOF
                    {
                    pushFollow(FOLLOW_indexing_in_prog105);
                    i=indexing();

                    state._fsp--;
                    if (state.failed) return bonSource;
                    pushFollow(FOLLOW_bon_specification_in_prog109);
                    bs=bon_specification();

                    state._fsp--;
                    if (state.failed) return bonSource;
                    match(input,EOF,FOLLOW_EOF_in_prog111); if (state.failed) return bonSource;
                    if ( state.backtracking==0 ) {
                       if(isOk()) bonSource = BonSourceFile.mk((bs!=null?bs.spec_els:null), (i!=null?i.indexing:null), getSLoc((i!=null?((Token)i.start):null), (bs!=null?((Token)bs.stop):null))); 
                    }

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:45:10: e= EOF
                    {
                    e=(Token)match(input,EOF,FOLLOW_EOF_in_prog144); if (state.failed) return bonSource;
                    if ( state.backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(e), "at least one specification entry", "in source file", true)); 
                    }
                    if ( state.backtracking==0 ) {
                       bonSource = BonSourceFile.mk(Constants.NO_SPEC_ELEMS, null, getSLoc(e)); 
                    }

                    }
                    break;
                case 4 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:49:10: indexing e= EOF
                    {
                    pushFollow(FOLLOW_indexing_in_prog188);
                    indexing1=indexing();

                    state._fsp--;
                    if (state.failed) return bonSource;
                    e=(Token)match(input,EOF,FOLLOW_EOF_in_prog192); if (state.failed) return bonSource;
                    if ( state.backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(e), "at least one specification entry", "in source file", true)); 
                    }
                    if ( state.backtracking==0 ) {
                       if(isOk()) bonSource = BonSourceFile.mk(Constants.NO_SPEC_ELEMS, (indexing1!=null?indexing1.indexing:null), getSLoc((indexing1!=null?((Token)indexing1.start):null),(indexing1!=null?((Token)indexing1.stop):null))); 
                    }

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
        return bonSource;
    }
    // $ANTLR end "prog"

    public static class bon_specification_return extends ParserRuleReturnScope {
        public List<SpecificationElement> spec_els;
    };

    // $ANTLR start "bon_specification"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:54:1: bon_specification returns [List<SpecificationElement> spec_els] : (se= specification_element )+ ;
    public final BONParser.bon_specification_return bon_specification() throws RecognitionException {
        BONParser.bon_specification_return retval = new BONParser.bon_specification_return();
        retval.start = input.LT(1);

        SpecificationElement se = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:58:65: ( (se= specification_element )+ )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:59:3: (se= specification_element )+
            {
            if ( state.backtracking==0 ) {
               retval.spec_els = createList(); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:60:3: (se= specification_element )+
            int cnt2=0;
            loop2:
            do {
                int alt2=2;
                int LA2_0 = input.LA(1);

                if ( (LA2_0==24||LA2_0==28||(LA2_0>=36 && LA2_0<=37)||LA2_0==44||LA2_0==49||LA2_0==51||LA2_0==54||LA2_0==92) ) {
                    alt2=1;
                }


                switch (alt2) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:60:5: se= specification_element
            	    {
            	    pushFollow(FOLLOW_specification_element_in_bon_specification241);
            	    se=specification_element();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.spec_els.add(se); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt2 >= 1 ) break loop2;
            	    if (state.backtracking>0) {state.failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(2, input);
                        throw eee;
                }
                cnt2++;
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
    // $ANTLR end "bon_specification"


    // $ANTLR start "specification_element"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:65:1: specification_element returns [SpecificationElement se] : (ic= informal_chart | cd= class_dictionary | sd= static_diagram | dd= dynamic_diagram );
    public final SpecificationElement specification_element() throws RecognitionException {
        SpecificationElement se = null;

        InformalChart ic = null;

        ClassDictionary cd = null;

        StaticDiagram sd = null;

        DynamicDiagram dd = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:65:57: (ic= informal_chart | cd= class_dictionary | sd= static_diagram | dd= dynamic_diagram )
            int alt3=4;
            switch ( input.LA(1) ) {
            case 28:
            case 36:
            case 37:
            case 44:
            case 49:
            case 51:
                {
                alt3=1;
                }
                break;
            case 24:
                {
                alt3=2;
                }
                break;
            case 54:
                {
                alt3=3;
                }
                break;
            case 92:
                {
                alt3=4;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return se;}
                NoViableAltException nvae =
                    new NoViableAltException("", 3, 0, input);

                throw nvae;
            }

            switch (alt3) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:66:5: ic= informal_chart
                    {
                    pushFollow(FOLLOW_informal_chart_in_specification_element272);
                    ic=informal_chart();

                    state._fsp--;
                    if (state.failed) return se;
                    if ( state.backtracking==0 ) {
                       if(isOk()) se = ic; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:68:5: cd= class_dictionary
                    {
                    pushFollow(FOLLOW_class_dictionary_in_specification_element286);
                    cd=class_dictionary();

                    state._fsp--;
                    if (state.failed) return se;
                    if ( state.backtracking==0 ) {
                       if(isOk()) se = cd; 
                    }

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:70:5: sd= static_diagram
                    {
                    pushFollow(FOLLOW_static_diagram_in_specification_element300);
                    sd=static_diagram();

                    state._fsp--;
                    if (state.failed) return se;
                    if ( state.backtracking==0 ) {
                       if(isOk()) se = sd; 
                    }

                    }
                    break;
                case 4 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:72:5: dd= dynamic_diagram
                    {
                    pushFollow(FOLLOW_dynamic_diagram_in_specification_element314);
                    dd=dynamic_diagram();

                    state._fsp--;
                    if (state.failed) return se;
                    if ( state.backtracking==0 ) {
                       if(isOk()) se = dd; 
                    }

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
        return se;
    }
    // $ANTLR end "specification_element"


    // $ANTLR start "informal_chart"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:78:1: informal_chart returns [InformalChart ic] : ( system_chart | cluster_chart | class_chart | event_chart | scenario_chart | creation_chart );
    public final InformalChart informal_chart() throws RecognitionException {
        InformalChart ic = null;

        ClusterChart system_chart2 = null;

        ClusterChart cluster_chart3 = null;

        ClassChart class_chart4 = null;

        EventChart event_chart5 = null;

        ScenarioChart scenario_chart6 = null;

        BONParser.creation_chart_return creation_chart7 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:82:43: ( system_chart | cluster_chart | class_chart | event_chart | scenario_chart | creation_chart )
            int alt4=6;
            switch ( input.LA(1) ) {
            case 28:
                {
                alt4=1;
                }
                break;
            case 36:
                {
                alt4=2;
                }
                break;
            case 37:
                {
                alt4=3;
                }
                break;
            case 44:
                {
                alt4=4;
                }
                break;
            case 49:
                {
                alt4=5;
                }
                break;
            case 51:
                {
                alt4=6;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return ic;}
                NoViableAltException nvae =
                    new NoViableAltException("", 4, 0, input);

                throw nvae;
            }

            switch (alt4) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:83:5: system_chart
                    {
                    pushFollow(FOLLOW_system_chart_in_informal_chart342);
                    system_chart2=system_chart();

                    state._fsp--;
                    if (state.failed) return ic;
                    if ( state.backtracking==0 ) {
                       if(isOk()) ic = system_chart2; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:85:5: cluster_chart
                    {
                    pushFollow(FOLLOW_cluster_chart_in_informal_chart354);
                    cluster_chart3=cluster_chart();

                    state._fsp--;
                    if (state.failed) return ic;
                    if ( state.backtracking==0 ) {
                       if(isOk()) ic = cluster_chart3; 
                    }

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:87:5: class_chart
                    {
                    pushFollow(FOLLOW_class_chart_in_informal_chart366);
                    class_chart4=class_chart();

                    state._fsp--;
                    if (state.failed) return ic;
                    if ( state.backtracking==0 ) {
                       if(isOk()) ic = class_chart4; 
                    }

                    }
                    break;
                case 4 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:89:5: event_chart
                    {
                    pushFollow(FOLLOW_event_chart_in_informal_chart378);
                    event_chart5=event_chart();

                    state._fsp--;
                    if (state.failed) return ic;
                    if ( state.backtracking==0 ) {
                       if(isOk()) ic = event_chart5; 
                    }

                    }
                    break;
                case 5 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:91:5: scenario_chart
                    {
                    pushFollow(FOLLOW_scenario_chart_in_informal_chart390);
                    scenario_chart6=scenario_chart();

                    state._fsp--;
                    if (state.failed) return ic;
                    if ( state.backtracking==0 ) {
                       if(isOk()) ic = scenario_chart6; 
                    }

                    }
                    break;
                case 6 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:93:5: creation_chart
                    {
                    pushFollow(FOLLOW_creation_chart_in_informal_chart402);
                    creation_chart7=creation_chart();

                    state._fsp--;
                    if (state.failed) return ic;
                    if ( state.backtracking==0 ) {
                       if(isOk()) ic = (creation_chart7!=null?creation_chart7.cc:null); 
                    }

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
        return ic;
    }
    // $ANTLR end "informal_chart"


    // $ANTLR start "class_dictionary"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:97:1: class_dictionary returns [ClassDictionary cd] : d= 'dictionary' system_name ( indexing )? ( explanation )? ( part )? (de= dictionary_entry )+ e= 'end' ;
    public final ClassDictionary class_dictionary() throws RecognitionException {
        ClassDictionary cd = null;

        Token d=null;
        Token e=null;
        DictionaryEntry de = null;

        BONParser.indexing_return indexing8 = null;

        String explanation9 = null;

        String part10 = null;

        String system_name11 = null;


         Indexing index = null; String expl = null; String p = null; 
                List<DictionaryEntry> entries = createList(); 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:100:1: (d= 'dictionary' system_name ( indexing )? ( explanation )? ( part )? (de= dictionary_entry )+ e= 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:101:3: d= 'dictionary' system_name ( indexing )? ( explanation )? ( part )? (de= dictionary_entry )+ e= 'end'
            {
            d=(Token)match(input,24,FOLLOW_24_in_class_dictionary437); if (state.failed) return cd;
            pushFollow(FOLLOW_system_name_in_class_dictionary442);
            system_name11=system_name();

            state._fsp--;
            if (state.failed) return cd;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:103:3: ( indexing )?
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0==30) ) {
                alt5=1;
            }
            switch (alt5) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:103:4: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_class_dictionary448);
                    indexing8=indexing();

                    state._fsp--;
                    if (state.failed) return cd;
                    if ( state.backtracking==0 ) {
                       if(isOk()) index = (indexing8!=null?indexing8.indexing:null); 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:104:3: ( explanation )?
            int alt6=2;
            int LA6_0 = input.LA(1);

            if ( (LA6_0==29) ) {
                alt6=1;
            }
            switch (alt6) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:104:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_class_dictionary458);
                    explanation9=explanation();

                    state._fsp--;
                    if (state.failed) return cd;
                    if ( state.backtracking==0 ) {
                       if(isOk()) expl = explanation9; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:105:3: ( part )?
            int alt7=2;
            int LA7_0 = input.LA(1);

            if ( (LA7_0==31) ) {
                alt7=1;
            }
            switch (alt7) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:105:4: part
                    {
                    pushFollow(FOLLOW_part_in_class_dictionary469);
                    part10=part();

                    state._fsp--;
                    if (state.failed) return cd;
                    if ( state.backtracking==0 ) {
                       if(isOk()) p = part10; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:106:3: (de= dictionary_entry )+
            int cnt8=0;
            loop8:
            do {
                int alt8=2;
                int LA8_0 = input.LA(1);

                if ( (LA8_0==26) ) {
                    alt8=1;
                }


                switch (alt8) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:106:4: de= dictionary_entry
            	    {
            	    pushFollow(FOLLOW_dictionary_entry_in_class_dictionary482);
            	    de=dictionary_entry();

            	    state._fsp--;
            	    if (state.failed) return cd;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) entries.add(de); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt8 >= 1 ) break loop8;
            	    if (state.backtracking>0) {state.failed=true; return cd;}
                        EarlyExitException eee =
                            new EarlyExitException(8, input);
                        throw eee;
                }
                cnt8++;
            } while (true);

            e=(Token)match(input,25,FOLLOW_25_in_class_dictionary499); if (state.failed) return cd;
            if ( state.backtracking==0 ) {
               if(isOk()) cd = ClassDictionary.mk(system_name11, entries, index, expl, p, getSLoc(d,e)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return cd;
    }
    // $ANTLR end "class_dictionary"


    // $ANTLR start "dictionary_entry"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:113:1: dictionary_entry returns [DictionaryEntry entry] : c= 'class' class_name 'cluster' cluster_name_list description ;
    public final DictionaryEntry dictionary_entry() throws RecognitionException {
        DictionaryEntry entry = null;

        Token c=null;
        BONParser.class_name_return class_name12 = null;

        List<String> cluster_name_list13 = null;

        BONParser.description_return description14 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:113:50: (c= 'class' class_name 'cluster' cluster_name_list description )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:114:3: c= 'class' class_name 'cluster' cluster_name_list description
            {
            c=(Token)match(input,26,FOLLOW_26_in_dictionary_entry525); if (state.failed) return entry;
            pushFollow(FOLLOW_class_name_in_dictionary_entry527);
            class_name12=class_name();

            state._fsp--;
            if (state.failed) return entry;
            match(input,27,FOLLOW_27_in_dictionary_entry532); if (state.failed) return entry;
            pushFollow(FOLLOW_cluster_name_list_in_dictionary_entry534);
            cluster_name_list13=cluster_name_list();

            state._fsp--;
            if (state.failed) return entry;
            pushFollow(FOLLOW_description_in_dictionary_entry539);
            description14=description();

            state._fsp--;
            if (state.failed) return entry;
            if ( state.backtracking==0 ) {
               if(isOk()) entry = DictionaryEntry.mk((class_name12!=null?input.toString(class_name12.start,class_name12.stop):null), cluster_name_list13, (description14!=null?input.toString(description14.start,description14.stop):null), getSLoc(c, (description14!=null?((Token)description14.stop):null))); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return entry;
    }
    // $ANTLR end "dictionary_entry"


    // $ANTLR start "system_chart"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:120:1: system_chart returns [ClusterChart sc] : s= 'system_chart' system_name ( indexing )? ( explanation )? ( part )? (ce= cluster_entries | ) e= 'end' ;
    public final ClusterChart system_chart() throws RecognitionException {
        ClusterChart sc = null;

        Token s=null;
        Token e=null;
        List<ClusterEntry> ce = null;

        BONParser.indexing_return indexing15 = null;

        String explanation16 = null;

        String part17 = null;

        String system_name18 = null;


         Indexing index = null; String expl = null; String p = null; 
                List<ClusterEntry> entries = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:125:1: (s= 'system_chart' system_name ( indexing )? ( explanation )? ( part )? (ce= cluster_entries | ) e= 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:126:3: s= 'system_chart' system_name ( indexing )? ( explanation )? ( part )? (ce= cluster_entries | ) e= 'end'
            {
            s=(Token)match(input,28,FOLLOW_28_in_system_chart570); if (state.failed) return sc;
            pushFollow(FOLLOW_system_name_in_system_chart575);
            system_name18=system_name();

            state._fsp--;
            if (state.failed) return sc;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:128:3: ( indexing )?
            int alt9=2;
            int LA9_0 = input.LA(1);

            if ( (LA9_0==30) ) {
                alt9=1;
            }
            switch (alt9) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:128:4: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_system_chart581);
                    indexing15=indexing();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) index = (indexing15!=null?indexing15.indexing:null); 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:129:3: ( explanation )?
            int alt10=2;
            int LA10_0 = input.LA(1);

            if ( (LA10_0==29) ) {
                alt10=1;
            }
            switch (alt10) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:129:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_system_chart591);
                    explanation16=explanation();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) expl = explanation16; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:130:3: ( part )?
            int alt11=2;
            int LA11_0 = input.LA(1);

            if ( (LA11_0==31) ) {
                alt11=1;
            }
            switch (alt11) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:130:4: part
                    {
                    pushFollow(FOLLOW_part_in_system_chart602);
                    part17=part();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) p = part17; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:131:3: (ce= cluster_entries | )
            int alt12=2;
            int LA12_0 = input.LA(1);

            if ( (LA12_0==27) ) {
                alt12=1;
            }
            else if ( (LA12_0==25) ) {
                alt12=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return sc;}
                NoViableAltException nvae =
                    new NoViableAltException("", 12, 0, input);

                throw nvae;
            }
            switch (alt12) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:131:6: ce= cluster_entries
                    {
                    pushFollow(FOLLOW_cluster_entries_in_system_chart617);
                    ce=cluster_entries();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) entries = ce; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:133:6: 
                    {
                    if ( state.backtracking==0 ) {
                       if(isOk()) entries = emptyList(); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_system_chart644); if (state.failed) return sc;
            if ( state.backtracking==0 ) {
               if(isOk()) sc = ClusterChart.mk(system_name18, true, Constants.NO_CLASS_ENTRIES, entries, index, expl, p, getSLoc(s,e)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return sc;
    }
    // $ANTLR end "system_chart"


    // $ANTLR start "explanation"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:139:1: explanation returns [String explanation] : (e= 'explanation' m= manifest_textblock | e= 'explanation' );
    public final String explanation() throws RecognitionException {
        String explanation = null;

        Token e=null;
        BONParser.manifest_textblock_return m = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:139:42: (e= 'explanation' m= manifest_textblock | e= 'explanation' )
            int alt13=2;
            int LA13_0 = input.LA(1);

            if ( (LA13_0==29) ) {
                int LA13_1 = input.LA(2);

                if ( (LA13_1==MANIFEST_STRING||LA13_1==MANIFEST_TEXTBLOCK_START) ) {
                    alt13=1;
                }
                else if ( ((LA13_1>=25 && LA13_1<=27)||LA13_1==31||(LA13_1>=38 && LA13_1<=41)||LA13_1==47||LA13_1==50||LA13_1==52) ) {
                    alt13=2;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return explanation;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 13, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return explanation;}
                NoViableAltException nvae =
                    new NoViableAltException("", 13, 0, input);

                throw nvae;
            }
            switch (alt13) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:140:3: e= 'explanation' m= manifest_textblock
                    {
                    e=(Token)match(input,29,FOLLOW_29_in_explanation665); if (state.failed) return explanation;
                    pushFollow(FOLLOW_manifest_textblock_in_explanation669);
                    m=manifest_textblock();

                    state._fsp--;
                    if (state.failed) return explanation;
                    if ( state.backtracking==0 ) {
                       if(isOk()) explanation = (m!=null?input.toString(m.start,m.stop):null); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:143:3: e= 'explanation'
                    {
                    e=(Token)match(input,29,FOLLOW_29_in_explanation682); if (state.failed) return explanation;
                    if ( state.backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(e), "explanation text", "after 'explanation'", false)); 
                    }

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
        return explanation;
    }
    // $ANTLR end "explanation"

    public static class indexing_return extends ParserRuleReturnScope {
        public Indexing indexing;
    };

    // $ANTLR start "indexing"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:147:1: indexing returns [Indexing indexing] : (i= 'indexing' index_list | i= 'indexing' );
    public final BONParser.indexing_return indexing() throws RecognitionException {
        BONParser.indexing_return retval = new BONParser.indexing_return();
        retval.start = input.LT(1);

        Token i=null;
        BONParser.index_list_return index_list19 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:147:38: (i= 'indexing' index_list | i= 'indexing' )
            int alt14=2;
            int LA14_0 = input.LA(1);

            if ( (LA14_0==30) ) {
                int LA14_1 = input.LA(2);

                if ( (LA14_1==IDENTIFIER) ) {
                    alt14=1;
                }
                else if ( (LA14_1==EOF||(LA14_1>=24 && LA14_1<=29)||LA14_1==31||(LA14_1>=36 && LA14_1<=41)||LA14_1==44||LA14_1==47||(LA14_1>=49 && LA14_1<=52)||LA14_1==54||(LA14_1>=71 && LA14_1<=72)||LA14_1==92) ) {
                    alt14=2;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 14, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 14, 0, input);

                throw nvae;
            }
            switch (alt14) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:148:4: i= 'indexing' index_list
                    {
                    i=(Token)match(input,30,FOLLOW_30_in_indexing707); if (state.failed) return retval;
                    pushFollow(FOLLOW_index_list_in_indexing709);
                    index_list19=index_list();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.indexing = Indexing.mk((index_list19!=null?index_list19.list:null), getSLoc(i,(index_list19!=null?((Token)index_list19.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:151:4: i= 'indexing'
                    {
                    i=(Token)match(input,30,FOLLOW_30_in_indexing725); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(i), "indexing entries", "after 'indexing'", false)); 
                    }
                    if ( state.backtracking==0 ) {
                       retval.indexing = Indexing.mk(Constants.NO_INDEX_CLAUSES, getSLoc(i)); 
                    }

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
    // $ANTLR end "indexing"


    // $ANTLR start "part"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:156:1: part returns [String part] : (p= 'part' m= MANIFEST_STRING | p= 'part' );
    public final String part() throws RecognitionException {
        String part = null;

        Token p=null;
        Token m=null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:156:28: (p= 'part' m= MANIFEST_STRING | p= 'part' )
            int alt15=2;
            int LA15_0 = input.LA(1);

            if ( (LA15_0==31) ) {
                int LA15_1 = input.LA(2);

                if ( (LA15_1==MANIFEST_STRING) ) {
                    alt15=1;
                }
                else if ( ((LA15_1>=25 && LA15_1<=27)||(LA15_1>=38 && LA15_1<=41)||LA15_1==47||LA15_1==50||LA15_1==52) ) {
                    alt15=2;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return part;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 15, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return part;}
                NoViableAltException nvae =
                    new NoViableAltException("", 15, 0, input);

                throw nvae;
            }
            switch (alt15) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:157:5: p= 'part' m= MANIFEST_STRING
                    {
                    p=(Token)match(input,31,FOLLOW_31_in_part755); if (state.failed) return part;
                    m=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_part759); if (state.failed) return part;
                    if ( state.backtracking==0 ) {
                       if(isOk()) part = (m!=null?m.getText():null); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:160:5: p= 'part'
                    {
                    p=(Token)match(input,31,FOLLOW_31_in_part777); if (state.failed) return part;
                    if ( state.backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(p), "part text", "after 'part'", false)); 
                    }
                    if ( state.backtracking==0 ) {
                       if(isOk()) part = ""; 
                    }

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
        return part;
    }
    // $ANTLR end "part"

    public static class description_return extends ParserRuleReturnScope {
        public String description;
    };

    // $ANTLR start "description"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:165:1: description returns [String description] : d= 'description' m= manifest_textblock ;
    public final BONParser.description_return description() throws RecognitionException {
        BONParser.description_return retval = new BONParser.description_return();
        retval.start = input.LT(1);

        Token d=null;
        BONParser.manifest_textblock_return m = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:165:42: (d= 'description' m= manifest_textblock )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:166:3: d= 'description' m= manifest_textblock
            {
            d=(Token)match(input,32,FOLLOW_32_in_description807); if (state.failed) return retval;
            pushFollow(FOLLOW_manifest_textblock_in_description811);
            m=manifest_textblock();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.description = (m!=null?input.toString(m.start,m.stop):null); 
            }

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
    // $ANTLR end "description"


    // $ANTLR start "cluster_entries"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:170:1: cluster_entries returns [List<ClusterEntry> entries] : ( cluster_entry )+ ;
    public final List<ClusterEntry> cluster_entries() throws RecognitionException {
        List<ClusterEntry> entries = null;

        ClusterEntry cluster_entry20 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:170:54: ( ( cluster_entry )+ )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:171:3: ( cluster_entry )+
            {
            if ( state.backtracking==0 ) {
               entries = createList(); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:172:3: ( cluster_entry )+
            int cnt16=0;
            loop16:
            do {
                int alt16=2;
                int LA16_0 = input.LA(1);

                if ( (LA16_0==27) ) {
                    alt16=1;
                }


                switch (alt16) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:172:4: cluster_entry
            	    {
            	    pushFollow(FOLLOW_cluster_entry_in_cluster_entries836);
            	    cluster_entry20=cluster_entry();

            	    state._fsp--;
            	    if (state.failed) return entries;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) entries.add(cluster_entry20); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt16 >= 1 ) break loop16;
            	    if (state.backtracking>0) {state.failed=true; return entries;}
                        EarlyExitException eee =
                            new EarlyExitException(16, input);
                        throw eee;
                }
                cnt16++;
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return entries;
    }
    // $ANTLR end "cluster_entries"


    // $ANTLR start "cluster_entry"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:175:1: cluster_entry returns [ClusterEntry ce] : c= 'cluster' cluster_name description ;
    public final ClusterEntry cluster_entry() throws RecognitionException {
        ClusterEntry ce = null;

        Token c=null;
        BONParser.cluster_name_return cluster_name21 = null;

        BONParser.description_return description22 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:175:41: (c= 'cluster' cluster_name description )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:176:3: c= 'cluster' cluster_name description
            {
            c=(Token)match(input,27,FOLLOW_27_in_cluster_entry875); if (state.failed) return ce;
            pushFollow(FOLLOW_cluster_name_in_cluster_entry877);
            cluster_name21=cluster_name();

            state._fsp--;
            if (state.failed) return ce;
            pushFollow(FOLLOW_description_in_cluster_entry879);
            description22=description();

            state._fsp--;
            if (state.failed) return ce;
            if ( state.backtracking==0 ) {
               if(isOk()) ce = ClusterEntry.mk((cluster_name21!=null?input.toString(cluster_name21.start,cluster_name21.stop):null), (description22!=null?description22.description:null), getSLoc(c, (description22!=null?((Token)description22.stop):null))); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ce;
    }
    // $ANTLR end "cluster_entry"


    // $ANTLR start "system_name"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:180:1: system_name returns [String name] : i= IDENTIFIER ;
    public final String system_name() throws RecognitionException {
        String name = null;

        Token i=null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:180:35: (i= IDENTIFIER )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:181:3: i= IDENTIFIER
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_system_name916); if (state.failed) return name;
            if ( state.backtracking==0 ) {
               if(isOk()) name = (i!=null?i.getText():null); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return name;
    }
    // $ANTLR end "system_name"

    public static class index_list_return extends ParserRuleReturnScope {
        public List<IndexClause> list;
    };

    // $ANTLR start "index_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:185:1: index_list returns [List<IndexClause> list] : i1= index_clause ( ( ';' i2= index_clause ) | i= index_clause )* ( ';' )? ;
    public final BONParser.index_list_return index_list() throws RecognitionException {
        BONParser.index_list_return retval = new BONParser.index_list_return();
        retval.start = input.LT(1);

        BONParser.index_clause_return i1 = null;

        BONParser.index_clause_return i2 = null;

        BONParser.index_clause_return i = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:187:45: (i1= index_clause ( ( ';' i2= index_clause ) | i= index_clause )* ( ';' )? )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:188:16: i1= index_clause ( ( ';' i2= index_clause ) | i= index_clause )* ( ';' )?
            {
            if ( state.backtracking==0 ) {
               retval.list = createList(); 
            }
            pushFollow(FOLLOW_index_clause_in_index_list973);
            i1=index_clause();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.list.add((i1!=null?i1.clause:null)); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:191:16: ( ( ';' i2= index_clause ) | i= index_clause )*
            loop17:
            do {
                int alt17=3;
                int LA17_0 = input.LA(1);

                if ( (LA17_0==33) ) {
                    int LA17_1 = input.LA(2);

                    if ( (LA17_1==IDENTIFIER) ) {
                        alt17=1;
                    }


                }
                else if ( (LA17_0==IDENTIFIER) ) {
                    alt17=2;
                }


                switch (alt17) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:191:19: ( ';' i2= index_clause )
            	    {
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:191:19: ( ';' i2= index_clause )
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:191:20: ';' i2= index_clause
            	    {
            	    match(input,33,FOLLOW_33_in_index_list1012); if (state.failed) return retval;
            	    pushFollow(FOLLOW_index_clause_in_index_list1016);
            	    i2=index_clause();

            	    state._fsp--;
            	    if (state.failed) return retval;

            	    }

            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.list.add((i2!=null?i2.clause:null)); 
            	    }

            	    }
            	    break;
            	case 2 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:193:19: i= index_clause
            	    {
            	    pushFollow(FOLLOW_index_clause_in_index_list1059);
            	    i=index_clause();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       addParseProblem(new MissingElementParseError(getSourceLocation((i!=null?((Token)i.start):null)), "semi-colon", "before additional index clause", false)); 
            	    }
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.list.add((i!=null?i.clause:null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop17;
                }
            } while (true);

            // /home/fintan/workspaces/bon/bonc/src/BON.g:196:16: ( ';' )?
            int alt18=2;
            int LA18_0 = input.LA(1);

            if ( (LA18_0==33) ) {
                alt18=1;
            }
            switch (alt18) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:196:16: ';'
                    {
                    match(input,33,FOLLOW_33_in_index_list1117); if (state.failed) return retval;

                    }
                    break;

            }


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
    // $ANTLR end "index_list"

    public static class index_clause_return extends ParserRuleReturnScope {
        public IndexClause clause;
    };

    // $ANTLR start "index_clause"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:199:1: index_clause returns [IndexClause clause] : (i= IDENTIFIER ':' index_term_list | i= IDENTIFIER ':' );
    public final BONParser.index_clause_return index_clause() throws RecognitionException {
        BONParser.index_clause_return retval = new BONParser.index_clause_return();
        retval.start = input.LT(1);

        Token i=null;
        BONParser.index_term_list_return index_term_list23 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:199:43: (i= IDENTIFIER ':' index_term_list | i= IDENTIFIER ':' )
            int alt19=2;
            int LA19_0 = input.LA(1);

            if ( (LA19_0==IDENTIFIER) ) {
                int LA19_1 = input.LA(2);

                if ( (LA19_1==34) ) {
                    int LA19_2 = input.LA(3);

                    if ( (LA19_2==EOF||LA19_2==IDENTIFIER||(LA19_2>=24 && LA19_2<=29)||LA19_2==31||LA19_2==33||(LA19_2>=36 && LA19_2<=41)||LA19_2==44||LA19_2==47||(LA19_2>=49 && LA19_2<=52)||LA19_2==54||(LA19_2>=71 && LA19_2<=72)||LA19_2==92) ) {
                        alt19=2;
                    }
                    else if ( (LA19_2==MANIFEST_STRING||LA19_2==MANIFEST_TEXTBLOCK_START) ) {
                        alt19=1;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return retval;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 19, 2, input);

                        throw nvae;
                    }
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 19, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 19, 0, input);

                throw nvae;
            }
            switch (alt19) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:200:3: i= IDENTIFIER ':' index_term_list
                    {
                    i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_index_clause1150); if (state.failed) return retval;
                    match(input,34,FOLLOW_34_in_index_clause1152); if (state.failed) return retval;
                    pushFollow(FOLLOW_index_term_list_in_index_clause1154);
                    index_term_list23=index_term_list();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.clause = IndexClause.mk((i!=null?i.getText():null), (index_term_list23!=null?index_term_list23.strings:null), getSLoc(i, (index_term_list23!=null?((Token)index_term_list23.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:203:3: i= IDENTIFIER ':'
                    {
                    i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_index_clause1168); if (state.failed) return retval;
                    match(input,34,FOLLOW_34_in_index_clause1170); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(i), "index term(s)", "in index clause", true)); 
                    }

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
    // $ANTLR end "index_clause"

    public static class index_term_list_return extends ParserRuleReturnScope {
        public List<String> strings;
    };

    // $ANTLR start "index_term_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:207:1: index_term_list returns [List<String> strings] : i1= index_string ( ',' i= index_string )* ;
    public final BONParser.index_term_list_return index_term_list() throws RecognitionException {
        BONParser.index_term_list_return retval = new BONParser.index_term_list_return();
        retval.start = input.LT(1);

        BONParser.index_string_return i1 = null;

        BONParser.index_string_return i = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:207:48: (i1= index_string ( ',' i= index_string )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:208:3: i1= index_string ( ',' i= index_string )*
            {
            if ( state.backtracking==0 ) {
               retval.strings = createList(); 
            }
            pushFollow(FOLLOW_index_string_in_index_term_list1212);
            i1=index_string();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.strings.add((i1!=null?input.toString(i1.start,i1.stop):null)); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:211:3: ( ',' i= index_string )*
            loop20:
            do {
                int alt20=2;
                int LA20_0 = input.LA(1);

                if ( (LA20_0==35) ) {
                    alt20=1;
                }


                switch (alt20) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:211:4: ',' i= index_string
            	    {
            	    match(input,35,FOLLOW_35_in_index_term_list1222); if (state.failed) return retval;
            	    pushFollow(FOLLOW_index_string_in_index_term_list1226);
            	    i=index_string();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.strings.add((i!=null?input.toString(i.start,i.stop):null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop20;
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
    // $ANTLR end "index_term_list"

    public static class index_string_return extends ParserRuleReturnScope {
        public String s;
    };

    // $ANTLR start "index_string"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:216:1: index_string returns [String s] : m= manifest_textblock ;
    public final BONParser.index_string_return index_string() throws RecognitionException {
        BONParser.index_string_return retval = new BONParser.index_string_return();
        retval.start = input.LT(1);

        BONParser.manifest_textblock_return m = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:216:33: (m= manifest_textblock )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:217:3: m= manifest_textblock
            {
            pushFollow(FOLLOW_manifest_textblock_in_index_string1271);
            m=manifest_textblock();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.s = (m!=null?input.toString(m.start,m.stop):null); 
            }

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
    // $ANTLR end "index_string"


    // $ANTLR start "cluster_chart"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:221:1: cluster_chart returns [ClusterChart cc] : c= 'cluster_chart' cluster_name (i= indexing )? ( explanation )? ( part )? (ce= class_entries | ) (cle= cluster_entries | ) e= 'end' ;
    public final ClusterChart cluster_chart() throws RecognitionException {
        ClusterChart cc = null;

        Token c=null;
        Token e=null;
        BONParser.indexing_return i = null;

        List<ClassEntry> ce = null;

        List<ClusterEntry> cle = null;

        String explanation24 = null;

        String part25 = null;

        BONParser.cluster_name_return cluster_name26 = null;


         List<ClassEntry> classes = null; List<ClusterEntry> clusters = null; 
                Indexing indexing = null; String explanation = null; String part = null;  
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:226:1: (c= 'cluster_chart' cluster_name (i= indexing )? ( explanation )? ( part )? (ce= class_entries | ) (cle= cluster_entries | ) e= 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:227:3: c= 'cluster_chart' cluster_name (i= indexing )? ( explanation )? ( part )? (ce= class_entries | ) (cle= cluster_entries | ) e= 'end'
            {
            c=(Token)match(input,36,FOLLOW_36_in_cluster_chart1305); if (state.failed) return cc;
            pushFollow(FOLLOW_cluster_name_in_cluster_chart1307);
            cluster_name26=cluster_name();

            state._fsp--;
            if (state.failed) return cc;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:228:3: (i= indexing )?
            int alt21=2;
            int LA21_0 = input.LA(1);

            if ( (LA21_0==30) ) {
                alt21=1;
            }
            switch (alt21) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:228:4: i= indexing
                    {
                    pushFollow(FOLLOW_indexing_in_cluster_chart1315);
                    i=indexing();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) indexing = (i!=null?i.indexing:null); 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:229:3: ( explanation )?
            int alt22=2;
            int LA22_0 = input.LA(1);

            if ( (LA22_0==29) ) {
                alt22=1;
            }
            switch (alt22) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:229:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_cluster_chart1326);
                    explanation24=explanation();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) explanation = explanation24; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:230:3: ( part )?
            int alt23=2;
            int LA23_0 = input.LA(1);

            if ( (LA23_0==31) ) {
                alt23=1;
            }
            switch (alt23) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:230:4: part
                    {
                    pushFollow(FOLLOW_part_in_cluster_chart1337);
                    part25=part();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) part = part25; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:231:3: (ce= class_entries | )
            int alt24=2;
            int LA24_0 = input.LA(1);

            if ( (LA24_0==26) ) {
                alt24=1;
            }
            else if ( (LA24_0==25||LA24_0==27) ) {
                alt24=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return cc;}
                NoViableAltException nvae =
                    new NoViableAltException("", 24, 0, input);

                throw nvae;
            }
            switch (alt24) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:231:6: ce= class_entries
                    {
                    pushFollow(FOLLOW_class_entries_in_cluster_chart1352);
                    ce=class_entries();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) classes = ce; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:232:6: 
                    {
                    if ( state.backtracking==0 ) {
                       if(isOk()) classes = emptyList(); 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:234:3: (cle= cluster_entries | )
            int alt25=2;
            int LA25_0 = input.LA(1);

            if ( (LA25_0==27) ) {
                alt25=1;
            }
            else if ( (LA25_0==25) ) {
                alt25=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return cc;}
                NoViableAltException nvae =
                    new NoViableAltException("", 25, 0, input);

                throw nvae;
            }
            switch (alt25) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:234:6: cle= cluster_entries
                    {
                    pushFollow(FOLLOW_cluster_entries_in_cluster_chart1376);
                    cle=cluster_entries();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       clusters = cle; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:235:6: 
                    {
                    if ( state.backtracking==0 ) {
                       if(isOk()) clusters = emptyList(); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_cluster_chart1397); if (state.failed) return cc;
            if ( state.backtracking==0 ) {
               if(isOk()) cc = ClusterChart.mk((cluster_name26!=null?cluster_name26.name:null), false, classes, clusters, indexing, explanation, part, getSLoc(c,e)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return cc;
    }
    // $ANTLR end "cluster_chart"


    // $ANTLR start "class_entries"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:241:1: class_entries returns [List<ClassEntry> entries] : ( class_entry )+ ;
    public final List<ClassEntry> class_entries() throws RecognitionException {
        List<ClassEntry> entries = null;

        ClassEntry class_entry27 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:241:50: ( ( class_entry )+ )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:242:3: ( class_entry )+
            {
            if ( state.backtracking==0 ) {
               entries = createList(); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:243:3: ( class_entry )+
            int cnt26=0;
            loop26:
            do {
                int alt26=2;
                int LA26_0 = input.LA(1);

                if ( (LA26_0==26) ) {
                    alt26=1;
                }


                switch (alt26) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:243:4: class_entry
            	    {
            	    pushFollow(FOLLOW_class_entry_in_class_entries1436);
            	    class_entry27=class_entry();

            	    state._fsp--;
            	    if (state.failed) return entries;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) entries.add(class_entry27); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt26 >= 1 ) break loop26;
            	    if (state.backtracking>0) {state.failed=true; return entries;}
                        EarlyExitException eee =
                            new EarlyExitException(26, input);
                        throw eee;
                }
                cnt26++;
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return entries;
    }
    // $ANTLR end "class_entries"


    // $ANTLR start "class_entry"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:246:1: class_entry returns [ClassEntry entry] : c= 'class' class_name description ;
    public final ClassEntry class_entry() throws RecognitionException {
        ClassEntry entry = null;

        Token c=null;
        BONParser.class_name_return class_name28 = null;

        BONParser.description_return description29 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:246:40: (c= 'class' class_name description )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:247:3: c= 'class' class_name description
            {
            c=(Token)match(input,26,FOLLOW_26_in_class_entry1474); if (state.failed) return entry;
            pushFollow(FOLLOW_class_name_in_class_entry1476);
            class_name28=class_name();

            state._fsp--;
            if (state.failed) return entry;
            pushFollow(FOLLOW_description_in_class_entry1480);
            description29=description();

            state._fsp--;
            if (state.failed) return entry;
            if ( state.backtracking==0 ) {
               if(isOk()) entry = ClassEntry.mk((class_name28!=null?input.toString(class_name28.start,class_name28.stop):null), (description29!=null?description29.description:null), getSLoc(c, (description29!=null?((Token)description29.stop):null))); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return entry;
    }
    // $ANTLR end "class_entry"

    public static class cluster_name_return extends ParserRuleReturnScope {
        public String name;
    };

    // $ANTLR start "cluster_name"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:252:1: cluster_name returns [String name] : i= IDENTIFIER ;
    public final BONParser.cluster_name_return cluster_name() throws RecognitionException {
        BONParser.cluster_name_return retval = new BONParser.cluster_name_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:252:36: (i= IDENTIFIER )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:253:3: i= IDENTIFIER
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_cluster_name1514); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.name = (i!=null?i.getText():null); 
            }

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
    // $ANTLR end "cluster_name"


    // $ANTLR start "class_chart"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:257:1: class_chart returns [ClassChart cc] : c= 'class_chart' class_name (i= indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? e= 'end' ;
    public final ClassChart class_chart() throws RecognitionException {
        ClassChart cc = null;

        Token c=null;
        Token e=null;
        BONParser.indexing_return i = null;

        String explanation30 = null;

        String part31 = null;

        List<ClassName> inherits32 = null;

        List<String> queries33 = null;

        List<String> commands34 = null;

        List<String> constraints35 = null;

        BONParser.class_name_return class_name36 = null;


         Indexing indexing = null; String explanation = null; String part = null;
                List<ClassName> inherits = emptyList(); List<String> commands = emptyList(); List<String> queries = emptyList(); 
                List<String> constraints = emptyList();  
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:263:1: (c= 'class_chart' class_name (i= indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? e= 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:264:3: c= 'class_chart' class_name (i= indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? e= 'end'
            {
            c=(Token)match(input,37,FOLLOW_37_in_class_chart1545); if (state.failed) return cc;
            pushFollow(FOLLOW_class_name_in_class_chart1547);
            class_name36=class_name();

            state._fsp--;
            if (state.failed) return cc;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:265:3: (i= indexing )?
            int alt27=2;
            int LA27_0 = input.LA(1);

            if ( (LA27_0==30) ) {
                alt27=1;
            }
            switch (alt27) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:265:4: i= indexing
                    {
                    pushFollow(FOLLOW_indexing_in_class_chart1555);
                    i=indexing();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) indexing = (i!=null?i.indexing:null); 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:266:3: ( explanation )?
            int alt28=2;
            int LA28_0 = input.LA(1);

            if ( (LA28_0==29) ) {
                alt28=1;
            }
            switch (alt28) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:266:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_class_chart1566);
                    explanation30=explanation();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) explanation = explanation30; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:267:3: ( part )?
            int alt29=2;
            int LA29_0 = input.LA(1);

            if ( (LA29_0==31) ) {
                alt29=1;
            }
            switch (alt29) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:267:4: part
                    {
                    pushFollow(FOLLOW_part_in_class_chart1577);
                    part31=part();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) part = part31; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:268:3: ( inherits )?
            int alt30=2;
            int LA30_0 = input.LA(1);

            if ( (LA30_0==38) ) {
                alt30=1;
            }
            switch (alt30) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:268:6: inherits
                    {
                    pushFollow(FOLLOW_inherits_in_class_chart1590);
                    inherits32=inherits();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) inherits = inherits32; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:271:3: ( queries )?
            int alt31=2;
            int LA31_0 = input.LA(1);

            if ( (LA31_0==39) ) {
                alt31=1;
            }
            switch (alt31) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:271:6: queries
                    {
                    pushFollow(FOLLOW_queries_in_class_chart1609);
                    queries33=queries();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) queries = queries33; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:274:3: ( commands )?
            int alt32=2;
            int LA32_0 = input.LA(1);

            if ( (LA32_0==40) ) {
                alt32=1;
            }
            switch (alt32) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:274:6: commands
                    {
                    pushFollow(FOLLOW_commands_in_class_chart1628);
                    commands34=commands();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) commands = commands34; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:277:3: ( constraints )?
            int alt33=2;
            int LA33_0 = input.LA(1);

            if ( (LA33_0==41) ) {
                alt33=1;
            }
            switch (alt33) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:277:6: constraints
                    {
                    pushFollow(FOLLOW_constraints_in_class_chart1647);
                    constraints35=constraints();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) constraints = constraints35; 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_class_chart1665); if (state.failed) return cc;
            if ( state.backtracking==0 ) {
               if(isOk()) cc = ClassChart.mk((class_name36!=null?class_name36.name:null), inherits, queries, commands, constraints, indexing, explanation, part, getSLoc(c,e)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return cc;
    }
    // $ANTLR end "class_chart"


    // $ANTLR start "inherits"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:284:1: inherits returns [List<ClassName> inherits] : (i= 'inherit' class_name_list | i= 'inherit' );
    public final List<ClassName> inherits() throws RecognitionException {
        List<ClassName> inherits = null;

        Token i=null;
        List<ClassName> class_name_list37 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:284:45: (i= 'inherit' class_name_list | i= 'inherit' )
            int alt34=2;
            int LA34_0 = input.LA(1);

            if ( (LA34_0==38) ) {
                int LA34_1 = input.LA(2);

                if ( (LA34_1==25||(LA34_1>=39 && LA34_1<=41)) ) {
                    alt34=2;
                }
                else if ( (LA34_1==IDENTIFIER) ) {
                    alt34=1;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return inherits;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 34, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return inherits;}
                NoViableAltException nvae =
                    new NoViableAltException("", 34, 0, input);

                throw nvae;
            }
            switch (alt34) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:285:3: i= 'inherit' class_name_list
                    {
                    i=(Token)match(input,38,FOLLOW_38_in_inherits1699); if (state.failed) return inherits;
                    pushFollow(FOLLOW_class_name_list_in_inherits1704);
                    class_name_list37=class_name_list();

                    state._fsp--;
                    if (state.failed) return inherits;
                    if ( state.backtracking==0 ) {
                       if(isOk()) inherits = class_name_list37; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:289:3: i= 'inherit'
                    {
                    i=(Token)match(input,38,FOLLOW_38_in_inherits1718); if (state.failed) return inherits;
                    if ( state.backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(i), "class name(s)", "in inherits clause", true)); 
                    }

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
        return inherits;
    }
    // $ANTLR end "inherits"


    // $ANTLR start "queries"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:293:1: queries returns [List<String> queries] : 'query' query_list ;
    public final List<String> queries() throws RecognitionException {
        List<String> queries = null;

        List<String> query_list38 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:293:40: ( 'query' query_list )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:294:3: 'query' query_list
            {
            match(input,39,FOLLOW_39_in_queries1738); if (state.failed) return queries;
            pushFollow(FOLLOW_query_list_in_queries1740);
            query_list38=query_list();

            state._fsp--;
            if (state.failed) return queries;
            if ( state.backtracking==0 ) {
               if(isOk()) queries = query_list38; 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return queries;
    }
    // $ANTLR end "queries"


    // $ANTLR start "commands"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:298:1: commands returns [List<String> commands] : 'command' command_list ;
    public final List<String> commands() throws RecognitionException {
        List<String> commands = null;

        List<String> command_list39 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:298:42: ( 'command' command_list )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:299:3: 'command' command_list
            {
            match(input,40,FOLLOW_40_in_commands1770); if (state.failed) return commands;
            pushFollow(FOLLOW_command_list_in_commands1772);
            command_list39=command_list();

            state._fsp--;
            if (state.failed) return commands;
            if ( state.backtracking==0 ) {
               if(isOk()) commands = command_list39; 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return commands;
    }
    // $ANTLR end "commands"


    // $ANTLR start "constraints"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:303:1: constraints returns [List<String> constraints] : 'constraint' constraint_list ;
    public final List<String> constraints() throws RecognitionException {
        List<String> constraints = null;

        List<String> constraint_list40 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:303:48: ( 'constraint' constraint_list )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:304:3: 'constraint' constraint_list
            {
            match(input,41,FOLLOW_41_in_constraints1791); if (state.failed) return constraints;
            pushFollow(FOLLOW_constraint_list_in_constraints1793);
            constraint_list40=constraint_list();

            state._fsp--;
            if (state.failed) return constraints;
            if ( state.backtracking==0 ) {
               if(isOk()) constraints = constraint_list40; 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return constraints;
    }
    // $ANTLR end "constraints"


    // $ANTLR start "query_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:309:1: query_list returns [List<String> queries] : m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? ;
    public final List<String> query_list() throws RecognitionException {
        List<String> queries = null;

        BONParser.manifest_textblock_return m1 = null;

        BONParser.manifest_textblock_return m = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:309:43: (m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:310:3: m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )?
            {
            if ( state.backtracking==0 ) {
               queries = createList(); 
            }
            pushFollow(FOLLOW_manifest_textblock_in_query_list1819);
            m1=manifest_textblock();

            state._fsp--;
            if (state.failed) return queries;
            if ( state.backtracking==0 ) {
               if(isOk()) queries.add((m1!=null?input.toString(m1.start,m1.stop):null)); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:313:3: ( ( ',' m= manifest_textblock ) | m= manifest_textblock )*
            loop35:
            do {
                int alt35=3;
                int LA35_0 = input.LA(1);

                if ( (LA35_0==35) ) {
                    int LA35_1 = input.LA(2);

                    if ( (LA35_1==MANIFEST_STRING||LA35_1==MANIFEST_TEXTBLOCK_START) ) {
                        alt35=1;
                    }


                }
                else if ( (LA35_0==MANIFEST_STRING||LA35_0==MANIFEST_TEXTBLOCK_START) ) {
                    alt35=2;
                }


                switch (alt35) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:313:6: ( ',' m= manifest_textblock )
            	    {
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:313:6: ( ',' m= manifest_textblock )
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:313:7: ',' m= manifest_textblock
            	    {
            	    match(input,35,FOLLOW_35_in_query_list1832); if (state.failed) return queries;
            	    pushFollow(FOLLOW_manifest_textblock_in_query_list1836);
            	    m=manifest_textblock();

            	    state._fsp--;
            	    if (state.failed) return queries;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) queries.add((m!=null?input.toString(m.start,m.stop):null)); 
            	    }

            	    }


            	    }
            	    break;
            	case 2 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:316:6: m= manifest_textblock
            	    {
            	    pushFollow(FOLLOW_manifest_textblock_in_query_list1868);
            	    m=manifest_textblock();

            	    state._fsp--;
            	    if (state.failed) return queries;
            	    if ( state.backtracking==0 ) {
            	       addParseProblem(new MissingElementParseError(getSourceLocation((m!=null?((Token)m.start):null)), "comma", "before additional query item", false)); 
            	    }
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) queries.add((m!=null?input.toString(m.start,m.stop):null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop35;
                }
            } while (true);

            // /home/fintan/workspaces/bon/bonc/src/BON.g:320:3: ( ',' )?
            int alt36=2;
            int LA36_0 = input.LA(1);

            if ( (LA36_0==35) ) {
                alt36=1;
            }
            switch (alt36) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:320:3: ','
                    {
                    match(input,35,FOLLOW_35_in_query_list1894); if (state.failed) return queries;

                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return queries;
    }
    // $ANTLR end "query_list"


    // $ANTLR start "command_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:323:1: command_list returns [List<String> commands] : m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? ;
    public final List<String> command_list() throws RecognitionException {
        List<String> commands = null;

        BONParser.manifest_textblock_return m1 = null;

        BONParser.manifest_textblock_return m = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:323:46: (m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:324:3: m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )?
            {
            if ( state.backtracking==0 ) {
               commands = createList(); 
            }
            pushFollow(FOLLOW_manifest_textblock_in_command_list1941);
            m1=manifest_textblock();

            state._fsp--;
            if (state.failed) return commands;
            if ( state.backtracking==0 ) {
               if(isOk()) commands.add((m1!=null?input.toString(m1.start,m1.stop):null)); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:327:3: ( ( ',' m= manifest_textblock ) | m= manifest_textblock )*
            loop37:
            do {
                int alt37=3;
                int LA37_0 = input.LA(1);

                if ( (LA37_0==35) ) {
                    int LA37_1 = input.LA(2);

                    if ( (LA37_1==MANIFEST_STRING||LA37_1==MANIFEST_TEXTBLOCK_START) ) {
                        alt37=1;
                    }


                }
                else if ( (LA37_0==MANIFEST_STRING||LA37_0==MANIFEST_TEXTBLOCK_START) ) {
                    alt37=2;
                }


                switch (alt37) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:327:6: ( ',' m= manifest_textblock )
            	    {
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:327:6: ( ',' m= manifest_textblock )
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:327:7: ',' m= manifest_textblock
            	    {
            	    match(input,35,FOLLOW_35_in_command_list1954); if (state.failed) return commands;
            	    pushFollow(FOLLOW_manifest_textblock_in_command_list1958);
            	    m=manifest_textblock();

            	    state._fsp--;
            	    if (state.failed) return commands;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) commands.add((m!=null?input.toString(m.start,m.stop):null)); 
            	    }

            	    }


            	    }
            	    break;
            	case 2 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:330:6: m= manifest_textblock
            	    {
            	    pushFollow(FOLLOW_manifest_textblock_in_command_list1984);
            	    m=manifest_textblock();

            	    state._fsp--;
            	    if (state.failed) return commands;
            	    if ( state.backtracking==0 ) {
            	       addParseProblem(new MissingElementParseError(getSourceLocation((m!=null?((Token)m.start):null)), "comma", "before additional command item", false)); 
            	    }
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) commands.add((m!=null?input.toString(m.start,m.stop):null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop37;
                }
            } while (true);

            // /home/fintan/workspaces/bon/bonc/src/BON.g:334:3: ( ',' )?
            int alt38=2;
            int LA38_0 = input.LA(1);

            if ( (LA38_0==35) ) {
                alt38=1;
            }
            switch (alt38) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:334:3: ','
                    {
                    match(input,35,FOLLOW_35_in_command_list2009); if (state.failed) return commands;

                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return commands;
    }
    // $ANTLR end "command_list"


    // $ANTLR start "constraint_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:337:1: constraint_list returns [List<String> constraints] : m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? ;
    public final List<String> constraint_list() throws RecognitionException {
        List<String> constraints = null;

        BONParser.manifest_textblock_return m1 = null;

        BONParser.manifest_textblock_return m = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:337:52: (m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:338:3: m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )?
            {
            if ( state.backtracking==0 ) {
               constraints = createList(); 
            }
            pushFollow(FOLLOW_manifest_textblock_in_constraint_list2045);
            m1=manifest_textblock();

            state._fsp--;
            if (state.failed) return constraints;
            if ( state.backtracking==0 ) {
               if(isOk()) constraints.add((m1!=null?input.toString(m1.start,m1.stop):null)); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:341:3: ( ( ',' m= manifest_textblock ) | m= manifest_textblock )*
            loop39:
            do {
                int alt39=3;
                int LA39_0 = input.LA(1);

                if ( (LA39_0==35) ) {
                    int LA39_1 = input.LA(2);

                    if ( (LA39_1==MANIFEST_STRING||LA39_1==MANIFEST_TEXTBLOCK_START) ) {
                        alt39=1;
                    }


                }
                else if ( (LA39_0==MANIFEST_STRING||LA39_0==MANIFEST_TEXTBLOCK_START) ) {
                    alt39=2;
                }


                switch (alt39) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:341:6: ( ',' m= manifest_textblock )
            	    {
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:341:6: ( ',' m= manifest_textblock )
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:341:7: ',' m= manifest_textblock
            	    {
            	    match(input,35,FOLLOW_35_in_constraint_list2058); if (state.failed) return constraints;
            	    pushFollow(FOLLOW_manifest_textblock_in_constraint_list2062);
            	    m=manifest_textblock();

            	    state._fsp--;
            	    if (state.failed) return constraints;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) constraints.add((m!=null?input.toString(m.start,m.stop):null)); 
            	    }

            	    }


            	    }
            	    break;
            	case 2 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:344:6: m= manifest_textblock
            	    {
            	    pushFollow(FOLLOW_manifest_textblock_in_constraint_list2087);
            	    m=manifest_textblock();

            	    state._fsp--;
            	    if (state.failed) return constraints;
            	    if ( state.backtracking==0 ) {
            	       addParseProblem(new MissingElementParseError(getSourceLocation((m!=null?((Token)m.start):null)), "comma", "before additional constraint item", false)); 
            	    }
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) constraints.add((m!=null?input.toString(m.start,m.stop):null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop39;
                }
            } while (true);

            // /home/fintan/workspaces/bon/bonc/src/BON.g:348:3: ( ',' )?
            int alt40=2;
            int LA40_0 = input.LA(1);

            if ( (LA40_0==35) ) {
                alt40=1;
            }
            switch (alt40) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:348:3: ','
                    {
                    match(input,35,FOLLOW_35_in_constraint_list2111); if (state.failed) return constraints;

                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return constraints;
    }
    // $ANTLR end "constraint_list"


    // $ANTLR start "class_name_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:351:1: class_name_list returns [List<ClassName> list] : c1= class_name ( ( ',' c= class_name ) | (c= class_name ) )* ;
    public final List<ClassName> class_name_list() throws RecognitionException {
        List<ClassName> list = null;

        BONParser.class_name_return c1 = null;

        BONParser.class_name_return c = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:351:48: (c1= class_name ( ( ',' c= class_name ) | (c= class_name ) )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:352:3: c1= class_name ( ( ',' c= class_name ) | (c= class_name ) )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_class_name_in_class_name_list2133);
            c1=class_name();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               if(isOk()) list.add((c1!=null?c1.name:null)); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:355:3: ( ( ',' c= class_name ) | (c= class_name ) )*
            loop41:
            do {
                int alt41=3;
                int LA41_0 = input.LA(1);

                if ( (LA41_0==35) ) {
                    alt41=1;
                }
                else if ( (LA41_0==IDENTIFIER) ) {
                    alt41=2;
                }


                switch (alt41) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:355:6: ( ',' c= class_name )
            	    {
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:355:6: ( ',' c= class_name )
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:355:8: ',' c= class_name
            	    {
            	    match(input,35,FOLLOW_35_in_class_name_list2147); if (state.failed) return list;
            	    pushFollow(FOLLOW_class_name_in_class_name_list2151);
            	    c=class_name();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) list.add((c!=null?c.name:null)); 
            	    }

            	    }


            	    }
            	    break;
            	case 2 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:358:6: (c= class_name )
            	    {
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:358:6: (c= class_name )
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:358:8: c= class_name
            	    {
            	    pushFollow(FOLLOW_class_name_in_class_name_list2180);
            	    c=class_name();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) list.add((c!=null?c.name:null)); 
            	    }

            	    }


            	    }
            	    break;

            	default :
            	    break loop41;
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
        return list;
    }
    // $ANTLR end "class_name_list"


    // $ANTLR start "cluster_name_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:365:1: cluster_name_list returns [List<String> list] : c1= cluster_name ( ( ',' c= cluster_name ) | (c= cluster_name ) )* ;
    public final List<String> cluster_name_list() throws RecognitionException {
        List<String> list = null;

        BONParser.cluster_name_return c1 = null;

        BONParser.cluster_name_return c = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:365:47: (c1= cluster_name ( ( ',' c= cluster_name ) | (c= cluster_name ) )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:366:3: c1= cluster_name ( ( ',' c= cluster_name ) | (c= cluster_name ) )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_cluster_name_in_cluster_name_list2249);
            c1=cluster_name();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               if(isOk()) list.add((c1!=null?input.toString(c1.start,c1.stop):null)); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:369:3: ( ( ',' c= cluster_name ) | (c= cluster_name ) )*
            loop42:
            do {
                int alt42=3;
                int LA42_0 = input.LA(1);

                if ( (LA42_0==35) ) {
                    alt42=1;
                }
                else if ( (LA42_0==IDENTIFIER) ) {
                    alt42=2;
                }


                switch (alt42) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:369:6: ( ',' c= cluster_name )
            	    {
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:369:6: ( ',' c= cluster_name )
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:369:8: ',' c= cluster_name
            	    {
            	    match(input,35,FOLLOW_35_in_cluster_name_list2262); if (state.failed) return list;
            	    pushFollow(FOLLOW_cluster_name_in_cluster_name_list2266);
            	    c=cluster_name();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) list.add((c!=null?input.toString(c.start,c.stop):null)); 
            	    }

            	    }


            	    }
            	    break;
            	case 2 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:372:6: (c= cluster_name )
            	    {
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:372:6: (c= cluster_name )
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:372:8: c= cluster_name
            	    {
            	    pushFollow(FOLLOW_cluster_name_in_cluster_name_list2294);
            	    c=cluster_name();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       addParseProblem(new MissingElementParseError(getSourceLocation((c!=null?((Token)c.start):null)), "comma", "before additional class name", false)); 
            	    }
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) list.add((c!=null?input.toString(c.start,c.stop):null)); 
            	    }

            	    }


            	    }
            	    break;

            	default :
            	    break loop42;
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
        return list;
    }
    // $ANTLR end "cluster_name_list"

    public static class class_or_cluster_name_list_return extends ParserRuleReturnScope {
        public List<String> list;
    };

    // $ANTLR start "class_or_cluster_name_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:379:1: class_or_cluster_name_list returns [List<String> list] : c1= class_or_bracketed_cluster_name ( ',' c= class_or_bracketed_cluster_name )* ;
    public final BONParser.class_or_cluster_name_list_return class_or_cluster_name_list() throws RecognitionException {
        BONParser.class_or_cluster_name_list_return retval = new BONParser.class_or_cluster_name_list_return();
        retval.start = input.LT(1);

        String c1 = null;

        String c = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:379:56: (c1= class_or_bracketed_cluster_name ( ',' c= class_or_bracketed_cluster_name )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:380:3: c1= class_or_bracketed_cluster_name ( ',' c= class_or_bracketed_cluster_name )*
            {
            if ( state.backtracking==0 ) {
               retval.list = createList(); 
            }
            pushFollow(FOLLOW_class_or_bracketed_cluster_name_in_class_or_cluster_name_list2391);
            c1=class_or_bracketed_cluster_name();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.list.add(c1); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:383:3: ( ',' c= class_or_bracketed_cluster_name )*
            loop43:
            do {
                int alt43=2;
                int LA43_0 = input.LA(1);

                if ( (LA43_0==35) ) {
                    alt43=1;
                }


                switch (alt43) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:383:5: ',' c= class_or_bracketed_cluster_name
            	    {
            	    match(input,35,FOLLOW_35_in_class_or_cluster_name_list2401); if (state.failed) return retval;
            	    pushFollow(FOLLOW_class_or_bracketed_cluster_name_in_class_or_cluster_name_list2405);
            	    c=class_or_bracketed_cluster_name();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.list.add(c); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop43;
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
    // $ANTLR end "class_or_cluster_name_list"


    // $ANTLR start "class_or_bracketed_cluster_name"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:388:1: class_or_bracketed_cluster_name returns [String name] : ( class_name | '(' cluster_name ')' );
    public final String class_or_bracketed_cluster_name() throws RecognitionException {
        String name = null;

        BONParser.class_name_return class_name41 = null;

        BONParser.cluster_name_return cluster_name42 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:388:55: ( class_name | '(' cluster_name ')' )
            int alt44=2;
            int LA44_0 = input.LA(1);

            if ( (LA44_0==IDENTIFIER) ) {
                alt44=1;
            }
            else if ( (LA44_0==42) ) {
                alt44=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return name;}
                NoViableAltException nvae =
                    new NoViableAltException("", 44, 0, input);

                throw nvae;
            }
            switch (alt44) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:389:4: class_name
                    {
                    pushFollow(FOLLOW_class_name_in_class_or_bracketed_cluster_name2433);
                    class_name41=class_name();

                    state._fsp--;
                    if (state.failed) return name;
                    if ( state.backtracking==0 ) {
                       if(isOk()) name = (class_name41!=null?class_name41.name:null).getName(); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:392:4: '(' cluster_name ')'
                    {
                    match(input,42,FOLLOW_42_in_class_or_bracketed_cluster_name2447); if (state.failed) return name;
                    pushFollow(FOLLOW_cluster_name_in_class_or_bracketed_cluster_name2449);
                    cluster_name42=cluster_name();

                    state._fsp--;
                    if (state.failed) return name;
                    match(input,43,FOLLOW_43_in_class_or_bracketed_cluster_name2451); if (state.failed) return name;
                    if ( state.backtracking==0 ) {
                       if(isOk()) name = (cluster_name42!=null?cluster_name42.name:null); 
                    }

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
        return name;
    }
    // $ANTLR end "class_or_bracketed_cluster_name"

    public static class class_name_return extends ParserRuleReturnScope {
        public ClassName name;
    };

    // $ANTLR start "class_name"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:396:1: class_name returns [ClassName name] : i= IDENTIFIER ;
    public final BONParser.class_name_return class_name() throws RecognitionException {
        BONParser.class_name_return retval = new BONParser.class_name_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:396:37: (i= IDENTIFIER )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:397:3: i= IDENTIFIER
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_class_name2473); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.name = ClassName.mk((i!=null?i.getText():null), getSLoc(i)); 
            }

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
    // $ANTLR end "class_name"


    // $ANTLR start "event_chart"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:401:1: event_chart returns [EventChart ec] : e= 'event_chart' system_name ( 'incoming' | 'outgoing' )? ( indexing )? ( explanation )? ( part )? (ee= event_entries | ) end= 'end' ;
    public final EventChart event_chart() throws RecognitionException {
        EventChart ec = null;

        Token e=null;
        Token end=null;
        List<EventEntry> ee = null;

        BONParser.indexing_return indexing43 = null;

        String explanation44 = null;

        String part45 = null;

        String system_name46 = null;


         boolean incoming = false; boolean outgoing = false; Indexing indexing = null;
                String explanation = null; String part = null; List<EventEntry> eventEntries = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:406:1: (e= 'event_chart' system_name ( 'incoming' | 'outgoing' )? ( indexing )? ( explanation )? ( part )? (ee= event_entries | ) end= 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:407:3: e= 'event_chart' system_name ( 'incoming' | 'outgoing' )? ( indexing )? ( explanation )? ( part )? (ee= event_entries | ) end= 'end'
            {
            e=(Token)match(input,44,FOLLOW_44_in_event_chart2504); if (state.failed) return ec;
            pushFollow(FOLLOW_system_name_in_event_chart2506);
            system_name46=system_name();

            state._fsp--;
            if (state.failed) return ec;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:408:3: ( 'incoming' | 'outgoing' )?
            int alt45=3;
            int LA45_0 = input.LA(1);

            if ( (LA45_0==45) ) {
                alt45=1;
            }
            else if ( (LA45_0==46) ) {
                alt45=2;
            }
            switch (alt45) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:408:6: 'incoming'
                    {
                    match(input,45,FOLLOW_45_in_event_chart2514); if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       incoming = true; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:409:6: 'outgoing'
                    {
                    match(input,46,FOLLOW_46_in_event_chart2524); if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       outgoing = true; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:411:3: ( indexing )?
            int alt46=2;
            int LA46_0 = input.LA(1);

            if ( (LA46_0==30) ) {
                alt46=1;
            }
            switch (alt46) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:411:4: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_event_chart2536);
                    indexing43=indexing();

                    state._fsp--;
                    if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) indexing = (indexing43!=null?indexing43.indexing:null); 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:412:3: ( explanation )?
            int alt47=2;
            int LA47_0 = input.LA(1);

            if ( (LA47_0==29) ) {
                alt47=1;
            }
            switch (alt47) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:412:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_event_chart2545);
                    explanation44=explanation();

                    state._fsp--;
                    if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) explanation = explanation44; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:413:3: ( part )?
            int alt48=2;
            int LA48_0 = input.LA(1);

            if ( (LA48_0==31) ) {
                alt48=1;
            }
            switch (alt48) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:413:4: part
                    {
                    pushFollow(FOLLOW_part_in_event_chart2555);
                    part45=part();

                    state._fsp--;
                    if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) part = part45; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:414:3: (ee= event_entries | )
            int alt49=2;
            int LA49_0 = input.LA(1);

            if ( (LA49_0==47) ) {
                alt49=1;
            }
            else if ( (LA49_0==25) ) {
                alt49=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return ec;}
                NoViableAltException nvae =
                    new NoViableAltException("", 49, 0, input);

                throw nvae;
            }
            switch (alt49) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:414:5: ee= event_entries
                    {
                    pushFollow(FOLLOW_event_entries_in_event_chart2568);
                    ee=event_entries();

                    state._fsp--;
                    if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) eventEntries = ee; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:417:5: 
                    {
                    if ( state.backtracking==0 ) {
                       eventEntries = createList(); 
                    }

                    }
                    break;

            }

            end=(Token)match(input,25,FOLLOW_25_in_event_chart2595); if (state.failed) return ec;
            if ( state.backtracking==0 ) {
               if(isOk()) ec = EventChart.mk(system_name46, incoming, outgoing, eventEntries, indexing, explanation, part, getSLoc(e,end)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ec;
    }
    // $ANTLR end "event_chart"


    // $ANTLR start "event_entries"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:423:1: event_entries returns [List<EventEntry> entries] : ( event_entry )+ ;
    public final List<EventEntry> event_entries() throws RecognitionException {
        List<EventEntry> entries = null;

        EventEntry event_entry47 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:423:50: ( ( event_entry )+ )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:424:3: ( event_entry )+
            {
            if ( state.backtracking==0 ) {
               entries = createList(); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:425:3: ( event_entry )+
            int cnt50=0;
            loop50:
            do {
                int alt50=2;
                int LA50_0 = input.LA(1);

                if ( (LA50_0==47) ) {
                    alt50=1;
                }


                switch (alt50) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:425:4: event_entry
            	    {
            	    pushFollow(FOLLOW_event_entry_in_event_entries2632);
            	    event_entry47=event_entry();

            	    state._fsp--;
            	    if (state.failed) return entries;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) entries.add(event_entry47); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt50 >= 1 ) break loop50;
            	    if (state.backtracking>0) {state.failed=true; return entries;}
                        EarlyExitException eee =
                            new EarlyExitException(50, input);
                        throw eee;
                }
                cnt50++;
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return entries;
    }
    // $ANTLR end "event_entries"


    // $ANTLR start "event_entry"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:428:1: event_entry returns [EventEntry entry] : e= 'event' ( (m= manifest_textblock ) | ) i= 'involves' ( (ccns= class_or_cluster_name_list ) | ) ;
    public final EventEntry event_entry() throws RecognitionException {
        EventEntry entry = null;

        Token e=null;
        Token i=null;
        BONParser.manifest_textblock_return m = null;

        BONParser.class_or_cluster_name_list_return ccns = null;


         boolean mok=false; boolean cok=false; List<String> ccnl = null; String description = null; Token stop=null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:429:119: (e= 'event' ( (m= manifest_textblock ) | ) i= 'involves' ( (ccns= class_or_cluster_name_list ) | ) )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:430:3: e= 'event' ( (m= manifest_textblock ) | ) i= 'involves' ( (ccns= class_or_cluster_name_list ) | )
            {
            e=(Token)match(input,47,FOLLOW_47_in_event_entry2675); if (state.failed) return entry;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:431:3: ( (m= manifest_textblock ) | )
            int alt51=2;
            int LA51_0 = input.LA(1);

            if ( (LA51_0==MANIFEST_STRING||LA51_0==MANIFEST_TEXTBLOCK_START) ) {
                alt51=1;
            }
            else if ( (LA51_0==48) ) {
                alt51=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return entry;}
                NoViableAltException nvae =
                    new NoViableAltException("", 51, 0, input);

                throw nvae;
            }
            switch (alt51) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:431:6: (m= manifest_textblock )
                    {
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:431:6: (m= manifest_textblock )
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:431:8: m= manifest_textblock
                    {
                    pushFollow(FOLLOW_manifest_textblock_in_event_entry2686);
                    m=manifest_textblock();

                    state._fsp--;
                    if (state.failed) return entry;
                    if ( state.backtracking==0 ) {
                      mok=true; if(isOk()) description=(m!=null?input.toString(m.start,m.stop):null);
                    }

                    }


                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:435:4: 
                    {
                    if ( state.backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(e), "event name", "in event entry clause", true)); 
                    }

                    }
                    break;

            }

            i=(Token)match(input,48,FOLLOW_48_in_event_entry2726); if (state.failed) return entry;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:438:3: ( (ccns= class_or_cluster_name_list ) | )
            int alt52=2;
            int LA52_0 = input.LA(1);

            if ( (LA52_0==IDENTIFIER||LA52_0==42) ) {
                alt52=1;
            }
            else if ( (LA52_0==25||LA52_0==47) ) {
                alt52=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return entry;}
                NoViableAltException nvae =
                    new NoViableAltException("", 52, 0, input);

                throw nvae;
            }
            switch (alt52) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:438:6: (ccns= class_or_cluster_name_list )
                    {
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:438:6: (ccns= class_or_cluster_name_list )
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:438:7: ccns= class_or_cluster_name_list
                    {
                    pushFollow(FOLLOW_class_or_cluster_name_list_in_event_entry2736);
                    ccns=class_or_cluster_name_list();

                    state._fsp--;
                    if (state.failed) return entry;
                    if ( state.backtracking==0 ) {
                       cok=true; if(isOk()) ccnl = (ccns!=null?ccns.list:null); 
                    }
                    if ( state.backtracking==0 ) {
                       stop = (ccns!=null?((Token)ccns.stop):null); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:443:6: 
                    {
                    if ( state.backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(i), "class name list", "in involves clause of event entry", true)); 
                    }
                    if ( state.backtracking==0 ) {
                       stop = i; 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               if (mok && cok && isOk()) entry = EventEntry.mk(description, ccnl, getSLoc(e,stop)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return entry;
    }
    // $ANTLR end "event_entry"


    // $ANTLR start "scenario_chart"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:449:1: scenario_chart returns [ScenarioChart sc] : s= 'scenario_chart' system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries | ) e= 'end' ;
    public final ScenarioChart scenario_chart() throws RecognitionException {
        ScenarioChart sc = null;

        Token s=null;
        Token e=null;
        BONParser.indexing_return indexing48 = null;

        String explanation49 = null;

        String part50 = null;

        List<ScenarioEntry> scenario_entries51 = null;

        String system_name52 = null;


         Indexing indexing = null; String explanation = null; String part = null; List<ScenarioEntry> entries = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:453:1: (s= 'scenario_chart' system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries | ) e= 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:454:3: s= 'scenario_chart' system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries | ) e= 'end'
            {
            s=(Token)match(input,49,FOLLOW_49_in_scenario_chart2816); if (state.failed) return sc;
            pushFollow(FOLLOW_system_name_in_scenario_chart2818);
            system_name52=system_name();

            state._fsp--;
            if (state.failed) return sc;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:455:3: ( indexing )?
            int alt53=2;
            int LA53_0 = input.LA(1);

            if ( (LA53_0==30) ) {
                alt53=1;
            }
            switch (alt53) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:455:4: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_scenario_chart2823);
                    indexing48=indexing();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) indexing = (indexing48!=null?indexing48.indexing:null); 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:456:3: ( explanation )?
            int alt54=2;
            int LA54_0 = input.LA(1);

            if ( (LA54_0==29) ) {
                alt54=1;
            }
            switch (alt54) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:456:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_scenario_chart2833);
                    explanation49=explanation();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) explanation = explanation49; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:457:3: ( part )?
            int alt55=2;
            int LA55_0 = input.LA(1);

            if ( (LA55_0==31) ) {
                alt55=1;
            }
            switch (alt55) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:457:4: part
                    {
                    pushFollow(FOLLOW_part_in_scenario_chart2843);
                    part50=part();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) part = part50; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:458:3: ( scenario_entries | )
            int alt56=2;
            int LA56_0 = input.LA(1);

            if ( (LA56_0==50) ) {
                alt56=1;
            }
            else if ( (LA56_0==25) ) {
                alt56=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return sc;}
                NoViableAltException nvae =
                    new NoViableAltException("", 56, 0, input);

                throw nvae;
            }
            switch (alt56) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:458:5: scenario_entries
                    {
                    pushFollow(FOLLOW_scenario_entries_in_scenario_chart2854);
                    scenario_entries51=scenario_entries();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) entries = scenario_entries51; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:459:6: 
                    {
                    if ( state.backtracking==0 ) {
                       if(isOk()) entries = emptyList(); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_scenario_chart2875); if (state.failed) return sc;
            if ( state.backtracking==0 ) {
               if(isOk()) sc = ScenarioChart.mk(system_name52, entries, indexing, explanation, part, getSLoc(s,e)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return sc;
    }
    // $ANTLR end "scenario_chart"


    // $ANTLR start "scenario_entries"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:465:1: scenario_entries returns [List<ScenarioEntry> entries] : ( scenario_entry )+ ;
    public final List<ScenarioEntry> scenario_entries() throws RecognitionException {
        List<ScenarioEntry> entries = null;

        ScenarioEntry scenario_entry53 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:465:56: ( ( scenario_entry )+ )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:466:3: ( scenario_entry )+
            {
            if ( state.backtracking==0 ) {
               entries = createList(); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:467:3: ( scenario_entry )+
            int cnt57=0;
            loop57:
            do {
                int alt57=2;
                int LA57_0 = input.LA(1);

                if ( (LA57_0==50) ) {
                    alt57=1;
                }


                switch (alt57) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:467:4: scenario_entry
            	    {
            	    pushFollow(FOLLOW_scenario_entry_in_scenario_entries2915);
            	    scenario_entry53=scenario_entry();

            	    state._fsp--;
            	    if (state.failed) return entries;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) entries.add(scenario_entry53); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt57 >= 1 ) break loop57;
            	    if (state.backtracking>0) {state.failed=true; return entries;}
                        EarlyExitException eee =
                            new EarlyExitException(57, input);
                        throw eee;
                }
                cnt57++;
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return entries;
    }
    // $ANTLR end "scenario_entries"


    // $ANTLR start "scenario_entry"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:470:1: scenario_entry returns [ScenarioEntry entry] : s= 'scenario' m= MANIFEST_STRING d= description ;
    public final ScenarioEntry scenario_entry() throws RecognitionException {
        ScenarioEntry entry = null;

        Token s=null;
        Token m=null;
        BONParser.description_return d = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:470:46: (s= 'scenario' m= MANIFEST_STRING d= description )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:471:3: s= 'scenario' m= MANIFEST_STRING d= description
            {
            s=(Token)match(input,50,FOLLOW_50_in_scenario_entry2956); if (state.failed) return entry;
            m=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_scenario_entry2960); if (state.failed) return entry;
            pushFollow(FOLLOW_description_in_scenario_entry2964);
            d=description();

            state._fsp--;
            if (state.failed) return entry;
            if ( state.backtracking==0 ) {
               if(isOk()) entry =  ScenarioEntry.mk((m!=null?m.getText():null), (d!=null?d.description:null), getSLoc(s,(d!=null?((Token)d.stop):null))); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return entry;
    }
    // $ANTLR end "scenario_entry"

    public static class creation_chart_return extends ParserRuleReturnScope {
        public CreationChart cc;
    };

    // $ANTLR start "creation_chart"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:475:1: creation_chart returns [CreationChart cc] : start= 'creation_chart' system_name ( indexing )? ( explanation )? ( part )? ( creation_entries | ) end= 'end' ;
    public final BONParser.creation_chart_return creation_chart() throws RecognitionException {
        BONParser.creation_chart_return retval = new BONParser.creation_chart_return();
        retval.start = input.LT(1);

        Token start=null;
        Token end=null;
        BONParser.indexing_return indexing54 = null;

        String explanation55 = null;

        String part56 = null;

        List<CreationEntry> creation_entries57 = null;

        String system_name58 = null;


         List<CreationEntry> entries = null; Indexing indexing = null; String explanation = null; String part = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:479:1: (start= 'creation_chart' system_name ( indexing )? ( explanation )? ( part )? ( creation_entries | ) end= 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:480:3: start= 'creation_chart' system_name ( indexing )? ( explanation )? ( part )? ( creation_entries | ) end= 'end'
            {
            start=(Token)match(input,51,FOLLOW_51_in_creation_chart2993); if (state.failed) return retval;
            pushFollow(FOLLOW_system_name_in_creation_chart2995);
            system_name58=system_name();

            state._fsp--;
            if (state.failed) return retval;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:481:3: ( indexing )?
            int alt58=2;
            int LA58_0 = input.LA(1);

            if ( (LA58_0==30) ) {
                alt58=1;
            }
            switch (alt58) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:481:4: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_creation_chart3000);
                    indexing54=indexing();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) indexing = (indexing54!=null?indexing54.indexing:null); 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:482:3: ( explanation )?
            int alt59=2;
            int LA59_0 = input.LA(1);

            if ( (LA59_0==29) ) {
                alt59=1;
            }
            switch (alt59) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:482:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_creation_chart3010);
                    explanation55=explanation();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) explanation = explanation55; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:483:3: ( part )?
            int alt60=2;
            int LA60_0 = input.LA(1);

            if ( (LA60_0==31) ) {
                alt60=1;
            }
            switch (alt60) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:483:4: part
                    {
                    pushFollow(FOLLOW_part_in_creation_chart3020);
                    part56=part();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) part = part56; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:484:3: ( creation_entries | )
            int alt61=2;
            int LA61_0 = input.LA(1);

            if ( (LA61_0==52) ) {
                alt61=1;
            }
            else if ( (LA61_0==25) ) {
                alt61=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 61, 0, input);

                throw nvae;
            }
            switch (alt61) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:484:5: creation_entries
                    {
                    pushFollow(FOLLOW_creation_entries_in_creation_chart3031);
                    creation_entries57=creation_entries();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) entries = creation_entries57; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:485:6: 
                    {
                    if ( state.backtracking==0 ) {
                       entries = emptyList(); 
                    }

                    }
                    break;

            }

            end=(Token)match(input,25,FOLLOW_25_in_creation_chart3048); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.cc = CreationChart.mk(system_name58, entries, indexing, explanation, part,getSLoc(start,end)); 
            }

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
    // $ANTLR end "creation_chart"


    // $ANTLR start "creation_entries"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:490:1: creation_entries returns [List<CreationEntry> entries] : ( creation_entry )+ ;
    public final List<CreationEntry> creation_entries() throws RecognitionException {
        List<CreationEntry> entries = null;

        CreationEntry creation_entry59 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:490:56: ( ( creation_entry )+ )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:491:3: ( creation_entry )+
            {
            if ( state.backtracking==0 ) {
               entries = createList(); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:492:3: ( creation_entry )+
            int cnt62=0;
            loop62:
            do {
                int alt62=2;
                int LA62_0 = input.LA(1);

                if ( (LA62_0==52) ) {
                    alt62=1;
                }


                switch (alt62) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:492:4: creation_entry
            	    {
            	    pushFollow(FOLLOW_creation_entry_in_creation_entries3089);
            	    creation_entry59=creation_entry();

            	    state._fsp--;
            	    if (state.failed) return entries;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) entries.add(creation_entry59); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt62 >= 1 ) break loop62;
            	    if (state.backtracking>0) {state.failed=true; return entries;}
                        EarlyExitException eee =
                            new EarlyExitException(62, input);
                        throw eee;
                }
                cnt62++;
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return entries;
    }
    // $ANTLR end "creation_entries"


    // $ANTLR start "creation_entry"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:495:1: creation_entry returns [CreationEntry entry] : c= 'creator' class_name 'creates' ccnl= class_or_cluster_name_list ;
    public final CreationEntry creation_entry() throws RecognitionException {
        CreationEntry entry = null;

        Token c=null;
        BONParser.class_or_cluster_name_list_return ccnl = null;

        BONParser.class_name_return class_name60 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:495:46: (c= 'creator' class_name 'creates' ccnl= class_or_cluster_name_list )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:496:3: c= 'creator' class_name 'creates' ccnl= class_or_cluster_name_list
            {
            c=(Token)match(input,52,FOLLOW_52_in_creation_entry3129); if (state.failed) return entry;
            pushFollow(FOLLOW_class_name_in_creation_entry3131);
            class_name60=class_name();

            state._fsp--;
            if (state.failed) return entry;
            match(input,53,FOLLOW_53_in_creation_entry3136); if (state.failed) return entry;
            pushFollow(FOLLOW_class_or_cluster_name_list_in_creation_entry3140);
            ccnl=class_or_cluster_name_list();

            state._fsp--;
            if (state.failed) return entry;
            if ( state.backtracking==0 ) {
               if(isOk()) entry = CreationEntry.mk((class_name60!=null?class_name60.name:null), (ccnl!=null?ccnl.list:null), getSLoc(c,(ccnl!=null?((Token)ccnl.stop):null))); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return entry;
    }
    // $ANTLR end "creation_entry"


    // $ANTLR start "static_diagram"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:501:1: static_diagram returns [StaticDiagram sd] : s= 'static_diagram' ( extended_id )? comment 'component' sb= static_block e= 'end' ;
    public final StaticDiagram static_diagram() throws RecognitionException {
        StaticDiagram sd = null;

        Token s=null;
        Token e=null;
        List<StaticComponent> sb = null;

        BONParser.extended_id_return extended_id61 = null;

        String comment62 = null;


         String eid = null; String comment = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:507:1: (s= 'static_diagram' ( extended_id )? comment 'component' sb= static_block e= 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:508:3: s= 'static_diagram' ( extended_id )? comment 'component' sb= static_block e= 'end'
            {
            s=(Token)match(input,54,FOLLOW_54_in_static_diagram3173); if (state.failed) return sd;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:509:3: ( extended_id )?
            int alt63=2;
            int LA63_0 = input.LA(1);

            if ( ((LA63_0>=IDENTIFIER && LA63_0<=INTEGER)) ) {
                alt63=1;
            }
            switch (alt63) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:509:4: extended_id
                    {
                    pushFollow(FOLLOW_extended_id_in_static_diagram3179);
                    extended_id61=extended_id();

                    state._fsp--;
                    if (state.failed) return sd;
                    if ( state.backtracking==0 ) {
                       if(isOk()) eid=(extended_id61!=null?extended_id61.eid:null); 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_comment_in_static_diagram3188);
            comment62=comment();

            state._fsp--;
            if (state.failed) return sd;
            if ( state.backtracking==0 ) {
               comment = comment62; 
            }
            match(input,55,FOLLOW_55_in_static_diagram3195); if (state.failed) return sd;
            pushFollow(FOLLOW_static_block_in_static_diagram3202);
            sb=static_block();

            state._fsp--;
            if (state.failed) return sd;
            e=(Token)match(input,25,FOLLOW_25_in_static_diagram3209); if (state.failed) return sd;
            if ( state.backtracking==0 ) {
               if(isOk()) sd = StaticDiagram.mk(sb, eid, comment, getSLoc(s,e)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return sd;
    }
    // $ANTLR end "static_diagram"

    public static class extended_id_return extends ParserRuleReturnScope {
        public String eid;
    };

    // $ANTLR start "extended_id"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:517:1: extended_id returns [String eid] : (i= IDENTIFIER | i= INTEGER );
    public final BONParser.extended_id_return extended_id() throws RecognitionException {
        BONParser.extended_id_return retval = new BONParser.extended_id_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:517:34: (i= IDENTIFIER | i= INTEGER )
            int alt64=2;
            int LA64_0 = input.LA(1);

            if ( (LA64_0==IDENTIFIER) ) {
                alt64=1;
            }
            else if ( (LA64_0==INTEGER) ) {
                alt64=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 64, 0, input);

                throw nvae;
            }
            switch (alt64) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:518:4: i= IDENTIFIER
                    {
                    i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_extended_id3265); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.eid = (i!=null?i.getText():null); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:520:4: i= INTEGER
                    {
                    i=(Token)match(input,INTEGER,FOLLOW_INTEGER_in_extended_id3278); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.eid = (i!=null?i.getText():null); 
                    }

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
    // $ANTLR end "extended_id"


    // $ANTLR start "static_block"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:524:1: static_block returns [List<StaticComponent> components] : (sc= static_component )* ;
    public final List<StaticComponent> static_block() throws RecognitionException {
        List<StaticComponent> components = null;

        StaticComponent sc = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:524:57: ( (sc= static_component )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:525:3: (sc= static_component )*
            {
            if ( state.backtracking==0 ) {
               components = createList(); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:526:3: (sc= static_component )*
            loop65:
            do {
                int alt65=2;
                int LA65_0 = input.LA(1);

                if ( (LA65_0==IDENTIFIER||(LA65_0>=26 && LA65_0<=27)||(LA65_0>=57 && LA65_0<=59)) ) {
                    alt65=1;
                }


                switch (alt65) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:526:4: sc= static_component
            	    {
            	    pushFollow(FOLLOW_static_component_in_static_block3319);
            	    sc=static_component();

            	    state._fsp--;
            	    if (state.failed) return components;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) components.add(sc); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop65;
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
        return components;
    }
    // $ANTLR end "static_block"


    // $ANTLR start "static_component"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:529:1: static_component returns [StaticComponent component] : (c1= cluster | c2= clazz | s= static_relation );
    public final StaticComponent static_component() throws RecognitionException {
        StaticComponent component = null;

        Cluster c1 = null;

        Clazz c2 = null;

        StaticRelation s = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:529:54: (c1= cluster | c2= clazz | s= static_relation )
            int alt66=3;
            switch ( input.LA(1) ) {
            case 27:
                {
                alt66=1;
                }
                break;
            case 26:
            case 57:
            case 58:
            case 59:
                {
                alt66=2;
                }
                break;
            case IDENTIFIER:
                {
                alt66=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return component;}
                NoViableAltException nvae =
                    new NoViableAltException("", 66, 0, input);

                throw nvae;
            }

            switch (alt66) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:530:4: c1= cluster
                    {
                    pushFollow(FOLLOW_cluster_in_static_component3354);
                    c1=cluster();

                    state._fsp--;
                    if (state.failed) return component;
                    if ( state.backtracking==0 ) {
                       if(isOk()) component = c1; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:532:4: c2= clazz
                    {
                    pushFollow(FOLLOW_clazz_in_static_component3367);
                    c2=clazz();

                    state._fsp--;
                    if (state.failed) return component;
                    if ( state.backtracking==0 ) {
                       if(isOk()) component = c2; 
                    }

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:534:4: s= static_relation
                    {
                    pushFollow(FOLLOW_static_relation_in_static_component3380);
                    s=static_relation();

                    state._fsp--;
                    if (state.failed) return component;
                    if ( state.backtracking==0 ) {
                       if(isOk()) component = s; 
                    }

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
        return component;
    }
    // $ANTLR end "static_component"


    // $ANTLR start "cluster"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:538:1: cluster returns [Cluster cluster] : c= 'cluster' cluster_name (r= 'reused' )? comment (cc= cluster_components | ) ;
    public final Cluster cluster() throws RecognitionException {
        Cluster cluster = null;

        Token c=null;
        Token r=null;
        BONParser.cluster_components_return cc = null;

        BONParser.cluster_name_return cluster_name63 = null;

        String comment64 = null;


         boolean reused = false; String comment = null; List<StaticComponent> components = null; Token end = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:542:1: (c= 'cluster' cluster_name (r= 'reused' )? comment (cc= cluster_components | ) )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:543:3: c= 'cluster' cluster_name (r= 'reused' )? comment (cc= cluster_components | )
            {
            c=(Token)match(input,27,FOLLOW_27_in_cluster3412); if (state.failed) return cluster;
            pushFollow(FOLLOW_cluster_name_in_cluster3414);
            cluster_name63=cluster_name();

            state._fsp--;
            if (state.failed) return cluster;
            if ( state.backtracking==0 ) {
               end = (cluster_name63!=null?((Token)cluster_name63.stop):null); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:544:3: (r= 'reused' )?
            int alt67=2;
            int LA67_0 = input.LA(1);

            if ( (LA67_0==56) ) {
                alt67=1;
            }
            switch (alt67) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:544:4: r= 'reused'
                    {
                    r=(Token)match(input,56,FOLLOW_56_in_cluster3423); if (state.failed) return cluster;
                    if ( state.backtracking==0 ) {
                       if(isOk()) reused = true; end = r; 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_comment_in_cluster3433);
            comment64=comment();

            state._fsp--;
            if (state.failed) return cluster;
            if ( state.backtracking==0 ) {
               comment = comment64; 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:546:3: (cc= cluster_components | )
            int alt68=2;
            int LA68_0 = input.LA(1);

            if ( (LA68_0==55) ) {
                alt68=1;
            }
            else if ( (LA68_0==IDENTIFIER||(LA68_0>=25 && LA68_0<=27)||(LA68_0>=57 && LA68_0<=59)) ) {
                alt68=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return cluster;}
                NoViableAltException nvae =
                    new NoViableAltException("", 68, 0, input);

                throw nvae;
            }
            switch (alt68) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:546:6: cc= cluster_components
                    {
                    pushFollow(FOLLOW_cluster_components_in_cluster3447);
                    cc=cluster_components();

                    state._fsp--;
                    if (state.failed) return cluster;
                    if ( state.backtracking==0 ) {
                       if(isOk()) components = (cc!=null?cc.components:null); end = (cc!=null?((Token)cc.stop):null);
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:549:6: 
                    {
                    if ( state.backtracking==0 ) {
                       components = emptyList(); 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               if(isOk()) cluster = Cluster.mk((cluster_name63!=null?cluster_name63.name:null), components, reused, comment, getSLoc(c,end)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return cluster;
    }
    // $ANTLR end "cluster"

    public static class cluster_components_return extends ParserRuleReturnScope {
        public List<StaticComponent> components;
    };

    // $ANTLR start "cluster_components"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:554:1: cluster_components returns [List<StaticComponent> components] : 'component' static_block 'end' ;
    public final BONParser.cluster_components_return cluster_components() throws RecognitionException {
        BONParser.cluster_components_return retval = new BONParser.cluster_components_return();
        retval.start = input.LT(1);

        List<StaticComponent> static_block65 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:554:63: ( 'component' static_block 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:555:3: 'component' static_block 'end'
            {
            match(input,55,FOLLOW_55_in_cluster_components3502); if (state.failed) return retval;
            pushFollow(FOLLOW_static_block_in_cluster_components3504);
            static_block65=static_block();

            state._fsp--;
            if (state.failed) return retval;
            match(input,25,FOLLOW_25_in_cluster_components3506); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.components = static_block65; 
            }

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
    // $ANTLR end "cluster_components"


    // $ANTLR start "clazz"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:559:1: clazz returns [Clazz clazz] : (r= 'root' | d= 'deferred' | e= 'effective' | ) c= 'class' cn= class_name (fg= formal_generics | ) (ru= 'reused' )? (p= 'persistent' )? (i= 'interfaced' )? comment (ci= class_interface )? ;
    public final Clazz clazz() throws RecognitionException {
        Clazz clazz = null;

        Token r=null;
        Token d=null;
        Token e=null;
        Token c=null;
        Token ru=null;
        Token p=null;
        Token i=null;
        BONParser.class_name_return cn = null;

        BONParser.formal_generics_return fg = null;

        BONParser.class_interface_return ci = null;

        String comment66 = null;


         Clazz.Mod mod = null; List<FormalGeneric> generics = null; Token start = null; Token end = null;
                boolean reused = false; boolean persistent = false; boolean interfaced = false; 
                String comment = null; ClassInterface classInterface = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:563:1: ( (r= 'root' | d= 'deferred' | e= 'effective' | ) c= 'class' cn= class_name (fg= formal_generics | ) (ru= 'reused' )? (p= 'persistent' )? (i= 'interfaced' )? comment (ci= class_interface )? )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:564:3: (r= 'root' | d= 'deferred' | e= 'effective' | ) c= 'class' cn= class_name (fg= formal_generics | ) (ru= 'reused' )? (p= 'persistent' )? (i= 'interfaced' )? comment (ci= class_interface )?
            {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:564:3: (r= 'root' | d= 'deferred' | e= 'effective' | )
            int alt69=4;
            switch ( input.LA(1) ) {
            case 57:
                {
                alt69=1;
                }
                break;
            case 58:
                {
                alt69=2;
                }
                break;
            case 59:
                {
                alt69=3;
                }
                break;
            case 26:
                {
                alt69=4;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return clazz;}
                NoViableAltException nvae =
                    new NoViableAltException("", 69, 0, input);

                throw nvae;
            }

            switch (alt69) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:564:7: r= 'root'
                    {
                    r=(Token)match(input,57,FOLLOW_57_in_clazz3557); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       mod = Clazz.Mod.ROOT; start = r; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:565:7: d= 'deferred'
                    {
                    d=(Token)match(input,58,FOLLOW_58_in_clazz3574); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       mod = Clazz.Mod.DEFERRED; start = d; 
                    }

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:566:7: e= 'effective'
                    {
                    e=(Token)match(input,59,FOLLOW_59_in_clazz3587); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       mod = Clazz.Mod.EFFECTIVE; start = e; 
                    }

                    }
                    break;
                case 4 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:567:21: 
                    {
                    if ( state.backtracking==0 ) {
                       mod = Clazz.Mod.NONE; 
                    }

                    }
                    break;

            }

            c=(Token)match(input,26,FOLLOW_26_in_clazz3621); if (state.failed) return clazz;
            if ( state.backtracking==0 ) {
               if (start == null) start = c; 
            }
            pushFollow(FOLLOW_class_name_in_clazz3632);
            cn=class_name();

            state._fsp--;
            if (state.failed) return clazz;
            if ( state.backtracking==0 ) {
               end = (cn!=null?((Token)cn.stop):null); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:573:3: (fg= formal_generics | )
            int alt70=2;
            int LA70_0 = input.LA(1);

            if ( (LA70_0==66) ) {
                alt70=1;
            }
            else if ( (LA70_0==IDENTIFIER||(LA70_0>=25 && LA70_0<=27)||LA70_0==30||LA70_0==38||(LA70_0>=56 && LA70_0<=61)||(LA70_0>=71 && LA70_0<=72)) ) {
                alt70=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return clazz;}
                NoViableAltException nvae =
                    new NoViableAltException("", 70, 0, input);

                throw nvae;
            }
            switch (alt70) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:573:6: fg= formal_generics
                    {
                    pushFollow(FOLLOW_formal_generics_in_clazz3645);
                    fg=formal_generics();

                    state._fsp--;
                    if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       if(isOk()) generics = (fg!=null?fg.generics:null); end = (fg!=null?((Token)fg.stop):null); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:574:6: 
                    {
                    if ( state.backtracking==0 ) {
                       generics = emptyList(); 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:576:3: (ru= 'reused' )?
            int alt71=2;
            int LA71_0 = input.LA(1);

            if ( (LA71_0==56) ) {
                alt71=1;
            }
            switch (alt71) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:576:4: ru= 'reused'
                    {
                    ru=(Token)match(input,56,FOLLOW_56_in_clazz3667); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       reused = true; end = ru; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:577:3: (p= 'persistent' )?
            int alt72=2;
            int LA72_0 = input.LA(1);

            if ( (LA72_0==60) ) {
                alt72=1;
            }
            switch (alt72) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:577:4: p= 'persistent'
                    {
                    p=(Token)match(input,60,FOLLOW_60_in_clazz3680); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       persistent = true; end = p; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:578:3: (i= 'interfaced' )?
            int alt73=2;
            int LA73_0 = input.LA(1);

            if ( (LA73_0==61) ) {
                alt73=1;
            }
            switch (alt73) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:578:4: i= 'interfaced'
                    {
                    i=(Token)match(input,61,FOLLOW_61_in_clazz3694); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       interfaced = true; end = i; 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_comment_in_clazz3702);
            comment66=comment();

            state._fsp--;
            if (state.failed) return clazz;
            if ( state.backtracking==0 ) {
               comment = comment66; 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:581:3: (ci= class_interface )?
            int alt74=2;
            int LA74_0 = input.LA(1);

            if ( (LA74_0==30||LA74_0==38||(LA74_0>=71 && LA74_0<=72)) ) {
                alt74=1;
            }
            switch (alt74) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:581:4: ci= class_interface
                    {
                    pushFollow(FOLLOW_class_interface_in_clazz3714);
                    ci=class_interface();

                    state._fsp--;
                    if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       if(isOk()) classInterface = (ci!=null?ci.ci:null); end = (ci!=null?((Token)ci.stop):null); 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               if(isOk()) clazz = Clazz.mk((cn!=null?cn.name:null), generics, mod, classInterface, reused, persistent, interfaced, comment, getSLoc(start,end)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return clazz;
    }
    // $ANTLR end "clazz"


    // $ANTLR start "comment"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:586:1: comment returns [String comment] : ;
    public final String comment() throws RecognitionException {
        String comment = null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:586:34: ()
            // /home/fintan/workspaces/bon/bonc/src/BON.g:587:3: 
            {
            if ( state.backtracking==0 ) {
               comment = lookForCommentBefore(); 
            }

            }

        }
        finally {
        }
        return comment;
    }
    // $ANTLR end "comment"


    // $ANTLR start "static_relation"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:590:1: static_relation returns [StaticRelation relation] : (ir= inheritance_relation | cr= client_relation );
    public final StaticRelation static_relation() throws RecognitionException {
        StaticRelation relation = null;

        InheritanceRelation ir = null;

        ClientRelation cr = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:590:51: (ir= inheritance_relation | cr= client_relation )
            int alt75=2;
            alt75 = dfa75.predict(input);
            switch (alt75) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:591:4: ir= inheritance_relation
                    {
                    pushFollow(FOLLOW_inheritance_relation_in_static_relation3772);
                    ir=inheritance_relation();

                    state._fsp--;
                    if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       if(isOk()) relation = ir; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:593:4: cr= client_relation
                    {
                    pushFollow(FOLLOW_client_relation_in_static_relation3784);
                    cr=client_relation();

                    state._fsp--;
                    if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       if(isOk()) relation = cr; 
                    }

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
        return relation;
    }
    // $ANTLR end "static_relation"


    // $ANTLR start "inheritance_relation"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:597:1: inheritance_relation returns [InheritanceRelation relation] : c= child 'inherit' (a= '{' multiplicity b= '}' )? p= parent ( semantic_label )? ;
    public final InheritanceRelation inheritance_relation() throws RecognitionException {
        InheritanceRelation relation = null;

        Token a=null;
        Token b=null;
        BONParser.child_return c = null;

        BONParser.parent_return p = null;

        BONParser.multiplicity_return multiplicity67 = null;

        BONParser.semantic_label_return semantic_label68 = null;


         Multiplicity multiplicity = null; String semanticLabel = null; Token end = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:601:1: (c= child 'inherit' (a= '{' multiplicity b= '}' )? p= parent ( semantic_label )? )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:602:3: c= child 'inherit' (a= '{' multiplicity b= '}' )? p= parent ( semantic_label )?
            {
            pushFollow(FOLLOW_child_in_inheritance_relation3815);
            c=child();

            state._fsp--;
            if (state.failed) return relation;
            match(input,38,FOLLOW_38_in_inheritance_relation3817); if (state.failed) return relation;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:603:3: (a= '{' multiplicity b= '}' )?
            int alt76=2;
            int LA76_0 = input.LA(1);

            if ( (LA76_0==62) ) {
                alt76=1;
            }
            switch (alt76) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:603:4: a= '{' multiplicity b= '}'
                    {
                    a=(Token)match(input,62,FOLLOW_62_in_inheritance_relation3825); if (state.failed) return relation;
                    pushFollow(FOLLOW_multiplicity_in_inheritance_relation3827);
                    multiplicity67=multiplicity();

                    state._fsp--;
                    if (state.failed) return relation;
                    b=(Token)match(input,63,FOLLOW_63_in_inheritance_relation3831); if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       if(isOk()) multiplicity = Multiplicity.mk((multiplicity67!=null?multiplicity67.num:null), getSLoc(a,b)); 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_parent_in_inheritance_relation3848);
            p=parent();

            state._fsp--;
            if (state.failed) return relation;
            if ( state.backtracking==0 ) {
               end = (p!=null?((Token)p.stop):null); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:608:3: ( semantic_label )?
            int alt77=2;
            int LA77_0 = input.LA(1);

            if ( (LA77_0==MANIFEST_STRING) ) {
                alt77=1;
            }
            switch (alt77) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:608:5: semantic_label
                    {
                    pushFollow(FOLLOW_semantic_label_in_inheritance_relation3859);
                    semantic_label68=semantic_label();

                    state._fsp--;
                    if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       if(isOk()) semanticLabel = (semantic_label68!=null?semantic_label68.label:null); end = (semantic_label68!=null?((Token)semantic_label68.stop):null); 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               if(isOk()) relation = InheritanceRelation.mk((c!=null?c.ref:null), (p!=null?p.ref:null), multiplicity, semanticLabel, getSLoc((c!=null?((Token)c.start):null), end)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return relation;
    }
    // $ANTLR end "inheritance_relation"


    // $ANTLR start "client_relation"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:614:1: client_relation returns [ClientRelation relation] : c= client 'client' ( client_entities )? ( type_mark | ) s= supplier ( semantic_label )? ;
    public final ClientRelation client_relation() throws RecognitionException {
        ClientRelation relation = null;

        BONParser.client_return c = null;

        BONParser.supplier_return s = null;

        ClientEntityExpression client_entities69 = null;

        BONParser.type_mark_return type_mark70 = null;

        BONParser.semantic_label_return semantic_label71 = null;


         ClientEntityExpression entities = null; TypeMark mark = null; String semanticLabel = null; Token end = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:616:1: (c= client 'client' ( client_entities )? ( type_mark | ) s= supplier ( semantic_label )? )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:617:3: c= client 'client' ( client_entities )? ( type_mark | ) s= supplier ( semantic_label )?
            {
            pushFollow(FOLLOW_client_in_client_relation3918);
            c=client();

            state._fsp--;
            if (state.failed) return relation;
            match(input,64,FOLLOW_64_in_client_relation3920); if (state.failed) return relation;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:618:3: ( client_entities )?
            int alt78=2;
            int LA78_0 = input.LA(1);

            if ( (LA78_0==62) ) {
                alt78=1;
            }
            switch (alt78) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:618:4: client_entities
                    {
                    pushFollow(FOLLOW_client_entities_in_client_relation3925);
                    client_entities69=client_entities();

                    state._fsp--;
                    if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       if(isOk()) entities = client_entities69; 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:619:3: ( type_mark | )
            int alt79=2;
            int LA79_0 = input.LA(1);

            if ( (LA79_0==34||LA79_0==69) ) {
                alt79=1;
            }
            else if ( (LA79_0==IDENTIFIER) ) {
                alt79=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return relation;}
                NoViableAltException nvae =
                    new NoViableAltException("", 79, 0, input);

                throw nvae;
            }
            switch (alt79) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:619:5: type_mark
                    {
                    pushFollow(FOLLOW_type_mark_in_client_relation3937);
                    type_mark70=type_mark();

                    state._fsp--;
                    if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       if(isOk()) mark = (type_mark70!=null?type_mark70.mark:null); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:622:4: 
                    {
                    if ( state.backtracking==0 ) {
                       mark = Constants.NO_TYPE_MARK; 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_supplier_in_client_relation3963);
            s=supplier();

            state._fsp--;
            if (state.failed) return relation;
            if ( state.backtracking==0 ) {
               end = (s!=null?((Token)s.stop):null); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:626:3: ( semantic_label )?
            int alt80=2;
            int LA80_0 = input.LA(1);

            if ( (LA80_0==MANIFEST_STRING) ) {
                alt80=1;
            }
            switch (alt80) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:626:4: semantic_label
                    {
                    pushFollow(FOLLOW_semantic_label_in_client_relation3973);
                    semantic_label71=semantic_label();

                    state._fsp--;
                    if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       if(isOk()) semanticLabel = (semantic_label71!=null?semantic_label71.label:null); end = (semantic_label71!=null?((Token)semantic_label71.stop):null); 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               if(isOk()) relation = ClientRelation.mk((c!=null?c.ref:null),(s!=null?s.ref:null),entities,mark,semanticLabel,getSLoc((c!=null?((Token)c.start):null),end)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return relation;
    }
    // $ANTLR end "client_relation"


    // $ANTLR start "client_entities"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:630:1: client_entities returns [ClientEntityExpression entities] : '{' cee= client_entity_expression '}' ;
    public final ClientEntityExpression client_entities() throws RecognitionException {
        ClientEntityExpression entities = null;

        ClientEntityExpression cee = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:630:59: ( '{' cee= client_entity_expression '}' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:631:3: '{' cee= client_entity_expression '}'
            {
            match(input,62,FOLLOW_62_in_client_entities4014); if (state.failed) return entities;
            pushFollow(FOLLOW_client_entity_expression_in_client_entities4018);
            cee=client_entity_expression();

            state._fsp--;
            if (state.failed) return entities;
            match(input,63,FOLLOW_63_in_client_entities4020); if (state.failed) return entities;
            if ( state.backtracking==0 ) {
               if(isOk()) entities = cee; 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return entities;
    }
    // $ANTLR end "client_entities"


    // $ANTLR start "client_entity_expression"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:635:1: client_entity_expression returns [ClientEntityExpression entities] : (cel= client_entity_list | m= multiplicity );
    public final ClientEntityExpression client_entity_expression() throws RecognitionException {
        ClientEntityExpression entities = null;

        BONParser.client_entity_list_return cel = null;

        BONParser.multiplicity_return m = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:635:68: (cel= client_entity_list | m= multiplicity )
            int alt81=2;
            int LA81_0 = input.LA(1);

            if ( (LA81_0==IDENTIFIER||LA81_0==42||(LA81_0>=65 && LA81_0<=66)||LA81_0==68||LA81_0==79||LA81_0==81) ) {
                alt81=1;
            }
            else if ( (LA81_0==INTEGER) ) {
                alt81=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return entities;}
                NoViableAltException nvae =
                    new NoViableAltException("", 81, 0, input);

                throw nvae;
            }
            switch (alt81) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:636:4: cel= client_entity_list
                    {
                    pushFollow(FOLLOW_client_entity_list_in_client_entity_expression4059);
                    cel=client_entity_list();

                    state._fsp--;
                    if (state.failed) return entities;
                    if ( state.backtracking==0 ) {
                       if(isOk()) entities = ClientEntityList.mk((cel!=null?cel.entities:null),getSLoc((cel!=null?((Token)cel.start):null),(cel!=null?((Token)cel.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:638:4: m= multiplicity
                    {
                    pushFollow(FOLLOW_multiplicity_in_client_entity_expression4072);
                    m=multiplicity();

                    state._fsp--;
                    if (state.failed) return entities;
                    if ( state.backtracking==0 ) {
                       if(isOk()) entities = Multiplicity.mk((m!=null?m.num:null), getSLoc((m!=null?((Token)m.start):null),(m!=null?((Token)m.stop):null))); 
                    }

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
        return entities;
    }
    // $ANTLR end "client_entity_expression"

    public static class client_entity_list_return extends ParserRuleReturnScope {
        public List<ClientEntity> entities;
    };

    // $ANTLR start "client_entity_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:642:1: client_entity_list returns [List<ClientEntity> entities] : ce= client_entity ( ',' c= client_entity )* ;
    public final BONParser.client_entity_list_return client_entity_list() throws RecognitionException {
        BONParser.client_entity_list_return retval = new BONParser.client_entity_list_return();
        retval.start = input.LT(1);

        ClientEntity ce = null;

        ClientEntity c = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:642:58: (ce= client_entity ( ',' c= client_entity )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:643:3: ce= client_entity ( ',' c= client_entity )*
            {
            if ( state.backtracking==0 ) {
               retval.entities = createList(); 
            }
            pushFollow(FOLLOW_client_entity_in_client_entity_list4125);
            ce=client_entity();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.entities.add(ce); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:646:3: ( ',' c= client_entity )*
            loop82:
            do {
                int alt82=2;
                int LA82_0 = input.LA(1);

                if ( (LA82_0==35) ) {
                    alt82=1;
                }


                switch (alt82) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:646:4: ',' c= client_entity
            	    {
            	    match(input,35,FOLLOW_35_in_client_entity_list4134); if (state.failed) return retval;
            	    pushFollow(FOLLOW_client_entity_in_client_entity_list4138);
            	    c=client_entity();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.entities.add(c); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop82;
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
    // $ANTLR end "client_entity_list"


    // $ANTLR start "client_entity"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:655:1: client_entity returns [ClientEntity entity] : ( prefix | infix | supplier_indirection | parent_indirection );
    public final ClientEntity client_entity() throws RecognitionException {
        ClientEntity entity = null;

        SupplierIndirection supplier_indirection72 = null;

        ParentIndirection parent_indirection73 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:655:45: ( prefix | infix | supplier_indirection | parent_indirection )
            int alt83=4;
            alt83 = dfa83.predict(input);
            switch (alt83) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:656:4: prefix
                    {
                    pushFollow(FOLLOW_prefix_in_client_entity4189);
                    prefix();

                    state._fsp--;
                    if (state.failed) return entity;

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:657:4: infix
                    {
                    pushFollow(FOLLOW_infix_in_client_entity4194);
                    infix();

                    state._fsp--;
                    if (state.failed) return entity;

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:658:4: supplier_indirection
                    {
                    pushFollow(FOLLOW_supplier_indirection_in_client_entity4199);
                    supplier_indirection72=supplier_indirection();

                    state._fsp--;
                    if (state.failed) return entity;
                    if ( state.backtracking==0 ) {
                       if(isOk()) entity = supplier_indirection72; 
                    }

                    }
                    break;
                case 4 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:660:4: parent_indirection
                    {
                    pushFollow(FOLLOW_parent_indirection_in_client_entity4210);
                    parent_indirection73=parent_indirection();

                    state._fsp--;
                    if (state.failed) return entity;
                    if ( state.backtracking==0 ) {
                       if(isOk()) entity = parent_indirection73; 
                    }

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
        return entity;
    }
    // $ANTLR end "client_entity"


    // $ANTLR start "supplier_indirection"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:664:1: supplier_indirection returns [SupplierIndirection indirection] : (ifp= indirection_feature_part ':' )? gi= generic_indirection ;
    public final SupplierIndirection supplier_indirection() throws RecognitionException {
        SupplierIndirection indirection = null;

        BONParser.indirection_feature_part_return ifp = null;

        BONParser.generic_indirection_return gi = null;


        IndirectionFeaturePart part = null; Token start = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:666:1: ( (ifp= indirection_feature_part ':' )? gi= generic_indirection )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:667:3: (ifp= indirection_feature_part ':' )? gi= generic_indirection
            {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:667:3: (ifp= indirection_feature_part ':' )?
            int alt84=2;
            int LA84_0 = input.LA(1);

            if ( (LA84_0==IDENTIFIER) ) {
                int LA84_1 = input.LA(2);

                if ( (LA84_1==34) ) {
                    alt84=1;
                }
            }
            else if ( (LA84_0==42||LA84_0==79||LA84_0==81) ) {
                alt84=1;
            }
            switch (alt84) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:667:4: ifp= indirection_feature_part ':'
                    {
                    pushFollow(FOLLOW_indirection_feature_part_in_supplier_indirection4256);
                    ifp=indirection_feature_part();

                    state._fsp--;
                    if (state.failed) return indirection;
                    if ( state.backtracking==0 ) {
                       start = (ifp!=null?((Token)ifp.start):null); 
                    }
                    match(input,34,FOLLOW_34_in_supplier_indirection4260); if (state.failed) return indirection;

                    }
                    break;

            }

            pushFollow(FOLLOW_generic_indirection_in_supplier_indirection4269);
            gi=generic_indirection();

            state._fsp--;
            if (state.failed) return indirection;
            if ( state.backtracking==0 ) {
               if (start==null) start=(gi!=null?((Token)gi.start):null); 
            }
            if ( state.backtracking==0 ) {
               if(isOk()) indirection = SupplierIndirection.mk(part, (gi!=null?gi.indirection:null),getSLoc(start,(gi!=null?((Token)gi.stop):null))); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return indirection;
    }
    // $ANTLR end "supplier_indirection"

    public static class indirection_feature_part_return extends ParserRuleReturnScope {
        public IndirectionFeaturePart part;
    };

    // $ANTLR start "indirection_feature_part"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:673:1: indirection_feature_part returns [IndirectionFeaturePart part] : ( feature_name | indirection_feature_list );
    public final BONParser.indirection_feature_part_return indirection_feature_part() throws RecognitionException {
        BONParser.indirection_feature_part_return retval = new BONParser.indirection_feature_part_return();
        retval.start = input.LT(1);

        BONParser.feature_name_return feature_name74 = null;

        IndirectionFeatureList indirection_feature_list75 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:673:64: ( feature_name | indirection_feature_list )
            int alt85=2;
            int LA85_0 = input.LA(1);

            if ( (LA85_0==IDENTIFIER||LA85_0==79||LA85_0==81) ) {
                alt85=1;
            }
            else if ( (LA85_0==42) ) {
                alt85=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 85, 0, input);

                throw nvae;
            }
            switch (alt85) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:674:4: feature_name
                    {
                    pushFollow(FOLLOW_feature_name_in_indirection_feature_part4318);
                    feature_name74=feature_name();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.part = (feature_name74!=null?feature_name74.name:null); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:676:4: indirection_feature_list
                    {
                    pushFollow(FOLLOW_indirection_feature_list_in_indirection_feature_part4329);
                    indirection_feature_list75=indirection_feature_list();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.part = indirection_feature_list75; 
                    }

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
    // $ANTLR end "indirection_feature_part"


    // $ANTLR start "indirection_feature_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:680:1: indirection_feature_list returns [IndirectionFeatureList list] : s= '(' fnl= feature_name_list e= ')' ;
    public final IndirectionFeatureList indirection_feature_list() throws RecognitionException {
        IndirectionFeatureList list = null;

        Token s=null;
        Token e=null;
        BONParser.feature_name_list_return fnl = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:680:64: (s= '(' fnl= feature_name_list e= ')' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:681:3: s= '(' fnl= feature_name_list e= ')'
            {
            s=(Token)match(input,42,FOLLOW_42_in_indirection_feature_list4379); if (state.failed) return list;
            pushFollow(FOLLOW_feature_name_list_in_indirection_feature_list4383);
            fnl=feature_name_list();

            state._fsp--;
            if (state.failed) return list;
            e=(Token)match(input,43,FOLLOW_43_in_indirection_feature_list4387); if (state.failed) return list;
            if ( state.backtracking==0 ) {
               if(isOk()) list = IndirectionFeatureList.mk((fnl!=null?fnl.list:null),getSLoc(s,e)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return list;
    }
    // $ANTLR end "indirection_feature_list"


    // $ANTLR start "parent_indirection"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:685:1: parent_indirection returns [ParentIndirection indirection] : '->' gi= generic_indirection ;
    public final ParentIndirection parent_indirection() throws RecognitionException {
        ParentIndirection indirection = null;

        BONParser.generic_indirection_return gi = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:685:60: ( '->' gi= generic_indirection )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:686:3: '->' gi= generic_indirection
            {
            match(input,65,FOLLOW_65_in_parent_indirection4435); if (state.failed) return indirection;
            pushFollow(FOLLOW_generic_indirection_in_parent_indirection4439);
            gi=generic_indirection();

            state._fsp--;
            if (state.failed) return indirection;
            if ( state.backtracking==0 ) {
               if(isOk()) indirection = ParentIndirection.mk((gi!=null?gi.indirection:null),getSLoc((gi!=null?((Token)gi.start):null),(gi!=null?((Token)gi.stop):null))); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return indirection;
    }
    // $ANTLR end "parent_indirection"

    public static class generic_indirection_return extends ParserRuleReturnScope {
        public GenericIndirection indirection;
    };

    // $ANTLR start "generic_indirection"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:690:1: generic_indirection returns [GenericIndirection indirection] : ie= indirection_element ;
    public final BONParser.generic_indirection_return generic_indirection() throws RecognitionException {
        BONParser.generic_indirection_return retval = new BONParser.generic_indirection_return();
        retval.start = input.LT(1);

        BONParser.indirection_element_return ie = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:692:62: (ie= indirection_element )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:696:5: ie= indirection_element
            {
            pushFollow(FOLLOW_indirection_element_in_generic_indirection4491);
            ie=indirection_element();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.indirection = GenericIndirection.mk((ie!=null?ie.el:null),getSLoc((ie!=null?((Token)ie.start):null),(ie!=null?((Token)ie.stop):null))); 
            }

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
    // $ANTLR end "generic_indirection"


    // $ANTLR start "named_indirection"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:700:1: named_indirection returns [NamedIndirection indirection] : (cn= class_name '[' il= indirection_list e= ']' | s= '[' indirection_list ']' );
    public final NamedIndirection named_indirection() throws RecognitionException {
        NamedIndirection indirection = null;

        Token e=null;
        Token s=null;
        BONParser.class_name_return cn = null;

        List<IndirectionElement> il = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:700:58: (cn= class_name '[' il= indirection_list e= ']' | s= '[' indirection_list ']' )
            int alt86=2;
            int LA86_0 = input.LA(1);

            if ( (LA86_0==IDENTIFIER) ) {
                alt86=1;
            }
            else if ( (LA86_0==66) ) {
                alt86=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return indirection;}
                NoViableAltException nvae =
                    new NoViableAltException("", 86, 0, input);

                throw nvae;
            }
            switch (alt86) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:701:4: cn= class_name '[' il= indirection_list e= ']'
                    {
                    pushFollow(FOLLOW_class_name_in_named_indirection4536);
                    cn=class_name();

                    state._fsp--;
                    if (state.failed) return indirection;
                    match(input,66,FOLLOW_66_in_named_indirection4538); if (state.failed) return indirection;
                    pushFollow(FOLLOW_indirection_list_in_named_indirection4542);
                    il=indirection_list();

                    state._fsp--;
                    if (state.failed) return indirection;
                    e=(Token)match(input,67,FOLLOW_67_in_named_indirection4546); if (state.failed) return indirection;
                    if ( state.backtracking==0 ) {
                       if(isOk()) indirection = NamedIndirection.mk((cn!=null?cn.name:null), il, getSLoc((cn!=null?((Token)cn.start):null),e)); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:704:4: s= '[' indirection_list ']'
                    {
                    s=(Token)match(input,66,FOLLOW_66_in_named_indirection4561); if (state.failed) return indirection;
                    pushFollow(FOLLOW_indirection_list_in_named_indirection4563);
                    indirection_list();

                    state._fsp--;
                    if (state.failed) return indirection;
                    match(input,67,FOLLOW_67_in_named_indirection4565); if (state.failed) return indirection;
                    if ( state.backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSLoc(s), "class name", "before indirection list", true)); 
                    }

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
        return indirection;
    }
    // $ANTLR end "named_indirection"


    // $ANTLR start "indirection_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:708:1: indirection_list returns [List<IndirectionElement> list] : i1= indirection_element ( ',' i= indirection_element )* ;
    public final List<IndirectionElement> indirection_list() throws RecognitionException {
        List<IndirectionElement> list = null;

        BONParser.indirection_element_return i1 = null;

        BONParser.indirection_element_return i = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:708:58: (i1= indirection_element ( ',' i= indirection_element )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:709:3: i1= indirection_element ( ',' i= indirection_element )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_indirection_element_in_indirection_list4612);
            i1=indirection_element();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               if(isOk()) list.add((i1!=null?i1.el:null)); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:712:3: ( ',' i= indirection_element )*
            loop87:
            do {
                int alt87=2;
                int LA87_0 = input.LA(1);

                if ( (LA87_0==35) ) {
                    alt87=1;
                }


                switch (alt87) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:712:4: ',' i= indirection_element
            	    {
            	    match(input,35,FOLLOW_35_in_indirection_list4622); if (state.failed) return list;
            	    pushFollow(FOLLOW_indirection_element_in_indirection_list4626);
            	    i=indirection_element();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) list.add((i!=null?i.el:null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop87;
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
        return list;
    }
    // $ANTLR end "indirection_list"

    public static class indirection_element_return extends ParserRuleReturnScope {
        public IndirectionElement el;
    };

    // $ANTLR start "indirection_element"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:717:1: indirection_element returns [IndirectionElement el] : (t= '...' | named_indirection | class_name );
    public final BONParser.indirection_element_return indirection_element() throws RecognitionException {
        BONParser.indirection_element_return retval = new BONParser.indirection_element_return();
        retval.start = input.LT(1);

        Token t=null;
        NamedIndirection named_indirection76 = null;

        BONParser.class_name_return class_name77 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:717:53: (t= '...' | named_indirection | class_name )
            int alt88=3;
            switch ( input.LA(1) ) {
            case 68:
                {
                alt88=1;
                }
                break;
            case IDENTIFIER:
                {
                int LA88_2 = input.LA(2);

                if ( (LA88_2==35||LA88_2==63||LA88_2==67) ) {
                    alt88=3;
                }
                else if ( (LA88_2==66) ) {
                    alt88=2;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 88, 2, input);

                    throw nvae;
                }
                }
                break;
            case 66:
                {
                alt88=2;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 88, 0, input);

                throw nvae;
            }

            switch (alt88) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:718:4: t= '...'
                    {
                    t=(Token)match(input,68,FOLLOW_68_in_indirection_element4680); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.el = CompactedIndirectionElementImpl.mk(getSLoc(t)); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:720:4: named_indirection
                    {
                    pushFollow(FOLLOW_named_indirection_in_indirection_element4690);
                    named_indirection76=named_indirection();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.el = named_indirection76; 
                    }

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:722:4: class_name
                    {
                    pushFollow(FOLLOW_class_name_in_indirection_element4701);
                    class_name77=class_name();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.el = (class_name77!=null?class_name77.name:null); 
                    }

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
    // $ANTLR end "indirection_element"

    public static class type_mark_return extends ParserRuleReturnScope {
        public TypeMark mark;
    };

    // $ANTLR start "type_mark"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:727:1: type_mark returns [TypeMark mark] : (m= ':' | m= ':{' | sm= shared_mark );
    public final BONParser.type_mark_return type_mark() throws RecognitionException {
        BONParser.type_mark_return retval = new BONParser.type_mark_return();
        retval.start = input.LT(1);

        Token m=null;
        TypeMark sm = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:727:35: (m= ':' | m= ':{' | sm= shared_mark )
            int alt89=3;
            int LA89_0 = input.LA(1);

            if ( (LA89_0==34) ) {
                int LA89_1 = input.LA(2);

                if ( (LA89_1==42) ) {
                    alt89=3;
                }
                else if ( (LA89_1==IDENTIFIER||LA89_1==74) ) {
                    alt89=1;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 89, 1, input);

                    throw nvae;
                }
            }
            else if ( (LA89_0==69) ) {
                alt89=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 89, 0, input);

                throw nvae;
            }
            switch (alt89) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:728:4: m= ':'
                    {
                    m=(Token)match(input,34,FOLLOW_34_in_type_mark4746); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.mark = TypeMark.mk(TypeMark.Mark.HASTYPE, null, getSLoc(m)); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:730:4: m= ':{'
                    {
                    m=(Token)match(input,69,FOLLOW_69_in_type_mark4759); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.mark = TypeMark.mk(TypeMark.Mark.AGGREGATE, null, getSLoc(m)); 
                    }

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:732:4: sm= shared_mark
                    {
                    pushFollow(FOLLOW_shared_mark_in_type_mark4772);
                    sm=shared_mark();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.mark = sm; 
                    }

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
    // $ANTLR end "type_mark"


    // $ANTLR start "shared_mark"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:736:1: shared_mark returns [TypeMark mark] : a= ':' '(' m= multiplicity b= ')' ;
    public final TypeMark shared_mark() throws RecognitionException {
        TypeMark mark = null;

        Token a=null;
        Token b=null;
        BONParser.multiplicity_return m = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:736:37: (a= ':' '(' m= multiplicity b= ')' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:737:3: a= ':' '(' m= multiplicity b= ')'
            {
            a=(Token)match(input,34,FOLLOW_34_in_shared_mark4818); if (state.failed) return mark;
            match(input,42,FOLLOW_42_in_shared_mark4820); if (state.failed) return mark;
            pushFollow(FOLLOW_multiplicity_in_shared_mark4824);
            m=multiplicity();

            state._fsp--;
            if (state.failed) return mark;
            b=(Token)match(input,43,FOLLOW_43_in_shared_mark4828); if (state.failed) return mark;
            if ( state.backtracking==0 ) {
               if(isOk()) mark = TypeMark.mk(TypeMark.Mark.SHAREDMARK, m.num, getSLoc(a, b)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return mark;
    }
    // $ANTLR end "shared_mark"

    public static class child_return extends ParserRuleReturnScope {
        public StaticRef ref;
    };

    // $ANTLR start "child"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:741:1: child returns [StaticRef ref] : s= static_ref ;
    public final BONParser.child_return child() throws RecognitionException {
        BONParser.child_return retval = new BONParser.child_return();
        retval.start = input.LT(1);

        StaticRef s = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:743:31: (s= static_ref )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:744:3: s= static_ref
            {
            pushFollow(FOLLOW_static_ref_in_child4852);
            s=static_ref();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.ref = s; 
            }

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
    // $ANTLR end "child"

    public static class parent_return extends ParserRuleReturnScope {
        public StaticRef ref;
    };

    // $ANTLR start "parent"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:748:1: parent returns [StaticRef ref] : s= static_ref ;
    public final BONParser.parent_return parent() throws RecognitionException {
        BONParser.parent_return retval = new BONParser.parent_return();
        retval.start = input.LT(1);

        StaticRef s = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:748:32: (s= static_ref )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:749:3: s= static_ref
            {
            pushFollow(FOLLOW_static_ref_in_parent4880);
            s=static_ref();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.ref = s; 
            }

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
    // $ANTLR end "parent"

    public static class client_return extends ParserRuleReturnScope {
        public StaticRef ref;
    };

    // $ANTLR start "client"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:753:1: client returns [StaticRef ref] : s= static_ref ;
    public final BONParser.client_return client() throws RecognitionException {
        BONParser.client_return retval = new BONParser.client_return();
        retval.start = input.LT(1);

        StaticRef s = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:753:32: (s= static_ref )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:754:3: s= static_ref
            {
            pushFollow(FOLLOW_static_ref_in_client4918);
            s=static_ref();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.ref = s; 
            }

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
    // $ANTLR end "client"

    public static class supplier_return extends ParserRuleReturnScope {
        public StaticRef ref;
    };

    // $ANTLR start "supplier"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:758:1: supplier returns [StaticRef ref] : s= static_ref ;
    public final BONParser.supplier_return supplier() throws RecognitionException {
        BONParser.supplier_return retval = new BONParser.supplier_return();
        retval.start = input.LT(1);

        StaticRef s = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:758:34: (s= static_ref )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:759:3: s= static_ref
            {
            pushFollow(FOLLOW_static_ref_in_supplier4948);
            s=static_ref();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.ref = s; 
            }

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
    // $ANTLR end "supplier"


    // $ANTLR start "static_ref"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:763:1: static_ref returns [StaticRef ref] : (s= static_component_name | cp= cluster_prefix s= static_component_name );
    public final StaticRef static_ref() throws RecognitionException {
        StaticRef ref = null;

        BONParser.static_component_name_return s = null;

        BONParser.cluster_prefix_return cp = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:763:36: (s= static_component_name | cp= cluster_prefix s= static_component_name )
            int alt90=2;
            int LA90_0 = input.LA(1);

            if ( (LA90_0==IDENTIFIER) ) {
                int LA90_1 = input.LA(2);

                if ( (LA90_1==70) ) {
                    alt90=2;
                }
                else if ( ((LA90_1>=MANIFEST_STRING && LA90_1<=IDENTIFIER)||(LA90_1>=25 && LA90_1<=27)||LA90_1==38||(LA90_1>=57 && LA90_1<=59)||LA90_1==64) ) {
                    alt90=1;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return ref;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 90, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return ref;}
                NoViableAltException nvae =
                    new NoViableAltException("", 90, 0, input);

                throw nvae;
            }
            switch (alt90) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:764:4: s= static_component_name
                    {
                    pushFollow(FOLLOW_static_component_name_in_static_ref4982);
                    s=static_component_name();

                    state._fsp--;
                    if (state.failed) return ref;
                    if ( state.backtracking==0 ) {
                       List<StaticRefPart> empty = emptyList(); if(isOk()) ref = StaticRef.mk(empty, (s!=null?s.ref:null), getSLoc((s!=null?((Token)s.start):null),(s!=null?((Token)s.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:767:4: cp= cluster_prefix s= static_component_name
                    {
                    pushFollow(FOLLOW_cluster_prefix_in_static_ref4998);
                    cp=cluster_prefix();

                    state._fsp--;
                    if (state.failed) return ref;
                    pushFollow(FOLLOW_static_component_name_in_static_ref5002);
                    s=static_component_name();

                    state._fsp--;
                    if (state.failed) return ref;
                    if ( state.backtracking==0 ) {
                       if(isOk()) ref = StaticRef.mk((cp!=null?cp.prefix:null), (s!=null?s.ref:null), getSLoc((cp!=null?((Token)cp.start):null),(s!=null?((Token)s.stop):null))); 
                    }

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
        return ref;
    }
    // $ANTLR end "static_ref"

    public static class cluster_prefix_return extends ParserRuleReturnScope {
        public List<StaticRefPart> prefix;
    };

    // $ANTLR start "cluster_prefix"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:771:1: cluster_prefix returns [List<StaticRefPart> prefix] : c1= cluster_name '.' (c= cluster_name '.' )* ;
    public final BONParser.cluster_prefix_return cluster_prefix() throws RecognitionException {
        BONParser.cluster_prefix_return retval = new BONParser.cluster_prefix_return();
        retval.start = input.LT(1);

        BONParser.cluster_name_return c1 = null;

        BONParser.cluster_name_return c = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:771:53: (c1= cluster_name '.' (c= cluster_name '.' )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:772:3: c1= cluster_name '.' (c= cluster_name '.' )*
            {
            if ( state.backtracking==0 ) {
               retval.prefix = createList(); 
            }
            pushFollow(FOLLOW_cluster_name_in_cluster_prefix5041);
            c1=cluster_name();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.prefix.add(StaticRefPart.mk((c1!=null?c1.name:null), getSLoc((c1!=null?((Token)c1.start):null),(c1!=null?((Token)c1.stop):null)))); 
            }
            match(input,70,FOLLOW_70_in_cluster_prefix5050); if (state.failed) return retval;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:776:3: (c= cluster_name '.' )*
            loop91:
            do {
                int alt91=2;
                int LA91_0 = input.LA(1);

                if ( (LA91_0==IDENTIFIER) ) {
                    int LA91_1 = input.LA(2);

                    if ( (LA91_1==70) ) {
                        alt91=1;
                    }


                }


                switch (alt91) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:776:5: c= cluster_name '.'
            	    {
            	    pushFollow(FOLLOW_cluster_name_in_cluster_prefix5059);
            	    c=cluster_name();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    match(input,70,FOLLOW_70_in_cluster_prefix5061); if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.prefix.add(StaticRefPart.mk((c!=null?c.name:null), getSLoc((c!=null?((Token)c.start):null),(c!=null?((Token)c.stop):null)))); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop91;
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
    // $ANTLR end "cluster_prefix"

    public static class static_component_name_return extends ParserRuleReturnScope {
        public StaticRefPart ref;
    };

    // $ANTLR start "static_component_name"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:783:1: static_component_name returns [StaticRefPart ref] : i= IDENTIFIER ;
    public final BONParser.static_component_name_return static_component_name() throws RecognitionException {
        BONParser.static_component_name_return retval = new BONParser.static_component_name_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:783:51: (i= IDENTIFIER )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:784:3: i= IDENTIFIER
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_static_component_name5093); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.ref = StaticRefPart.mk((i!=null?i.getText():null), getSLoc(i)); 
            }

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
    // $ANTLR end "static_component_name"

    public static class multiplicity_return extends ParserRuleReturnScope {
        public Integer num;
    };

    // $ANTLR start "multiplicity"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:788:1: multiplicity returns [Integer num] : i= INTEGER ;
    public final BONParser.multiplicity_return multiplicity() throws RecognitionException {
        BONParser.multiplicity_return retval = new BONParser.multiplicity_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:788:36: (i= INTEGER )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:789:3: i= INTEGER
            {
            i=(Token)match(input,INTEGER,FOLLOW_INTEGER_in_multiplicity5137); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.num = new Integer((i!=null?i.getText():null)); 
            }

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
    // $ANTLR end "multiplicity"

    public static class semantic_label_return extends ParserRuleReturnScope {
        public String label;
    };

    // $ANTLR start "semantic_label"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:793:1: semantic_label returns [String label] : m= MANIFEST_STRING ;
    public final BONParser.semantic_label_return semantic_label() throws RecognitionException {
        BONParser.semantic_label_return retval = new BONParser.semantic_label_return();
        retval.start = input.LT(1);

        Token m=null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:793:39: (m= MANIFEST_STRING )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:794:3: m= MANIFEST_STRING
            {
            m=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_semantic_label5173); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.label = (m!=null?m.getText():null); 
            }

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
    // $ANTLR end "semantic_label"

    public static class class_interface_return extends ParserRuleReturnScope {
        public ClassInterface ci;
    };

    // $ANTLR start "class_interface"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:798:1: class_interface returns [ClassInterface ci] : (cisi= class_interface_start_indexing | cisp= class_interface_start_inherit | cisf= class_interface_start_features | cisv= class_interface_start_invariant );
    public final BONParser.class_interface_return class_interface() throws RecognitionException {
        BONParser.class_interface_return retval = new BONParser.class_interface_return();
        retval.start = input.LT(1);

        ClassInterface cisi = null;

        ClassInterface cisp = null;

        ClassInterface cisf = null;

        ClassInterface cisv = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:802:45: (cisi= class_interface_start_indexing | cisp= class_interface_start_inherit | cisf= class_interface_start_features | cisv= class_interface_start_invariant )
            int alt92=4;
            switch ( input.LA(1) ) {
            case 30:
                {
                alt92=1;
                }
                break;
            case 38:
                {
                alt92=2;
                }
                break;
            case 72:
                {
                alt92=3;
                }
                break;
            case 71:
                {
                alt92=4;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 92, 0, input);

                throw nvae;
            }

            switch (alt92) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:803:5: cisi= class_interface_start_indexing
                    {
                    pushFollow(FOLLOW_class_interface_start_indexing_in_class_interface5199);
                    cisi=class_interface_start_indexing();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                      if(isOk()) retval.ci =cisi;
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:804:5: cisp= class_interface_start_inherit
                    {
                    pushFollow(FOLLOW_class_interface_start_inherit_in_class_interface5209);
                    cisp=class_interface_start_inherit();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                      if(isOk()) retval.ci =cisp;
                    }

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:805:5: cisf= class_interface_start_features
                    {
                    pushFollow(FOLLOW_class_interface_start_features_in_class_interface5219);
                    cisf=class_interface_start_features();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                      if(isOk()) retval.ci =cisf;
                    }

                    }
                    break;
                case 4 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:806:5: cisv= class_interface_start_invariant
                    {
                    pushFollow(FOLLOW_class_interface_start_invariant_in_class_interface5229);
                    cisv=class_interface_start_invariant();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                      if(isOk()) retval.ci =cisv;
                    }

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
    // $ANTLR end "class_interface"


    // $ANTLR start "class_interface_start_indexing"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:809:1: class_interface_start_indexing returns [ClassInterface ci] : indexing (pcl= parent_class_list )? ( features )? (inv= class_invariant )? e= 'end' ;
    public final ClassInterface class_interface_start_indexing() throws RecognitionException {
        ClassInterface ci = null;

        Token e=null;
        BONParser.parent_class_list_return pcl = null;

        BONParser.class_invariant_return inv = null;

        BONParser.indexing_return indexing78 = null;

        BONParser.features_return features79 = null;


         Indexing indexing = null; List<Type> parents = emptyList(); 
                List<Expression> invariant = emptyList(); Token start = null; 
                List<Feature> features = emptyList(); 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:813:1: ( indexing (pcl= parent_class_list )? ( features )? (inv= class_invariant )? e= 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:814:3: indexing (pcl= parent_class_list )? ( features )? (inv= class_invariant )? e= 'end'
            {
            pushFollow(FOLLOW_indexing_in_class_interface_start_indexing5251);
            indexing78=indexing();

            state._fsp--;
            if (state.failed) return ci;
            if ( state.backtracking==0 ) {
               if(isOk()) indexing = (indexing78!=null?indexing78.indexing:null); start = (indexing78!=null?((Token)indexing78.start):null); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:815:3: (pcl= parent_class_list )?
            int alt93=2;
            int LA93_0 = input.LA(1);

            if ( (LA93_0==38) ) {
                alt93=1;
            }
            switch (alt93) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:815:6: pcl= parent_class_list
                    {
                    pushFollow(FOLLOW_parent_class_list_in_class_interface_start_indexing5263);
                    pcl=parent_class_list();

                    state._fsp--;
                    if (state.failed) return ci;
                    if ( state.backtracking==0 ) {
                       if(isOk()) parents = (pcl!=null?pcl.parents:null); if (start == null) start = (pcl!=null?((Token)pcl.start):null); 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:816:3: ( features )?
            int alt94=2;
            int LA94_0 = input.LA(1);

            if ( (LA94_0==72) ) {
                alt94=1;
            }
            switch (alt94) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:816:7: features
                    {
                    pushFollow(FOLLOW_features_in_class_interface_start_indexing5276);
                    features79=features();

                    state._fsp--;
                    if (state.failed) return ci;
                    if ( state.backtracking==0 ) {
                       if(isOk()) features = (features79!=null?features79.features:null); 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:817:3: (inv= class_invariant )?
            int alt95=2;
            int LA95_0 = input.LA(1);

            if ( (LA95_0==71) ) {
                alt95=1;
            }
            switch (alt95) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:817:6: inv= class_invariant
                    {
                    pushFollow(FOLLOW_class_invariant_in_class_interface_start_indexing5290);
                    inv=class_invariant();

                    state._fsp--;
                    if (state.failed) return ci;
                    if ( state.backtracking==0 ) {
                       if(isOk()) invariant = (inv!=null?inv.invariant:null); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_class_interface_start_indexing5301); if (state.failed) return ci;
            if ( state.backtracking==0 ) {
               if(isOk()) ci = ClassInterface.mk(features, parents, invariant, indexing, getSLoc(start, e)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ci;
    }
    // $ANTLR end "class_interface_start_indexing"


    // $ANTLR start "class_interface_start_inherit"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:822:1: class_interface_start_inherit returns [ClassInterface ci] : pcl= parent_class_list ( features )? (inv= class_invariant )? e= 'end' ;
    public final ClassInterface class_interface_start_inherit() throws RecognitionException {
        ClassInterface ci = null;

        Token e=null;
        BONParser.parent_class_list_return pcl = null;

        BONParser.class_invariant_return inv = null;

        BONParser.features_return features80 = null;


         Indexing indexing = null; List<Type> parents = emptyList(); 
                List<Expression> invariant = emptyList(); Token start = null; 
                List<Feature> features = emptyList(); 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:826:1: (pcl= parent_class_list ( features )? (inv= class_invariant )? e= 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:827:3: pcl= parent_class_list ( features )? (inv= class_invariant )? e= 'end'
            {
            pushFollow(FOLLOW_parent_class_list_in_class_interface_start_inherit5327);
            pcl=parent_class_list();

            state._fsp--;
            if (state.failed) return ci;
            if ( state.backtracking==0 ) {
               start = (pcl!=null?((Token)pcl.start):null); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:828:3: ( features )?
            int alt96=2;
            int LA96_0 = input.LA(1);

            if ( (LA96_0==72) ) {
                alt96=1;
            }
            switch (alt96) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:828:7: features
                    {
                    pushFollow(FOLLOW_features_in_class_interface_start_inherit5337);
                    features80=features();

                    state._fsp--;
                    if (state.failed) return ci;
                    if ( state.backtracking==0 ) {
                       if(isOk()) features = (features80!=null?features80.features:null); 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:829:3: (inv= class_invariant )?
            int alt97=2;
            int LA97_0 = input.LA(1);

            if ( (LA97_0==71) ) {
                alt97=1;
            }
            switch (alt97) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:829:6: inv= class_invariant
                    {
                    pushFollow(FOLLOW_class_invariant_in_class_interface_start_inherit5351);
                    inv=class_invariant();

                    state._fsp--;
                    if (state.failed) return ci;
                    if ( state.backtracking==0 ) {
                       if(isOk()) invariant = (inv!=null?inv.invariant:null); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_class_interface_start_inherit5362); if (state.failed) return ci;
            if ( state.backtracking==0 ) {
               if(isOk()) ci = ClassInterface.mk(features, (pcl!=null?pcl.parents:null), invariant, indexing, getSLoc(start, e)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ci;
    }
    // $ANTLR end "class_interface_start_inherit"


    // $ANTLR start "class_interface_start_features"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:834:1: class_interface_start_features returns [ClassInterface ci] : features (inv= class_invariant )? e= 'end' ;
    public final ClassInterface class_interface_start_features() throws RecognitionException {
        ClassInterface ci = null;

        Token e=null;
        BONParser.class_invariant_return inv = null;

        BONParser.features_return features81 = null;


         Indexing indexing = null; List<Type> parents = emptyList(); 
                List<Expression> invariant = emptyList(); Token start = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:837:1: ( features (inv= class_invariant )? e= 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:838:3: features (inv= class_invariant )? e= 'end'
            {
            pushFollow(FOLLOW_features_in_class_interface_start_features5386);
            features81=features();

            state._fsp--;
            if (state.failed) return ci;
            if ( state.backtracking==0 ) {
               start = (features81!=null?((Token)features81.start):null); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:839:3: (inv= class_invariant )?
            int alt98=2;
            int LA98_0 = input.LA(1);

            if ( (LA98_0==71) ) {
                alt98=1;
            }
            switch (alt98) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:839:6: inv= class_invariant
                    {
                    pushFollow(FOLLOW_class_invariant_in_class_interface_start_features5397);
                    inv=class_invariant();

                    state._fsp--;
                    if (state.failed) return ci;
                    if ( state.backtracking==0 ) {
                       if(isOk()) invariant = (inv!=null?inv.invariant:null); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_class_interface_start_features5408); if (state.failed) return ci;
            if ( state.backtracking==0 ) {
               if(isOk()) ci = ClassInterface.mk((features81!=null?features81.features:null), parents, invariant, indexing, getSLoc(start, e)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ci;
    }
    // $ANTLR end "class_interface_start_features"


    // $ANTLR start "class_interface_start_invariant"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:844:1: class_interface_start_invariant returns [ClassInterface ci] : inv= class_invariant e= 'end' ;
    public final ClassInterface class_interface_start_invariant() throws RecognitionException {
        ClassInterface ci = null;

        Token e=null;
        BONParser.class_invariant_return inv = null;


         Indexing indexing = null; List<Type> parents = emptyList(); 
                Token start = null; List<Feature> features = emptyList(); 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:847:1: (inv= class_invariant e= 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:848:3: inv= class_invariant e= 'end'
            {
            pushFollow(FOLLOW_class_invariant_in_class_interface_start_invariant5434);
            inv=class_invariant();

            state._fsp--;
            if (state.failed) return ci;
            if ( state.backtracking==0 ) {
               start = (inv!=null?((Token)inv.start):null); 
            }
            e=(Token)match(input,25,FOLLOW_25_in_class_interface_start_invariant5442); if (state.failed) return ci;
            if ( state.backtracking==0 ) {
               if(isOk()) ci = ClassInterface.mk(features, parents, (inv!=null?inv.invariant:null), indexing, getSLoc(start, e)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ci;
    }
    // $ANTLR end "class_interface_start_invariant"

    public static class class_invariant_return extends ParserRuleReturnScope {
        public List<Expression> invariant;
    };

    // $ANTLR start "class_invariant"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:853:1: class_invariant returns [List<Expression> invariant] : 'invariant' assertion ;
    public final BONParser.class_invariant_return class_invariant() throws RecognitionException {
        BONParser.class_invariant_return retval = new BONParser.class_invariant_return();
        retval.start = input.LT(1);

        List<Expression> assertion82 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:853:54: ( 'invariant' assertion )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:854:3: 'invariant' assertion
            {
            match(input,71,FOLLOW_71_in_class_invariant5461); if (state.failed) return retval;
            pushFollow(FOLLOW_assertion_in_class_invariant5463);
            assertion82=assertion();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.invariant = assertion82; 
            }

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
    // $ANTLR end "class_invariant"

    public static class parent_class_list_return extends ParserRuleReturnScope {
        public List<Type> parents;
    };

    // $ANTLR start "parent_class_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:858:1: parent_class_list returns [List<Type> parents] : ( 'inherit' c1= class_type ( ';' c= class_type )* ( ';' )? | i= 'inherit' );
    public final BONParser.parent_class_list_return parent_class_list() throws RecognitionException {
        BONParser.parent_class_list_return retval = new BONParser.parent_class_list_return();
        retval.start = input.LT(1);

        Token i=null;
        BONParser.class_type_return c1 = null;

        BONParser.class_type_return c = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:858:48: ( 'inherit' c1= class_type ( ';' c= class_type )* ( ';' )? | i= 'inherit' )
            int alt101=2;
            int LA101_0 = input.LA(1);

            if ( (LA101_0==38) ) {
                int LA101_1 = input.LA(2);

                if ( (LA101_1==25||(LA101_1>=71 && LA101_1<=72)) ) {
                    alt101=2;
                }
                else if ( (LA101_1==IDENTIFIER) ) {
                    alt101=1;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 101, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 101, 0, input);

                throw nvae;
            }
            switch (alt101) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:859:3: 'inherit' c1= class_type ( ';' c= class_type )* ( ';' )?
                    {
                    if ( state.backtracking==0 ) {
                       retval.parents = createList(); 
                    }
                    match(input,38,FOLLOW_38_in_parent_class_list5504); if (state.failed) return retval;
                    pushFollow(FOLLOW_class_type_in_parent_class_list5508);
                    c1=class_type();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.parents.add((c1!=null?c1.type:null)); 
                    }
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:862:3: ( ';' c= class_type )*
                    loop99:
                    do {
                        int alt99=2;
                        int LA99_0 = input.LA(1);

                        if ( (LA99_0==33) ) {
                            int LA99_1 = input.LA(2);

                            if ( (LA99_1==IDENTIFIER) ) {
                                alt99=1;
                            }


                        }


                        switch (alt99) {
                    	case 1 :
                    	    // /home/fintan/workspaces/bon/bonc/src/BON.g:862:4: ';' c= class_type
                    	    {
                    	    match(input,33,FOLLOW_33_in_parent_class_list5519); if (state.failed) return retval;
                    	    pushFollow(FOLLOW_class_type_in_parent_class_list5523);
                    	    c=class_type();

                    	    state._fsp--;
                    	    if (state.failed) return retval;
                    	    if ( state.backtracking==0 ) {
                    	       if(isOk()) retval.parents.add((c!=null?c.type:null)); 
                    	    }

                    	    }
                    	    break;

                    	default :
                    	    break loop99;
                        }
                    } while (true);

                    // /home/fintan/workspaces/bon/bonc/src/BON.g:865:3: ( ';' )?
                    int alt100=2;
                    int LA100_0 = input.LA(1);

                    if ( (LA100_0==33) ) {
                        alt100=1;
                    }
                    switch (alt100) {
                        case 1 :
                            // /home/fintan/workspaces/bon/bonc/src/BON.g:865:3: ';'
                            {
                            match(input,33,FOLLOW_33_in_parent_class_list5540); if (state.failed) return retval;

                            }
                            break;

                    }


                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:867:3: i= 'inherit'
                    {
                    i=(Token)match(input,38,FOLLOW_38_in_parent_class_list5551); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(i), "class name(s)", "in inherits clause", true)); 
                    }

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
    // $ANTLR end "parent_class_list"

    public static class features_return extends ParserRuleReturnScope {
        public List<Feature> features;
    };

    // $ANTLR start "features"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:871:1: features returns [List<Feature> features] : ( feature_clause )+ ;
    public final BONParser.features_return features() throws RecognitionException {
        BONParser.features_return retval = new BONParser.features_return();
        retval.start = input.LT(1);

        Feature feature_clause83 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:871:43: ( ( feature_clause )+ )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:872:3: ( feature_clause )+
            {
            if ( state.backtracking==0 ) {
               retval.features = createList(); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:873:3: ( feature_clause )+
            int cnt102=0;
            loop102:
            do {
                int alt102=2;
                int LA102_0 = input.LA(1);

                if ( (LA102_0==72) ) {
                    alt102=1;
                }


                switch (alt102) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:873:4: feature_clause
            	    {
            	    pushFollow(FOLLOW_feature_clause_in_features5595);
            	    feature_clause83=feature_clause();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.features.add(feature_clause83); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt102 >= 1 ) break loop102;
            	    if (state.backtracking>0) {state.failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(102, input);
                        throw eee;
                }
                cnt102++;
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
    // $ANTLR end "features"


    // $ANTLR start "feature_clause"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:876:1: feature_clause returns [Feature feature] : f= 'feature' (se= selective_export | ) comment fs= feature_specifications ;
    public final Feature feature_clause() throws RecognitionException {
        Feature feature = null;

        Token f=null;
        List<ClassName> se = null;

        BONParser.feature_specifications_return fs = null;

        String comment84 = null;


         String comment = null; List<ClassName> selectiveExport = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:880:1: (f= 'feature' (se= selective_export | ) comment fs= feature_specifications )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:881:3: f= 'feature' (se= selective_export | ) comment fs= feature_specifications
            {
            f=(Token)match(input,72,FOLLOW_72_in_feature_clause5636); if (state.failed) return feature;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:882:3: (se= selective_export | )
            int alt103=2;
            int LA103_0 = input.LA(1);

            if ( (LA103_0==62) ) {
                alt103=1;
            }
            else if ( (LA103_0==IDENTIFIER||(LA103_0>=58 && LA103_0<=59)||LA103_0==73||LA103_0==79||LA103_0==81) ) {
                alt103=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return feature;}
                NoViableAltException nvae =
                    new NoViableAltException("", 103, 0, input);

                throw nvae;
            }
            switch (alt103) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:882:6: se= selective_export
                    {
                    pushFollow(FOLLOW_selective_export_in_feature_clause5646);
                    se=selective_export();

                    state._fsp--;
                    if (state.failed) return feature;
                    if ( state.backtracking==0 ) {
                       if(isOk()) selectiveExport = se; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:883:6: 
                    {
                    if ( state.backtracking==0 ) {
                       selectiveExport = emptyList(); 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_comment_in_feature_clause5665);
            comment84=comment();

            state._fsp--;
            if (state.failed) return feature;
            if ( state.backtracking==0 ) {
               comment = comment84; 
            }
            pushFollow(FOLLOW_feature_specifications_in_feature_clause5673);
            fs=feature_specifications();

            state._fsp--;
            if (state.failed) return feature;
            if ( state.backtracking==0 ) {
               if(isOk()) feature = Feature.mk((fs!=null?fs.specs:null), selectiveExport, comment, getSLoc(f,(fs!=null?((Token)fs.stop):null))); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return feature;
    }
    // $ANTLR end "feature_clause"

    public static class feature_specifications_return extends ParserRuleReturnScope {
        public List<FeatureSpecification> specs;
    };

    // $ANTLR start "feature_specifications"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:890:1: feature_specifications returns [List<FeatureSpecification> specs] : (fs= feature_specification )+ ;
    public final BONParser.feature_specifications_return feature_specifications() throws RecognitionException {
        BONParser.feature_specifications_return retval = new BONParser.feature_specifications_return();
        retval.start = input.LT(1);

        FeatureSpecification fs = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:890:67: ( (fs= feature_specification )+ )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:891:3: (fs= feature_specification )+
            {
            if ( state.backtracking==0 ) {
               retval.specs = createList(); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:892:3: (fs= feature_specification )+
            int cnt104=0;
            loop104:
            do {
                int alt104=2;
                int LA104_0 = input.LA(1);

                if ( (LA104_0==IDENTIFIER||(LA104_0>=58 && LA104_0<=59)||LA104_0==73||LA104_0==79||LA104_0==81) ) {
                    alt104=1;
                }


                switch (alt104) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:892:4: fs= feature_specification
            	    {
            	    pushFollow(FOLLOW_feature_specification_in_feature_specifications5716);
            	    fs=feature_specification();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.specs.add(fs); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt104 >= 1 ) break loop104;
            	    if (state.backtracking>0) {state.failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(104, input);
                        throw eee;
                }
                cnt104++;
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
    // $ANTLR end "feature_specifications"


    // $ANTLR start "feature_specification"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:895:1: feature_specification returns [FeatureSpecification spec] : (d= 'deferred' | e= 'effective' | r= 'redefined' | ) fnl= feature_name_list ( has_type )? (rc= rename_clause )? comment (fa= feature_arguments | ) (cc= contract_clause | ) ;
    public final FeatureSpecification feature_specification() throws RecognitionException {
        FeatureSpecification spec = null;

        Token d=null;
        Token e=null;
        Token r=null;
        BONParser.feature_name_list_return fnl = null;

        BONParser.rename_clause_return rc = null;

        BONParser.feature_arguments_return fa = null;

        BONParser.contract_clause_return cc = null;

        BONParser.has_type_return has_type85 = null;

        String comment86 = null;


         FeatureSpecification.Modifier modifier = FeatureSpecification.Modifier.NONE; 
                List<FeatureArgument> args = null; HasType hasType = null; Token start = null; Token end = null;
                RenameClause renaming = null; String comment = null; ContractClause contracts = null;
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:899:1: ( (d= 'deferred' | e= 'effective' | r= 'redefined' | ) fnl= feature_name_list ( has_type )? (rc= rename_clause )? comment (fa= feature_arguments | ) (cc= contract_clause | ) )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:900:3: (d= 'deferred' | e= 'effective' | r= 'redefined' | ) fnl= feature_name_list ( has_type )? (rc= rename_clause )? comment (fa= feature_arguments | ) (cc= contract_clause | )
            {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:900:3: (d= 'deferred' | e= 'effective' | r= 'redefined' | )
            int alt105=4;
            switch ( input.LA(1) ) {
            case 58:
                {
                alt105=1;
                }
                break;
            case 59:
                {
                alt105=2;
                }
                break;
            case 73:
                {
                alt105=3;
                }
                break;
            case IDENTIFIER:
            case 79:
            case 81:
                {
                alt105=4;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return spec;}
                NoViableAltException nvae =
                    new NoViableAltException("", 105, 0, input);

                throw nvae;
            }

            switch (alt105) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:900:6: d= 'deferred'
                    {
                    d=(Token)match(input,58,FOLLOW_58_in_feature_specification5771); if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       modifier = FeatureSpecification.Modifier.DEFERRED; start = d; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:901:6: e= 'effective'
                    {
                    e=(Token)match(input,59,FOLLOW_59_in_feature_specification5784); if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       modifier = FeatureSpecification.Modifier.EFFECTIVE; start = e; 
                    }

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:902:6: r= 'redefined'
                    {
                    r=(Token)match(input,73,FOLLOW_73_in_feature_specification5795); if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       modifier = FeatureSpecification.Modifier.REDEFINED; start = r; 
                    }

                    }
                    break;
                case 4 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:903:18: 
                    {
                    if ( state.backtracking==0 ) {
                       modifier = FeatureSpecification.Modifier.NONE; 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_feature_name_list_in_feature_specification5826);
            fnl=feature_name_list();

            state._fsp--;
            if (state.failed) return spec;
            if ( state.backtracking==0 ) {
               end=(fnl!=null?((Token)fnl.stop):null); if (start==null) start=(fnl!=null?((Token)fnl.start):null); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:907:3: ( has_type )?
            int alt106=2;
            int LA106_0 = input.LA(1);

            if ( (LA106_0==34||LA106_0==69) ) {
                alt106=1;
            }
            switch (alt106) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:907:4: has_type
                    {
                    pushFollow(FOLLOW_has_type_in_feature_specification5835);
                    has_type85=has_type();

                    state._fsp--;
                    if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) hasType = (has_type85!=null?has_type85.htype:null); end=(has_type85!=null?((Token)has_type85.stop):null); 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:908:3: (rc= rename_clause )?
            int alt107=2;
            int LA107_0 = input.LA(1);

            if ( (LA107_0==62) ) {
                alt107=1;
            }
            switch (alt107) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:908:4: rc= rename_clause
                    {
                    pushFollow(FOLLOW_rename_clause_in_feature_specification5847);
                    rc=rename_clause();

                    state._fsp--;
                    if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) renaming = (rc!=null?rc.rename:null); end=(rc!=null?((Token)rc.stop):null); 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_comment_in_feature_specification5856);
            comment86=comment();

            state._fsp--;
            if (state.failed) return spec;
            if ( state.backtracking==0 ) {
               comment = comment86; 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:910:3: (fa= feature_arguments | )
            int alt108=2;
            int LA108_0 = input.LA(1);

            if ( (LA108_0==65||LA108_0==78) ) {
                alt108=1;
            }
            else if ( (LA108_0==IDENTIFIER||LA108_0==25||(LA108_0>=58 && LA108_0<=59)||(LA108_0>=71 && LA108_0<=73)||(LA108_0>=75 && LA108_0<=76)||LA108_0==79||LA108_0==81) ) {
                alt108=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return spec;}
                NoViableAltException nvae =
                    new NoViableAltException("", 108, 0, input);

                throw nvae;
            }
            switch (alt108) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:910:6: fa= feature_arguments
                    {
                    pushFollow(FOLLOW_feature_arguments_in_feature_specification5867);
                    fa=feature_arguments();

                    state._fsp--;
                    if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) args = (fa!=null?fa.args:null); end=(fa!=null?((Token)fa.stop):null); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:912:6: 
                    {
                    if ( state.backtracking==0 ) {
                       args = emptyList(); 
                    }

                    }
                    break;

            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:914:3: (cc= contract_clause | )
            int alt109=2;
            int LA109_0 = input.LA(1);

            if ( ((LA109_0>=75 && LA109_0<=76)) ) {
                alt109=1;
            }
            else if ( (LA109_0==IDENTIFIER||LA109_0==25||(LA109_0>=58 && LA109_0<=59)||(LA109_0>=71 && LA109_0<=73)||LA109_0==79||LA109_0==81) ) {
                alt109=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return spec;}
                NoViableAltException nvae =
                    new NoViableAltException("", 109, 0, input);

                throw nvae;
            }
            switch (alt109) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:914:6: cc= contract_clause
                    {
                    pushFollow(FOLLOW_contract_clause_in_feature_specification5894);
                    cc=contract_clause();

                    state._fsp--;
                    if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) contracts = (cc!=null?cc.contracts:null); end=(cc!=null?((Token)cc.stop):null); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:916:6: 
                    {
                    if ( state.backtracking==0 ) {
                       contracts = Constants.EMPTY_CONTRACT; 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               if(isOk()) spec = FeatureSpecification.mk(modifier, (fnl!=null?fnl.list:null), args, contracts, hasType, renaming, comment, getSLoc(start,end)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return spec;
    }
    // $ANTLR end "feature_specification"

    public static class has_type_return extends ParserRuleReturnScope {
        public HasType htype;
    };

    // $ANTLR start "has_type"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:921:1: has_type returns [HasType htype] : type_mark ( type | v= 'Void' ) ;
    public final BONParser.has_type_return has_type() throws RecognitionException {
        BONParser.has_type_return retval = new BONParser.has_type_return();
        retval.start = input.LT(1);

        Token v=null;
        BONParser.type_mark_return type_mark87 = null;

        BONParser.type_return type88 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:921:34: ( type_mark ( type | v= 'Void' ) )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:922:3: type_mark ( type | v= 'Void' )
            {
            pushFollow(FOLLOW_type_mark_in_has_type5957);
            type_mark87=type_mark();

            state._fsp--;
            if (state.failed) return retval;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:923:3: ( type | v= 'Void' )
            int alt110=2;
            int LA110_0 = input.LA(1);

            if ( (LA110_0==IDENTIFIER) ) {
                alt110=1;
            }
            else if ( (LA110_0==74) ) {
                alt110=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 110, 0, input);

                throw nvae;
            }
            switch (alt110) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:923:6: type
                    {
                    pushFollow(FOLLOW_type_in_has_type5965);
                    type88=type();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.htype = HasType.mk((type_mark87!=null?type_mark87.mark:null), (type88!=null?type88.type:null), getSLoc((type_mark87!=null?((Token)type_mark87.start):null),(type88!=null?((Token)type88.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:925:6: v= 'Void'
                    {
                    v=(Token)match(input,74,FOLLOW_74_in_has_type5982); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.htype = HasType.mk((type_mark87!=null?type_mark87.mark:null), Type.mk("Void", Constants.EMPTY_TYPE_LIST, getSLoc(v)), getSLoc(v)); 
                    }

                    }
                    break;

            }


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
    // $ANTLR end "has_type"

    public static class contract_clause_return extends ParserRuleReturnScope {
        public ContractClause contracts;
    };

    // $ANTLR start "contract_clause"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:930:1: contract_clause returns [ContractClause contracts] : cc= contracting_conditions 'end' ;
    public final BONParser.contract_clause_return contract_clause() throws RecognitionException {
        BONParser.contract_clause_return retval = new BONParser.contract_clause_return();
        retval.start = input.LT(1);

        ContractClause cc = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:932:52: (cc= contracting_conditions 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:933:3: cc= contracting_conditions 'end'
            {
            pushFollow(FOLLOW_contracting_conditions_in_contract_clause6013);
            cc=contracting_conditions();

            state._fsp--;
            if (state.failed) return retval;
            match(input,25,FOLLOW_25_in_contract_clause6015); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.contracts = cc; 
            }

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
    // $ANTLR end "contract_clause"


    // $ANTLR start "contracting_conditions"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:938:1: contracting_conditions returns [ContractClause contracts] : ( (pre= precondition (post= postcondition )? ) | post= postcondition ) ;
    public final ContractClause contracting_conditions() throws RecognitionException {
        ContractClause contracts = null;

        BONParser.precondition_return pre = null;

        BONParser.postcondition_return post = null;


         List<Expression> postC = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:940:1: ( ( (pre= precondition (post= postcondition )? ) | post= postcondition ) )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:941:3: ( (pre= precondition (post= postcondition )? ) | post= postcondition )
            {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:941:3: ( (pre= precondition (post= postcondition )? ) | post= postcondition )
            int alt112=2;
            int LA112_0 = input.LA(1);

            if ( (LA112_0==75) ) {
                alt112=1;
            }
            else if ( (LA112_0==76) ) {
                alt112=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return contracts;}
                NoViableAltException nvae =
                    new NoViableAltException("", 112, 0, input);

                throw nvae;
            }
            switch (alt112) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:941:6: (pre= precondition (post= postcondition )? )
                    {
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:941:6: (pre= precondition (post= postcondition )? )
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:941:7: pre= precondition (post= postcondition )?
                    {
                    pushFollow(FOLLOW_precondition_in_contracting_conditions6047);
                    pre=precondition();

                    state._fsp--;
                    if (state.failed) return contracts;
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:941:24: (post= postcondition )?
                    int alt111=2;
                    int LA111_0 = input.LA(1);

                    if ( (LA111_0==76) ) {
                        alt111=1;
                    }
                    switch (alt111) {
                        case 1 :
                            // /home/fintan/workspaces/bon/bonc/src/BON.g:941:25: post= postcondition
                            {
                            pushFollow(FOLLOW_postcondition_in_contracting_conditions6052);
                            post=postcondition();

                            state._fsp--;
                            if (state.failed) return contracts;
                            if ( state.backtracking==0 ) {
                               if(isOk()) postC = (post!=null?post.assertions:null); 
                            }

                            }
                            break;

                    }


                    }

                    if ( state.backtracking==0 ) {
                       if (postC == null && isOk()) contracts = ContractClause.mk((pre!=null?pre.assertions:null), Constants.NO_EXPRESSIONS, getSLoc((pre!=null?((Token)pre.start):null),(pre!=null?((Token)pre.stop):null))); 
                             else if (isOk()) contracts = ContractClause.mk((pre!=null?pre.assertions:null), postC, getSLoc((pre!=null?((Token)pre.start):null),(post!=null?((Token)post.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:944:6: post= postcondition
                    {
                    pushFollow(FOLLOW_postcondition_in_contracting_conditions6076);
                    post=postcondition();

                    state._fsp--;
                    if (state.failed) return contracts;
                    if ( state.backtracking==0 ) {
                       if(isOk()) contracts = ContractClause.mk(Constants.NO_EXPRESSIONS, (post!=null?post.assertions:null), getSLoc((post!=null?((Token)post.start):null),(post!=null?((Token)post.stop):null))); 
                    }

                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return contracts;
    }
    // $ANTLR end "contracting_conditions"

    public static class precondition_return extends ParserRuleReturnScope {
        public List<Expression> assertions;
    };

    // $ANTLR start "precondition"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:949:1: precondition returns [List<Expression> assertions] : 'require' assertion ;
    public final BONParser.precondition_return precondition() throws RecognitionException {
        BONParser.precondition_return retval = new BONParser.precondition_return();
        retval.start = input.LT(1);

        List<Expression> assertion89 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:949:52: ( 'require' assertion )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:950:3: 'require' assertion
            {
            match(input,75,FOLLOW_75_in_precondition6102); if (state.failed) return retval;
            pushFollow(FOLLOW_assertion_in_precondition6104);
            assertion89=assertion();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.assertions = assertion89; 
            }

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
    // $ANTLR end "precondition"

    public static class postcondition_return extends ParserRuleReturnScope {
        public List<Expression> assertions;
    };

    // $ANTLR start "postcondition"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:954:1: postcondition returns [List<Expression> assertions] : 'ensure' assertion ;
    public final BONParser.postcondition_return postcondition() throws RecognitionException {
        BONParser.postcondition_return retval = new BONParser.postcondition_return();
        retval.start = input.LT(1);

        List<Expression> assertion90 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:954:53: ( 'ensure' assertion )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:955:3: 'ensure' assertion
            {
            match(input,76,FOLLOW_76_in_postcondition6138); if (state.failed) return retval;
            pushFollow(FOLLOW_assertion_in_postcondition6140);
            assertion90=assertion();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.assertions = assertion90; 
            }

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
    // $ANTLR end "postcondition"


    // $ANTLR start "selective_export"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:959:1: selective_export returns [List<ClassName> exports] : '{' cnl= class_name_list '}' ;
    public final List<ClassName> selective_export() throws RecognitionException {
        List<ClassName> exports = null;

        List<ClassName> cnl = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:961:52: ( '{' cnl= class_name_list '}' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:962:3: '{' cnl= class_name_list '}'
            {
            match(input,62,FOLLOW_62_in_selective_export6163); if (state.failed) return exports;
            pushFollow(FOLLOW_class_name_list_in_selective_export6167);
            cnl=class_name_list();

            state._fsp--;
            if (state.failed) return exports;
            match(input,63,FOLLOW_63_in_selective_export6169); if (state.failed) return exports;
            if ( state.backtracking==0 ) {
               if(isOk()) exports = cnl; 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return exports;
    }
    // $ANTLR end "selective_export"

    public static class feature_name_list_return extends ParserRuleReturnScope {
        public List<FeatureName> list;
    };

    // $ANTLR start "feature_name_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:966:1: feature_name_list returns [List<FeatureName> list] : f1= feature_name ( ',' f= feature_name )* ;
    public final BONParser.feature_name_list_return feature_name_list() throws RecognitionException {
        BONParser.feature_name_list_return retval = new BONParser.feature_name_list_return();
        retval.start = input.LT(1);

        BONParser.feature_name_return f1 = null;

        BONParser.feature_name_return f = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:966:52: (f1= feature_name ( ',' f= feature_name )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:967:3: f1= feature_name ( ',' f= feature_name )*
            {
            if ( state.backtracking==0 ) {
               retval.list = createList(); 
            }
            pushFollow(FOLLOW_feature_name_in_feature_name_list6214);
            f1=feature_name();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.list.add((f1!=null?f1.name:null)); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:970:3: ( ',' f= feature_name )*
            loop113:
            do {
                int alt113=2;
                int LA113_0 = input.LA(1);

                if ( (LA113_0==35) ) {
                    alt113=1;
                }


                switch (alt113) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:970:4: ',' f= feature_name
            	    {
            	    match(input,35,FOLLOW_35_in_feature_name_list6224); if (state.failed) return retval;
            	    pushFollow(FOLLOW_feature_name_in_feature_name_list6228);
            	    f=feature_name();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.list.add((f!=null?f.name:null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop113;
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
    // $ANTLR end "feature_name_list"

    public static class feature_name_return extends ParserRuleReturnScope {
        public FeatureName name;
    };

    // $ANTLR start "feature_name"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:975:1: feature_name returns [FeatureName name] : (i= IDENTIFIER | prefix | infix );
    public final BONParser.feature_name_return feature_name() throws RecognitionException {
        BONParser.feature_name_return retval = new BONParser.feature_name_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:975:41: (i= IDENTIFIER | prefix | infix )
            int alt114=3;
            switch ( input.LA(1) ) {
            case IDENTIFIER:
                {
                alt114=1;
                }
                break;
            case 79:
                {
                alt114=2;
                }
                break;
            case 81:
                {
                alt114=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 114, 0, input);

                throw nvae;
            }

            switch (alt114) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:976:4: i= IDENTIFIER
                    {
                    i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_feature_name6277); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.name = FeatureName.mk((i!=null?i.getText():null), getSLoc(i)); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:978:4: prefix
                    {
                    pushFollow(FOLLOW_prefix_in_feature_name6287);
                    prefix();

                    state._fsp--;
                    if (state.failed) return retval;

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:979:4: infix
                    {
                    pushFollow(FOLLOW_infix_in_feature_name6293);
                    infix();

                    state._fsp--;
                    if (state.failed) return retval;

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
    // $ANTLR end "feature_name"

    public static class rename_clause_return extends ParserRuleReturnScope {
        public RenameClause rename;
    };

    // $ANTLR start "rename_clause"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:982:1: rename_clause returns [RenameClause rename] : '{' renaming '}' ;
    public final BONParser.rename_clause_return rename_clause() throws RecognitionException {
        BONParser.rename_clause_return retval = new BONParser.rename_clause_return();
        retval.start = input.LT(1);

        RenameClause renaming91 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:982:45: ( '{' renaming '}' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:983:3: '{' renaming '}'
            {
            match(input,62,FOLLOW_62_in_rename_clause6323); if (state.failed) return retval;
            pushFollow(FOLLOW_renaming_in_rename_clause6325);
            renaming91=renaming();

            state._fsp--;
            if (state.failed) return retval;
            match(input,63,FOLLOW_63_in_rename_clause6327); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.rename = renaming91; 
            }

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
    // $ANTLR end "rename_clause"


    // $ANTLR start "renaming"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:987:1: renaming returns [RenameClause renaming] : s= '^' class_name '.' feature_name ;
    public final RenameClause renaming() throws RecognitionException {
        RenameClause renaming = null;

        Token s=null;
        BONParser.class_name_return class_name92 = null;

        BONParser.feature_name_return feature_name93 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:987:42: (s= '^' class_name '.' feature_name )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:988:3: s= '^' class_name '.' feature_name
            {
            s=(Token)match(input,77,FOLLOW_77_in_renaming6363); if (state.failed) return renaming;
            pushFollow(FOLLOW_class_name_in_renaming6365);
            class_name92=class_name();

            state._fsp--;
            if (state.failed) return renaming;
            match(input,70,FOLLOW_70_in_renaming6367); if (state.failed) return renaming;
            pushFollow(FOLLOW_feature_name_in_renaming6369);
            feature_name93=feature_name();

            state._fsp--;
            if (state.failed) return renaming;
            if ( state.backtracking==0 ) {
               if(isOk()) renaming = RenameClause.mk((class_name92!=null?class_name92.name:null), (feature_name93!=null?feature_name93.name:null), getSLoc(s,(feature_name93!=null?((Token)feature_name93.stop):null))); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return renaming;
    }
    // $ANTLR end "renaming"

    public static class feature_arguments_return extends ParserRuleReturnScope {
        public List<FeatureArgument> args;
    };

    // $ANTLR start "feature_arguments"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:992:1: feature_arguments returns [List<FeatureArgument> args] : ( feature_argument )+ ;
    public final BONParser.feature_arguments_return feature_arguments() throws RecognitionException {
        BONParser.feature_arguments_return retval = new BONParser.feature_arguments_return();
        retval.start = input.LT(1);

        List<FeatureArgument> feature_argument94 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:992:56: ( ( feature_argument )+ )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:993:3: ( feature_argument )+
            {
            if ( state.backtracking==0 ) {
               retval.args = createList(); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:994:3: ( feature_argument )+
            int cnt115=0;
            loop115:
            do {
                int alt115=2;
                int LA115_0 = input.LA(1);

                if ( (LA115_0==65||LA115_0==78) ) {
                    alt115=1;
                }


                switch (alt115) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:994:4: feature_argument
            	    {
            	    pushFollow(FOLLOW_feature_argument_in_feature_arguments6404);
            	    feature_argument94=feature_argument();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.args.addAll(feature_argument94); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt115 >= 1 ) break loop115;
            	    if (state.backtracking>0) {state.failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(115, input);
                        throw eee;
                }
                cnt115++;
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
    // $ANTLR end "feature_arguments"


    // $ANTLR start "feature_argument"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:997:1: feature_argument returns [List<FeatureArgument> args] : ( '->' | '<-' ) ( ( identifier_list ':' t1= type ) | (t2= type ) ) ;
    public final List<FeatureArgument> feature_argument() throws RecognitionException {
        List<FeatureArgument> args = null;

        BONParser.type_return t1 = null;

        BONParser.type_return t2 = null;

        BONParser.identifier_list_return identifier_list95 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:997:55: ( ( '->' | '<-' ) ( ( identifier_list ':' t1= type ) | (t2= type ) ) )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:998:3: ( '->' | '<-' ) ( ( identifier_list ':' t1= type ) | (t2= type ) )
            {
            if ( input.LA(1)==65||input.LA(1)==78 ) {
                input.consume();
                state.errorRecovery=false;state.failed=false;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return args;}
                MismatchedSetException mse = new MismatchedSetException(null,input);
                throw mse;
            }

            // /home/fintan/workspaces/bon/bonc/src/BON.g:999:3: ( ( identifier_list ':' t1= type ) | (t2= type ) )
            int alt116=2;
            int LA116_0 = input.LA(1);

            if ( (LA116_0==IDENTIFIER) ) {
                int LA116_1 = input.LA(2);

                if ( ((LA116_1>=34 && LA116_1<=35)) ) {
                    alt116=1;
                }
                else if ( (LA116_1==IDENTIFIER||LA116_1==25||(LA116_1>=58 && LA116_1<=59)||(LA116_1>=65 && LA116_1<=66)||(LA116_1>=71 && LA116_1<=73)||(LA116_1>=75 && LA116_1<=76)||(LA116_1>=78 && LA116_1<=79)||LA116_1==81) ) {
                    alt116=2;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return args;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 116, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return args;}
                NoViableAltException nvae =
                    new NoViableAltException("", 116, 0, input);

                throw nvae;
            }
            switch (alt116) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1000:6: ( identifier_list ':' t1= type )
                    {
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1000:6: ( identifier_list ':' t1= type )
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1000:8: identifier_list ':' t1= type
                    {
                    pushFollow(FOLLOW_identifier_list_in_feature_argument6468);
                    identifier_list95=identifier_list();

                    state._fsp--;
                    if (state.failed) return args;
                    match(input,34,FOLLOW_34_in_feature_argument6470); if (state.failed) return args;
                    pushFollow(FOLLOW_type_in_feature_argument6474);
                    t1=type();

                    state._fsp--;
                    if (state.failed) return args;
                    if ( state.backtracking==0 ) {
                       if(isOk()) { List<String> ids = (identifier_list95!=null?identifier_list95.list:null); args = new ArrayList<FeatureArgument>(ids.size()); for (String id : (identifier_list95!=null?identifier_list95.list:null)) args.add(FeatureArgument.mk(id, (t1!=null?t1.type:null), getSLoc((identifier_list95!=null?((Token)identifier_list95.start):null), (t1!=null?((Token)t1.stop):null)))); } 
                    }

                    }


                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1003:6: (t2= type )
                    {
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1003:6: (t2= type )
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1003:8: t2= type
                    {
                    pushFollow(FOLLOW_type_in_feature_argument6506);
                    t2=type();

                    state._fsp--;
                    if (state.failed) return args;
                    if ( state.backtracking==0 ) {
                       if(isOk()) { args = new ArrayList<FeatureArgument>(1); args.add(FeatureArgument.mk(null, (t2!=null?t2.type:null), getSLoc((t2!=null?((Token)t2.start):null),(t2!=null?((Token)t2.stop):null)))); } 
                    }

                    }


                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return args;
    }
    // $ANTLR end "feature_argument"

    public static class identifier_list_return extends ParserRuleReturnScope {
        public List<String> list;
    };

    // $ANTLR start "identifier_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1009:1: identifier_list returns [List<String> list] : i1= IDENTIFIER ( ',' i= IDENTIFIER )* ;
    public final BONParser.identifier_list_return identifier_list() throws RecognitionException {
        BONParser.identifier_list_return retval = new BONParser.identifier_list_return();
        retval.start = input.LT(1);

        Token i1=null;
        Token i=null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1009:45: (i1= IDENTIFIER ( ',' i= IDENTIFIER )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1010:3: i1= IDENTIFIER ( ',' i= IDENTIFIER )*
            {
            if ( state.backtracking==0 ) {
               retval.list = createList(); 
            }
            i1=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_identifier_list6566); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.list.add((i1!=null?i1.getText():null)); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1013:3: ( ',' i= IDENTIFIER )*
            loop117:
            do {
                int alt117=2;
                int LA117_0 = input.LA(1);

                if ( (LA117_0==35) ) {
                    alt117=1;
                }


                switch (alt117) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1013:4: ',' i= IDENTIFIER
            	    {
            	    match(input,35,FOLLOW_35_in_identifier_list6576); if (state.failed) return retval;
            	    i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_identifier_list6580); if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.list.add((i!=null?i.getText():null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop117;
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
    // $ANTLR end "identifier_list"


    // $ANTLR start "prefix"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1017:1: prefix : 'prefix' '\"' prefix_operator '\"' ;
    public final void prefix() throws RecognitionException {
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1017:9: ( 'prefix' '\"' prefix_operator '\"' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1017:12: 'prefix' '\"' prefix_operator '\"'
            {
            match(input,79,FOLLOW_79_in_prefix6597); if (state.failed) return ;
            match(input,80,FOLLOW_80_in_prefix6599); if (state.failed) return ;
            pushFollow(FOLLOW_prefix_operator_in_prefix6601);
            prefix_operator();

            state._fsp--;
            if (state.failed) return ;
            match(input,80,FOLLOW_80_in_prefix6603); if (state.failed) return ;

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
    // $ANTLR end "prefix"


    // $ANTLR start "infix"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1020:1: infix : 'infix' '\"' infix_operator '\"' ;
    public final void infix() throws RecognitionException {
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1020:8: ( 'infix' '\"' infix_operator '\"' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1020:11: 'infix' '\"' infix_operator '\"'
            {
            match(input,81,FOLLOW_81_in_infix6622); if (state.failed) return ;
            match(input,80,FOLLOW_80_in_infix6624); if (state.failed) return ;
            pushFollow(FOLLOW_infix_operator_in_infix6626);
            infix_operator();

            state._fsp--;
            if (state.failed) return ;
            match(input,80,FOLLOW_80_in_infix6628); if (state.failed) return ;

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
    // $ANTLR end "infix"


    // $ANTLR start "prefix_operator"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1024:1: prefix_operator : unary ;
    public final void prefix_operator() throws RecognitionException {
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1024:18: ( unary )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1024:21: unary
            {
            pushFollow(FOLLOW_unary_in_prefix_operator6648);
            unary();

            state._fsp--;
            if (state.failed) return ;

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
    // $ANTLR end "prefix_operator"


    // $ANTLR start "infix_operator"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1028:1: infix_operator : binary ;
    public final void infix_operator() throws RecognitionException {
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1028:17: ( binary )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1029:3: binary
            {
            pushFollow(FOLLOW_binary_in_infix_operator6663);
            binary();

            state._fsp--;
            if (state.failed) return ;

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
    // $ANTLR end "infix_operator"

    public static class formal_generics_return extends ParserRuleReturnScope {
        public List<FormalGeneric> generics;
    };

    // $ANTLR start "formal_generics"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1033:1: formal_generics returns [List<FormalGeneric> generics] : '[' fgl= formal_generic_list ']' ;
    public final BONParser.formal_generics_return formal_generics() throws RecognitionException {
        BONParser.formal_generics_return retval = new BONParser.formal_generics_return();
        retval.start = input.LT(1);

        List<FormalGeneric> fgl = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1035:56: ( '[' fgl= formal_generic_list ']' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1036:3: '[' fgl= formal_generic_list ']'
            {
            match(input,66,FOLLOW_66_in_formal_generics6682); if (state.failed) return retval;
            pushFollow(FOLLOW_formal_generic_list_in_formal_generics6686);
            fgl=formal_generic_list();

            state._fsp--;
            if (state.failed) return retval;
            match(input,67,FOLLOW_67_in_formal_generics6688); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.generics = fgl; 
            }

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
    // $ANTLR end "formal_generics"


    // $ANTLR start "formal_generic_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1040:1: formal_generic_list returns [List<FormalGeneric> list] : fg1= formal_generic ( ',' fg= formal_generic )* ;
    public final List<FormalGeneric> formal_generic_list() throws RecognitionException {
        List<FormalGeneric> list = null;

        FormalGeneric fg1 = null;

        FormalGeneric fg = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1040:56: (fg1= formal_generic ( ',' fg= formal_generic )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1041:3: fg1= formal_generic ( ',' fg= formal_generic )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_formal_generic_in_formal_generic_list6731);
            fg1=formal_generic();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               if(isOk()) list.add(fg1); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1044:3: ( ',' fg= formal_generic )*
            loop118:
            do {
                int alt118=2;
                int LA118_0 = input.LA(1);

                if ( (LA118_0==35) ) {
                    alt118=1;
                }


                switch (alt118) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1044:4: ',' fg= formal_generic
            	    {
            	    match(input,35,FOLLOW_35_in_formal_generic_list6740); if (state.failed) return list;
            	    pushFollow(FOLLOW_formal_generic_in_formal_generic_list6744);
            	    fg=formal_generic();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) list.add(fg); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop118;
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
        return list;
    }
    // $ANTLR end "formal_generic_list"


    // $ANTLR start "formal_generic"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1049:1: formal_generic returns [FormalGeneric generic] : (f= formal_generic_name | f= formal_generic_name '->' ct= class_type );
    public final FormalGeneric formal_generic() throws RecognitionException {
        FormalGeneric generic = null;

        BONParser.formal_generic_name_return f = null;

        BONParser.class_type_return ct = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1049:48: (f= formal_generic_name | f= formal_generic_name '->' ct= class_type )
            int alt119=2;
            int LA119_0 = input.LA(1);

            if ( (LA119_0==IDENTIFIER) ) {
                int LA119_1 = input.LA(2);

                if ( (LA119_1==35||LA119_1==67) ) {
                    alt119=1;
                }
                else if ( (LA119_1==65) ) {
                    alt119=2;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return generic;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 119, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return generic;}
                NoViableAltException nvae =
                    new NoViableAltException("", 119, 0, input);

                throw nvae;
            }
            switch (alt119) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1050:4: f= formal_generic_name
                    {
                    pushFollow(FOLLOW_formal_generic_name_in_formal_generic6794);
                    f=formal_generic_name();

                    state._fsp--;
                    if (state.failed) return generic;
                    if ( state.backtracking==0 ) {
                       if(isOk()) generic = FormalGeneric.mk((f!=null?f.name:null), null, getSLoc((f!=null?((Token)f.start):null),(f!=null?((Token)f.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1052:4: f= formal_generic_name '->' ct= class_type
                    {
                    pushFollow(FOLLOW_formal_generic_name_in_formal_generic6806);
                    f=formal_generic_name();

                    state._fsp--;
                    if (state.failed) return generic;
                    match(input,65,FOLLOW_65_in_formal_generic6808); if (state.failed) return generic;
                    pushFollow(FOLLOW_class_type_in_formal_generic6812);
                    ct=class_type();

                    state._fsp--;
                    if (state.failed) return generic;
                    if ( state.backtracking==0 ) {
                       if(isOk()) generic = FormalGeneric.mk((f!=null?f.name:null), (ct!=null?ct.type:null), getSLoc((f!=null?((Token)f.start):null), (ct!=null?((Token)ct.stop):null))); 
                    }

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
        return generic;
    }
    // $ANTLR end "formal_generic"

    public static class formal_generic_name_return extends ParserRuleReturnScope {
        public String name;
    };

    // $ANTLR start "formal_generic_name"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1056:1: formal_generic_name returns [String name] : i= IDENTIFIER ;
    public final BONParser.formal_generic_name_return formal_generic_name() throws RecognitionException {
        BONParser.formal_generic_name_return retval = new BONParser.formal_generic_name_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1056:43: (i= IDENTIFIER )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1057:3: i= IDENTIFIER
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_formal_generic_name6851); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.name = (i!=null?i.getText():null); 
            }

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
    // $ANTLR end "formal_generic_name"

    public static class class_type_return extends ParserRuleReturnScope {
        public Type type;
    };

    // $ANTLR start "class_type"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1061:1: class_type returns [Type type] : c= class_name ( actual_generics | ) ;
    public final BONParser.class_type_return class_type() throws RecognitionException {
        BONParser.class_type_return retval = new BONParser.class_type_return();
        retval.start = input.LT(1);

        BONParser.class_name_return c = null;

        BONParser.actual_generics_return actual_generics96 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1061:32: (c= class_name ( actual_generics | ) )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1062:3: c= class_name ( actual_generics | )
            {
            pushFollow(FOLLOW_class_name_in_class_type6896);
            c=class_name();

            state._fsp--;
            if (state.failed) return retval;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1063:3: ( actual_generics | )
            int alt120=2;
            int LA120_0 = input.LA(1);

            if ( (LA120_0==66) ) {
                alt120=1;
            }
            else if ( (LA120_0==25||LA120_0==33||LA120_0==35||LA120_0==67||(LA120_0>=71 && LA120_0<=72)) ) {
                alt120=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 120, 0, input);

                throw nvae;
            }
            switch (alt120) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1063:6: actual_generics
                    {
                    pushFollow(FOLLOW_actual_generics_in_class_type6904);
                    actual_generics96=actual_generics();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.type = Type.mk((c!=null?input.toString(c.start,c.stop):null), (actual_generics96!=null?actual_generics96.types:null), getSLoc((c!=null?((Token)c.start):null), (actual_generics96!=null?((Token)actual_generics96.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1066:6: 
                    {
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.type = Type.mk((c!=null?input.toString(c.start,c.stop):null), Constants.EMPTY_TYPE_LIST, getSLoc((c!=null?((Token)c.start):null),(c!=null?((Token)c.stop):null))); 
                    }

                    }
                    break;

            }


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
    // $ANTLR end "class_type"

    public static class actual_generics_return extends ParserRuleReturnScope {
        public List<Type> types;
    };

    // $ANTLR start "actual_generics"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1070:1: actual_generics returns [List<Type> types] : '[' type_list ']' ;
    public final BONParser.actual_generics_return actual_generics() throws RecognitionException {
        BONParser.actual_generics_return retval = new BONParser.actual_generics_return();
        retval.start = input.LT(1);

        List<Type> type_list97 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1070:44: ( '[' type_list ']' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1071:19: '[' type_list ']'
            {
            match(input,66,FOLLOW_66_in_actual_generics6975); if (state.failed) return retval;
            pushFollow(FOLLOW_type_list_in_actual_generics6977);
            type_list97=type_list();

            state._fsp--;
            if (state.failed) return retval;
            match(input,67,FOLLOW_67_in_actual_generics6979); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.types = type_list97; 
            }

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
    // $ANTLR end "actual_generics"


    // $ANTLR start "type_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1075:1: type_list returns [List<Type> types] : t1= type ( ',' t= type )* ;
    public final List<Type> type_list() throws RecognitionException {
        List<Type> types = null;

        BONParser.type_return t1 = null;

        BONParser.type_return t = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1075:39: (t1= type ( ',' t= type )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1076:12: t1= type ( ',' t= type )*
            {
            pushFollow(FOLLOW_type_in_type_list7043);
            t1=type();

            state._fsp--;
            if (state.failed) return types;
            if ( state.backtracking==0 ) {
               types = createList(); if(isOk()) types.add((t1!=null?t1.type:null)); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1078:12: ( ',' t= type )*
            loop121:
            do {
                int alt121=2;
                int LA121_0 = input.LA(1);

                if ( (LA121_0==35) ) {
                    alt121=1;
                }


                switch (alt121) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1078:13: ',' t= type
            	    {
            	    match(input,35,FOLLOW_35_in_type_list7071); if (state.failed) return types;
            	    pushFollow(FOLLOW_type_in_type_list7075);
            	    t=type();

            	    state._fsp--;
            	    if (state.failed) return types;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) types.add((t!=null?t.type:null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop121;
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
        return types;
    }
    // $ANTLR end "type_list"

    public static class type_return extends ParserRuleReturnScope {
        public Type type;
    };

    // $ANTLR start "type"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1086:1: type returns [Type type] : i= IDENTIFIER ( ( actual_generics ) | ) ;
    public final BONParser.type_return type() throws RecognitionException {
        BONParser.type_return retval = new BONParser.type_return();
        retval.start = input.LT(1);

        Token i=null;
        BONParser.actual_generics_return actual_generics98 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1086:26: (i= IDENTIFIER ( ( actual_generics ) | ) )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1087:8: i= IDENTIFIER ( ( actual_generics ) | )
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_type7130); if (state.failed) return retval;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1088:8: ( ( actual_generics ) | )
            int alt122=2;
            int LA122_0 = input.LA(1);

            if ( (LA122_0==66) ) {
                alt122=1;
            }
            else if ( (LA122_0==IDENTIFIER||LA122_0==25||LA122_0==33||LA122_0==35||(LA122_0>=58 && LA122_0<=59)||LA122_0==62||LA122_0==65||LA122_0==67||(LA122_0>=71 && LA122_0<=73)||(LA122_0>=75 && LA122_0<=76)||(LA122_0>=78 && LA122_0<=79)||LA122_0==81||(LA122_0>=84 && LA122_0<=85)) ) {
                alt122=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 122, 0, input);

                throw nvae;
            }
            switch (alt122) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1089:9: ( actual_generics )
                    {
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1089:9: ( actual_generics )
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1089:11: actual_generics
                    {
                    pushFollow(FOLLOW_actual_generics_in_type7152);
                    actual_generics98=actual_generics();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.type = Type.mk((i!=null?i.getText():null), (actual_generics98!=null?actual_generics98.types:null), getSLoc(i,(actual_generics98!=null?((Token)actual_generics98.stop):null))); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1093:9: 
                    {
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.type = Type.mk((i!=null?i.getText():null), Constants.EMPTY_TYPE_LIST, getSLoc(i)); 
                    }

                    }
                    break;

            }


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
    // $ANTLR end "type"


    // $ANTLR start "assertion"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1097:1: assertion returns [List<Expression> clauses] : a1= assertion_clause ( ';' a= assertion_clause )* ( ';' )? ;
    public final List<Expression> assertion() throws RecognitionException {
        List<Expression> clauses = null;

        Expression a1 = null;

        Expression a = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1102:46: (a1= assertion_clause ( ';' a= assertion_clause )* ( ';' )? )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1103:3: a1= assertion_clause ( ';' a= assertion_clause )* ( ';' )?
            {
            if ( state.backtracking==0 ) {
               clauses = createList(); 
            }
            pushFollow(FOLLOW_assertion_clause_in_assertion7231);
            a1=assertion_clause();

            state._fsp--;
            if (state.failed) return clauses;
            if ( state.backtracking==0 ) {
               if(isOk()) clauses.add(a1); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1106:3: ( ';' a= assertion_clause )*
            loop123:
            do {
                int alt123=2;
                int LA123_0 = input.LA(1);

                if ( (LA123_0==33) ) {
                    int LA123_1 = input.LA(2);

                    if ( ((LA123_1>=MANIFEST_STRING && LA123_1<=REAL)||LA123_1==42||LA123_1==62||LA123_1==74||(LA123_1>=82 && LA123_1<=83)||(LA123_1>=88 && LA123_1<=91)||(LA123_1>=103 && LA123_1<=104)||(LA123_1>=108 && LA123_1<=110)) ) {
                        alt123=1;
                    }


                }


                switch (alt123) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1106:4: ';' a= assertion_clause
            	    {
            	    match(input,33,FOLLOW_33_in_assertion7240); if (state.failed) return clauses;
            	    pushFollow(FOLLOW_assertion_clause_in_assertion7244);
            	    a=assertion_clause();

            	    state._fsp--;
            	    if (state.failed) return clauses;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) clauses.add(a); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop123;
                }
            } while (true);

            // /home/fintan/workspaces/bon/bonc/src/BON.g:1109:3: ( ';' )?
            int alt124=2;
            int LA124_0 = input.LA(1);

            if ( (LA124_0==33) ) {
                alt124=1;
            }
            switch (alt124) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1109:3: ';'
                    {
                    match(input,33,FOLLOW_33_in_assertion7261); if (state.failed) return clauses;

                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return clauses;
    }
    // $ANTLR end "assertion"


    // $ANTLR start "assertion_clause"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1112:1: assertion_clause returns [Expression clause] : be= boolean_expression ;
    public final Expression assertion_clause() throws RecognitionException {
        Expression clause = null;

        Expression be = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1112:46: (be= boolean_expression )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1113:3: be= boolean_expression
            {
            pushFollow(FOLLOW_boolean_expression_in_assertion_clause7290);
            be=boolean_expression();

            state._fsp--;
            if (state.failed) return clause;
            if ( state.backtracking==0 ) {
               if(isOk()) clause = be; 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return clause;
    }
    // $ANTLR end "assertion_clause"


    // $ANTLR start "boolean_expression"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1120:1: boolean_expression returns [Expression exp] : expression ;
    public final Expression boolean_expression() throws RecognitionException {
        Expression exp = null;

        BONParser.expression_return expression99 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1120:45: ( expression )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1121:3: expression
            {
            pushFollow(FOLLOW_expression_in_boolean_expression7312);
            expression99=expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp = (expression99!=null?expression99.exp:null); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return exp;
    }
    // $ANTLR end "boolean_expression"


    // $ANTLR start "quantification"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1125:1: quantification returns [Quantification quantification] : q= quantifier rexp= range_expression (r= restriction )? p= proposition ;
    public final Quantification quantification() throws RecognitionException {
        Quantification quantification = null;

        BONParser.quantifier_return q = null;

        List<VariableRange> rexp = null;

        Expression r = null;

        BONParser.proposition_return p = null;


         Expression restrict = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1127:1: (q= quantifier rexp= range_expression (r= restriction )? p= proposition )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1128:3: q= quantifier rexp= range_expression (r= restriction )? p= proposition
            {
            pushFollow(FOLLOW_quantifier_in_quantification7352);
            q=quantifier();

            state._fsp--;
            if (state.failed) return quantification;
            pushFollow(FOLLOW_range_expression_in_quantification7359);
            rexp=range_expression();

            state._fsp--;
            if (state.failed) return quantification;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1130:3: (r= restriction )?
            int alt125=2;
            int LA125_0 = input.LA(1);

            if ( (LA125_0==84) ) {
                alt125=1;
            }
            switch (alt125) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1130:4: r= restriction
                    {
                    pushFollow(FOLLOW_restriction_in_quantification7367);
                    r=restriction();

                    state._fsp--;
                    if (state.failed) return quantification;
                    if ( state.backtracking==0 ) {
                       if(isOk()) restrict = r; 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_proposition_in_quantification7379);
            p=proposition();

            state._fsp--;
            if (state.failed) return quantification;
            if ( state.backtracking==0 ) {
               if(isOk()) quantification = Quantification.mk((q!=null?q.q:null), rexp, restrict, (p!=null?p.exp:null), getSLoc((q!=null?((Token)q.start):null),(p!=null?((Token)p.stop):null))); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return quantification;
    }
    // $ANTLR end "quantification"

    public static class quantifier_return extends ParserRuleReturnScope {
        public Quantification.Quantifier q;
    };

    // $ANTLR start "quantifier"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1135:1: quantifier returns [Quantification.Quantifier q] : (f= 'for_all' | e= 'exists' );
    public final BONParser.quantifier_return quantifier() throws RecognitionException {
        BONParser.quantifier_return retval = new BONParser.quantifier_return();
        retval.start = input.LT(1);

        Token f=null;
        Token e=null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1135:50: (f= 'for_all' | e= 'exists' )
            int alt126=2;
            int LA126_0 = input.LA(1);

            if ( (LA126_0==82) ) {
                alt126=1;
            }
            else if ( (LA126_0==83) ) {
                alt126=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 126, 0, input);

                throw nvae;
            }
            switch (alt126) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1136:4: f= 'for_all'
                    {
                    f=(Token)match(input,82,FOLLOW_82_in_quantifier7418); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.q = Quantification.Quantifier.FORALL; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1138:4: e= 'exists'
                    {
                    e=(Token)match(input,83,FOLLOW_83_in_quantifier7431); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.q = Quantification.Quantifier.EXISTS; 
                    }

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
    // $ANTLR end "quantifier"


    // $ANTLR start "range_expression"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1142:1: range_expression returns [List<VariableRange> ranges] : vr1= variable_range ( ';' vr= variable_range )* ( ';' )? ;
    public final List<VariableRange> range_expression() throws RecognitionException {
        List<VariableRange> ranges = null;

        VariableRange vr1 = null;

        VariableRange vr = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1142:55: (vr1= variable_range ( ';' vr= variable_range )* ( ';' )? )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1143:3: vr1= variable_range ( ';' vr= variable_range )* ( ';' )?
            {
            if ( state.backtracking==0 ) {
               ranges = createList(); 
            }
            pushFollow(FOLLOW_variable_range_in_range_expression7469);
            vr1=variable_range();

            state._fsp--;
            if (state.failed) return ranges;
            if ( state.backtracking==0 ) {
               if(isOk()) ranges.add(vr); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1146:3: ( ';' vr= variable_range )*
            loop127:
            do {
                int alt127=2;
                int LA127_0 = input.LA(1);

                if ( (LA127_0==33) ) {
                    int LA127_1 = input.LA(2);

                    if ( (LA127_1==IDENTIFIER) ) {
                        alt127=1;
                    }


                }


                switch (alt127) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1146:4: ';' vr= variable_range
            	    {
            	    match(input,33,FOLLOW_33_in_range_expression7479); if (state.failed) return ranges;
            	    pushFollow(FOLLOW_variable_range_in_range_expression7483);
            	    vr=variable_range();

            	    state._fsp--;
            	    if (state.failed) return ranges;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) ranges.add(vr); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop127;
                }
            } while (true);

            // /home/fintan/workspaces/bon/bonc/src/BON.g:1149:3: ( ';' )?
            int alt128=2;
            int LA128_0 = input.LA(1);

            if ( (LA128_0==33) ) {
                alt128=1;
            }
            switch (alt128) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1149:3: ';'
                    {
                    match(input,33,FOLLOW_33_in_range_expression7498); if (state.failed) return ranges;

                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ranges;
    }
    // $ANTLR end "range_expression"


    // $ANTLR start "restriction"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1152:1: restriction returns [Expression exp] : st= 'such_that' be= boolean_expression ;
    public final Expression restriction() throws RecognitionException {
        Expression exp = null;

        Token st=null;
        Expression be = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1152:38: (st= 'such_that' be= boolean_expression )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1153:3: st= 'such_that' be= boolean_expression
            {
            st=(Token)match(input,84,FOLLOW_84_in_restriction7535); if (state.failed) return exp;
            pushFollow(FOLLOW_boolean_expression_in_restriction7539);
            be=boolean_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp =  be; 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return exp;
    }
    // $ANTLR end "restriction"

    public static class proposition_return extends ParserRuleReturnScope {
        public Expression exp;
    };

    // $ANTLR start "proposition"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1157:1: proposition returns [Expression exp] : ih= 'it_holds' be= boolean_expression ;
    public final BONParser.proposition_return proposition() throws RecognitionException {
        BONParser.proposition_return retval = new BONParser.proposition_return();
        retval.start = input.LT(1);

        Token ih=null;
        Expression be = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1157:38: (ih= 'it_holds' be= boolean_expression )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1158:3: ih= 'it_holds' be= boolean_expression
            {
            ih=(Token)match(input,85,FOLLOW_85_in_proposition7573); if (state.failed) return retval;
            pushFollow(FOLLOW_boolean_expression_in_proposition7577);
            be=boolean_expression();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.exp = be; 
            }

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
    // $ANTLR end "proposition"


    // $ANTLR start "variable_range"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1162:1: variable_range returns [VariableRange range] : (mr= member_range | tr= type_range );
    public final VariableRange variable_range() throws RecognitionException {
        VariableRange range = null;

        MemberRange mr = null;

        TypeRange tr = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1162:46: (mr= member_range | tr= type_range )
            int alt129=2;
            alt129 = dfa129.predict(input);
            switch (alt129) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1163:4: mr= member_range
                    {
                    pushFollow(FOLLOW_member_range_in_variable_range7613);
                    mr=member_range();

                    state._fsp--;
                    if (state.failed) return range;
                    if ( state.backtracking==0 ) {
                       if(isOk()) range = mr; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1165:4: tr= type_range
                    {
                    pushFollow(FOLLOW_type_range_in_variable_range7625);
                    tr=type_range();

                    state._fsp--;
                    if (state.failed) return range;
                    if ( state.backtracking==0 ) {
                       if(isOk()) range = tr; 
                    }

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
        return range;
    }
    // $ANTLR end "variable_range"


    // $ANTLR start "member_range"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1169:1: member_range returns [MemberRange range] : il= identifier_list 'member_of' e= expression ;
    public final MemberRange member_range() throws RecognitionException {
        MemberRange range = null;

        BONParser.identifier_list_return il = null;

        BONParser.expression_return e = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1169:42: (il= identifier_list 'member_of' e= expression )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1170:3: il= identifier_list 'member_of' e= expression
            {
            pushFollow(FOLLOW_identifier_list_in_member_range7665);
            il=identifier_list();

            state._fsp--;
            if (state.failed) return range;
            match(input,86,FOLLOW_86_in_member_range7667); if (state.failed) return range;
            pushFollow(FOLLOW_expression_in_member_range7671);
            e=expression();

            state._fsp--;
            if (state.failed) return range;
            if ( state.backtracking==0 ) {
               if(isOk()) range = MemberRange.mk((il!=null?il.list:null), (e!=null?e.exp:null), getSLoc((il!=null?((Token)il.start):null),(e!=null?((Token)e.stop):null))); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return range;
    }
    // $ANTLR end "member_range"


    // $ANTLR start "type_range"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1174:1: type_range returns [TypeRange range] : il= identifier_list ':' t= type ;
    public final TypeRange type_range() throws RecognitionException {
        TypeRange range = null;

        BONParser.identifier_list_return il = null;

        BONParser.type_return t = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1174:38: (il= identifier_list ':' t= type )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1175:3: il= identifier_list ':' t= type
            {
            pushFollow(FOLLOW_identifier_list_in_type_range7707);
            il=identifier_list();

            state._fsp--;
            if (state.failed) return range;
            match(input,34,FOLLOW_34_in_type_range7709); if (state.failed) return range;
            pushFollow(FOLLOW_type_in_type_range7713);
            t=type();

            state._fsp--;
            if (state.failed) return range;
            if ( state.backtracking==0 ) {
               if(isOk()) range = TypeRange.mk((il!=null?il.list:null), (t!=null?t.type:null), getSLoc((il!=null?((Token)il.start):null),(t!=null?((Token)t.stop):null))); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return range;
    }
    // $ANTLR end "type_range"

    public static class call_chain_return extends ParserRuleReturnScope {
        public List<UnqualifiedCall> calls;
    };

    // $ANTLR start "call_chain"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1179:1: call_chain returns [List<UnqualifiedCall> calls] : uc1= unqualified_call ( '.' uc= unqualified_call )* ;
    public final BONParser.call_chain_return call_chain() throws RecognitionException {
        BONParser.call_chain_return retval = new BONParser.call_chain_return();
        retval.start = input.LT(1);

        UnqualifiedCall uc1 = null;

        UnqualifiedCall uc = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1181:50: (uc1= unqualified_call ( '.' uc= unqualified_call )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1182:3: uc1= unqualified_call ( '.' uc= unqualified_call )*
            {
            if ( state.backtracking==0 ) {
               if(isOk()) retval.calls = createList(); 
            }
            pushFollow(FOLLOW_unqualified_call_in_call_chain7773);
            uc1=unqualified_call();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.calls.add(uc1); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1185:3: ( '.' uc= unqualified_call )*
            loop130:
            do {
                int alt130=2;
                int LA130_0 = input.LA(1);

                if ( (LA130_0==70) ) {
                    alt130=1;
                }


                switch (alt130) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1185:4: '.' uc= unqualified_call
            	    {
            	    match(input,70,FOLLOW_70_in_call_chain7782); if (state.failed) return retval;
            	    pushFollow(FOLLOW_unqualified_call_in_call_chain7786);
            	    uc=unqualified_call();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.calls.add(uc); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop130;
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
    // $ANTLR end "call_chain"


    // $ANTLR start "unqualified_call"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1188:1: unqualified_call returns [UnqualifiedCall call] : i= IDENTIFIER (aa= actual_arguments | ) ;
    public final UnqualifiedCall unqualified_call() throws RecognitionException {
        UnqualifiedCall call = null;

        Token i=null;
        BONParser.actual_arguments_return aa = null;


         List<Expression> args = null; Token end = null;
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1190:1: (i= IDENTIFIER (aa= actual_arguments | ) )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1191:3: i= IDENTIFIER (aa= actual_arguments | )
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_unqualified_call7827); if (state.failed) return call;
            if ( state.backtracking==0 ) {
               end = i; 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1193:3: (aa= actual_arguments | )
            int alt131=2;
            int LA131_0 = input.LA(1);

            if ( (LA131_0==42) ) {
                alt131=1;
            }
            else if ( (LA131_0==25||(LA131_0>=33 && LA131_0<=35)||LA131_0==43||LA131_0==63||LA131_0==65||LA131_0==70||(LA131_0>=76 && LA131_0<=77)||(LA131_0>=84 && LA131_0<=86)||(LA131_0>=102 && LA131_0<=107)||(LA131_0>=110 && LA131_0<=120)) ) {
                alt131=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return call;}
                NoViableAltException nvae =
                    new NoViableAltException("", 131, 0, input);

                throw nvae;
            }
            switch (alt131) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1193:6: aa= actual_arguments
                    {
                    pushFollow(FOLLOW_actual_arguments_in_unqualified_call7841);
                    aa=actual_arguments();

                    state._fsp--;
                    if (state.failed) return call;
                    if ( state.backtracking==0 ) {
                       if(isOk()) args = (aa!=null?aa.args:null); end = (aa!=null?((Token)aa.stop):null); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1195:6: 
                    {
                    if ( state.backtracking==0 ) {
                       args = emptyList(); 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               if(isOk()) call = UnqualifiedCall.mk((i!=null?i.getText():null), args, getSLoc(i,end)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return call;
    }
    // $ANTLR end "unqualified_call"

    public static class actual_arguments_return extends ParserRuleReturnScope {
        public List<Expression> args;
    };

    // $ANTLR start "actual_arguments"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1200:1: actual_arguments returns [List<Expression> args] : '(' (el= expression_list | ) ')' ;
    public final BONParser.actual_arguments_return actual_arguments() throws RecognitionException {
        BONParser.actual_arguments_return retval = new BONParser.actual_arguments_return();
        retval.start = input.LT(1);

        List<Expression> el = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1201:1: ( '(' (el= expression_list | ) ')' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1202:3: '(' (el= expression_list | ) ')'
            {
            match(input,42,FOLLOW_42_in_actual_arguments7880); if (state.failed) return retval;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1203:3: (el= expression_list | )
            int alt132=2;
            int LA132_0 = input.LA(1);

            if ( ((LA132_0>=MANIFEST_STRING && LA132_0<=REAL)||LA132_0==42||LA132_0==62||LA132_0==74||(LA132_0>=82 && LA132_0<=83)||(LA132_0>=88 && LA132_0<=91)||(LA132_0>=103 && LA132_0<=104)||(LA132_0>=108 && LA132_0<=110)) ) {
                alt132=1;
            }
            else if ( (LA132_0==43) ) {
                alt132=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 132, 0, input);

                throw nvae;
            }
            switch (alt132) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1203:6: el= expression_list
                    {
                    pushFollow(FOLLOW_expression_list_in_actual_arguments7890);
                    el=expression_list();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.args = el; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1205:6: 
                    {
                    if ( state.backtracking==0 ) {
                       retval.args = emptyList(); 
                    }

                    }
                    break;

            }

            match(input,43,FOLLOW_43_in_actual_arguments7913); if (state.failed) return retval;

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
    // $ANTLR end "actual_arguments"


    // $ANTLR start "expression_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1210:1: expression_list returns [List<Expression> list] : e1= expression ( ',' e= expression )* ;
    public final List<Expression> expression_list() throws RecognitionException {
        List<Expression> list = null;

        BONParser.expression_return e1 = null;

        BONParser.expression_return e = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1210:49: (e1= expression ( ',' e= expression )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1211:3: e1= expression ( ',' e= expression )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_expression_in_expression_list7949);
            e1=expression();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               if(isOk()) list.add((e1!=null?e1.exp:null)); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1214:3: ( ',' e= expression )*
            loop133:
            do {
                int alt133=2;
                int LA133_0 = input.LA(1);

                if ( (LA133_0==35) ) {
                    alt133=1;
                }


                switch (alt133) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1214:4: ',' e= expression
            	    {
            	    match(input,35,FOLLOW_35_in_expression_list7959); if (state.failed) return list;
            	    pushFollow(FOLLOW_expression_in_expression_list7963);
            	    e=expression();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) list.add((e!=null?e.exp:null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop133;
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
        return list;
    }
    // $ANTLR end "expression_list"

    public static class enumerated_set_return extends ParserRuleReturnScope {
        public List<EnumerationElement> list;
    };

    // $ANTLR start "enumerated_set"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1217:1: enumerated_set returns [List<EnumerationElement> list] : '{' el= enumeration_list '}' ;
    public final BONParser.enumerated_set_return enumerated_set() throws RecognitionException {
        BONParser.enumerated_set_return retval = new BONParser.enumerated_set_return();
        retval.start = input.LT(1);

        List<EnumerationElement> el = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1225:56: ( '{' el= enumeration_list '}' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1226:3: '{' el= enumeration_list '}'
            {
            match(input,62,FOLLOW_62_in_enumerated_set8009); if (state.failed) return retval;
            pushFollow(FOLLOW_enumeration_list_in_enumerated_set8013);
            el=enumeration_list();

            state._fsp--;
            if (state.failed) return retval;
            match(input,63,FOLLOW_63_in_enumerated_set8015); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.list = el; 
            }

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
    // $ANTLR end "enumerated_set"


    // $ANTLR start "enumeration_list"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1230:1: enumeration_list returns [List<EnumerationElement> list] : el1= enumeration_element ( ',' el= enumeration_element )* ;
    public final List<EnumerationElement> enumeration_list() throws RecognitionException {
        List<EnumerationElement> list = null;

        EnumerationElement el1 = null;

        EnumerationElement el = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1230:58: (el1= enumeration_element ( ',' el= enumeration_element )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1231:3: el1= enumeration_element ( ',' el= enumeration_element )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_enumeration_element_in_enumeration_list8057);
            el1=enumeration_element();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               if(isOk()) list.add(el1); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1234:3: ( ',' el= enumeration_element )*
            loop134:
            do {
                int alt134=2;
                int LA134_0 = input.LA(1);

                if ( (LA134_0==35) ) {
                    alt134=1;
                }


                switch (alt134) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1234:4: ',' el= enumeration_element
            	    {
            	    match(input,35,FOLLOW_35_in_enumeration_list8067); if (state.failed) return list;
            	    pushFollow(FOLLOW_enumeration_element_in_enumeration_list8071);
            	    el=enumeration_element();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) list.add(el); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop134;
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
        return list;
    }
    // $ANTLR end "enumeration_list"


    // $ANTLR start "enumeration_element"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1237:1: enumeration_element returns [EnumerationElement el] : (e= expression | i= interval );
    public final EnumerationElement enumeration_element() throws RecognitionException {
        EnumerationElement el = null;

        BONParser.expression_return e = null;

        Interval i = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1237:53: (e= expression | i= interval )
            int alt135=2;
            switch ( input.LA(1) ) {
            case MANIFEST_STRING:
            case IDENTIFIER:
            case REAL:
            case 42:
            case 62:
            case 74:
            case 82:
            case 83:
            case 88:
            case 89:
            case 90:
            case 91:
            case 108:
            case 109:
            case 110:
                {
                alt135=1;
                }
                break;
            case CHARACTER_CONSTANT:
                {
                int LA135_2 = input.LA(2);

                if ( (LA135_2==87) ) {
                    alt135=2;
                }
                else if ( ((LA135_2>=34 && LA135_2<=35)||LA135_2==63||LA135_2==65||LA135_2==70||LA135_2==77||LA135_2==86||(LA135_2>=102 && LA135_2<=107)||(LA135_2>=110 && LA135_2<=120)) ) {
                    alt135=1;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return el;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 135, 2, input);

                    throw nvae;
                }
                }
                break;
            case 103:
                {
                int LA135_3 = input.LA(2);

                if ( ((LA135_3>=MANIFEST_STRING && LA135_3<=IDENTIFIER)||(LA135_3>=CHARACTER_CONSTANT && LA135_3<=REAL)||LA135_3==42||LA135_3==62||LA135_3==74||(LA135_3>=88 && LA135_3<=91)||(LA135_3>=103 && LA135_3<=104)||(LA135_3>=108 && LA135_3<=110)) ) {
                    alt135=1;
                }
                else if ( (LA135_3==INTEGER) ) {
                    int LA135_7 = input.LA(3);

                    if ( (LA135_7==87) ) {
                        alt135=2;
                    }
                    else if ( ((LA135_7>=34 && LA135_7<=35)||LA135_7==63||LA135_7==65||LA135_7==70||LA135_7==77||LA135_7==86||(LA135_7>=102 && LA135_7<=107)||(LA135_7>=110 && LA135_7<=120)) ) {
                        alt135=1;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return el;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 135, 7, input);

                        throw nvae;
                    }
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return el;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 135, 3, input);

                    throw nvae;
                }
                }
                break;
            case 104:
                {
                int LA135_4 = input.LA(2);

                if ( ((LA135_4>=MANIFEST_STRING && LA135_4<=IDENTIFIER)||(LA135_4>=CHARACTER_CONSTANT && LA135_4<=REAL)||LA135_4==42||LA135_4==62||LA135_4==74||(LA135_4>=88 && LA135_4<=91)||(LA135_4>=103 && LA135_4<=104)||(LA135_4>=108 && LA135_4<=110)) ) {
                    alt135=1;
                }
                else if ( (LA135_4==INTEGER) ) {
                    int LA135_7 = input.LA(3);

                    if ( (LA135_7==87) ) {
                        alt135=2;
                    }
                    else if ( ((LA135_7>=34 && LA135_7<=35)||LA135_7==63||LA135_7==65||LA135_7==70||LA135_7==77||LA135_7==86||(LA135_7>=102 && LA135_7<=107)||(LA135_7>=110 && LA135_7<=120)) ) {
                        alt135=1;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return el;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 135, 7, input);

                        throw nvae;
                    }
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return el;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 135, 4, input);

                    throw nvae;
                }
                }
                break;
            case INTEGER:
                {
                int LA135_5 = input.LA(2);

                if ( (LA135_5==87) ) {
                    alt135=2;
                }
                else if ( ((LA135_5>=34 && LA135_5<=35)||LA135_5==63||LA135_5==65||LA135_5==70||LA135_5==77||LA135_5==86||(LA135_5>=102 && LA135_5<=107)||(LA135_5>=110 && LA135_5<=120)) ) {
                    alt135=1;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return el;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 135, 5, input);

                    throw nvae;
                }
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return el;}
                NoViableAltException nvae =
                    new NoViableAltException("", 135, 0, input);

                throw nvae;
            }

            switch (alt135) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1238:4: e= expression
                    {
                    pushFollow(FOLLOW_expression_in_enumeration_element8103);
                    e=expression();

                    state._fsp--;
                    if (state.failed) return el;
                    if ( state.backtracking==0 ) {
                       if(isOk()) el = (e!=null?e.exp:null); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1240:4: i= interval
                    {
                    pushFollow(FOLLOW_interval_in_enumeration_element8117);
                    i=interval();

                    state._fsp--;
                    if (state.failed) return el;
                    if ( state.backtracking==0 ) {
                       if(isOk()) el = i; 
                    }

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
        return el;
    }
    // $ANTLR end "enumeration_element"


    // $ANTLR start "interval"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1244:1: interval returns [Interval interval] : (ii= integer_interval | ci= character_interval );
    public final Interval interval() throws RecognitionException {
        Interval interval = null;

        IntegerInterval ii = null;

        CharacterInterval ci = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1244:39: (ii= integer_interval | ci= character_interval )
            int alt136=2;
            int LA136_0 = input.LA(1);

            if ( (LA136_0==INTEGER||(LA136_0>=103 && LA136_0<=104)) ) {
                alt136=1;
            }
            else if ( (LA136_0==CHARACTER_CONSTANT) ) {
                alt136=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return interval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 136, 0, input);

                throw nvae;
            }
            switch (alt136) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1245:4: ii= integer_interval
                    {
                    pushFollow(FOLLOW_integer_interval_in_interval8164);
                    ii=integer_interval();

                    state._fsp--;
                    if (state.failed) return interval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) interval = ii; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1247:4: ci= character_interval
                    {
                    pushFollow(FOLLOW_character_interval_in_interval8176);
                    ci=character_interval();

                    state._fsp--;
                    if (state.failed) return interval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) interval = ci; 
                    }

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
        return interval;
    }
    // $ANTLR end "interval"


    // $ANTLR start "integer_interval"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1251:1: integer_interval returns [IntegerInterval interval] : i1= integer_constant '..' i2= integer_constant ;
    public final IntegerInterval integer_interval() throws RecognitionException {
        IntegerInterval interval = null;

        BONParser.integer_constant_return i1 = null;

        BONParser.integer_constant_return i2 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1251:53: (i1= integer_constant '..' i2= integer_constant )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1252:3: i1= integer_constant '..' i2= integer_constant
            {
            pushFollow(FOLLOW_integer_constant_in_integer_interval8209);
            i1=integer_constant();

            state._fsp--;
            if (state.failed) return interval;
            match(input,87,FOLLOW_87_in_integer_interval8211); if (state.failed) return interval;
            pushFollow(FOLLOW_integer_constant_in_integer_interval8215);
            i2=integer_constant();

            state._fsp--;
            if (state.failed) return interval;
            if ( state.backtracking==0 ) {
               if(isOk()) interval = IntegerInterval.mk((i1!=null?i1.value:null),(i2!=null?i2.value:null),getSLoc((i1!=null?((Token)i1.start):null),(i2!=null?((Token)i2.stop):null))); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return interval;
    }
    // $ANTLR end "integer_interval"


    // $ANTLR start "character_interval"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1256:1: character_interval returns [CharacterInterval interval] : c1= character_constant '..' c2= character_constant ;
    public final CharacterInterval character_interval() throws RecognitionException {
        CharacterInterval interval = null;

        BONParser.character_constant_return c1 = null;

        BONParser.character_constant_return c2 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1256:57: (c1= character_constant '..' c2= character_constant )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1257:3: c1= character_constant '..' c2= character_constant
            {
            pushFollow(FOLLOW_character_constant_in_character_interval8257);
            c1=character_constant();

            state._fsp--;
            if (state.failed) return interval;
            match(input,87,FOLLOW_87_in_character_interval8259); if (state.failed) return interval;
            pushFollow(FOLLOW_character_constant_in_character_interval8263);
            c2=character_constant();

            state._fsp--;
            if (state.failed) return interval;
            if ( state.backtracking==0 ) {
               if(isOk()) interval = CharacterInterval.mk((c1!=null?c1.value:null),(c2!=null?c2.value:null),getSLoc((c1!=null?((Token)c1.start):null),(c2!=null?((Token)c2.stop):null))); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return interval;
    }
    // $ANTLR end "character_interval"

    public static class constant_return extends ParserRuleReturnScope {
        public Constant constant;
    };

    // $ANTLR start "constant"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1261:1: constant returns [Constant constant] : (mc= manifest_constant | c= 'Current' | v= 'Void' | v= 'Result' );
    public final BONParser.constant_return constant() throws RecognitionException {
        BONParser.constant_return retval = new BONParser.constant_return();
        retval.start = input.LT(1);

        Token c=null;
        Token v=null;
        ManifestConstant mc = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1263:38: (mc= manifest_constant | c= 'Current' | v= 'Void' | v= 'Result' )
            int alt137=4;
            switch ( input.LA(1) ) {
            case MANIFEST_STRING:
            case INTEGER:
            case CHARACTER_CONSTANT:
            case REAL:
            case 62:
            case 90:
            case 91:
            case 103:
            case 104:
                {
                alt137=1;
                }
                break;
            case 88:
                {
                alt137=2;
                }
                break;
            case 74:
                {
                alt137=3;
                }
                break;
            case 89:
                {
                alt137=4;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 137, 0, input);

                throw nvae;
            }

            switch (alt137) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1264:4: mc= manifest_constant
                    {
                    pushFollow(FOLLOW_manifest_constant_in_constant8289);
                    mc=manifest_constant();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.constant = mc; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1266:4: c= 'Current'
                    {
                    c=(Token)match(input,88,FOLLOW_88_in_constant8302); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.constant = KeywordConstant.mk(KeywordConstant.Constant.CURRENT, getSLoc(c)); 
                    }

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1268:4: v= 'Void'
                    {
                    v=(Token)match(input,74,FOLLOW_74_in_constant8315); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.constant = KeywordConstant.mk(KeywordConstant.Constant.VOID, getSLoc(v)); 
                    }

                    }
                    break;
                case 4 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1270:4: v= 'Result'
                    {
                    v=(Token)match(input,89,FOLLOW_89_in_constant8339); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.constant = KeywordConstant.mk(KeywordConstant.Constant.RESULT, getSLoc(v)); 
                    }

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
    // $ANTLR end "constant"


    // $ANTLR start "manifest_constant"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1274:1: manifest_constant returns [ManifestConstant constant] : (bc= boolean_constant | cc= character_constant | ic= integer_constant | rc= real_constant | ms= MANIFEST_STRING | es= enumerated_set );
    public final ManifestConstant manifest_constant() throws RecognitionException {
        ManifestConstant constant = null;

        Token ms=null;
        BONParser.boolean_constant_return bc = null;

        BONParser.character_constant_return cc = null;

        BONParser.integer_constant_return ic = null;

        BONParser.real_constant_return rc = null;

        BONParser.enumerated_set_return es = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1274:55: (bc= boolean_constant | cc= character_constant | ic= integer_constant | rc= real_constant | ms= MANIFEST_STRING | es= enumerated_set )
            int alt138=6;
            switch ( input.LA(1) ) {
            case 90:
            case 91:
                {
                alt138=1;
                }
                break;
            case CHARACTER_CONSTANT:
                {
                alt138=2;
                }
                break;
            case 103:
                {
                int LA138_3 = input.LA(2);

                if ( (LA138_3==REAL) ) {
                    alt138=4;
                }
                else if ( (LA138_3==INTEGER) ) {
                    alt138=3;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return constant;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 138, 3, input);

                    throw nvae;
                }
                }
                break;
            case 104:
                {
                int LA138_4 = input.LA(2);

                if ( (LA138_4==REAL) ) {
                    alt138=4;
                }
                else if ( (LA138_4==INTEGER) ) {
                    alt138=3;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return constant;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 138, 4, input);

                    throw nvae;
                }
                }
                break;
            case INTEGER:
                {
                alt138=3;
                }
                break;
            case REAL:
                {
                alt138=4;
                }
                break;
            case MANIFEST_STRING:
                {
                alt138=5;
                }
                break;
            case 62:
                {
                alt138=6;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return constant;}
                NoViableAltException nvae =
                    new NoViableAltException("", 138, 0, input);

                throw nvae;
            }

            switch (alt138) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1275:4: bc= boolean_constant
                    {
                    pushFollow(FOLLOW_boolean_constant_in_manifest_constant8362);
                    bc=boolean_constant();

                    state._fsp--;
                    if (state.failed) return constant;
                    if ( state.backtracking==0 ) {
                       constant = BooleanConstant.mk((bc!=null?bc.value:null),getSLoc((bc!=null?((Token)bc.start):null),(bc!=null?((Token)bc.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1277:4: cc= character_constant
                    {
                    pushFollow(FOLLOW_character_constant_in_manifest_constant8375);
                    cc=character_constant();

                    state._fsp--;
                    if (state.failed) return constant;
                    if ( state.backtracking==0 ) {
                       constant = CharacterConstant.mk((cc!=null?cc.value:null),getSLoc((cc!=null?((Token)cc.start):null),(cc!=null?((Token)cc.stop):null))); 
                    }

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1279:4: ic= integer_constant
                    {
                    pushFollow(FOLLOW_integer_constant_in_manifest_constant8388);
                    ic=integer_constant();

                    state._fsp--;
                    if (state.failed) return constant;
                    if ( state.backtracking==0 ) {
                       constant = IntegerConstant.mk((ic!=null?ic.value:null),getSLoc((ic!=null?((Token)ic.start):null),(ic!=null?((Token)ic.stop):null))); 
                    }

                    }
                    break;
                case 4 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1281:4: rc= real_constant
                    {
                    pushFollow(FOLLOW_real_constant_in_manifest_constant8401);
                    rc=real_constant();

                    state._fsp--;
                    if (state.failed) return constant;
                    if ( state.backtracking==0 ) {
                       constant = RealConstant.mk((rc!=null?rc.value:null),getSLoc((rc!=null?((Token)rc.start):null),(rc!=null?((Token)rc.stop):null))); 
                    }

                    }
                    break;
                case 5 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1283:4: ms= MANIFEST_STRING
                    {
                    ms=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_manifest_constant8414); if (state.failed) return constant;
                    if ( state.backtracking==0 ) {
                       constant = StringConstant.mk((ms!=null?ms.getText():null),getSLoc(ms)); 
                    }

                    }
                    break;
                case 6 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1285:4: es= enumerated_set
                    {
                    pushFollow(FOLLOW_enumerated_set_in_manifest_constant8427);
                    es=enumerated_set();

                    state._fsp--;
                    if (state.failed) return constant;
                    if ( state.backtracking==0 ) {
                       constant = SetConstant.mk((es!=null?es.list:null), getSLoc((es!=null?((Token)es.start):null),(es!=null?((Token)es.stop):null))); 
                    }

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
        return constant;
    }
    // $ANTLR end "manifest_constant"


    // $ANTLR start "sign"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1289:1: sign returns [BinaryExp.Op op] : add_sub_op ;
    public final BinaryExp.Op sign() throws RecognitionException {
        BinaryExp.Op op = null;

        BinaryExp.Op add_sub_op100 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1289:32: ( add_sub_op )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1290:3: add_sub_op
            {
            pushFollow(FOLLOW_add_sub_op_in_sign8466);
            add_sub_op100=add_sub_op();

            state._fsp--;
            if (state.failed) return op;
            if ( state.backtracking==0 ) {
               if(isOk()) op = add_sub_op100; 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return op;
    }
    // $ANTLR end "sign"

    public static class boolean_constant_return extends ParserRuleReturnScope {
        public Boolean value;
    };

    // $ANTLR start "boolean_constant"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1294:1: boolean_constant returns [Boolean value] : ( 'true' | 'false' );
    public final BONParser.boolean_constant_return boolean_constant() throws RecognitionException {
        BONParser.boolean_constant_return retval = new BONParser.boolean_constant_return();
        retval.start = input.LT(1);

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1294:42: ( 'true' | 'false' )
            int alt139=2;
            int LA139_0 = input.LA(1);

            if ( (LA139_0==90) ) {
                alt139=1;
            }
            else if ( (LA139_0==91) ) {
                alt139=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 139, 0, input);

                throw nvae;
            }
            switch (alt139) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1295:4: 'true'
                    {
                    match(input,90,FOLLOW_90_in_boolean_constant8492); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.value = true; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1297:4: 'false'
                    {
                    match(input,91,FOLLOW_91_in_boolean_constant8503); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.value = false; 
                    }

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
    // $ANTLR end "boolean_constant"

    public static class character_constant_return extends ParserRuleReturnScope {
        public Character value;
    };

    // $ANTLR start "character_constant"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1303:1: character_constant returns [Character value] : cc= CHARACTER_CONSTANT ;
    public final BONParser.character_constant_return character_constant() throws RecognitionException {
        BONParser.character_constant_return retval = new BONParser.character_constant_return();
        retval.start = input.LT(1);

        Token cc=null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1303:46: (cc= CHARACTER_CONSTANT )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1304:2: cc= CHARACTER_CONSTANT
            {
            cc=(Token)match(input,CHARACTER_CONSTANT,FOLLOW_CHARACTER_CONSTANT_in_character_constant8527); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.value = (cc!=null?cc.getText():null).charAt(1); 
            }

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
    // $ANTLR end "character_constant"

    public static class integer_constant_return extends ParserRuleReturnScope {
        public Integer value;
    };

    // $ANTLR start "integer_constant"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1312:1: integer_constant returns [Integer value] : ( sign )? i= INTEGER ;
    public final BONParser.integer_constant_return integer_constant() throws RecognitionException {
        BONParser.integer_constant_return retval = new BONParser.integer_constant_return();
        retval.start = input.LT(1);

        Token i=null;
        BinaryExp.Op sign101 = null;


         boolean negative = false; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1314:1: ( ( sign )? i= INTEGER )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1315:3: ( sign )? i= INTEGER
            {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1315:3: ( sign )?
            int alt140=2;
            int LA140_0 = input.LA(1);

            if ( ((LA140_0>=103 && LA140_0<=104)) ) {
                alt140=1;
            }
            switch (alt140) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1315:4: sign
                    {
                    pushFollow(FOLLOW_sign_in_integer_constant8593);
                    sign101=sign();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if (sign101 == BinaryExp.Op.SUB) negative = true; 
                    }

                    }
                    break;

            }

            i=(Token)match(input,INTEGER,FOLLOW_INTEGER_in_integer_constant8604); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.value = new Integer((i!=null?i.getText():null)); if (negative) retval.value = -retval.value; 
            }

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
    // $ANTLR end "integer_constant"

    public static class real_constant_return extends ParserRuleReturnScope {
        public Double value;
    };

    // $ANTLR start "real_constant"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1320:1: real_constant returns [Double value] : ( sign )? r= REAL ;
    public final BONParser.real_constant_return real_constant() throws RecognitionException {
        BONParser.real_constant_return retval = new BONParser.real_constant_return();
        retval.start = input.LT(1);

        Token r=null;
        BinaryExp.Op sign102 = null;


         boolean negative = false; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1322:1: ( ( sign )? r= REAL )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1323:3: ( sign )? r= REAL
            {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1323:3: ( sign )?
            int alt141=2;
            int LA141_0 = input.LA(1);

            if ( ((LA141_0>=103 && LA141_0<=104)) ) {
                alt141=1;
            }
            switch (alt141) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1323:4: sign
                    {
                    pushFollow(FOLLOW_sign_in_real_constant8649);
                    sign102=sign();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if (sign102 == BinaryExp.Op.SUB) negative = true; 
                    }

                    }
                    break;

            }

            r=(Token)match(input,REAL,FOLLOW_REAL_in_real_constant8661); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.value = new Double((r!=null?r.getText():null)); if (negative) retval.value = -retval.value; 
            }

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
    // $ANTLR end "real_constant"


    // $ANTLR start "dynamic_diagram"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1328:1: dynamic_diagram returns [DynamicDiagram dd] : s= 'dynamic_diagram' (eid= extended_id )? comment 'component' (db= dynamic_block | ) e= 'end' ;
    public final DynamicDiagram dynamic_diagram() throws RecognitionException {
        DynamicDiagram dd = null;

        Token s=null;
        Token e=null;
        BONParser.extended_id_return eid = null;

        List<DynamicComponent> db = null;

        String comment103 = null;


         String id = null; String comment = null; List<DynamicComponent> components = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1334:1: (s= 'dynamic_diagram' (eid= extended_id )? comment 'component' (db= dynamic_block | ) e= 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1335:3: s= 'dynamic_diagram' (eid= extended_id )? comment 'component' (db= dynamic_block | ) e= 'end'
            {
            s=(Token)match(input,92,FOLLOW_92_in_dynamic_diagram8692); if (state.failed) return dd;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1336:3: (eid= extended_id )?
            int alt142=2;
            int LA142_0 = input.LA(1);

            if ( ((LA142_0>=IDENTIFIER && LA142_0<=INTEGER)) ) {
                alt142=1;
            }
            switch (alt142) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1336:4: eid= extended_id
                    {
                    pushFollow(FOLLOW_extended_id_in_dynamic_diagram8700);
                    eid=extended_id();

                    state._fsp--;
                    if (state.failed) return dd;
                    if ( state.backtracking==0 ) {
                       if(isOk()) id = (eid!=null?eid.eid:null); 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_comment_in_dynamic_diagram8710);
            comment103=comment();

            state._fsp--;
            if (state.failed) return dd;
            if ( state.backtracking==0 ) {
               comment = comment103; 
            }
            match(input,55,FOLLOW_55_in_dynamic_diagram8716); if (state.failed) return dd;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1339:3: (db= dynamic_block | )
            int alt143=2;
            int LA143_0 = input.LA(1);

            if ( ((LA143_0>=IDENTIFIER && LA143_0<=INTEGER)||LA143_0==50||(LA143_0>=94 && LA143_0<=97)) ) {
                alt143=1;
            }
            else if ( (LA143_0==25) ) {
                alt143=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return dd;}
                NoViableAltException nvae =
                    new NoViableAltException("", 143, 0, input);

                throw nvae;
            }
            switch (alt143) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1339:5: db= dynamic_block
                    {
                    pushFollow(FOLLOW_dynamic_block_in_dynamic_diagram8725);
                    db=dynamic_block();

                    state._fsp--;
                    if (state.failed) return dd;
                    if ( state.backtracking==0 ) {
                       if(isOk()) components = db; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1341:6: 
                    {
                    if ( state.backtracking==0 ) {
                       components = emptyList(); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_dynamic_diagram8749); if (state.failed) return dd;
            if ( state.backtracking==0 ) {
               if(isOk()) dd = DynamicDiagram.mk(components, id, comment, getSLoc(s,e)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return dd;
    }
    // $ANTLR end "dynamic_diagram"


    // $ANTLR start "dynamic_block"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1347:1: dynamic_block returns [List<DynamicComponent> components] : (dc= dynamic_component )+ ;
    public final List<DynamicComponent> dynamic_block() throws RecognitionException {
        List<DynamicComponent> components = null;

        DynamicComponent dc = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1347:59: ( (dc= dynamic_component )+ )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1348:3: (dc= dynamic_component )+
            {
            if ( state.backtracking==0 ) {
               components = createList(); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1349:3: (dc= dynamic_component )+
            int cnt144=0;
            loop144:
            do {
                int alt144=2;
                int LA144_0 = input.LA(1);

                if ( ((LA144_0>=IDENTIFIER && LA144_0<=INTEGER)||LA144_0==50||(LA144_0>=94 && LA144_0<=97)) ) {
                    alt144=1;
                }


                switch (alt144) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1349:4: dc= dynamic_component
            	    {
            	    pushFollow(FOLLOW_dynamic_component_in_dynamic_block8792);
            	    dc=dynamic_component();

            	    state._fsp--;
            	    if (state.failed) return components;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) components.add(dc); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt144 >= 1 ) break loop144;
            	    if (state.backtracking>0) {state.failed=true; return components;}
                        EarlyExitException eee =
                            new EarlyExitException(144, input);
                        throw eee;
                }
                cnt144++;
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return components;
    }
    // $ANTLR end "dynamic_block"


    // $ANTLR start "dynamic_component"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1352:1: dynamic_component returns [DynamicComponent component] : ( scenario_description | object_group | object_stack | object | message_relation );
    public final DynamicComponent dynamic_component() throws RecognitionException {
        DynamicComponent component = null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1352:56: ( scenario_description | object_group | object_stack | object | message_relation )
            int alt145=5;
            switch ( input.LA(1) ) {
            case 50:
                {
                alt145=1;
                }
                break;
            case 94:
            case 95:
                {
                alt145=2;
                }
                break;
            case 96:
                {
                alt145=3;
                }
                break;
            case 97:
                {
                alt145=4;
                }
                break;
            case IDENTIFIER:
            case INTEGER:
                {
                alt145=5;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return component;}
                NoViableAltException nvae =
                    new NoViableAltException("", 145, 0, input);

                throw nvae;
            }

            switch (alt145) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1353:4: scenario_description
                    {
                    pushFollow(FOLLOW_scenario_description_in_dynamic_component8829);
                    scenario_description();

                    state._fsp--;
                    if (state.failed) return component;

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1354:4: object_group
                    {
                    pushFollow(FOLLOW_object_group_in_dynamic_component8834);
                    object_group();

                    state._fsp--;
                    if (state.failed) return component;

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1355:4: object_stack
                    {
                    pushFollow(FOLLOW_object_stack_in_dynamic_component8840);
                    object_stack();

                    state._fsp--;
                    if (state.failed) return component;

                    }
                    break;
                case 4 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1356:4: object
                    {
                    pushFollow(FOLLOW_object_in_dynamic_component8845);
                    object();

                    state._fsp--;
                    if (state.failed) return component;

                    }
                    break;
                case 5 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1357:4: message_relation
                    {
                    pushFollow(FOLLOW_message_relation_in_dynamic_component8850);
                    message_relation();

                    state._fsp--;
                    if (state.failed) return component;

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
        return component;
    }
    // $ANTLR end "dynamic_component"


    // $ANTLR start "scenario_description"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1360:1: scenario_description returns [ScenarioDescription description] : s= 'scenario' scenario_name comment 'action' la= labelled_actions e= 'end' ;
    public final ScenarioDescription scenario_description() throws RecognitionException {
        ScenarioDescription description = null;

        Token s=null;
        Token e=null;
        List<LabelledAction> la = null;

        String comment104 = null;

        String scenario_name105 = null;


         String comment = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1364:1: (s= 'scenario' scenario_name comment 'action' la= labelled_actions e= 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1365:3: s= 'scenario' scenario_name comment 'action' la= labelled_actions e= 'end'
            {
            s=(Token)match(input,50,FOLLOW_50_in_scenario_description8878); if (state.failed) return description;
            pushFollow(FOLLOW_scenario_name_in_scenario_description8880);
            scenario_name105=scenario_name();

            state._fsp--;
            if (state.failed) return description;
            pushFollow(FOLLOW_comment_in_scenario_description8885);
            comment104=comment();

            state._fsp--;
            if (state.failed) return description;
            if ( state.backtracking==0 ) {
               comment = comment104; 
            }
            match(input,93,FOLLOW_93_in_scenario_description8891); if (state.failed) return description;
            pushFollow(FOLLOW_labelled_actions_in_scenario_description8898);
            la=labelled_actions();

            state._fsp--;
            if (state.failed) return description;
            e=(Token)match(input,25,FOLLOW_25_in_scenario_description8905); if (state.failed) return description;
            if ( state.backtracking==0 ) {
               if(isOk()) description = ScenarioDescription.mk(scenario_name105, la, comment, getSLoc(s,e)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return description;
    }
    // $ANTLR end "scenario_description"


    // $ANTLR start "labelled_actions"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1373:1: labelled_actions returns [List<LabelledAction> actions] : (la= labelled_action )+ ;
    public final List<LabelledAction> labelled_actions() throws RecognitionException {
        List<LabelledAction> actions = null;

        LabelledAction la = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1373:57: ( (la= labelled_action )+ )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1374:3: (la= labelled_action )+
            {
            if ( state.backtracking==0 ) {
               actions = createList(); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1375:3: (la= labelled_action )+
            int cnt146=0;
            loop146:
            do {
                int alt146=2;
                int LA146_0 = input.LA(1);

                if ( (LA146_0==MANIFEST_STRING) ) {
                    alt146=1;
                }


                switch (alt146) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1375:4: la= labelled_action
            	    {
            	    pushFollow(FOLLOW_labelled_action_in_labelled_actions8953);
            	    la=labelled_action();

            	    state._fsp--;
            	    if (state.failed) return actions;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) actions.add(la); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt146 >= 1 ) break loop146;
            	    if (state.backtracking>0) {state.failed=true; return actions;}
                        EarlyExitException eee =
                            new EarlyExitException(146, input);
                        throw eee;
                }
                cnt146++;
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return actions;
    }
    // $ANTLR end "labelled_actions"


    // $ANTLR start "labelled_action"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1378:1: labelled_action returns [LabelledAction action] : al= action_label ad= action_description ;
    public final LabelledAction labelled_action() throws RecognitionException {
        LabelledAction action = null;

        BONParser.action_label_return al = null;

        BONParser.action_description_return ad = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1378:49: (al= action_label ad= action_description )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1379:3: al= action_label ad= action_description
            {
            pushFollow(FOLLOW_action_label_in_labelled_action8994);
            al=action_label();

            state._fsp--;
            if (state.failed) return action;
            pushFollow(FOLLOW_action_description_in_labelled_action8998);
            ad=action_description();

            state._fsp--;
            if (state.failed) return action;
            if ( state.backtracking==0 ) {
               if(isOk()) action = LabelledAction.mk((al!=null?al.label:null), (ad!=null?ad.description:null), getSLoc((al!=null?((Token)al.start):null),(ad!=null?((Token)ad.stop):null))); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return action;
    }
    // $ANTLR end "labelled_action"

    public static class action_label_return extends ParserRuleReturnScope {
        public String label;
    };

    // $ANTLR start "action_label"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1383:1: action_label returns [String label] : m= MANIFEST_STRING ;
    public final BONParser.action_label_return action_label() throws RecognitionException {
        BONParser.action_label_return retval = new BONParser.action_label_return();
        retval.start = input.LT(1);

        Token m=null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1383:37: (m= MANIFEST_STRING )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1384:3: m= MANIFEST_STRING
            {
            m=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_action_label9037); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.label = (m!=null?m.getText():null); 
            }

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
    // $ANTLR end "action_label"

    public static class action_description_return extends ParserRuleReturnScope {
        public String description;
    };

    // $ANTLR start "action_description"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1388:1: action_description returns [String description] : m= manifest_textblock ;
    public final BONParser.action_description_return action_description() throws RecognitionException {
        BONParser.action_description_return retval = new BONParser.action_description_return();
        retval.start = input.LT(1);

        BONParser.manifest_textblock_return m = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1388:49: (m= manifest_textblock )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1389:3: m= manifest_textblock
            {
            pushFollow(FOLLOW_manifest_textblock_in_action_description9072);
            m=manifest_textblock();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.description = (m!=null?input.toString(m.start,m.stop):null); 
            }

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
    // $ANTLR end "action_description"


    // $ANTLR start "scenario_name"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1393:1: scenario_name returns [String name] : m= manifest_textblock ;
    public final String scenario_name() throws RecognitionException {
        String name = null;

        BONParser.manifest_textblock_return m = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1393:37: (m= manifest_textblock )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1394:3: m= manifest_textblock
            {
            pushFollow(FOLLOW_manifest_textblock_in_scenario_name9113);
            m=manifest_textblock();

            state._fsp--;
            if (state.failed) return name;
            if ( state.backtracking==0 ) {
               if(isOk()) name = (m!=null?input.toString(m.start,m.stop):null); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return name;
    }
    // $ANTLR end "scenario_name"


    // $ANTLR start "object_group"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1398:1: object_group returns [ObjectGroup group] : (n= 'nameless' | ) s= 'object_group' group_name comment (gc= group_components | ) ;
    public final ObjectGroup object_group() throws RecognitionException {
        ObjectGroup group = null;

        Token n=null;
        Token s=null;
        List<DynamicComponent> gc = null;

        BONParser.group_name_return group_name106 = null;

        String comment107 = null;


         String comment = null; List<DynamicComponent> components = null; 
                ObjectGroup.Nameless nameless = ObjectGroup.Nameless.NOTNAMELESS; 
                Token start = null; Token end = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1404:1: ( (n= 'nameless' | ) s= 'object_group' group_name comment (gc= group_components | ) )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1405:3: (n= 'nameless' | ) s= 'object_group' group_name comment (gc= group_components | )
            {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1405:3: (n= 'nameless' | )
            int alt147=2;
            int LA147_0 = input.LA(1);

            if ( (LA147_0==94) ) {
                alt147=1;
            }
            else if ( (LA147_0==95) ) {
                alt147=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return group;}
                NoViableAltException nvae =
                    new NoViableAltException("", 147, 0, input);

                throw nvae;
            }
            switch (alt147) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1405:6: n= 'nameless'
                    {
                    n=(Token)match(input,94,FOLLOW_94_in_object_group9146); if (state.failed) return group;
                    if ( state.backtracking==0 ) {
                       nameless = ObjectGroup.Nameless.NAMELESS; start = n; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1407:6: 
                    {
                    if ( state.backtracking==0 ) {
                       nameless = ObjectGroup.Nameless.NOTNAMELESS; 
                    }

                    }
                    break;

            }

            s=(Token)match(input,95,FOLLOW_95_in_object_group9171); if (state.failed) return group;
            if ( state.backtracking==0 ) {
               if (start==null) start=s; 
            }
            pushFollow(FOLLOW_group_name_in_object_group9177);
            group_name106=group_name();

            state._fsp--;
            if (state.failed) return group;
            if ( state.backtracking==0 ) {
               end = (group_name106!=null?((Token)group_name106.stop):null); 
            }
            pushFollow(FOLLOW_comment_in_object_group9186);
            comment107=comment();

            state._fsp--;
            if (state.failed) return group;
            if ( state.backtracking==0 ) {
               comment = comment107; 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1413:3: (gc= group_components | )
            int alt148=2;
            int LA148_0 = input.LA(1);

            if ( (LA148_0==55) ) {
                alt148=1;
            }
            else if ( ((LA148_0>=IDENTIFIER && LA148_0<=INTEGER)||LA148_0==25||LA148_0==50||(LA148_0>=94 && LA148_0<=97)) ) {
                alt148=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return group;}
                NoViableAltException nvae =
                    new NoViableAltException("", 148, 0, input);

                throw nvae;
            }
            switch (alt148) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1413:6: gc= group_components
                    {
                    pushFollow(FOLLOW_group_components_in_object_group9197);
                    gc=group_components();

                    state._fsp--;
                    if (state.failed) return group;
                    if ( state.backtracking==0 ) {
                       if(isOk()) components = gc; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1415:6: 
                    {
                    if ( state.backtracking==0 ) {
                       components = emptyList(); 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               if(isOk()) group = ObjectGroup.mk(nameless, (group_name106!=null?input.toString(group_name106.start,group_name106.stop):null), components, comment, getSLoc(start,end)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return group;
    }
    // $ANTLR end "object_group"


    // $ANTLR start "group_components"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1420:1: group_components returns [List<DynamicComponent> components] : 'component' dynamic_block 'end' ;
    public final List<DynamicComponent> group_components() throws RecognitionException {
        List<DynamicComponent> components = null;

        List<DynamicComponent> dynamic_block108 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1420:62: ( 'component' dynamic_block 'end' )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1421:3: 'component' dynamic_block 'end'
            {
            match(input,55,FOLLOW_55_in_group_components9248); if (state.failed) return components;
            pushFollow(FOLLOW_dynamic_block_in_group_components9250);
            dynamic_block108=dynamic_block();

            state._fsp--;
            if (state.failed) return components;
            match(input,25,FOLLOW_25_in_group_components9252); if (state.failed) return components;
            if ( state.backtracking==0 ) {
               if(isOk()) components = dynamic_block108; 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return components;
    }
    // $ANTLR end "group_components"


    // $ANTLR start "object_stack"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1425:1: object_stack returns [ObjectStack stack] : s= 'object_stack' n= object_name comment ;
    public final ObjectStack object_stack() throws RecognitionException {
        ObjectStack stack = null;

        Token s=null;
        BONParser.object_name_return n = null;

        String comment109 = null;


         String comment = null; Token end = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1427:1: (s= 'object_stack' n= object_name comment )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1428:3: s= 'object_stack' n= object_name comment
            {
            s=(Token)match(input,96,FOLLOW_96_in_object_stack9297); if (state.failed) return stack;
            pushFollow(FOLLOW_object_name_in_object_stack9304);
            n=object_name();

            state._fsp--;
            if (state.failed) return stack;
            if ( state.backtracking==0 ) {
               end = (n!=null?((Token)n.stop):null); 
            }
            pushFollow(FOLLOW_comment_in_object_stack9313);
            comment109=comment();

            state._fsp--;
            if (state.failed) return stack;
            if ( state.backtracking==0 ) {
               comment = comment109; 
            }
            if ( state.backtracking==0 ) {
               if(isOk()) stack = ObjectStack.mk((n!=null?n.name:null), comment, getSLoc(s,end)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return stack;
    }
    // $ANTLR end "object_stack"


    // $ANTLR start "object"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1435:1: object returns [ObjectInstance object] : s= 'object' n= object_name comment ;
    public final ObjectInstance object() throws RecognitionException {
        ObjectInstance object = null;

        Token s=null;
        BONParser.object_name_return n = null;

        String comment110 = null;


         String comment = null; Token end = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1437:1: (s= 'object' n= object_name comment )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1438:3: s= 'object' n= object_name comment
            {
            s=(Token)match(input,97,FOLLOW_97_in_object9358); if (state.failed) return object;
            pushFollow(FOLLOW_object_name_in_object9365);
            n=object_name();

            state._fsp--;
            if (state.failed) return object;
            if ( state.backtracking==0 ) {
               end = (n!=null?((Token)n.stop):null); 
            }
            pushFollow(FOLLOW_comment_in_object9374);
            comment110=comment();

            state._fsp--;
            if (state.failed) return object;
            if ( state.backtracking==0 ) {
               comment = comment110; 
            }
            if ( state.backtracking==0 ) {
               if(isOk()) object = ObjectInstance.mk((n!=null?n.name:null), comment, getSLoc(s,end)); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return object;
    }
    // $ANTLR end "object"


    // $ANTLR start "message_relation"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1445:1: message_relation : caller 'calls' receiver ( message_label )? ;
    public final void message_relation() throws RecognitionException {
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1447:19: ( caller 'calls' receiver ( message_label )? )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1447:22: caller 'calls' receiver ( message_label )?
            {
            pushFollow(FOLLOW_caller_in_message_relation9395);
            caller();

            state._fsp--;
            if (state.failed) return ;
            match(input,98,FOLLOW_98_in_message_relation9397); if (state.failed) return ;
            pushFollow(FOLLOW_receiver_in_message_relation9399);
            receiver();

            state._fsp--;
            if (state.failed) return ;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1447:46: ( message_label )?
            int alt149=2;
            int LA149_0 = input.LA(1);

            if ( (LA149_0==MANIFEST_STRING) ) {
                alt149=1;
            }
            switch (alt149) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1447:47: message_label
                    {
                    pushFollow(FOLLOW_message_label_in_message_relation9402);
                    message_label();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }


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
    // $ANTLR end "message_relation"


    // $ANTLR start "caller"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1450:1: caller : dynamic_ref ;
    public final void caller() throws RecognitionException {
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1450:9: ( dynamic_ref )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1450:12: dynamic_ref
            {
            pushFollow(FOLLOW_dynamic_ref_in_caller9434);
            dynamic_ref();

            state._fsp--;
            if (state.failed) return ;

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
    // $ANTLR end "caller"


    // $ANTLR start "receiver"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1453:1: receiver : dynamic_ref ;
    public final void receiver() throws RecognitionException {
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1453:11: ( dynamic_ref )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1453:14: dynamic_ref
            {
            pushFollow(FOLLOW_dynamic_ref_in_receiver9454);
            dynamic_ref();

            state._fsp--;
            if (state.failed) return ;

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
    // $ANTLR end "receiver"


    // $ANTLR start "dynamic_ref"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1460:1: dynamic_ref : extended_id ( '.' extended_id )* ;
    public final void dynamic_ref() throws RecognitionException {
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1460:14: ( extended_id ( '.' extended_id )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1460:17: extended_id ( '.' extended_id )*
            {
            pushFollow(FOLLOW_extended_id_in_dynamic_ref9480);
            extended_id();

            state._fsp--;
            if (state.failed) return ;
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1460:29: ( '.' extended_id )*
            loop150:
            do {
                int alt150=2;
                int LA150_0 = input.LA(1);

                if ( (LA150_0==70) ) {
                    alt150=1;
                }


                switch (alt150) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1460:30: '.' extended_id
            	    {
            	    match(input,70,FOLLOW_70_in_dynamic_ref9483); if (state.failed) return ;
            	    pushFollow(FOLLOW_extended_id_in_dynamic_ref9485);
            	    extended_id();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop150;
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
    // $ANTLR end "dynamic_ref"


    // $ANTLR start "dynamic_component_name"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1469:1: dynamic_component_name : ( ( IDENTIFIER ( '.' extended_id )? ) | INTEGER );
    public final void dynamic_component_name() throws RecognitionException {
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1469:25: ( ( IDENTIFIER ( '.' extended_id )? ) | INTEGER )
            int alt152=2;
            int LA152_0 = input.LA(1);

            if ( (LA152_0==IDENTIFIER) ) {
                alt152=1;
            }
            else if ( (LA152_0==INTEGER) ) {
                alt152=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 152, 0, input);

                throw nvae;
            }
            switch (alt152) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1470:4: ( IDENTIFIER ( '.' extended_id )? )
                    {
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1470:4: ( IDENTIFIER ( '.' extended_id )? )
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1470:5: IDENTIFIER ( '.' extended_id )?
                    {
                    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_dynamic_component_name9516); if (state.failed) return ;
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1470:16: ( '.' extended_id )?
                    int alt151=2;
                    int LA151_0 = input.LA(1);

                    if ( (LA151_0==70) ) {
                        alt151=1;
                    }
                    switch (alt151) {
                        case 1 :
                            // /home/fintan/workspaces/bon/bonc/src/BON.g:1470:17: '.' extended_id
                            {
                            match(input,70,FOLLOW_70_in_dynamic_component_name9519); if (state.failed) return ;
                            pushFollow(FOLLOW_extended_id_in_dynamic_component_name9521);
                            extended_id();

                            state._fsp--;
                            if (state.failed) return ;

                            }
                            break;

                    }


                    }


                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1471:4: INTEGER
                    {
                    match(input,INTEGER,FOLLOW_INTEGER_in_dynamic_component_name9530); if (state.failed) return ;

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
    // $ANTLR end "dynamic_component_name"

    public static class object_name_return extends ParserRuleReturnScope {
        public ObjectName name;
    };

    // $ANTLR start "object_name"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1474:1: object_name returns [ObjectName name] : n= class_name ( '.' e= extended_id )? ;
    public final BONParser.object_name_return object_name() throws RecognitionException {
        BONParser.object_name_return retval = new BONParser.object_name_return();
        retval.start = input.LT(1);

        BONParser.class_name_return n = null;

        BONParser.extended_id_return e = null;


         String id = null; Token end = null; 
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1476:1: (n= class_name ( '.' e= extended_id )? )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1477:3: n= class_name ( '.' e= extended_id )?
            {
            pushFollow(FOLLOW_class_name_in_object_name9553);
            n=class_name();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               end = (n!=null?((Token)n.stop):null); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1479:3: ( '.' e= extended_id )?
            int alt153=2;
            int LA153_0 = input.LA(1);

            if ( (LA153_0==70) ) {
                alt153=1;
            }
            switch (alt153) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1479:4: '.' e= extended_id
                    {
                    match(input,70,FOLLOW_70_in_object_name9563); if (state.failed) return retval;
                    pushFollow(FOLLOW_extended_id_in_object_name9567);
                    e=extended_id();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       id = (e!=null?e.eid:null); end=(e!=null?((Token)e.stop):null); 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               if(isOk()) retval.name = ObjectName.mk((n!=null?n.name:null), id, getSLoc((n!=null?((Token)n.start):null),end)); 
            }

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
    // $ANTLR end "object_name"

    public static class group_name_return extends ParserRuleReturnScope {
        public String name;
    };

    // $ANTLR start "group_name"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1483:1: group_name returns [String name] : e= extended_id ;
    public final BONParser.group_name_return group_name() throws RecognitionException {
        BONParser.group_name_return retval = new BONParser.group_name_return();
        retval.start = input.LT(1);

        BONParser.extended_id_return e = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1483:34: (e= extended_id )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1484:3: e= extended_id
            {
            pushFollow(FOLLOW_extended_id_in_group_name9607);
            e=extended_id();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.name = (e!=null?e.eid:null); 
            }

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
    // $ANTLR end "group_name"


    // $ANTLR start "message_label"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1488:1: message_label returns [String label] : m= MANIFEST_STRING ;
    public final String message_label() throws RecognitionException {
        String label = null;

        Token m=null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1488:38: (m= MANIFEST_STRING )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1489:3: m= MANIFEST_STRING
            {
            m=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_message_label9640); if (state.failed) return label;
            if ( state.backtracking==0 ) {
               if(isOk()) label = (m!=null?m.getText():null); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return label;
    }
    // $ANTLR end "message_label"


    // $ANTLR start "notational_tuning"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1493:1: notational_tuning : ( change_string_marks | change_concatenator | change_prefix );
    public final void notational_tuning() throws RecognitionException {
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1497:19: ( change_string_marks | change_concatenator | change_prefix )
            int alt154=3;
            switch ( input.LA(1) ) {
            case 99:
                {
                alt154=1;
                }
                break;
            case 100:
                {
                alt154=2;
                }
                break;
            case 101:
                {
                alt154=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 154, 0, input);

                throw nvae;
            }

            switch (alt154) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1498:4: change_string_marks
                    {
                    pushFollow(FOLLOW_change_string_marks_in_notational_tuning9664);
                    change_string_marks();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1499:4: change_concatenator
                    {
                    pushFollow(FOLLOW_change_concatenator_in_notational_tuning9670);
                    change_concatenator();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1500:4: change_prefix
                    {
                    pushFollow(FOLLOW_change_prefix_in_notational_tuning9675);
                    change_prefix();

                    state._fsp--;
                    if (state.failed) return ;

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
    // $ANTLR end "notational_tuning"


    // $ANTLR start "change_string_marks"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1503:1: change_string_marks : 'string_marks' MANIFEST_STRING MANIFEST_STRING ;
    public final void change_string_marks() throws RecognitionException {
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1503:22: ( 'string_marks' MANIFEST_STRING MANIFEST_STRING )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1504:3: 'string_marks' MANIFEST_STRING MANIFEST_STRING
            {
            match(input,99,FOLLOW_99_in_change_string_marks9690); if (state.failed) return ;
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_string_marks9692); if (state.failed) return ;
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_string_marks9694); if (state.failed) return ;

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
    // $ANTLR end "change_string_marks"


    // $ANTLR start "change_concatenator"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1507:1: change_concatenator : 'concatenator' MANIFEST_STRING ;
    public final void change_concatenator() throws RecognitionException {
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1507:22: ( 'concatenator' MANIFEST_STRING )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1508:3: 'concatenator' MANIFEST_STRING
            {
            match(input,100,FOLLOW_100_in_change_concatenator9728); if (state.failed) return ;
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_concatenator9730); if (state.failed) return ;

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
    // $ANTLR end "change_concatenator"


    // $ANTLR start "change_prefix"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1511:1: change_prefix : 'keyword_prefix' MANIFEST_STRING ;
    public final void change_prefix() throws RecognitionException {
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1511:16: ( 'keyword_prefix' MANIFEST_STRING )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1512:3: 'keyword_prefix' MANIFEST_STRING
            {
            match(input,101,FOLLOW_101_in_change_prefix9764); if (state.failed) return ;
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_prefix9766); if (state.failed) return ;

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
    // $ANTLR end "change_prefix"

    public static class expression_return extends ParserRuleReturnScope {
        public Expression exp;
    };

    // $ANTLR start "expression"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1515:1: expression returns [Expression exp] : (e= equivalence_expression | q= quantification );
    public final BONParser.expression_return expression() throws RecognitionException {
        BONParser.expression_return retval = new BONParser.expression_return();
        retval.start = input.LT(1);

        Expression e = null;

        Quantification q = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1519:37: (e= equivalence_expression | q= quantification )
            int alt155=2;
            int LA155_0 = input.LA(1);

            if ( ((LA155_0>=MANIFEST_STRING && LA155_0<=REAL)||LA155_0==42||LA155_0==62||LA155_0==74||(LA155_0>=88 && LA155_0<=91)||(LA155_0>=103 && LA155_0<=104)||(LA155_0>=108 && LA155_0<=110)) ) {
                alt155=1;
            }
            else if ( ((LA155_0>=82 && LA155_0<=83)) ) {
                alt155=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 155, 0, input);

                throw nvae;
            }
            switch (alt155) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1520:4: e= equivalence_expression
                    {
                    pushFollow(FOLLOW_equivalence_expression_in_expression9792);
                    e=equivalence_expression();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.exp = e; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1522:4: q= quantification
                    {
                    pushFollow(FOLLOW_quantification_in_expression9806);
                    q=quantification();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.exp = q; 
                    }

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
    // $ANTLR end "expression"


    // $ANTLR start "equivalence_expression"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1526:1: equivalence_expression returns [Expression exp] : l= implies_expression ( '<->' r= implies_expression )* ;
    public final Expression equivalence_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        Expression r = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1526:49: (l= implies_expression ( '<->' r= implies_expression )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1527:3: l= implies_expression ( '<->' r= implies_expression )*
            {
            pushFollow(FOLLOW_implies_expression_in_equivalence_expression9828);
            l=implies_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp = l; 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1529:3: ( '<->' r= implies_expression )*
            loop156:
            do {
                int alt156=2;
                int LA156_0 = input.LA(1);

                if ( (LA156_0==102) ) {
                    alt156=1;
                }


                switch (alt156) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1529:4: '<->' r= implies_expression
            	    {
            	    match(input,102,FOLLOW_102_in_equivalence_expression9838); if (state.failed) return exp;
            	    pushFollow(FOLLOW_implies_expression_in_equivalence_expression9842);
            	    r=implies_expression();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    if ( state.backtracking==0 ) {
            	       if (r == null) throw new RecognitionException();
            	           if(isOk()) exp = BinaryExp.mk(BinaryExp.Op.EQUIV, exp, r, getSLoc(exp.getLocation(),r.getLocation())); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop156;
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
        return exp;
    }
    // $ANTLR end "equivalence_expression"


    // $ANTLR start "implies_expression"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1536:1: implies_expression returns [Expression exp] : l= and_or_xor_expression ( '->' r= implies_expression )? ;
    public final Expression implies_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        Expression r = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1536:45: (l= and_or_xor_expression ( '->' r= implies_expression )? )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1537:3: l= and_or_xor_expression ( '->' r= implies_expression )?
            {
            pushFollow(FOLLOW_and_or_xor_expression_in_implies_expression9870);
            l=and_or_xor_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp = l; 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1539:3: ( '->' r= implies_expression )?
            int alt157=2;
            int LA157_0 = input.LA(1);

            if ( (LA157_0==65) ) {
                alt157=1;
            }
            switch (alt157) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1539:4: '->' r= implies_expression
                    {
                    match(input,65,FOLLOW_65_in_implies_expression9880); if (state.failed) return exp;
                    pushFollow(FOLLOW_implies_expression_in_implies_expression9884);
                    r=implies_expression();

                    state._fsp--;
                    if (state.failed) return exp;
                    if ( state.backtracking==0 ) {
                       if (r == null) throw new RecognitionException();
                           if(isOk()) exp = BinaryExp.mk(BinaryExp.Op.IMPLIES, exp, r, getSLoc(exp.getLocation(),r.getLocation())); 
                    }

                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return exp;
    }
    // $ANTLR end "implies_expression"


    // $ANTLR start "and_or_xor_expression"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1545:1: and_or_xor_expression returns [Expression exp] : l= comparison_expression (op= and_or_xor_op r= comparison_expression )* ;
    public final Expression and_or_xor_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        BinaryExp.Op op = null;

        Expression r = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1545:48: (l= comparison_expression (op= and_or_xor_op r= comparison_expression )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1546:3: l= comparison_expression (op= and_or_xor_op r= comparison_expression )*
            {
            pushFollow(FOLLOW_comparison_expression_in_and_or_xor_expression9911);
            l=comparison_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp = l; 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1548:3: (op= and_or_xor_op r= comparison_expression )*
            loop158:
            do {
                int alt158=2;
                int LA158_0 = input.LA(1);

                if ( ((LA158_0>=105 && LA158_0<=107)) ) {
                    alt158=1;
                }


                switch (alt158) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1548:5: op= and_or_xor_op r= comparison_expression
            	    {
            	    pushFollow(FOLLOW_and_or_xor_op_in_and_or_xor_expression9924);
            	    op=and_or_xor_op();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    pushFollow(FOLLOW_comparison_expression_in_and_or_xor_expression9928);
            	    r=comparison_expression();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    if ( state.backtracking==0 ) {
            	       if (r == null) throw new RecognitionException();
            	           if(isOk()) exp = BinaryExp.mk(op, exp, r, getSLoc(exp.getLocation(),r.getLocation())); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop158;
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
        return exp;
    }
    // $ANTLR end "and_or_xor_expression"


    // $ANTLR start "comparison_expression"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1554:1: comparison_expression returns [Expression exp] : l= add_sub_expression (op= comparison_op r= add_sub_expression )* ;
    public final Expression comparison_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        BinaryExp.Op op = null;

        Expression r = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1554:48: (l= add_sub_expression (op= comparison_op r= add_sub_expression )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1555:3: l= add_sub_expression (op= comparison_op r= add_sub_expression )*
            {
            pushFollow(FOLLOW_add_sub_expression_in_comparison_expression9956);
            l=add_sub_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp = l; 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1557:3: (op= comparison_op r= add_sub_expression )*
            loop159:
            do {
                int alt159=2;
                int LA159_0 = input.LA(1);

                if ( (LA159_0==34||LA159_0==86||(LA159_0>=110 && LA159_0<=116)) ) {
                    alt159=1;
                }


                switch (alt159) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1557:4: op= comparison_op r= add_sub_expression
            	    {
            	    pushFollow(FOLLOW_comparison_op_in_comparison_expression9968);
            	    op=comparison_op();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    pushFollow(FOLLOW_add_sub_expression_in_comparison_expression9973);
            	    r=add_sub_expression();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    if ( state.backtracking==0 ) {
            	       if (r == null) throw new RecognitionException();
            	           if(isOk()) exp = BinaryExp.mk(op, exp, r, getSLoc(exp.getLocation(),r.getLocation())); 
            	         
            	    }

            	    }
            	    break;

            	default :
            	    break loop159;
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
        return exp;
    }
    // $ANTLR end "comparison_expression"


    // $ANTLR start "add_sub_expression"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1564:1: add_sub_expression returns [Expression exp] : l= mul_div_expression (op= add_sub_op r= mul_div_expression )* ;
    public final Expression add_sub_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        BinaryExp.Op op = null;

        Expression r = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1564:45: (l= mul_div_expression (op= add_sub_op r= mul_div_expression )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1565:3: l= mul_div_expression (op= add_sub_op r= mul_div_expression )*
            {
            pushFollow(FOLLOW_mul_div_expression_in_add_sub_expression10001);
            l=mul_div_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp = l; 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1567:3: (op= add_sub_op r= mul_div_expression )*
            loop160:
            do {
                int alt160=2;
                int LA160_0 = input.LA(1);

                if ( ((LA160_0>=103 && LA160_0<=104)) ) {
                    alt160=1;
                }


                switch (alt160) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1567:4: op= add_sub_op r= mul_div_expression
            	    {
            	    pushFollow(FOLLOW_add_sub_op_in_add_sub_expression10013);
            	    op=add_sub_op();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    pushFollow(FOLLOW_mul_div_expression_in_add_sub_expression10017);
            	    r=mul_div_expression();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    if ( state.backtracking==0 ) {
            	       if (r == null) throw new RecognitionException();
            	           if(isOk()) exp = BinaryExp.mk(op, exp, r, getSLoc(exp.getLocation(),r.getLocation())); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop160;
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
        return exp;
    }
    // $ANTLR end "add_sub_expression"


    // $ANTLR start "mul_div_expression"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1573:1: mul_div_expression returns [Expression exp] : l= mod_pow_expression (op= mul_div_op r= mod_pow_expression )* ;
    public final Expression mul_div_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        BinaryExp.Op op = null;

        Expression r = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1573:45: (l= mod_pow_expression (op= mul_div_op r= mod_pow_expression )* )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1574:3: l= mod_pow_expression (op= mul_div_op r= mod_pow_expression )*
            {
            pushFollow(FOLLOW_mod_pow_expression_in_mul_div_expression10045);
            l=mod_pow_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp = l; 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1576:3: (op= mul_div_op r= mod_pow_expression )*
            loop161:
            do {
                int alt161=2;
                int LA161_0 = input.LA(1);

                if ( ((LA161_0>=117 && LA161_0<=119)) ) {
                    alt161=1;
                }


                switch (alt161) {
            	case 1 :
            	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1576:4: op= mul_div_op r= mod_pow_expression
            	    {
            	    pushFollow(FOLLOW_mul_div_op_in_mul_div_expression10057);
            	    op=mul_div_op();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    pushFollow(FOLLOW_mod_pow_expression_in_mul_div_expression10061);
            	    r=mod_pow_expression();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    if ( state.backtracking==0 ) {
            	       if (r == null) throw new RecognitionException();
            	           if(isOk()) exp = BinaryExp.mk(op, exp, r, getSLoc(exp.getLocation(),r.getLocation())); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop161;
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
        return exp;
    }
    // $ANTLR end "mul_div_expression"


    // $ANTLR start "mod_pow_expression"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1583:1: mod_pow_expression returns [Expression exp] : l= lowest_expression (op= mod_pow_op r= mod_pow_expression )? ;
    public final Expression mod_pow_expression() throws RecognitionException {
        Expression exp = null;

        BONParser.lowest_expression_return l = null;

        BinaryExp.Op op = null;

        Expression r = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1583:45: (l= lowest_expression (op= mod_pow_op r= mod_pow_expression )? )
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1584:3: l= lowest_expression (op= mod_pow_op r= mod_pow_expression )?
            {
            pushFollow(FOLLOW_lowest_expression_in_mod_pow_expression10090);
            l=lowest_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp = (l!=null?l.exp:null); 
            }
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1586:3: (op= mod_pow_op r= mod_pow_expression )?
            int alt162=2;
            int LA162_0 = input.LA(1);

            if ( (LA162_0==77||LA162_0==120) ) {
                alt162=1;
            }
            switch (alt162) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1586:4: op= mod_pow_op r= mod_pow_expression
                    {
                    pushFollow(FOLLOW_mod_pow_op_in_mod_pow_expression10102);
                    op=mod_pow_op();

                    state._fsp--;
                    if (state.failed) return exp;
                    pushFollow(FOLLOW_mod_pow_expression_in_mod_pow_expression10106);
                    r=mod_pow_expression();

                    state._fsp--;
                    if (state.failed) return exp;
                    if ( state.backtracking==0 ) {
                       if (r == null) throw new RecognitionException();
                           if(isOk()) exp = BinaryExp.mk(op, exp, r, getSLoc(exp.getLocation(),r.getLocation())); 
                    }

                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return exp;
    }
    // $ANTLR end "mod_pow_expression"

    public static class lowest_expression_return extends ParserRuleReturnScope {
        public Expression exp;
    };

    // $ANTLR start "lowest_expression"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1592:1: lowest_expression returns [Expression exp] : ( ( constant )=> constant ( ( '.' cc= call_chain ) | ) | unary le= lowest_expression | s= '(' e= expression ')' ( ( '.' cc= call_chain ) | ) | cc= call_chain );
    public final BONParser.lowest_expression_return lowest_expression() throws RecognitionException {
        BONParser.lowest_expression_return retval = new BONParser.lowest_expression_return();
        retval.start = input.LT(1);

        Token s=null;
        BONParser.call_chain_return cc = null;

        BONParser.lowest_expression_return le = null;

        BONParser.expression_return e = null;

        BONParser.constant_return constant111 = null;

        BONParser.unary_return unary112 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1592:44: ( ( constant )=> constant ( ( '.' cc= call_chain ) | ) | unary le= lowest_expression | s= '(' e= expression ')' ( ( '.' cc= call_chain ) | ) | cc= call_chain )
            int alt165=4;
            alt165 = dfa165.predict(input);
            switch (alt165) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1593:5: ( constant )=> constant ( ( '.' cc= call_chain ) | )
                    {
                    pushFollow(FOLLOW_constant_in_lowest_expression10139);
                    constant111=constant();

                    state._fsp--;
                    if (state.failed) return retval;
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1594:5: ( ( '.' cc= call_chain ) | )
                    int alt163=2;
                    int LA163_0 = input.LA(1);

                    if ( (LA163_0==70) ) {
                        alt163=1;
                    }
                    else if ( (LA163_0==25||(LA163_0>=33 && LA163_0<=35)||LA163_0==43||LA163_0==63||LA163_0==65||(LA163_0>=76 && LA163_0<=77)||(LA163_0>=84 && LA163_0<=86)||(LA163_0>=102 && LA163_0<=107)||(LA163_0>=110 && LA163_0<=120)) ) {
                        alt163=2;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return retval;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 163, 0, input);

                        throw nvae;
                    }
                    switch (alt163) {
                        case 1 :
                            // /home/fintan/workspaces/bon/bonc/src/BON.g:1594:7: ( '.' cc= call_chain )
                            {
                            // /home/fintan/workspaces/bon/bonc/src/BON.g:1594:7: ( '.' cc= call_chain )
                            // /home/fintan/workspaces/bon/bonc/src/BON.g:1594:8: '.' cc= call_chain
                            {
                            match(input,70,FOLLOW_70_in_lowest_expression10148); if (state.failed) return retval;
                            pushFollow(FOLLOW_call_chain_in_lowest_expression10152);
                            cc=call_chain();

                            state._fsp--;
                            if (state.failed) return retval;
                            if ( state.backtracking==0 ) {
                               if(isOk()) retval.exp = CallExp.mk((constant111!=null?constant111.constant:null), (cc!=null?cc.calls:null), getSLoc((constant111!=null?((Token)constant111.start):null),(cc!=null?((Token)cc.stop):null))); 
                            }

                            }


                            }
                            break;
                        case 2 :
                            // /home/fintan/workspaces/bon/bonc/src/BON.g:1598:7: 
                            {
                            if ( state.backtracking==0 ) {
                               if(isOk()) retval.exp = (constant111!=null?constant111.constant:null); 
                            }

                            }
                            break;

                    }


                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1600:4: unary le= lowest_expression
                    {
                    pushFollow(FOLLOW_unary_in_lowest_expression10202);
                    unary112=unary();

                    state._fsp--;
                    if (state.failed) return retval;
                    pushFollow(FOLLOW_lowest_expression_in_lowest_expression10206);
                    le=lowest_expression();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.exp = UnaryExp.mk((unary112!=null?unary112.op:null), (le!=null?le.exp:null), getSLoc((unary112!=null?((Token)unary112.start):null),(le!=null?((Token)le.stop):null))); 
                    }

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1602:4: s= '(' e= expression ')' ( ( '.' cc= call_chain ) | )
                    {
                    s=(Token)match(input,42,FOLLOW_42_in_lowest_expression10219); if (state.failed) return retval;
                    pushFollow(FOLLOW_expression_in_lowest_expression10223);
                    e=expression();

                    state._fsp--;
                    if (state.failed) return retval;
                    match(input,43,FOLLOW_43_in_lowest_expression10225); if (state.failed) return retval;
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1603:4: ( ( '.' cc= call_chain ) | )
                    int alt164=2;
                    int LA164_0 = input.LA(1);

                    if ( (LA164_0==70) ) {
                        alt164=1;
                    }
                    else if ( (LA164_0==25||(LA164_0>=33 && LA164_0<=35)||LA164_0==43||LA164_0==63||LA164_0==65||(LA164_0>=76 && LA164_0<=77)||(LA164_0>=84 && LA164_0<=86)||(LA164_0>=102 && LA164_0<=107)||(LA164_0>=110 && LA164_0<=120)) ) {
                        alt164=2;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return retval;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 164, 0, input);

                        throw nvae;
                    }
                    switch (alt164) {
                        case 1 :
                            // /home/fintan/workspaces/bon/bonc/src/BON.g:1603:6: ( '.' cc= call_chain )
                            {
                            // /home/fintan/workspaces/bon/bonc/src/BON.g:1603:6: ( '.' cc= call_chain )
                            // /home/fintan/workspaces/bon/bonc/src/BON.g:1603:7: '.' cc= call_chain
                            {
                            match(input,70,FOLLOW_70_in_lowest_expression10235); if (state.failed) return retval;
                            pushFollow(FOLLOW_call_chain_in_lowest_expression10239);
                            cc=call_chain();

                            state._fsp--;
                            if (state.failed) return retval;
                            if ( state.backtracking==0 ) {
                               if(isOk()) retval.exp = CallExp.mk((e!=null?e.exp:null), (cc!=null?cc.calls:null), getSLoc(s,(cc!=null?((Token)cc.stop):null))); 
                            }

                            }


                            }
                            break;
                        case 2 :
                            // /home/fintan/workspaces/bon/bonc/src/BON.g:1606:7: 
                            {
                            if ( state.backtracking==0 ) {
                               if(isOk()) retval.exp = (e!=null?e.exp:null); 
                            }

                            }
                            break;

                    }


                    }
                    break;
                case 4 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1608:4: cc= call_chain
                    {
                    pushFollow(FOLLOW_call_chain_in_lowest_expression10275);
                    cc=call_chain();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.exp =  CallExp.mk(null, (cc!=null?cc.calls:null), getSLoc((cc!=null?((Token)cc.start):null),(cc!=null?((Token)cc.stop):null))); 
                    }

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
    // $ANTLR end "lowest_expression"


    // $ANTLR start "add_sub_op"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1612:1: add_sub_op returns [BinaryExp.Op op] : ( '+' | '-' );
    public final BinaryExp.Op add_sub_op() throws RecognitionException {
        BinaryExp.Op op = null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1616:38: ( '+' | '-' )
            int alt166=2;
            int LA166_0 = input.LA(1);

            if ( (LA166_0==103) ) {
                alt166=1;
            }
            else if ( (LA166_0==104) ) {
                alt166=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 166, 0, input);

                throw nvae;
            }
            switch (alt166) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1617:4: '+'
                    {
                    match(input,103,FOLLOW_103_in_add_sub_op10299); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.ADD; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1618:4: '-'
                    {
                    match(input,104,FOLLOW_104_in_add_sub_op10307); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.SUB; 
                    }

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
        return op;
    }
    // $ANTLR end "add_sub_op"


    // $ANTLR start "add_sub_op_unary"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1621:1: add_sub_op_unary returns [UnaryExp.Op op] : ( '+' | '-' );
    public final UnaryExp.Op add_sub_op_unary() throws RecognitionException {
        UnaryExp.Op op = null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1621:43: ( '+' | '-' )
            int alt167=2;
            int LA167_0 = input.LA(1);

            if ( (LA167_0==103) ) {
                alt167=1;
            }
            else if ( (LA167_0==104) ) {
                alt167=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 167, 0, input);

                throw nvae;
            }
            switch (alt167) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1622:4: '+'
                    {
                    match(input,103,FOLLOW_103_in_add_sub_op_unary10325); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = UnaryExp.Op.ADD; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1623:4: '-'
                    {
                    match(input,104,FOLLOW_104_in_add_sub_op_unary10333); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = UnaryExp.Op.SUB; 
                    }

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
        return op;
    }
    // $ANTLR end "add_sub_op_unary"


    // $ANTLR start "and_or_xor_op"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1626:1: and_or_xor_op returns [BinaryExp.Op op] : ( 'and' | 'or' | 'xor' );
    public final BinaryExp.Op and_or_xor_op() throws RecognitionException {
        BinaryExp.Op op = null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1626:41: ( 'and' | 'or' | 'xor' )
            int alt168=3;
            switch ( input.LA(1) ) {
            case 105:
                {
                alt168=1;
                }
                break;
            case 106:
                {
                alt168=2;
                }
                break;
            case 107:
                {
                alt168=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 168, 0, input);

                throw nvae;
            }

            switch (alt168) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1627:4: 'and'
                    {
                    match(input,105,FOLLOW_105_in_and_or_xor_op10351); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.AND; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1628:4: 'or'
                    {
                    match(input,106,FOLLOW_106_in_and_or_xor_op10358); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.OR; 
                    }

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1629:4: 'xor'
                    {
                    match(input,107,FOLLOW_107_in_and_or_xor_op10366); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.XOR; 
                    }

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
        return op;
    }
    // $ANTLR end "and_or_xor_op"

    public static class unary_return extends ParserRuleReturnScope {
        public UnaryExp.Op op;
    };

    // $ANTLR start "unary"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1632:1: unary returns [UnaryExp.Op op] : ( other_unary | add_sub_op_unary );
    public final BONParser.unary_return unary() throws RecognitionException {
        BONParser.unary_return retval = new BONParser.unary_return();
        retval.start = input.LT(1);

        UnaryExp.Op other_unary113 = null;

        UnaryExp.Op add_sub_op_unary114 = null;


        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1632:33: ( other_unary | add_sub_op_unary )
            int alt169=2;
            int LA169_0 = input.LA(1);

            if ( ((LA169_0>=108 && LA169_0<=110)) ) {
                alt169=1;
            }
            else if ( ((LA169_0>=103 && LA169_0<=104)) ) {
                alt169=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 169, 0, input);

                throw nvae;
            }
            switch (alt169) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1633:4: other_unary
                    {
                    pushFollow(FOLLOW_other_unary_in_unary10386);
                    other_unary113=other_unary();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.op = other_unary113; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1634:4: add_sub_op_unary
                    {
                    pushFollow(FOLLOW_add_sub_op_unary_in_unary10400);
                    add_sub_op_unary114=add_sub_op_unary();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.op = add_sub_op_unary114; 
                    }

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
    // $ANTLR end "unary"


    // $ANTLR start "other_unary"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1637:1: other_unary returns [UnaryExp.Op op] : ( 'delta' | 'old' | 'not' );
    public final UnaryExp.Op other_unary() throws RecognitionException {
        UnaryExp.Op op = null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1637:39: ( 'delta' | 'old' | 'not' )
            int alt170=3;
            switch ( input.LA(1) ) {
            case 108:
                {
                alt170=1;
                }
                break;
            case 109:
                {
                alt170=2;
                }
                break;
            case 110:
                {
                alt170=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 170, 0, input);

                throw nvae;
            }

            switch (alt170) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1638:4: 'delta'
                    {
                    match(input,108,FOLLOW_108_in_other_unary10420); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = UnaryExp.Op.DELTA; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1639:4: 'old'
                    {
                    match(input,109,FOLLOW_109_in_other_unary10428); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = UnaryExp.Op.OLD; 
                    }

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1640:4: 'not'
                    {
                    match(input,110,FOLLOW_110_in_other_unary10437); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = UnaryExp.Op.NOT; 
                    }

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
        return op;
    }
    // $ANTLR end "other_unary"


    // $ANTLR start "binary"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1643:1: binary : ( add_sub_op | mul_div_op | comparison_op | mod_pow_op | and_or_xor_op | '->' | '<->' );
    public final void binary() throws RecognitionException {
        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1643:9: ( add_sub_op | mul_div_op | comparison_op | mod_pow_op | and_or_xor_op | '->' | '<->' )
            int alt171=7;
            switch ( input.LA(1) ) {
            case 103:
            case 104:
                {
                alt171=1;
                }
                break;
            case 117:
            case 118:
            case 119:
                {
                alt171=2;
                }
                break;
            case 34:
            case 86:
            case 110:
            case 111:
            case 112:
            case 113:
            case 114:
            case 115:
            case 116:
                {
                alt171=3;
                }
                break;
            case 77:
            case 120:
                {
                alt171=4;
                }
                break;
            case 105:
            case 106:
            case 107:
                {
                alt171=5;
                }
                break;
            case 65:
                {
                alt171=6;
                }
                break;
            case 102:
                {
                alt171=7;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 171, 0, input);

                throw nvae;
            }

            switch (alt171) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1643:13: add_sub_op
                    {
                    pushFollow(FOLLOW_add_sub_op_in_binary10468);
                    add_sub_op();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1643:26: mul_div_op
                    {
                    pushFollow(FOLLOW_mul_div_op_in_binary10472);
                    mul_div_op();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1643:39: comparison_op
                    {
                    pushFollow(FOLLOW_comparison_op_in_binary10476);
                    comparison_op();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 4 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1644:13: mod_pow_op
                    {
                    pushFollow(FOLLOW_mod_pow_op_in_binary10491);
                    mod_pow_op();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 5 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1644:26: and_or_xor_op
                    {
                    pushFollow(FOLLOW_and_or_xor_op_in_binary10495);
                    and_or_xor_op();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 6 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1645:13: '->'
                    {
                    match(input,65,FOLLOW_65_in_binary10510); if (state.failed) return ;

                    }
                    break;
                case 7 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1645:20: '<->'
                    {
                    match(input,102,FOLLOW_102_in_binary10514); if (state.failed) return ;

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
    // $ANTLR end "binary"


    // $ANTLR start "comparison_op"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1647:1: comparison_op returns [BinaryExp.Op op] : ( '<' | '>' | '<=' | '>=' | '=' | '/=' | 'member_of' | 'not' 'member_of' | ':' );
    public final BinaryExp.Op comparison_op() throws RecognitionException {
        BinaryExp.Op op = null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1647:41: ( '<' | '>' | '<=' | '>=' | '=' | '/=' | 'member_of' | 'not' 'member_of' | ':' )
            int alt172=9;
            alt172 = dfa172.predict(input);
            switch (alt172) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1648:4: '<'
                    {
                    match(input,111,FOLLOW_111_in_comparison_op10530); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.LT; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1649:4: '>'
                    {
                    match(input,112,FOLLOW_112_in_comparison_op10538); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.GT; 
                    }

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1650:4: '<='
                    {
                    match(input,113,FOLLOW_113_in_comparison_op10546); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.LE; 
                    }

                    }
                    break;
                case 4 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1651:4: '>='
                    {
                    match(input,114,FOLLOW_114_in_comparison_op10553); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.GE; 
                    }

                    }
                    break;
                case 5 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1652:4: '='
                    {
                    match(input,115,FOLLOW_115_in_comparison_op10560); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.EQ; 
                    }

                    }
                    break;
                case 6 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1653:4: '/='
                    {
                    match(input,116,FOLLOW_116_in_comparison_op10568); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.NEQ; 
                    }

                    }
                    break;
                case 7 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1654:4: 'member_of'
                    {
                    match(input,86,FOLLOW_86_in_comparison_op10575); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.MEMBEROF; 
                    }

                    }
                    break;
                case 8 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1655:4: 'not' 'member_of'
                    {
                    match(input,110,FOLLOW_110_in_comparison_op10582); if (state.failed) return op;
                    match(input,86,FOLLOW_86_in_comparison_op10584); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.NOTMEMBEROF; 
                    }

                    }
                    break;
                case 9 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1656:4: ':'
                    {
                    match(input,34,FOLLOW_34_in_comparison_op10591); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.HASTYPE; 
                    }

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
        return op;
    }
    // $ANTLR end "comparison_op"


    // $ANTLR start "mul_div_op"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1660:1: mul_div_op returns [BinaryExp.Op op] : ( '*' | '/' | '//' );
    public final BinaryExp.Op mul_div_op() throws RecognitionException {
        BinaryExp.Op op = null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1660:38: ( '*' | '/' | '//' )
            int alt173=3;
            switch ( input.LA(1) ) {
            case 117:
                {
                alt173=1;
                }
                break;
            case 118:
                {
                alt173=2;
                }
                break;
            case 119:
                {
                alt173=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 173, 0, input);

                throw nvae;
            }

            switch (alt173) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1661:4: '*'
                    {
                    match(input,117,FOLLOW_117_in_mul_div_op10618); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.MUL; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1662:4: '/'
                    {
                    match(input,118,FOLLOW_118_in_mul_div_op10626); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.DIV; 
                    }

                    }
                    break;
                case 3 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1663:4: '//'
                    {
                    match(input,119,FOLLOW_119_in_mul_div_op10634); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.INTDIV; 
                    }

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
        return op;
    }
    // $ANTLR end "mul_div_op"


    // $ANTLR start "mod_pow_op"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1666:1: mod_pow_op returns [BinaryExp.Op op] : ( '\\\\\\\\' | '^' );
    public final BinaryExp.Op mod_pow_op() throws RecognitionException {
        BinaryExp.Op op = null;

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1666:38: ( '\\\\\\\\' | '^' )
            int alt174=2;
            int LA174_0 = input.LA(1);

            if ( (LA174_0==120) ) {
                alt174=1;
            }
            else if ( (LA174_0==77) ) {
                alt174=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 174, 0, input);

                throw nvae;
            }
            switch (alt174) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1667:4: '\\\\\\\\'
                    {
                    match(input,120,FOLLOW_120_in_mod_pow_op10667); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.MOD; 
                    }

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1668:4: '^'
                    {
                    match(input,77,FOLLOW_77_in_mod_pow_op10675); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.POW; 
                    }

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
        return op;
    }
    // $ANTLR end "mod_pow_op"

    public static class manifest_textblock_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "manifest_textblock"
    // /home/fintan/workspaces/bon/bonc/src/BON.g:1710:1: manifest_textblock : ( MANIFEST_STRING | MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END );
    public final BONParser.manifest_textblock_return manifest_textblock() throws RecognitionException {
        BONParser.manifest_textblock_return retval = new BONParser.manifest_textblock_return();
        retval.start = input.LT(1);

        try {
            // /home/fintan/workspaces/bon/bonc/src/BON.g:1711:1: ( MANIFEST_STRING | MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END )
            int alt176=2;
            int LA176_0 = input.LA(1);

            if ( (LA176_0==MANIFEST_STRING) ) {
                alt176=1;
            }
            else if ( (LA176_0==MANIFEST_TEXTBLOCK_START) ) {
                alt176=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 176, 0, input);

                throw nvae;
            }
            switch (alt176) {
                case 1 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1712:3: MANIFEST_STRING
                    {
                    if ( state.backtracking==0 ) {
                       //TODO warn when not MANIFEST_STRING where we desire a single block. 
                        
                    }
                    match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_manifest_textblock10987); if (state.failed) return retval;

                    }
                    break;
                case 2 :
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1715:4: MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END
                    {
                    match(input,MANIFEST_TEXTBLOCK_START,FOLLOW_MANIFEST_TEXTBLOCK_START_in_manifest_textblock10993); if (state.failed) return retval;
                    // /home/fintan/workspaces/bon/bonc/src/BON.g:1715:29: ( MANIFEST_TEXTBLOCK_MIDDLE )*
                    loop175:
                    do {
                        int alt175=2;
                        int LA175_0 = input.LA(1);

                        if ( (LA175_0==MANIFEST_TEXTBLOCK_MIDDLE) ) {
                            alt175=1;
                        }


                        switch (alt175) {
                    	case 1 :
                    	    // /home/fintan/workspaces/bon/bonc/src/BON.g:1715:29: MANIFEST_TEXTBLOCK_MIDDLE
                    	    {
                    	    match(input,MANIFEST_TEXTBLOCK_MIDDLE,FOLLOW_MANIFEST_TEXTBLOCK_MIDDLE_in_manifest_textblock10995); if (state.failed) return retval;

                    	    }
                    	    break;

                    	default :
                    	    break loop175;
                        }
                    } while (true);

                    match(input,MANIFEST_TEXTBLOCK_END,FOLLOW_MANIFEST_TEXTBLOCK_END_in_manifest_textblock10998); if (state.failed) return retval;

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
    // $ANTLR end "manifest_textblock"

    // $ANTLR start synpred1_BON
    public final void synpred1_BON_fragment() throws RecognitionException {   
        // /home/fintan/workspaces/bon/bonc/src/BON.g:1593:5: ( constant )
        // /home/fintan/workspaces/bon/bonc/src/BON.g:1593:6: constant
        {
        pushFollow(FOLLOW_constant_in_synpred1_BON10135);
        constant();

        state._fsp--;
        if (state.failed) return ;

        }
    }
    // $ANTLR end synpred1_BON

    // Delegated rules

    public final boolean synpred1_BON() {
        state.backtracking++;
        int start = input.mark();
        try {
            synpred1_BON_fragment(); // can never throw exception
        } catch (RecognitionException re) {
            System.err.println("impossible: "+re);
        }
        boolean success = !state.failed;
        input.rewind(start);
        state.backtracking--;
        state.failed=false;
        return success;
    }


    protected DFA1 dfa1 = new DFA1(this);
    protected DFA75 dfa75 = new DFA75(this);
    protected DFA83 dfa83 = new DFA83(this);
    protected DFA129 dfa129 = new DFA129(this);
    protected DFA165 dfa165 = new DFA165(this);
    protected DFA172 dfa172 = new DFA172(this);
    static final String DFA1_eotS =
        "\50\uffff";
    static final String DFA1_eofS =
        "\1\3\1\uffff\1\4\4\uffff\2\4\1\uffff\1\4\2\uffff\1\4\2\uffff\3\4"+
        "\1\uffff\1\4\1\uffff\1\4\3\uffff\1\4\1\uffff\1\4\2\uffff\2\4\1\uffff"+
        "\1\4\2\uffff\1\4\1\uffff\1\4";
    static final String DFA1_minS =
        "\1\30\1\uffff\1\5\2\uffff\1\42\1\uffff\1\4\1\5\1\42\1\5\1\13\1\42"+
        "\2\4\1\13\1\5\1\4\1\5\1\13\1\5\1\13\1\5\1\13\1\4\1\13\1\5\1\13\1"+
        "\5\1\4\1\13\2\5\1\13\1\5\2\13\1\5\1\13\1\5";
    static final String DFA1_maxS =
        "\1\134\1\uffff\1\134\2\uffff\1\42\1\uffff\2\134\1\42\1\134\1\14"+
        "\1\42\1\134\1\12\1\14\3\134\1\14\1\134\1\14\1\134\1\14\1\12\1\14"+
        "\1\134\1\14\1\134\1\12\1\14\2\134\1\14\1\134\2\14\1\134\1\14\1\134";
    static final String DFA1_acceptS =
        "\1\uffff\1\1\1\uffff\1\3\1\4\1\uffff\1\2\41\uffff";
    static final String DFA1_specialS =
        "\50\uffff}>";
    static final String[] DFA1_transitionS = {
            "\1\1\3\uffff\1\1\1\uffff\1\2\5\uffff\2\1\6\uffff\1\1\4\uffff"+
            "\1\1\1\uffff\1\1\2\uffff\1\1\45\uffff\1\1",
            "",
            "\1\5\22\uffff\1\6\3\uffff\1\6\7\uffff\2\6\6\uffff\1\6\4\uffff"+
            "\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff\1\6",
            "",
            "",
            "\1\7",
            "",
            "\1\12\1\11\4\uffff\1\13\15\uffff\1\6\3\uffff\1\6\4\uffff\1"+
            "\10\2\uffff\2\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff"+
            "\1\6\45\uffff\1\6",
            "\1\14\22\uffff\1\6\3\uffff\1\6\7\uffff\2\6\6\uffff\1\6\4\uffff"+
            "\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff\1\6",
            "\1\15",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\16\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\17\1\20",
            "\1\21",
            "\1\22\1\11\4\uffff\1\23\15\uffff\1\6\3\uffff\1\6\4\uffff\1"+
            "\10\2\uffff\2\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff"+
            "\1\6\45\uffff\1\6",
            "\1\24\5\uffff\1\25",
            "\1\17\1\20",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\16\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\26\1\11\4\uffff\1\27\15\uffff\1\6\3\uffff\1\6\4\uffff\1"+
            "\10\2\uffff\2\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff"+
            "\1\6\45\uffff\1\6",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\30\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\31\1\32",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\16\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\33\1\34",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\35\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\36\1\37",
            "\1\40\5\uffff\1\41",
            "\1\31\1\32",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\30\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\33\1\34",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\16\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\42\5\uffff\1\43",
            "\1\36\1\37",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\35\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\30\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\44\1\45",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\35\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\46\1\47",
            "\1\44\1\45",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\30\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\46\1\47",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\35\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6"
    };

    static final short[] DFA1_eot = DFA.unpackEncodedString(DFA1_eotS);
    static final short[] DFA1_eof = DFA.unpackEncodedString(DFA1_eofS);
    static final char[] DFA1_min = DFA.unpackEncodedStringToUnsignedChars(DFA1_minS);
    static final char[] DFA1_max = DFA.unpackEncodedStringToUnsignedChars(DFA1_maxS);
    static final short[] DFA1_accept = DFA.unpackEncodedString(DFA1_acceptS);
    static final short[] DFA1_special = DFA.unpackEncodedString(DFA1_specialS);
    static final short[][] DFA1_transition;

    static {
        int numStates = DFA1_transitionS.length;
        DFA1_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA1_transition[i] = DFA.unpackEncodedString(DFA1_transitionS[i]);
        }
    }

    class DFA1 extends DFA {

        public DFA1(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 1;
            this.eot = DFA1_eot;
            this.eof = DFA1_eof;
            this.min = DFA1_min;
            this.max = DFA1_max;
            this.accept = DFA1_accept;
            this.special = DFA1_special;
            this.transition = DFA1_transition;
        }
        public String getDescription() {
            return "32:1: prog returns [BonSourceFile bonSource] : (bs= bon_specification EOF | i= indexing bs= bon_specification EOF | e= EOF | indexing e= EOF );";
        }
    }
    static final String DFA75_eotS =
        "\7\uffff";
    static final String DFA75_eofS =
        "\7\uffff";
    static final String DFA75_minS =
        "\1\5\1\46\1\uffff\1\5\1\uffff\1\46\1\5";
    static final String DFA75_maxS =
        "\1\5\1\106\1\uffff\1\5\1\uffff\1\106\1\5";
    static final String DFA75_acceptS =
        "\2\uffff\1\1\1\uffff\1\2\2\uffff";
    static final String DFA75_specialS =
        "\7\uffff}>";
    static final String[] DFA75_transitionS = {
            "\1\1",
            "\1\2\31\uffff\1\4\5\uffff\1\3",
            "",
            "\1\5",
            "",
            "\1\2\31\uffff\1\4\5\uffff\1\6",
            "\1\5"
    };

    static final short[] DFA75_eot = DFA.unpackEncodedString(DFA75_eotS);
    static final short[] DFA75_eof = DFA.unpackEncodedString(DFA75_eofS);
    static final char[] DFA75_min = DFA.unpackEncodedStringToUnsignedChars(DFA75_minS);
    static final char[] DFA75_max = DFA.unpackEncodedStringToUnsignedChars(DFA75_maxS);
    static final short[] DFA75_accept = DFA.unpackEncodedString(DFA75_acceptS);
    static final short[] DFA75_special = DFA.unpackEncodedString(DFA75_specialS);
    static final short[][] DFA75_transition;

    static {
        int numStates = DFA75_transitionS.length;
        DFA75_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA75_transition[i] = DFA.unpackEncodedString(DFA75_transitionS[i]);
        }
    }

    class DFA75 extends DFA {

        public DFA75(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 75;
            this.eot = DFA75_eot;
            this.eof = DFA75_eof;
            this.min = DFA75_min;
            this.max = DFA75_max;
            this.accept = DFA75_accept;
            this.special = DFA75_special;
            this.transition = DFA75_transition;
        }
        public String getDescription() {
            return "590:1: static_relation returns [StaticRelation relation] : (ir= inheritance_relation | cr= client_relation );";
        }
    }
    static final String DFA83_eotS =
        "\46\uffff";
    static final String DFA83_eofS =
        "\46\uffff";
    static final String DFA83_minS =
        "\1\5\2\120\2\uffff\1\147\1\42\21\120\1\126\10\120\2\42\1\120\2\uffff";
    static final String DFA83_maxS =
        "\1\121\2\120\2\uffff\1\156\1\170\21\120\1\126\10\120\2\77\1\120"+
        "\2\uffff";
    static final String DFA83_acceptS =
        "\3\uffff\1\3\1\4\37\uffff\1\1\1\2";
    static final String DFA83_specialS =
        "\46\uffff}>";
    static final String[] DFA83_transitionS = {
            "\1\3\44\uffff\1\3\26\uffff\1\4\1\3\1\uffff\1\3\12\uffff\1\1"+
            "\1\uffff\1\2",
            "\1\5",
            "\1\6",
            "",
            "",
            "\1\12\1\13\3\uffff\1\7\1\10\1\11",
            "\1\31\36\uffff\1\37\13\uffff\1\33\10\uffff\1\27\17\uffff\1"+
            "\40\1\14\1\15\1\34\1\35\1\36\2\uffff\1\30\1\21\1\22\1\23\1\24"+
            "\1\25\1\26\1\16\1\17\1\20\1\32",
            "\1\41",
            "\1\41",
            "\1\41",
            "\1\41",
            "\1\41",
            "\1\42",
            "\1\42",
            "\1\42",
            "\1\42",
            "\1\42",
            "\1\42",
            "\1\42",
            "\1\42",
            "\1\42",
            "\1\42",
            "\1\42",
            "\1\42",
            "\1\43",
            "\1\42",
            "\1\42",
            "\1\42",
            "\1\42",
            "\1\42",
            "\1\42",
            "\1\42",
            "\1\42",
            "\1\3\1\44\33\uffff\1\44",
            "\1\3\1\45\33\uffff\1\45",
            "\1\42",
            "",
            ""
    };

    static final short[] DFA83_eot = DFA.unpackEncodedString(DFA83_eotS);
    static final short[] DFA83_eof = DFA.unpackEncodedString(DFA83_eofS);
    static final char[] DFA83_min = DFA.unpackEncodedStringToUnsignedChars(DFA83_minS);
    static final char[] DFA83_max = DFA.unpackEncodedStringToUnsignedChars(DFA83_maxS);
    static final short[] DFA83_accept = DFA.unpackEncodedString(DFA83_acceptS);
    static final short[] DFA83_special = DFA.unpackEncodedString(DFA83_specialS);
    static final short[][] DFA83_transition;

    static {
        int numStates = DFA83_transitionS.length;
        DFA83_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA83_transition[i] = DFA.unpackEncodedString(DFA83_transitionS[i]);
        }
    }

    class DFA83 extends DFA {

        public DFA83(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 83;
            this.eot = DFA83_eot;
            this.eof = DFA83_eof;
            this.min = DFA83_min;
            this.max = DFA83_max;
            this.accept = DFA83_accept;
            this.special = DFA83_special;
            this.transition = DFA83_transition;
        }
        public String getDescription() {
            return "655:1: client_entity returns [ClientEntity entity] : ( prefix | infix | supplier_indirection | parent_indirection );";
        }
    }
    static final String DFA129_eotS =
        "\6\uffff";
    static final String DFA129_eofS =
        "\6\uffff";
    static final String DFA129_minS =
        "\1\5\1\42\1\5\2\uffff\1\42";
    static final String DFA129_maxS =
        "\1\5\1\126\1\5\2\uffff\1\126";
    static final String DFA129_acceptS =
        "\3\uffff\1\1\1\2\1\uffff";
    static final String DFA129_specialS =
        "\6\uffff}>";
    static final String[] DFA129_transitionS = {
            "\1\1",
            "\1\4\1\2\62\uffff\1\3",
            "\1\5",
            "",
            "",
            "\1\4\1\2\62\uffff\1\3"
    };

    static final short[] DFA129_eot = DFA.unpackEncodedString(DFA129_eotS);
    static final short[] DFA129_eof = DFA.unpackEncodedString(DFA129_eofS);
    static final char[] DFA129_min = DFA.unpackEncodedStringToUnsignedChars(DFA129_minS);
    static final char[] DFA129_max = DFA.unpackEncodedStringToUnsignedChars(DFA129_maxS);
    static final short[] DFA129_accept = DFA.unpackEncodedString(DFA129_acceptS);
    static final short[] DFA129_special = DFA.unpackEncodedString(DFA129_specialS);
    static final short[][] DFA129_transition;

    static {
        int numStates = DFA129_transitionS.length;
        DFA129_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA129_transition[i] = DFA.unpackEncodedString(DFA129_transitionS[i]);
        }
    }

    class DFA129 extends DFA {

        public DFA129(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 129;
            this.eot = DFA129_eot;
            this.eof = DFA129_eof;
            this.min = DFA129_min;
            this.max = DFA129_max;
            this.accept = DFA129_accept;
            this.special = DFA129_special;
            this.transition = DFA129_transition;
        }
        public String getDescription() {
            return "1162:1: variable_range returns [VariableRange range] : (mr= member_range | tr= type_range );";
        }
    }
    static final String DFA165_eotS =
        "\20\uffff";
    static final String DFA165_eofS =
        "\20\uffff";
    static final String DFA165_minS =
        "\1\4\3\uffff\2\0\12\uffff";
    static final String DFA165_maxS =
        "\1\156\3\uffff\2\0\12\uffff";
    static final String DFA165_acceptS =
        "\1\uffff\3\1\2\uffff\7\1\1\2\1\3\1\4";
    static final String DFA165_specialS =
        "\1\2\3\uffff\1\1\1\0\12\uffff}>";
    static final String[] DFA165_transitionS = {
            "\1\10\1\17\1\6\1\3\1\7\41\uffff\1\16\23\uffff\1\11\13\uffff"+
            "\1\13\15\uffff\1\12\1\14\1\1\1\2\13\uffff\1\4\1\5\3\uffff\3"+
            "\15",
            "",
            "",
            "",
            "\1\uffff",
            "\1\uffff",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            ""
    };

    static final short[] DFA165_eot = DFA.unpackEncodedString(DFA165_eotS);
    static final short[] DFA165_eof = DFA.unpackEncodedString(DFA165_eofS);
    static final char[] DFA165_min = DFA.unpackEncodedStringToUnsignedChars(DFA165_minS);
    static final char[] DFA165_max = DFA.unpackEncodedStringToUnsignedChars(DFA165_maxS);
    static final short[] DFA165_accept = DFA.unpackEncodedString(DFA165_acceptS);
    static final short[] DFA165_special = DFA.unpackEncodedString(DFA165_specialS);
    static final short[][] DFA165_transition;

    static {
        int numStates = DFA165_transitionS.length;
        DFA165_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA165_transition[i] = DFA.unpackEncodedString(DFA165_transitionS[i]);
        }
    }

    class DFA165 extends DFA {

        public DFA165(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 165;
            this.eot = DFA165_eot;
            this.eof = DFA165_eof;
            this.min = DFA165_min;
            this.max = DFA165_max;
            this.accept = DFA165_accept;
            this.special = DFA165_special;
            this.transition = DFA165_transition;
        }
        public String getDescription() {
            return "1592:1: lowest_expression returns [Expression exp] : ( ( constant )=> constant ( ( '.' cc= call_chain ) | ) | unary le= lowest_expression | s= '(' e= expression ')' ( ( '.' cc= call_chain ) | ) | cc= call_chain );";
        }
        public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
            TokenStream input = (TokenStream)_input;
        	int _s = s;
            switch ( s ) {
                    case 0 : 
                        int LA165_5 = input.LA(1);

                         
                        int index165_5 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred1_BON()) ) {s = 12;}

                        else if ( (true) ) {s = 13;}

                         
                        input.seek(index165_5);
                        if ( s>=0 ) return s;
                        break;
                    case 1 : 
                        int LA165_4 = input.LA(1);

                         
                        int index165_4 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred1_BON()) ) {s = 12;}

                        else if ( (true) ) {s = 13;}

                         
                        input.seek(index165_4);
                        if ( s>=0 ) return s;
                        break;
                    case 2 : 
                        int LA165_0 = input.LA(1);

                         
                        int index165_0 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (LA165_0==90) && (synpred1_BON())) {s = 1;}

                        else if ( (LA165_0==91) && (synpred1_BON())) {s = 2;}

                        else if ( (LA165_0==CHARACTER_CONSTANT) && (synpred1_BON())) {s = 3;}

                        else if ( (LA165_0==103) ) {s = 4;}

                        else if ( (LA165_0==104) ) {s = 5;}

                        else if ( (LA165_0==INTEGER) && (synpred1_BON())) {s = 6;}

                        else if ( (LA165_0==REAL) && (synpred1_BON())) {s = 7;}

                        else if ( (LA165_0==MANIFEST_STRING) && (synpred1_BON())) {s = 8;}

                        else if ( (LA165_0==62) && (synpred1_BON())) {s = 9;}

                        else if ( (LA165_0==88) && (synpred1_BON())) {s = 10;}

                        else if ( (LA165_0==74) && (synpred1_BON())) {s = 11;}

                        else if ( (LA165_0==89) && (synpred1_BON())) {s = 12;}

                        else if ( ((LA165_0>=108 && LA165_0<=110)) ) {s = 13;}

                        else if ( (LA165_0==42) ) {s = 14;}

                        else if ( (LA165_0==IDENTIFIER) ) {s = 15;}

                         
                        input.seek(index165_0);
                        if ( s>=0 ) return s;
                        break;
            }
            if (state.backtracking>0) {state.failed=true; return -1;}
            NoViableAltException nvae =
                new NoViableAltException(getDescription(), 165, _s, input);
            error(nvae);
            throw nvae;
        }
    }
    static final String DFA172_eotS =
        "\12\uffff";
    static final String DFA172_eofS =
        "\12\uffff";
    static final String DFA172_minS =
        "\1\42\11\uffff";
    static final String DFA172_maxS =
        "\1\164\11\uffff";
    static final String DFA172_acceptS =
        "\1\uffff\1\1\1\2\1\3\1\4\1\5\1\6\1\7\1\10\1\11";
    static final String DFA172_specialS =
        "\12\uffff}>";
    static final String[] DFA172_transitionS = {
            "\1\11\63\uffff\1\7\27\uffff\1\10\1\1\1\2\1\3\1\4\1\5\1\6",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            ""
    };

    static final short[] DFA172_eot = DFA.unpackEncodedString(DFA172_eotS);
    static final short[] DFA172_eof = DFA.unpackEncodedString(DFA172_eofS);
    static final char[] DFA172_min = DFA.unpackEncodedStringToUnsignedChars(DFA172_minS);
    static final char[] DFA172_max = DFA.unpackEncodedStringToUnsignedChars(DFA172_maxS);
    static final short[] DFA172_accept = DFA.unpackEncodedString(DFA172_acceptS);
    static final short[] DFA172_special = DFA.unpackEncodedString(DFA172_specialS);
    static final short[][] DFA172_transition;

    static {
        int numStates = DFA172_transitionS.length;
        DFA172_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA172_transition[i] = DFA.unpackEncodedString(DFA172_transitionS[i]);
        }
    }

    class DFA172 extends DFA {

        public DFA172(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 172;
            this.eot = DFA172_eot;
            this.eof = DFA172_eof;
            this.min = DFA172_min;
            this.max = DFA172_max;
            this.accept = DFA172_accept;
            this.special = DFA172_special;
            this.transition = DFA172_transition;
        }
        public String getDescription() {
            return "1647:1: comparison_op returns [BinaryExp.Op op] : ( '<' | '>' | '<=' | '>=' | '=' | '/=' | 'member_of' | 'not' 'member_of' | ':' );";
        }
    }
 

    public static final BitSet FOLLOW_bon_specification_in_prog70 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_prog72 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indexing_in_prog105 = new BitSet(new long[]{0x004A103011000000L,0x0000000010000000L});
    public static final BitSet FOLLOW_bon_specification_in_prog109 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_prog111 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_EOF_in_prog144 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indexing_in_prog188 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_prog192 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_specification_element_in_bon_specification241 = new BitSet(new long[]{0x004A103011000002L,0x0000000010000000L});
    public static final BitSet FOLLOW_informal_chart_in_specification_element272 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_dictionary_in_specification_element286 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_diagram_in_specification_element300 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_dynamic_diagram_in_specification_element314 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_system_chart_in_informal_chart342 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cluster_chart_in_informal_chart354 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_chart_in_informal_chart366 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_event_chart_in_informal_chart378 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_scenario_chart_in_informal_chart390 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_creation_chart_in_informal_chart402 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_24_in_class_dictionary437 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_system_name_in_class_dictionary442 = new BitSet(new long[]{0x00000000E4000000L});
    public static final BitSet FOLLOW_indexing_in_class_dictionary448 = new BitSet(new long[]{0x00000000E4000000L});
    public static final BitSet FOLLOW_explanation_in_class_dictionary458 = new BitSet(new long[]{0x00000000E4000000L});
    public static final BitSet FOLLOW_part_in_class_dictionary469 = new BitSet(new long[]{0x00000000E4000000L});
    public static final BitSet FOLLOW_dictionary_entry_in_class_dictionary482 = new BitSet(new long[]{0x00000000E6000000L});
    public static final BitSet FOLLOW_25_in_class_dictionary499 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_26_in_dictionary_entry525 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_in_dictionary_entry527 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_27_in_dictionary_entry532 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_cluster_name_list_in_dictionary_entry534 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_description_in_dictionary_entry539 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_28_in_system_chart570 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_system_name_in_system_chart575 = new BitSet(new long[]{0x00000000EA000000L});
    public static final BitSet FOLLOW_indexing_in_system_chart581 = new BitSet(new long[]{0x00000000AA000000L});
    public static final BitSet FOLLOW_explanation_in_system_chart591 = new BitSet(new long[]{0x000000008A000000L});
    public static final BitSet FOLLOW_part_in_system_chart602 = new BitSet(new long[]{0x000000000A000000L});
    public static final BitSet FOLLOW_cluster_entries_in_system_chart617 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_system_chart644 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_29_in_explanation665 = new BitSet(new long[]{0x0000000000000410L});
    public static final BitSet FOLLOW_manifest_textblock_in_explanation669 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_29_in_explanation682 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_30_in_indexing707 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_index_list_in_indexing709 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_30_in_indexing725 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_31_in_part755 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_part759 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_31_in_part777 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_32_in_description807 = new BitSet(new long[]{0x0000000000000410L});
    public static final BitSet FOLLOW_manifest_textblock_in_description811 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cluster_entry_in_cluster_entries836 = new BitSet(new long[]{0x0000000008000002L});
    public static final BitSet FOLLOW_27_in_cluster_entry875 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_entry877 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_description_in_cluster_entry879 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_system_name916 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_index_clause_in_index_list973 = new BitSet(new long[]{0x0000000200000022L});
    public static final BitSet FOLLOW_33_in_index_list1012 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_index_clause_in_index_list1016 = new BitSet(new long[]{0x0000000200000022L});
    public static final BitSet FOLLOW_index_clause_in_index_list1059 = new BitSet(new long[]{0x0000000200000022L});
    public static final BitSet FOLLOW_33_in_index_list1117 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_index_clause1150 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_34_in_index_clause1152 = new BitSet(new long[]{0x0000000000000410L});
    public static final BitSet FOLLOW_index_term_list_in_index_clause1154 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_index_clause1168 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_34_in_index_clause1170 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_index_string_in_index_term_list1212 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_index_term_list1222 = new BitSet(new long[]{0x0000000000000410L});
    public static final BitSet FOLLOW_index_string_in_index_term_list1226 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_index_string1271 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_36_in_cluster_chart1305 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_chart1307 = new BitSet(new long[]{0x00000000EE000000L});
    public static final BitSet FOLLOW_indexing_in_cluster_chart1315 = new BitSet(new long[]{0x00000000AE000000L});
    public static final BitSet FOLLOW_explanation_in_cluster_chart1326 = new BitSet(new long[]{0x000000008E000000L});
    public static final BitSet FOLLOW_part_in_cluster_chart1337 = new BitSet(new long[]{0x000000000E000000L});
    public static final BitSet FOLLOW_class_entries_in_cluster_chart1352 = new BitSet(new long[]{0x000000000A000000L});
    public static final BitSet FOLLOW_cluster_entries_in_cluster_chart1376 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_cluster_chart1397 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_entry_in_class_entries1436 = new BitSet(new long[]{0x0000000004000002L});
    public static final BitSet FOLLOW_26_in_class_entry1474 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_in_class_entry1476 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_description_in_class_entry1480 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_cluster_name1514 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_37_in_class_chart1545 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_in_class_chart1547 = new BitSet(new long[]{0x000003C0E2000000L});
    public static final BitSet FOLLOW_indexing_in_class_chart1555 = new BitSet(new long[]{0x000003C0A2000000L});
    public static final BitSet FOLLOW_explanation_in_class_chart1566 = new BitSet(new long[]{0x000003C082000000L});
    public static final BitSet FOLLOW_part_in_class_chart1577 = new BitSet(new long[]{0x000003C002000000L});
    public static final BitSet FOLLOW_inherits_in_class_chart1590 = new BitSet(new long[]{0x0000038002000000L});
    public static final BitSet FOLLOW_queries_in_class_chart1609 = new BitSet(new long[]{0x0000030002000000L});
    public static final BitSet FOLLOW_commands_in_class_chart1628 = new BitSet(new long[]{0x0000020002000000L});
    public static final BitSet FOLLOW_constraints_in_class_chart1647 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_class_chart1665 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_38_in_inherits1699 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_list_in_inherits1704 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_38_in_inherits1718 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_39_in_queries1738 = new BitSet(new long[]{0x0000000000000410L});
    public static final BitSet FOLLOW_query_list_in_queries1740 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_40_in_commands1770 = new BitSet(new long[]{0x0000000000000410L});
    public static final BitSet FOLLOW_command_list_in_commands1772 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_41_in_constraints1791 = new BitSet(new long[]{0x0000000000000410L});
    public static final BitSet FOLLOW_constraint_list_in_constraints1793 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_query_list1819 = new BitSet(new long[]{0x0000000800000412L});
    public static final BitSet FOLLOW_35_in_query_list1832 = new BitSet(new long[]{0x0000000000000410L});
    public static final BitSet FOLLOW_manifest_textblock_in_query_list1836 = new BitSet(new long[]{0x0000000800000412L});
    public static final BitSet FOLLOW_manifest_textblock_in_query_list1868 = new BitSet(new long[]{0x0000000800000412L});
    public static final BitSet FOLLOW_35_in_query_list1894 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_command_list1941 = new BitSet(new long[]{0x0000000800000412L});
    public static final BitSet FOLLOW_35_in_command_list1954 = new BitSet(new long[]{0x0000000000000410L});
    public static final BitSet FOLLOW_manifest_textblock_in_command_list1958 = new BitSet(new long[]{0x0000000800000412L});
    public static final BitSet FOLLOW_manifest_textblock_in_command_list1984 = new BitSet(new long[]{0x0000000800000412L});
    public static final BitSet FOLLOW_35_in_command_list2009 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_constraint_list2045 = new BitSet(new long[]{0x0000000800000412L});
    public static final BitSet FOLLOW_35_in_constraint_list2058 = new BitSet(new long[]{0x0000000000000410L});
    public static final BitSet FOLLOW_manifest_textblock_in_constraint_list2062 = new BitSet(new long[]{0x0000000800000412L});
    public static final BitSet FOLLOW_manifest_textblock_in_constraint_list2087 = new BitSet(new long[]{0x0000000800000412L});
    public static final BitSet FOLLOW_35_in_constraint_list2111 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_class_name_list2133 = new BitSet(new long[]{0x0000000800000022L});
    public static final BitSet FOLLOW_35_in_class_name_list2147 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_in_class_name_list2151 = new BitSet(new long[]{0x0000000800000022L});
    public static final BitSet FOLLOW_class_name_in_class_name_list2180 = new BitSet(new long[]{0x0000000800000022L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_name_list2249 = new BitSet(new long[]{0x0000000800000022L});
    public static final BitSet FOLLOW_35_in_cluster_name_list2262 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_name_list2266 = new BitSet(new long[]{0x0000000800000022L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_name_list2294 = new BitSet(new long[]{0x0000000800000022L});
    public static final BitSet FOLLOW_class_or_bracketed_cluster_name_in_class_or_cluster_name_list2391 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_class_or_cluster_name_list2401 = new BitSet(new long[]{0x0000040000000020L});
    public static final BitSet FOLLOW_class_or_bracketed_cluster_name_in_class_or_cluster_name_list2405 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_class_name_in_class_or_bracketed_cluster_name2433 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_42_in_class_or_bracketed_cluster_name2447 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_cluster_name_in_class_or_bracketed_cluster_name2449 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_43_in_class_or_bracketed_cluster_name2451 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_class_name2473 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_44_in_event_chart2504 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_system_name_in_event_chart2506 = new BitSet(new long[]{0x0000E000E2000000L});
    public static final BitSet FOLLOW_45_in_event_chart2514 = new BitSet(new long[]{0x00008000E2000000L});
    public static final BitSet FOLLOW_46_in_event_chart2524 = new BitSet(new long[]{0x00008000E2000000L});
    public static final BitSet FOLLOW_indexing_in_event_chart2536 = new BitSet(new long[]{0x00008000A2000000L});
    public static final BitSet FOLLOW_explanation_in_event_chart2545 = new BitSet(new long[]{0x0000800082000000L});
    public static final BitSet FOLLOW_part_in_event_chart2555 = new BitSet(new long[]{0x0000800002000000L});
    public static final BitSet FOLLOW_event_entries_in_event_chart2568 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_event_chart2595 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_event_entry_in_event_entries2632 = new BitSet(new long[]{0x0000800000000002L});
    public static final BitSet FOLLOW_47_in_event_entry2675 = new BitSet(new long[]{0x0001000000000410L});
    public static final BitSet FOLLOW_manifest_textblock_in_event_entry2686 = new BitSet(new long[]{0x0001000000000000L});
    public static final BitSet FOLLOW_48_in_event_entry2726 = new BitSet(new long[]{0x0000040000000022L});
    public static final BitSet FOLLOW_class_or_cluster_name_list_in_event_entry2736 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_49_in_scenario_chart2816 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_system_name_in_scenario_chart2818 = new BitSet(new long[]{0x00040000E2000000L});
    public static final BitSet FOLLOW_indexing_in_scenario_chart2823 = new BitSet(new long[]{0x00040000A2000000L});
    public static final BitSet FOLLOW_explanation_in_scenario_chart2833 = new BitSet(new long[]{0x0004000082000000L});
    public static final BitSet FOLLOW_part_in_scenario_chart2843 = new BitSet(new long[]{0x0004000002000000L});
    public static final BitSet FOLLOW_scenario_entries_in_scenario_chart2854 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_scenario_chart2875 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_scenario_entry_in_scenario_entries2915 = new BitSet(new long[]{0x0004000000000002L});
    public static final BitSet FOLLOW_50_in_scenario_entry2956 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_scenario_entry2960 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_description_in_scenario_entry2964 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_51_in_creation_chart2993 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_system_name_in_creation_chart2995 = new BitSet(new long[]{0x00100000E2000000L});
    public static final BitSet FOLLOW_indexing_in_creation_chart3000 = new BitSet(new long[]{0x00100000A2000000L});
    public static final BitSet FOLLOW_explanation_in_creation_chart3010 = new BitSet(new long[]{0x0010000082000000L});
    public static final BitSet FOLLOW_part_in_creation_chart3020 = new BitSet(new long[]{0x0010000002000000L});
    public static final BitSet FOLLOW_creation_entries_in_creation_chart3031 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_creation_chart3048 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_creation_entry_in_creation_entries3089 = new BitSet(new long[]{0x0010000000000002L});
    public static final BitSet FOLLOW_52_in_creation_entry3129 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_in_creation_entry3131 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_53_in_creation_entry3136 = new BitSet(new long[]{0x0000040000000020L});
    public static final BitSet FOLLOW_class_or_cluster_name_list_in_creation_entry3140 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_54_in_static_diagram3173 = new BitSet(new long[]{0x0080000000000060L});
    public static final BitSet FOLLOW_extended_id_in_static_diagram3179 = new BitSet(new long[]{0x0080000000000000L});
    public static final BitSet FOLLOW_comment_in_static_diagram3188 = new BitSet(new long[]{0x0080000000000000L});
    public static final BitSet FOLLOW_55_in_static_diagram3195 = new BitSet(new long[]{0x0E0000000E000020L});
    public static final BitSet FOLLOW_static_block_in_static_diagram3202 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_static_diagram3209 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_extended_id3265 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_INTEGER_in_extended_id3278 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_component_in_static_block3319 = new BitSet(new long[]{0x0E0000000C000022L});
    public static final BitSet FOLLOW_cluster_in_static_component3354 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_clazz_in_static_component3367 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_relation_in_static_component3380 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_27_in_cluster3412 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_cluster_name_in_cluster3414 = new BitSet(new long[]{0x0180000000000000L});
    public static final BitSet FOLLOW_56_in_cluster3423 = new BitSet(new long[]{0x0080000000000000L});
    public static final BitSet FOLLOW_comment_in_cluster3433 = new BitSet(new long[]{0x0080000000000002L});
    public static final BitSet FOLLOW_cluster_components_in_cluster3447 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_55_in_cluster_components3502 = new BitSet(new long[]{0x0E0000000E000020L});
    public static final BitSet FOLLOW_static_block_in_cluster_components3504 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_cluster_components3506 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_57_in_clazz3557 = new BitSet(new long[]{0x0000000004000000L});
    public static final BitSet FOLLOW_58_in_clazz3574 = new BitSet(new long[]{0x0000000004000000L});
    public static final BitSet FOLLOW_59_in_clazz3587 = new BitSet(new long[]{0x0000000004000000L});
    public static final BitSet FOLLOW_26_in_clazz3621 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_in_clazz3632 = new BitSet(new long[]{0x3100004040000000L,0x0000000000000184L});
    public static final BitSet FOLLOW_formal_generics_in_clazz3645 = new BitSet(new long[]{0x3100004040000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_56_in_clazz3667 = new BitSet(new long[]{0x3000004040000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_60_in_clazz3680 = new BitSet(new long[]{0x2000004040000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_61_in_clazz3694 = new BitSet(new long[]{0x0000004040000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_comment_in_clazz3702 = new BitSet(new long[]{0x0000004040000002L,0x0000000000000180L});
    public static final BitSet FOLLOW_class_interface_in_clazz3714 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_inheritance_relation_in_static_relation3772 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_client_relation_in_static_relation3784 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_child_in_inheritance_relation3815 = new BitSet(new long[]{0x0000004000000000L});
    public static final BitSet FOLLOW_38_in_inheritance_relation3817 = new BitSet(new long[]{0x4000000000000020L});
    public static final BitSet FOLLOW_62_in_inheritance_relation3825 = new BitSet(new long[]{0x0000000000000040L});
    public static final BitSet FOLLOW_multiplicity_in_inheritance_relation3827 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_63_in_inheritance_relation3831 = new BitSet(new long[]{0x4000000000000020L});
    public static final BitSet FOLLOW_parent_in_inheritance_relation3848 = new BitSet(new long[]{0x0000000000000012L});
    public static final BitSet FOLLOW_semantic_label_in_inheritance_relation3859 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_client_in_client_relation3918 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000001L});
    public static final BitSet FOLLOW_64_in_client_relation3920 = new BitSet(new long[]{0x4000000400000020L,0x0000000000000020L});
    public static final BitSet FOLLOW_client_entities_in_client_relation3925 = new BitSet(new long[]{0x4000000400000020L,0x0000000000000020L});
    public static final BitSet FOLLOW_type_mark_in_client_relation3937 = new BitSet(new long[]{0x4000000400000020L,0x0000000000000020L});
    public static final BitSet FOLLOW_supplier_in_client_relation3963 = new BitSet(new long[]{0x0000000000000012L});
    public static final BitSet FOLLOW_semantic_label_in_client_relation3973 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_62_in_client_entities4014 = new BitSet(new long[]{0x0000040000000060L,0x0000000000028016L});
    public static final BitSet FOLLOW_client_entity_expression_in_client_entities4018 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_63_in_client_entities4020 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_client_entity_list_in_client_entity_expression4059 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_multiplicity_in_client_entity_expression4072 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_client_entity_in_client_entity_list4125 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_client_entity_list4134 = new BitSet(new long[]{0x0000040000000020L,0x0000000000028016L});
    public static final BitSet FOLLOW_client_entity_in_client_entity_list4138 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_prefix_in_client_entity4189 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_infix_in_client_entity4194 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_supplier_indirection_in_client_entity4199 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_parent_indirection_in_client_entity4210 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indirection_feature_part_in_supplier_indirection4256 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_34_in_supplier_indirection4260 = new BitSet(new long[]{0x0000040000000020L,0x0000000000028014L});
    public static final BitSet FOLLOW_generic_indirection_in_supplier_indirection4269 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_name_in_indirection_feature_part4318 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indirection_feature_list_in_indirection_feature_part4329 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_42_in_indirection_feature_list4379 = new BitSet(new long[]{0x0000000000000020L,0x0000000000028000L});
    public static final BitSet FOLLOW_feature_name_list_in_indirection_feature_list4383 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_43_in_indirection_feature_list4387 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_65_in_parent_indirection4435 = new BitSet(new long[]{0x0000040000000020L,0x0000000000028014L});
    public static final BitSet FOLLOW_generic_indirection_in_parent_indirection4439 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indirection_element_in_generic_indirection4491 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_named_indirection4536 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000004L});
    public static final BitSet FOLLOW_66_in_named_indirection4538 = new BitSet(new long[]{0x0000040000000020L,0x0000000000028014L});
    public static final BitSet FOLLOW_indirection_list_in_named_indirection4542 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_67_in_named_indirection4546 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_66_in_named_indirection4561 = new BitSet(new long[]{0x0000040000000020L,0x0000000000028014L});
    public static final BitSet FOLLOW_indirection_list_in_named_indirection4563 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_67_in_named_indirection4565 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indirection_element_in_indirection_list4612 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_indirection_list4622 = new BitSet(new long[]{0x0000040000000020L,0x0000000000028014L});
    public static final BitSet FOLLOW_indirection_element_in_indirection_list4626 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_68_in_indirection_element4680 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_named_indirection_in_indirection_element4690 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_indirection_element4701 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_34_in_type_mark4746 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_69_in_type_mark4759 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_shared_mark_in_type_mark4772 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_34_in_shared_mark4818 = new BitSet(new long[]{0x0000040000000000L});
    public static final BitSet FOLLOW_42_in_shared_mark4820 = new BitSet(new long[]{0x0000000000000040L});
    public static final BitSet FOLLOW_multiplicity_in_shared_mark4824 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_43_in_shared_mark4828 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_ref_in_child4852 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_ref_in_parent4880 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_ref_in_client4918 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_ref_in_supplier4948 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_component_name_in_static_ref4982 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cluster_prefix_in_static_ref4998 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_static_component_name_in_static_ref5002 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_prefix5041 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_cluster_prefix5050 = new BitSet(new long[]{0x0000000000000022L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_prefix5059 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_cluster_prefix5061 = new BitSet(new long[]{0x0000000000000022L});
    public static final BitSet FOLLOW_IDENTIFIER_in_static_component_name5093 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_INTEGER_in_multiplicity5137 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_semantic_label5173 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_interface_start_indexing_in_class_interface5199 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_interface_start_inherit_in_class_interface5209 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_interface_start_features_in_class_interface5219 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_interface_start_invariant_in_class_interface5229 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indexing_in_class_interface_start_indexing5251 = new BitSet(new long[]{0x0000004042000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_parent_class_list_in_class_interface_start_indexing5263 = new BitSet(new long[]{0x0000004042000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_features_in_class_interface_start_indexing5276 = new BitSet(new long[]{0x0000004042000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_class_invariant_in_class_interface_start_indexing5290 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_class_interface_start_indexing5301 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_parent_class_list_in_class_interface_start_inherit5327 = new BitSet(new long[]{0x0000004042000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_features_in_class_interface_start_inherit5337 = new BitSet(new long[]{0x0000004042000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_class_invariant_in_class_interface_start_inherit5351 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_class_interface_start_inherit5362 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_features_in_class_interface_start_features5386 = new BitSet(new long[]{0x0000004042000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_class_invariant_in_class_interface_start_features5397 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_class_interface_start_features5408 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_invariant_in_class_interface_start_invariant5434 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_class_interface_start_invariant5442 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_71_in_class_invariant5461 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_assertion_in_class_invariant5463 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_38_in_parent_class_list5504 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_type_in_parent_class_list5508 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_parent_class_list5519 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_type_in_parent_class_list5523 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_parent_class_list5540 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_38_in_parent_class_list5551 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_clause_in_features5595 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000100L});
    public static final BitSet FOLLOW_72_in_feature_clause5636 = new BitSet(new long[]{0x4C00000000000020L,0x0000000000028200L});
    public static final BitSet FOLLOW_selective_export_in_feature_clause5646 = new BitSet(new long[]{0x4C00000000000020L,0x0000000000028200L});
    public static final BitSet FOLLOW_comment_in_feature_clause5665 = new BitSet(new long[]{0x4C00000000000020L,0x0000000000028200L});
    public static final BitSet FOLLOW_feature_specifications_in_feature_clause5673 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_specification_in_feature_specifications5716 = new BitSet(new long[]{0x4C00000000000022L,0x0000000000028200L});
    public static final BitSet FOLLOW_58_in_feature_specification5771 = new BitSet(new long[]{0x0000000000000020L,0x0000000000028000L});
    public static final BitSet FOLLOW_59_in_feature_specification5784 = new BitSet(new long[]{0x0000000000000020L,0x0000000000028000L});
    public static final BitSet FOLLOW_73_in_feature_specification5795 = new BitSet(new long[]{0x0000000000000020L,0x0000000000028000L});
    public static final BitSet FOLLOW_feature_name_list_in_feature_specification5826 = new BitSet(new long[]{0x4000000400000000L,0x0000000000005822L});
    public static final BitSet FOLLOW_has_type_in_feature_specification5835 = new BitSet(new long[]{0x4000000000000000L,0x0000000000005802L});
    public static final BitSet FOLLOW_rename_clause_in_feature_specification5847 = new BitSet(new long[]{0x0000000000000000L,0x0000000000005802L});
    public static final BitSet FOLLOW_comment_in_feature_specification5856 = new BitSet(new long[]{0x0000000000000002L,0x0000000000005802L});
    public static final BitSet FOLLOW_feature_arguments_in_feature_specification5867 = new BitSet(new long[]{0x0000000000000002L,0x0000000000001800L});
    public static final BitSet FOLLOW_contract_clause_in_feature_specification5894 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_type_mark_in_has_type5957 = new BitSet(new long[]{0x0000000000000020L,0x0000000000000400L});
    public static final BitSet FOLLOW_type_in_has_type5965 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_74_in_has_type5982 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_contracting_conditions_in_contract_clause6013 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_contract_clause6015 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_precondition_in_contracting_conditions6047 = new BitSet(new long[]{0x0000000000000002L,0x0000000000001800L});
    public static final BitSet FOLLOW_postcondition_in_contracting_conditions6052 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_postcondition_in_contracting_conditions6076 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_75_in_precondition6102 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_assertion_in_precondition6104 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_76_in_postcondition6138 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_assertion_in_postcondition6140 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_62_in_selective_export6163 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_list_in_selective_export6167 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_63_in_selective_export6169 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_name_in_feature_name_list6214 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_feature_name_list6224 = new BitSet(new long[]{0x0000000000000020L,0x0000000000028000L});
    public static final BitSet FOLLOW_feature_name_in_feature_name_list6228 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_feature_name6277 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_prefix_in_feature_name6287 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_infix_in_feature_name6293 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_62_in_rename_clause6323 = new BitSet(new long[]{0x0000000000000000L,0x0000000000002000L});
    public static final BitSet FOLLOW_renaming_in_rename_clause6325 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_63_in_rename_clause6327 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_77_in_renaming6363 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_in_renaming6365 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_renaming6367 = new BitSet(new long[]{0x0000000000000020L,0x0000000000028000L});
    public static final BitSet FOLLOW_feature_name_in_renaming6369 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_argument_in_feature_arguments6404 = new BitSet(new long[]{0x0000000000000002L,0x0000000000004002L});
    public static final BitSet FOLLOW_set_in_feature_argument6444 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_identifier_list_in_feature_argument6468 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_34_in_feature_argument6470 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_type_in_feature_argument6474 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_type_in_feature_argument6506 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_identifier_list6566 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_identifier_list6576 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_IDENTIFIER_in_identifier_list6580 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_79_in_prefix6597 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010000L});
    public static final BitSet FOLLOW_80_in_prefix6599 = new BitSet(new long[]{0x0000000000000000L,0x0000718000000000L});
    public static final BitSet FOLLOW_prefix_operator_in_prefix6601 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010000L});
    public static final BitSet FOLLOW_80_in_prefix6603 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_81_in_infix6622 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010000L});
    public static final BitSet FOLLOW_80_in_infix6624 = new BitSet(new long[]{0x0000000400000000L,0x01FFCFC000402002L});
    public static final BitSet FOLLOW_infix_operator_in_infix6626 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010000L});
    public static final BitSet FOLLOW_80_in_infix6628 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unary_in_prefix_operator6648 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_binary_in_infix_operator6663 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_66_in_formal_generics6682 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_formal_generic_list_in_formal_generics6686 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_67_in_formal_generics6688 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_formal_generic_in_formal_generic_list6731 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_formal_generic_list6740 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_formal_generic_in_formal_generic_list6744 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_formal_generic_name_in_formal_generic6794 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_formal_generic_name_in_formal_generic6806 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000002L});
    public static final BitSet FOLLOW_65_in_formal_generic6808 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_type_in_formal_generic6812 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_formal_generic_name6851 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_class_type6896 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000004L});
    public static final BitSet FOLLOW_actual_generics_in_class_type6904 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_66_in_actual_generics6975 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_type_list_in_actual_generics6977 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_67_in_actual_generics6979 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_type_in_type_list7043 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_type_list7071 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_type_in_type_list7075 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_type7130 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000004L});
    public static final BitSet FOLLOW_actual_generics_in_type7152 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_assertion_clause_in_assertion7231 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_assertion7240 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_assertion_clause_in_assertion7244 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_assertion7261 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_boolean_expression_in_assertion_clause7290 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_expression_in_boolean_expression7312 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_quantifier_in_quantification7352 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_range_expression_in_quantification7359 = new BitSet(new long[]{0x0000000000000000L,0x0000000000300000L});
    public static final BitSet FOLLOW_restriction_in_quantification7367 = new BitSet(new long[]{0x0000000000000000L,0x0000000000300000L});
    public static final BitSet FOLLOW_proposition_in_quantification7379 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_82_in_quantifier7418 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_83_in_quantifier7431 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_variable_range_in_range_expression7469 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_range_expression7479 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_variable_range_in_range_expression7483 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_range_expression7498 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_84_in_restriction7535 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_boolean_expression_in_restriction7539 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_85_in_proposition7573 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_boolean_expression_in_proposition7577 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_member_range_in_variable_range7613 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_type_range_in_variable_range7625 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_identifier_list_in_member_range7665 = new BitSet(new long[]{0x0000000000000000L,0x0000000000400000L});
    public static final BitSet FOLLOW_86_in_member_range7667 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_expression_in_member_range7671 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_identifier_list_in_type_range7707 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_34_in_type_range7709 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_type_in_type_range7713 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unqualified_call_in_call_chain7773 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_call_chain7782 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F000400L});
    public static final BitSet FOLLOW_unqualified_call_in_call_chain7786 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_IDENTIFIER_in_unqualified_call7827 = new BitSet(new long[]{0x0000040000000002L});
    public static final BitSet FOLLOW_actual_arguments_in_unqualified_call7841 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_42_in_actual_arguments7880 = new BitSet(new long[]{0x40000C00000001F0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_expression_list_in_actual_arguments7890 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_43_in_actual_arguments7913 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_expression_in_expression_list7949 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_expression_list7959 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_expression_in_expression_list7963 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_62_in_enumerated_set8009 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_enumeration_list_in_enumerated_set8013 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_63_in_enumerated_set8015 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_enumeration_element_in_enumeration_list8057 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_enumeration_list8067 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_enumeration_element_in_enumeration_list8071 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_expression_in_enumeration_element8103 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_interval_in_enumeration_element8117 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_integer_interval_in_interval8164 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_character_interval_in_interval8176 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_integer_constant_in_integer_interval8209 = new BitSet(new long[]{0x0000000000000000L,0x0000000000800000L});
    public static final BitSet FOLLOW_87_in_integer_interval8211 = new BitSet(new long[]{0x0000000000000040L,0x0000018000000000L});
    public static final BitSet FOLLOW_integer_constant_in_integer_interval8215 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_character_constant_in_character_interval8257 = new BitSet(new long[]{0x0000000000000000L,0x0000000000800000L});
    public static final BitSet FOLLOW_87_in_character_interval8259 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_character_constant_in_character_interval8263 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_constant_in_constant8289 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_88_in_constant8302 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_74_in_constant8315 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_89_in_constant8339 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_boolean_constant_in_manifest_constant8362 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_character_constant_in_manifest_constant8375 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_integer_constant_in_manifest_constant8388 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_real_constant_in_manifest_constant8401 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_manifest_constant8414 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_enumerated_set_in_manifest_constant8427 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_in_sign8466 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_90_in_boolean_constant8492 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_91_in_boolean_constant8503 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CHARACTER_CONSTANT_in_character_constant8527 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_integer_constant8593 = new BitSet(new long[]{0x0000000000000040L});
    public static final BitSet FOLLOW_INTEGER_in_integer_constant8604 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_real_constant8649 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_REAL_in_real_constant8661 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_92_in_dynamic_diagram8692 = new BitSet(new long[]{0x0080000000000060L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_diagram8700 = new BitSet(new long[]{0x0080000000000000L});
    public static final BitSet FOLLOW_comment_in_dynamic_diagram8710 = new BitSet(new long[]{0x0080000000000000L});
    public static final BitSet FOLLOW_55_in_dynamic_diagram8716 = new BitSet(new long[]{0x0004000002000060L,0x00000003C0000000L});
    public static final BitSet FOLLOW_dynamic_block_in_dynamic_diagram8725 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_dynamic_diagram8749 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_dynamic_component_in_dynamic_block8792 = new BitSet(new long[]{0x0004000000000062L,0x00000003C0000000L});
    public static final BitSet FOLLOW_scenario_description_in_dynamic_component8829 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_object_group_in_dynamic_component8834 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_object_stack_in_dynamic_component8840 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_object_in_dynamic_component8845 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_message_relation_in_dynamic_component8850 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_50_in_scenario_description8878 = new BitSet(new long[]{0x0000000000000410L});
    public static final BitSet FOLLOW_scenario_name_in_scenario_description8880 = new BitSet(new long[]{0x0000000000000000L,0x0000000020000000L});
    public static final BitSet FOLLOW_comment_in_scenario_description8885 = new BitSet(new long[]{0x0000000000000000L,0x0000000020000000L});
    public static final BitSet FOLLOW_93_in_scenario_description8891 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_labelled_actions_in_scenario_description8898 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_scenario_description8905 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_labelled_action_in_labelled_actions8953 = new BitSet(new long[]{0x0000000000000012L});
    public static final BitSet FOLLOW_action_label_in_labelled_action8994 = new BitSet(new long[]{0x0000000000000410L});
    public static final BitSet FOLLOW_action_description_in_labelled_action8998 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_action_label9037 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_action_description9072 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_scenario_name9113 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_94_in_object_group9146 = new BitSet(new long[]{0x0000000000000000L,0x0000000080000000L});
    public static final BitSet FOLLOW_95_in_object_group9171 = new BitSet(new long[]{0x0000000000000060L});
    public static final BitSet FOLLOW_group_name_in_object_group9177 = new BitSet(new long[]{0x0080000000000000L});
    public static final BitSet FOLLOW_comment_in_object_group9186 = new BitSet(new long[]{0x0080000000000002L});
    public static final BitSet FOLLOW_group_components_in_object_group9197 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_55_in_group_components9248 = new BitSet(new long[]{0x0004000000000060L,0x00000003C0000000L});
    public static final BitSet FOLLOW_dynamic_block_in_group_components9250 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_group_components9252 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_96_in_object_stack9297 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_object_name_in_object_stack9304 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_comment_in_object_stack9313 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_97_in_object9358 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_object_name_in_object9365 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_comment_in_object9374 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_caller_in_message_relation9395 = new BitSet(new long[]{0x0000000000000000L,0x0000000400000000L});
    public static final BitSet FOLLOW_98_in_message_relation9397 = new BitSet(new long[]{0x0004000000000060L,0x00000003C0000000L});
    public static final BitSet FOLLOW_receiver_in_message_relation9399 = new BitSet(new long[]{0x0000000000000012L});
    public static final BitSet FOLLOW_message_label_in_message_relation9402 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_dynamic_ref_in_caller9434 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_dynamic_ref_in_receiver9454 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_ref9480 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_dynamic_ref9483 = new BitSet(new long[]{0x0000000000000060L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_ref9485 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_IDENTIFIER_in_dynamic_component_name9516 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_dynamic_component_name9519 = new BitSet(new long[]{0x0000000000000060L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_component_name9521 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_INTEGER_in_dynamic_component_name9530 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_object_name9553 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_object_name9563 = new BitSet(new long[]{0x0000000000000060L});
    public static final BitSet FOLLOW_extended_id_in_object_name9567 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_extended_id_in_group_name9607 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_message_label9640 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_change_string_marks_in_notational_tuning9664 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_change_concatenator_in_notational_tuning9670 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_change_prefix_in_notational_tuning9675 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_99_in_change_string_marks9690 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_string_marks9692 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_string_marks9694 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_100_in_change_concatenator9728 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_concatenator9730 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_101_in_change_prefix9764 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_prefix9766 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_equivalence_expression_in_expression9792 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_quantification_in_expression9806 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_implies_expression_in_equivalence_expression9828 = new BitSet(new long[]{0x0000000000000002L,0x0000004000000000L});
    public static final BitSet FOLLOW_102_in_equivalence_expression9838 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F000400L});
    public static final BitSet FOLLOW_implies_expression_in_equivalence_expression9842 = new BitSet(new long[]{0x0000000000000002L,0x0000004000000000L});
    public static final BitSet FOLLOW_and_or_xor_expression_in_implies_expression9870 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000002L});
    public static final BitSet FOLLOW_65_in_implies_expression9880 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F000400L});
    public static final BitSet FOLLOW_implies_expression_in_implies_expression9884 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_comparison_expression_in_and_or_xor_expression9911 = new BitSet(new long[]{0x0000000000000002L,0x00000E0000000000L});
    public static final BitSet FOLLOW_and_or_xor_op_in_and_or_xor_expression9924 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F000400L});
    public static final BitSet FOLLOW_comparison_expression_in_and_or_xor_expression9928 = new BitSet(new long[]{0x0000000000000002L,0x00000E0000000000L});
    public static final BitSet FOLLOW_add_sub_expression_in_comparison_expression9956 = new BitSet(new long[]{0x0000000400000002L,0x001FC00000400000L});
    public static final BitSet FOLLOW_comparison_op_in_comparison_expression9968 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F000400L});
    public static final BitSet FOLLOW_add_sub_expression_in_comparison_expression9973 = new BitSet(new long[]{0x0000000400000002L,0x001FC00000400000L});
    public static final BitSet FOLLOW_mul_div_expression_in_add_sub_expression10001 = new BitSet(new long[]{0x0000000000000002L,0x0000018000000000L});
    public static final BitSet FOLLOW_add_sub_op_in_add_sub_expression10013 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F000400L});
    public static final BitSet FOLLOW_mul_div_expression_in_add_sub_expression10017 = new BitSet(new long[]{0x0000000000000002L,0x0000018000000000L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mul_div_expression10045 = new BitSet(new long[]{0x0000000000000002L,0x00E0000000000000L});
    public static final BitSet FOLLOW_mul_div_op_in_mul_div_expression10057 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F000400L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mul_div_expression10061 = new BitSet(new long[]{0x0000000000000002L,0x00E0000000000000L});
    public static final BitSet FOLLOW_lowest_expression_in_mod_pow_expression10090 = new BitSet(new long[]{0x0000000000000002L,0x0100000000002000L});
    public static final BitSet FOLLOW_mod_pow_op_in_mod_pow_expression10102 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F000400L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mod_pow_expression10106 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constant_in_lowest_expression10139 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_lowest_expression10148 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F000400L});
    public static final BitSet FOLLOW_call_chain_in_lowest_expression10152 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unary_in_lowest_expression10202 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F000400L});
    public static final BitSet FOLLOW_lowest_expression_in_lowest_expression10206 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_42_in_lowest_expression10219 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_expression_in_lowest_expression10223 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_43_in_lowest_expression10225 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_lowest_expression10235 = new BitSet(new long[]{0x40000400000001F0L,0x000071800F000400L});
    public static final BitSet FOLLOW_call_chain_in_lowest_expression10239 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_call_chain_in_lowest_expression10275 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_103_in_add_sub_op10299 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_104_in_add_sub_op10307 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_103_in_add_sub_op_unary10325 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_104_in_add_sub_op_unary10333 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_105_in_and_or_xor_op10351 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_106_in_and_or_xor_op10358 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_107_in_and_or_xor_op10366 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_other_unary_in_unary10386 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_unary_in_unary10400 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_108_in_other_unary10420 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_109_in_other_unary10428 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_110_in_other_unary10437 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_in_binary10468 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_mul_div_op_in_binary10472 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_comparison_op_in_binary10476 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_mod_pow_op_in_binary10491 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_and_or_xor_op_in_binary10495 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_65_in_binary10510 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_102_in_binary10514 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_111_in_comparison_op10530 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_112_in_comparison_op10538 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_113_in_comparison_op10546 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_114_in_comparison_op10553 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_115_in_comparison_op10560 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_116_in_comparison_op10568 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_86_in_comparison_op10575 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_110_in_comparison_op10582 = new BitSet(new long[]{0x0000000000000000L,0x0000000000400000L});
    public static final BitSet FOLLOW_86_in_comparison_op10584 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_34_in_comparison_op10591 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_117_in_mul_div_op10618 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_118_in_mul_div_op10626 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_119_in_mul_div_op10634 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_120_in_mod_pow_op10667 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_77_in_mod_pow_op10675 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_manifest_textblock10987 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_START_in_manifest_textblock10993 = new BitSet(new long[]{0x0000000000001800L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_MIDDLE_in_manifest_textblock10995 = new BitSet(new long[]{0x0000000000001800L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_END_in_manifest_textblock10998 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constant_in_synpred1_BON10135 = new BitSet(new long[]{0x0000000000000002L});

}