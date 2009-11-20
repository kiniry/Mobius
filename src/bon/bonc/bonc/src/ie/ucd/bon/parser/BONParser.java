// $ANTLR 3.1.3 Apr 15, 2009 15:48:38 BON.g 2009-11-20 10:00:39

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
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "MANIFEST_STRING", "IDENTIFIER", "COMMENT", "INTEGER", "CHARACTER_CONSTANT", "REAL", "NEWLINE", "MANIFEST_TEXTBLOCK_START", "MANIFEST_TEXTBLOCK_MIDDLE", "MANIFEST_TEXTBLOCK_END", "LINE_COMMENT", "COMMENT_START", "DIGIT", "ALPHA", "ALPHANUMERIC_OR_UNDERSCORE", "ALPHANUMERIC", "UNDERSCORE", "LOWER", "UPPER", "WHITESPACE", "'dictionary'", "'end'", "'class'", "'cluster'", "'system_chart'", "'explanation'", "'indexing'", "'part'", "'description'", "';'", "':'", "','", "'cluster_chart'", "'class_chart'", "'inherit'", "'query'", "'command'", "'constraint'", "'('", "')'", "'event_chart'", "'incoming'", "'outgoing'", "'event'", "'involves'", "'scenario_chart'", "'scenario'", "'creation_chart'", "'creator'", "'creates'", "'static_diagram'", "'component'", "'reused'", "'root'", "'deferred'", "'effective'", "'persistent'", "'interfaced'", "'{'", "'}'", "'client'", "'->'", "'['", "']'", "'...'", "':{'", "'.'", "'invariant'", "'feature'", "'redefined'", "'Void'", "'require'", "'ensure'", "'^'", "'<-'", "'prefix'", "'\"'", "'infix'", "'for_all'", "'exists'", "'such_that'", "'it_holds'", "'member_of'", "'..'", "'Current'", "'Result'", "'true'", "'false'", "'dynamic_diagram'", "'action'", "'nameless'", "'object_group'", "'object_stack'", "'object'", "'calls'", "'string_marks'", "'concatenator'", "'keyword_prefix'", "'<->'", "'+'", "'-'", "'and'", "'or'", "'xor'", "'delta'", "'old'", "'not'", "'<'", "'>'", "'<='", "'>='", "'='", "'/='", "'*'", "'/'", "'//'", "'\\\\\\\\'"
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
    public static final int MANIFEST_TEXTBLOCK_END=13;
    public static final int ALPHANUMERIC_OR_UNDERSCORE=18;
    public static final int COMMENT=6;
    public static final int T__99=99;
    public static final int T__98=98;
    public static final int T__97=97;
    public static final int T__96=96;
    public static final int T__95=95;
    public static final int T__80=80;
    public static final int T__81=81;
    public static final int T__82=82;
    public static final int T__83=83;
    public static final int LINE_COMMENT=14;
    public static final int WHITESPACE=23;
    public static final int UNDERSCORE=20;
    public static final int T__85=85;
    public static final int T__84=84;
    public static final int T__87=87;
    public static final int T__86=86;
    public static final int T__89=89;
    public static final int ALPHA=17;
    public static final int T__88=88;
    public static final int REAL=9;
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
    public static final int CHARACTER_CONSTANT=8;
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
    public static final int MANIFEST_TEXTBLOCK_START=11;
    public static final int T__104=104;
    public static final int T__105=105;
    public static final int T__106=106;
    public static final int T__111=111;
    public static final int T__110=110;
    public static final int T__113=113;
    public static final int T__112=112;
    public static final int DIGIT=16;
    public static final int T__50=50;
    public static final int INTEGER=7;
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
    public static final int NEWLINE=10;
    public static final int T__35=35;
    public static final int T__36=36;
    public static final int T__37=37;
    public static final int T__38=38;
    public static final int T__39=39;
    public static final int MANIFEST_TEXTBLOCK_MIDDLE=12;

    // delegates
    // delegators


        public BONParser(TokenStream input) {
            this(input, new RecognizerSharedState());
        }
        public BONParser(TokenStream input, RecognizerSharedState state) {
            super(input, state);
             
        }
        

    public String[] getTokenNames() { return BONParser.tokenNames; }
    public String getGrammarFileName() { return "BON.g"; }


      //Nothing



    // $ANTLR start "prog"
    // BON.g:32:1: prog returns [BonSourceFile bonSource] : (bs= bon_specification EOF | i= indexing bs= bon_specification EOF | e= EOF | indexing e= EOF );
    public final BonSourceFile prog() throws RecognitionException {
        BonSourceFile bonSource = null;

        Token e=null;
        BONParser.bon_specification_return bs = null;

        BONParser.indexing_return i = null;

        BONParser.indexing_return indexing1 = null;


        try {
            // BON.g:38:40: (bs= bon_specification EOF | i= indexing bs= bon_specification EOF | e= EOF | indexing e= EOF )
            int alt1=4;
            alt1 = dfa1.predict(input);
            switch (alt1) {
                case 1 :
                    // BON.g:39:10: bs= bon_specification EOF
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
                    // BON.g:42:10: i= indexing bs= bon_specification EOF
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
                    // BON.g:45:10: e= EOF
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
                    // BON.g:49:10: indexing e= EOF
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
    // BON.g:54:1: bon_specification returns [List<SpecificationElement> spec_els] : (se= specification_element )+ ;
    public final BONParser.bon_specification_return bon_specification() throws RecognitionException {
        BONParser.bon_specification_return retval = new BONParser.bon_specification_return();
        retval.start = input.LT(1);

        SpecificationElement se = null;


        try {
            // BON.g:58:65: ( (se= specification_element )+ )
            // BON.g:59:3: (se= specification_element )+
            {
            if ( state.backtracking==0 ) {
               retval.spec_els = createList(); 
            }
            // BON.g:60:3: (se= specification_element )+
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
            	    // BON.g:60:5: se= specification_element
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
    // BON.g:65:1: specification_element returns [SpecificationElement se] : (ic= informal_chart | cd= class_dictionary | sd= static_diagram | dd= dynamic_diagram );
    public final SpecificationElement specification_element() throws RecognitionException {
        SpecificationElement se = null;

        InformalChart ic = null;

        ClassDictionary cd = null;

        StaticDiagram sd = null;

        DynamicDiagram dd = null;


        try {
            // BON.g:65:57: (ic= informal_chart | cd= class_dictionary | sd= static_diagram | dd= dynamic_diagram )
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
                    // BON.g:66:5: ic= informal_chart
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
                    // BON.g:68:5: cd= class_dictionary
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
                    // BON.g:70:5: sd= static_diagram
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
                    // BON.g:72:5: dd= dynamic_diagram
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
    // BON.g:78:1: informal_chart returns [InformalChart ic] : ( system_chart | cluster_chart | class_chart | event_chart | scenario_chart | creation_chart );
    public final InformalChart informal_chart() throws RecognitionException {
        InformalChart ic = null;

        ClusterChart system_chart2 = null;

        ClusterChart cluster_chart3 = null;

        ClassChart class_chart4 = null;

        EventChart event_chart5 = null;

        ScenarioChart scenario_chart6 = null;

        BONParser.creation_chart_return creation_chart7 = null;


        try {
            // BON.g:82:43: ( system_chart | cluster_chart | class_chart | event_chart | scenario_chart | creation_chart )
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
                    // BON.g:83:5: system_chart
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
                    // BON.g:85:5: cluster_chart
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
                    // BON.g:87:5: class_chart
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
                    // BON.g:89:5: event_chart
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
                    // BON.g:91:5: scenario_chart
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
                    // BON.g:93:5: creation_chart
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
    // BON.g:97:1: class_dictionary returns [ClassDictionary cd] : d= 'dictionary' system_name ( indexing )? ( explanation )? ( part )? (de= dictionary_entry )+ e= 'end' ;
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
            // BON.g:100:1: (d= 'dictionary' system_name ( indexing )? ( explanation )? ( part )? (de= dictionary_entry )+ e= 'end' )
            // BON.g:101:3: d= 'dictionary' system_name ( indexing )? ( explanation )? ( part )? (de= dictionary_entry )+ e= 'end'
            {
            d=(Token)match(input,24,FOLLOW_24_in_class_dictionary437); if (state.failed) return cd;
            pushFollow(FOLLOW_system_name_in_class_dictionary442);
            system_name11=system_name();

            state._fsp--;
            if (state.failed) return cd;
            // BON.g:103:3: ( indexing )?
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0==30) ) {
                alt5=1;
            }
            switch (alt5) {
                case 1 :
                    // BON.g:103:4: indexing
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

            // BON.g:104:3: ( explanation )?
            int alt6=2;
            int LA6_0 = input.LA(1);

            if ( (LA6_0==29) ) {
                alt6=1;
            }
            switch (alt6) {
                case 1 :
                    // BON.g:104:4: explanation
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

            // BON.g:105:3: ( part )?
            int alt7=2;
            int LA7_0 = input.LA(1);

            if ( (LA7_0==31) ) {
                alt7=1;
            }
            switch (alt7) {
                case 1 :
                    // BON.g:105:4: part
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

            // BON.g:106:3: (de= dictionary_entry )+
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
            	    // BON.g:106:4: de= dictionary_entry
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
    // BON.g:113:1: dictionary_entry returns [DictionaryEntry entry] : c= 'class' class_name 'cluster' cluster_name_list description ;
    public final DictionaryEntry dictionary_entry() throws RecognitionException {
        DictionaryEntry entry = null;

        Token c=null;
        BONParser.class_name_return class_name12 = null;

        List<String> cluster_name_list13 = null;

        BONParser.description_return description14 = null;


        try {
            // BON.g:113:50: (c= 'class' class_name 'cluster' cluster_name_list description )
            // BON.g:114:3: c= 'class' class_name 'cluster' cluster_name_list description
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
    // BON.g:120:1: system_chart returns [ClusterChart sc] : s= 'system_chart' system_name ( indexing )? ( explanation )? ( part )? (ce= cluster_entries | ) e= 'end' ;
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
            // BON.g:125:1: (s= 'system_chart' system_name ( indexing )? ( explanation )? ( part )? (ce= cluster_entries | ) e= 'end' )
            // BON.g:126:3: s= 'system_chart' system_name ( indexing )? ( explanation )? ( part )? (ce= cluster_entries | ) e= 'end'
            {
            s=(Token)match(input,28,FOLLOW_28_in_system_chart570); if (state.failed) return sc;
            pushFollow(FOLLOW_system_name_in_system_chart575);
            system_name18=system_name();

            state._fsp--;
            if (state.failed) return sc;
            // BON.g:128:3: ( indexing )?
            int alt9=2;
            int LA9_0 = input.LA(1);

            if ( (LA9_0==30) ) {
                alt9=1;
            }
            switch (alt9) {
                case 1 :
                    // BON.g:128:4: indexing
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

            // BON.g:129:3: ( explanation )?
            int alt10=2;
            int LA10_0 = input.LA(1);

            if ( (LA10_0==29) ) {
                alt10=1;
            }
            switch (alt10) {
                case 1 :
                    // BON.g:129:4: explanation
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

            // BON.g:130:3: ( part )?
            int alt11=2;
            int LA11_0 = input.LA(1);

            if ( (LA11_0==31) ) {
                alt11=1;
            }
            switch (alt11) {
                case 1 :
                    // BON.g:130:4: part
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

            // BON.g:131:3: (ce= cluster_entries | )
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
                    // BON.g:131:6: ce= cluster_entries
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
                    // BON.g:133:6: 
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
    // BON.g:139:1: explanation returns [String explanation] : (e= 'explanation' m= manifest_textblock | e= 'explanation' );
    public final String explanation() throws RecognitionException {
        String explanation = null;

        Token e=null;
        BONParser.manifest_textblock_return m = null;


        try {
            // BON.g:139:42: (e= 'explanation' m= manifest_textblock | e= 'explanation' )
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
                    // BON.g:140:3: e= 'explanation' m= manifest_textblock
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
                    // BON.g:143:3: e= 'explanation'
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
    // BON.g:147:1: indexing returns [Indexing indexing] : (i= 'indexing' index_list | i= 'indexing' );
    public final BONParser.indexing_return indexing() throws RecognitionException {
        BONParser.indexing_return retval = new BONParser.indexing_return();
        retval.start = input.LT(1);

        Token i=null;
        BONParser.index_list_return index_list19 = null;


        try {
            // BON.g:147:38: (i= 'indexing' index_list | i= 'indexing' )
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
                    // BON.g:148:4: i= 'indexing' index_list
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
                    // BON.g:151:4: i= 'indexing'
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
    // BON.g:156:1: part returns [String part] : (p= 'part' m= MANIFEST_STRING | p= 'part' );
    public final String part() throws RecognitionException {
        String part = null;

        Token p=null;
        Token m=null;

        try {
            // BON.g:156:28: (p= 'part' m= MANIFEST_STRING | p= 'part' )
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
                    // BON.g:157:5: p= 'part' m= MANIFEST_STRING
                    {
                    p=(Token)match(input,31,FOLLOW_31_in_part755); if (state.failed) return part;
                    m=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_part759); if (state.failed) return part;
                    if ( state.backtracking==0 ) {
                       if(isOk()) part = (m!=null?m.getText():null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:160:5: p= 'part'
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
    // BON.g:165:1: description returns [String description] : d= 'description' m= manifest_textblock ;
    public final BONParser.description_return description() throws RecognitionException {
        BONParser.description_return retval = new BONParser.description_return();
        retval.start = input.LT(1);

        Token d=null;
        BONParser.manifest_textblock_return m = null;


        try {
            // BON.g:165:42: (d= 'description' m= manifest_textblock )
            // BON.g:166:3: d= 'description' m= manifest_textblock
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
    // BON.g:170:1: cluster_entries returns [List<ClusterEntry> entries] : ( cluster_entry )+ ;
    public final List<ClusterEntry> cluster_entries() throws RecognitionException {
        List<ClusterEntry> entries = null;

        ClusterEntry cluster_entry20 = null;


        try {
            // BON.g:170:54: ( ( cluster_entry )+ )
            // BON.g:171:3: ( cluster_entry )+
            {
            if ( state.backtracking==0 ) {
               entries = createList(); 
            }
            // BON.g:172:3: ( cluster_entry )+
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
            	    // BON.g:172:4: cluster_entry
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
    // BON.g:175:1: cluster_entry returns [ClusterEntry ce] : c= 'cluster' cluster_name description ;
    public final ClusterEntry cluster_entry() throws RecognitionException {
        ClusterEntry ce = null;

        Token c=null;
        BONParser.cluster_name_return cluster_name21 = null;

        BONParser.description_return description22 = null;


        try {
            // BON.g:175:41: (c= 'cluster' cluster_name description )
            // BON.g:176:3: c= 'cluster' cluster_name description
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
    // BON.g:180:1: system_name returns [String name] : i= IDENTIFIER ;
    public final String system_name() throws RecognitionException {
        String name = null;

        Token i=null;

        try {
            // BON.g:180:35: (i= IDENTIFIER )
            // BON.g:181:3: i= IDENTIFIER
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
    // BON.g:185:1: index_list returns [List<IndexClause> list] : i1= index_clause ( ( ';' i2= index_clause ) | i= index_clause )* ( ';' )? ;
    public final BONParser.index_list_return index_list() throws RecognitionException {
        BONParser.index_list_return retval = new BONParser.index_list_return();
        retval.start = input.LT(1);

        BONParser.index_clause_return i1 = null;

        BONParser.index_clause_return i2 = null;

        BONParser.index_clause_return i = null;


        try {
            // BON.g:187:45: (i1= index_clause ( ( ';' i2= index_clause ) | i= index_clause )* ( ';' )? )
            // BON.g:188:16: i1= index_clause ( ( ';' i2= index_clause ) | i= index_clause )* ( ';' )?
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
            // BON.g:191:16: ( ( ';' i2= index_clause ) | i= index_clause )*
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
            	    // BON.g:191:19: ( ';' i2= index_clause )
            	    {
            	    // BON.g:191:19: ( ';' i2= index_clause )
            	    // BON.g:191:20: ';' i2= index_clause
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
            	    // BON.g:193:19: i= index_clause
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

            // BON.g:196:16: ( ';' )?
            int alt18=2;
            int LA18_0 = input.LA(1);

            if ( (LA18_0==33) ) {
                alt18=1;
            }
            switch (alt18) {
                case 1 :
                    // BON.g:196:16: ';'
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
    // BON.g:199:1: index_clause returns [IndexClause clause] : (i= IDENTIFIER ':' index_term_list | i= IDENTIFIER ':' );
    public final BONParser.index_clause_return index_clause() throws RecognitionException {
        BONParser.index_clause_return retval = new BONParser.index_clause_return();
        retval.start = input.LT(1);

        Token i=null;
        BONParser.index_term_list_return index_term_list23 = null;


        try {
            // BON.g:199:43: (i= IDENTIFIER ':' index_term_list | i= IDENTIFIER ':' )
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
                    // BON.g:200:3: i= IDENTIFIER ':' index_term_list
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
                    // BON.g:203:3: i= IDENTIFIER ':'
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
    // BON.g:207:1: index_term_list returns [List<String> strings] : i1= index_string ( ',' i= index_string )* ;
    public final BONParser.index_term_list_return index_term_list() throws RecognitionException {
        BONParser.index_term_list_return retval = new BONParser.index_term_list_return();
        retval.start = input.LT(1);

        BONParser.index_string_return i1 = null;

        BONParser.index_string_return i = null;


        try {
            // BON.g:207:48: (i1= index_string ( ',' i= index_string )* )
            // BON.g:208:3: i1= index_string ( ',' i= index_string )*
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
            // BON.g:211:3: ( ',' i= index_string )*
            loop20:
            do {
                int alt20=2;
                int LA20_0 = input.LA(1);

                if ( (LA20_0==35) ) {
                    alt20=1;
                }


                switch (alt20) {
            	case 1 :
            	    // BON.g:211:4: ',' i= index_string
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
    // BON.g:216:1: index_string returns [String s] : m= manifest_textblock ;
    public final BONParser.index_string_return index_string() throws RecognitionException {
        BONParser.index_string_return retval = new BONParser.index_string_return();
        retval.start = input.LT(1);

        BONParser.manifest_textblock_return m = null;


        try {
            // BON.g:216:33: (m= manifest_textblock )
            // BON.g:217:3: m= manifest_textblock
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
    // BON.g:221:1: cluster_chart returns [ClusterChart cc] : c= 'cluster_chart' cluster_name (i= indexing )? ( explanation )? ( part )? (ce= class_entries | ) (cle= cluster_entries | ) e= 'end' ;
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
            // BON.g:226:1: (c= 'cluster_chart' cluster_name (i= indexing )? ( explanation )? ( part )? (ce= class_entries | ) (cle= cluster_entries | ) e= 'end' )
            // BON.g:227:3: c= 'cluster_chart' cluster_name (i= indexing )? ( explanation )? ( part )? (ce= class_entries | ) (cle= cluster_entries | ) e= 'end'
            {
            c=(Token)match(input,36,FOLLOW_36_in_cluster_chart1305); if (state.failed) return cc;
            pushFollow(FOLLOW_cluster_name_in_cluster_chart1307);
            cluster_name26=cluster_name();

            state._fsp--;
            if (state.failed) return cc;
            // BON.g:228:3: (i= indexing )?
            int alt21=2;
            int LA21_0 = input.LA(1);

            if ( (LA21_0==30) ) {
                alt21=1;
            }
            switch (alt21) {
                case 1 :
                    // BON.g:228:4: i= indexing
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

            // BON.g:229:3: ( explanation )?
            int alt22=2;
            int LA22_0 = input.LA(1);

            if ( (LA22_0==29) ) {
                alt22=1;
            }
            switch (alt22) {
                case 1 :
                    // BON.g:229:4: explanation
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

            // BON.g:230:3: ( part )?
            int alt23=2;
            int LA23_0 = input.LA(1);

            if ( (LA23_0==31) ) {
                alt23=1;
            }
            switch (alt23) {
                case 1 :
                    // BON.g:230:4: part
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

            // BON.g:231:3: (ce= class_entries | )
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
                    // BON.g:231:6: ce= class_entries
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
                    // BON.g:232:6: 
                    {
                    if ( state.backtracking==0 ) {
                       if(isOk()) classes = emptyList(); 
                    }

                    }
                    break;

            }

            // BON.g:234:3: (cle= cluster_entries | )
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
                    // BON.g:234:6: cle= cluster_entries
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
                    // BON.g:235:6: 
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
    // BON.g:241:1: class_entries returns [List<ClassEntry> entries] : ( class_entry )+ ;
    public final List<ClassEntry> class_entries() throws RecognitionException {
        List<ClassEntry> entries = null;

        ClassEntry class_entry27 = null;


        try {
            // BON.g:241:50: ( ( class_entry )+ )
            // BON.g:242:3: ( class_entry )+
            {
            if ( state.backtracking==0 ) {
               entries = createList(); 
            }
            // BON.g:243:3: ( class_entry )+
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
            	    // BON.g:243:4: class_entry
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
    // BON.g:246:1: class_entry returns [ClassEntry entry] : c= 'class' class_name description ;
    public final ClassEntry class_entry() throws RecognitionException {
        ClassEntry entry = null;

        Token c=null;
        BONParser.class_name_return class_name28 = null;

        BONParser.description_return description29 = null;


        try {
            // BON.g:246:40: (c= 'class' class_name description )
            // BON.g:247:3: c= 'class' class_name description
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
    // BON.g:252:1: cluster_name returns [String name] : i= IDENTIFIER ;
    public final BONParser.cluster_name_return cluster_name() throws RecognitionException {
        BONParser.cluster_name_return retval = new BONParser.cluster_name_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // BON.g:252:36: (i= IDENTIFIER )
            // BON.g:253:3: i= IDENTIFIER
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
    // BON.g:257:1: class_chart returns [ClassChart cc] : c= 'class_chart' class_name (i= indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? e= 'end' ;
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
            // BON.g:263:1: (c= 'class_chart' class_name (i= indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? e= 'end' )
            // BON.g:264:3: c= 'class_chart' class_name (i= indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? e= 'end'
            {
            c=(Token)match(input,37,FOLLOW_37_in_class_chart1545); if (state.failed) return cc;
            pushFollow(FOLLOW_class_name_in_class_chart1547);
            class_name36=class_name();

            state._fsp--;
            if (state.failed) return cc;
            // BON.g:265:3: (i= indexing )?
            int alt27=2;
            int LA27_0 = input.LA(1);

            if ( (LA27_0==30) ) {
                alt27=1;
            }
            switch (alt27) {
                case 1 :
                    // BON.g:265:4: i= indexing
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

            // BON.g:266:3: ( explanation )?
            int alt28=2;
            int LA28_0 = input.LA(1);

            if ( (LA28_0==29) ) {
                alt28=1;
            }
            switch (alt28) {
                case 1 :
                    // BON.g:266:4: explanation
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

            // BON.g:267:3: ( part )?
            int alt29=2;
            int LA29_0 = input.LA(1);

            if ( (LA29_0==31) ) {
                alt29=1;
            }
            switch (alt29) {
                case 1 :
                    // BON.g:267:4: part
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

            // BON.g:268:3: ( inherits )?
            int alt30=2;
            int LA30_0 = input.LA(1);

            if ( (LA30_0==38) ) {
                alt30=1;
            }
            switch (alt30) {
                case 1 :
                    // BON.g:268:6: inherits
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

            // BON.g:271:3: ( queries )?
            int alt31=2;
            int LA31_0 = input.LA(1);

            if ( (LA31_0==39) ) {
                alt31=1;
            }
            switch (alt31) {
                case 1 :
                    // BON.g:271:6: queries
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

            // BON.g:274:3: ( commands )?
            int alt32=2;
            int LA32_0 = input.LA(1);

            if ( (LA32_0==40) ) {
                alt32=1;
            }
            switch (alt32) {
                case 1 :
                    // BON.g:274:6: commands
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

            // BON.g:277:3: ( constraints )?
            int alt33=2;
            int LA33_0 = input.LA(1);

            if ( (LA33_0==41) ) {
                alt33=1;
            }
            switch (alt33) {
                case 1 :
                    // BON.g:277:6: constraints
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
    // BON.g:284:1: inherits returns [List<ClassName> inherits] : (i= 'inherit' class_name_list | i= 'inherit' );
    public final List<ClassName> inherits() throws RecognitionException {
        List<ClassName> inherits = null;

        Token i=null;
        List<ClassName> class_name_list37 = null;


        try {
            // BON.g:284:45: (i= 'inherit' class_name_list | i= 'inherit' )
            int alt34=2;
            int LA34_0 = input.LA(1);

            if ( (LA34_0==38) ) {
                int LA34_1 = input.LA(2);

                if ( (LA34_1==IDENTIFIER) ) {
                    alt34=1;
                }
                else if ( (LA34_1==25||(LA34_1>=39 && LA34_1<=41)) ) {
                    alt34=2;
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
                    // BON.g:285:3: i= 'inherit' class_name_list
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
                    // BON.g:289:3: i= 'inherit'
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
    // BON.g:293:1: queries returns [List<String> queries] : 'query' query_list ;
    public final List<String> queries() throws RecognitionException {
        List<String> queries = null;

        List<String> query_list38 = null;


        try {
            // BON.g:293:40: ( 'query' query_list )
            // BON.g:294:3: 'query' query_list
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
    // BON.g:298:1: commands returns [List<String> commands] : 'command' command_list ;
    public final List<String> commands() throws RecognitionException {
        List<String> commands = null;

        List<String> command_list39 = null;


        try {
            // BON.g:298:42: ( 'command' command_list )
            // BON.g:299:3: 'command' command_list
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
    // BON.g:303:1: constraints returns [List<String> constraints] : 'constraint' constraint_list ;
    public final List<String> constraints() throws RecognitionException {
        List<String> constraints = null;

        List<String> constraint_list40 = null;


        try {
            // BON.g:303:48: ( 'constraint' constraint_list )
            // BON.g:304:3: 'constraint' constraint_list
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
    // BON.g:309:1: query_list returns [List<String> queries] : m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? ;
    public final List<String> query_list() throws RecognitionException {
        List<String> queries = null;

        BONParser.manifest_textblock_return m1 = null;

        BONParser.manifest_textblock_return m = null;


        try {
            // BON.g:309:43: (m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? )
            // BON.g:310:3: m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )?
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
            // BON.g:313:3: ( ( ',' m= manifest_textblock ) | m= manifest_textblock )*
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
            	    // BON.g:313:6: ( ',' m= manifest_textblock )
            	    {
            	    // BON.g:313:6: ( ',' m= manifest_textblock )
            	    // BON.g:313:7: ',' m= manifest_textblock
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
            	    // BON.g:316:6: m= manifest_textblock
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

            // BON.g:320:3: ( ',' )?
            int alt36=2;
            int LA36_0 = input.LA(1);

            if ( (LA36_0==35) ) {
                alt36=1;
            }
            switch (alt36) {
                case 1 :
                    // BON.g:320:3: ','
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
    // BON.g:323:1: command_list returns [List<String> commands] : m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? ;
    public final List<String> command_list() throws RecognitionException {
        List<String> commands = null;

        BONParser.manifest_textblock_return m1 = null;

        BONParser.manifest_textblock_return m = null;


        try {
            // BON.g:323:46: (m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? )
            // BON.g:324:3: m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )?
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
            // BON.g:327:3: ( ( ',' m= manifest_textblock ) | m= manifest_textblock )*
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
            	    // BON.g:327:6: ( ',' m= manifest_textblock )
            	    {
            	    // BON.g:327:6: ( ',' m= manifest_textblock )
            	    // BON.g:327:7: ',' m= manifest_textblock
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
            	    // BON.g:330:6: m= manifest_textblock
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

            // BON.g:334:3: ( ',' )?
            int alt38=2;
            int LA38_0 = input.LA(1);

            if ( (LA38_0==35) ) {
                alt38=1;
            }
            switch (alt38) {
                case 1 :
                    // BON.g:334:3: ','
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
    // BON.g:337:1: constraint_list returns [List<String> constraints] : m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? ;
    public final List<String> constraint_list() throws RecognitionException {
        List<String> constraints = null;

        BONParser.manifest_textblock_return m1 = null;

        BONParser.manifest_textblock_return m = null;


        try {
            // BON.g:337:52: (m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? )
            // BON.g:338:3: m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )?
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
            // BON.g:341:3: ( ( ',' m= manifest_textblock ) | m= manifest_textblock )*
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
            	    // BON.g:341:6: ( ',' m= manifest_textblock )
            	    {
            	    // BON.g:341:6: ( ',' m= manifest_textblock )
            	    // BON.g:341:7: ',' m= manifest_textblock
            	    {
            	    match(input,35,FOLLOW_35_in_constraint_list2058); if (state.failed) return constraints;
            	    pushFollow(FOLLOW_manifest_textblock_in_constraint_list2062);
            	    m=manifest_textblock();

            	    state._fsp--;
            	    if (state.failed) return constraints;

            	    }


            	    }
            	    break;
            	case 2 :
            	    // BON.g:342:6: m= manifest_textblock
            	    {
            	    pushFollow(FOLLOW_manifest_textblock_in_constraint_list2073);
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

            // BON.g:346:3: ( ',' )?
            int alt40=2;
            int LA40_0 = input.LA(1);

            if ( (LA40_0==35) ) {
                alt40=1;
            }
            switch (alt40) {
                case 1 :
                    // BON.g:346:3: ','
                    {
                    match(input,35,FOLLOW_35_in_constraint_list2097); if (state.failed) return constraints;

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
    // BON.g:349:1: class_name_list returns [List<ClassName> list] : c1= class_name ( ( ',' c= class_name ) | (c= class_name ) )* ;
    public final List<ClassName> class_name_list() throws RecognitionException {
        List<ClassName> list = null;

        BONParser.class_name_return c1 = null;

        BONParser.class_name_return c = null;


        try {
            // BON.g:349:48: (c1= class_name ( ( ',' c= class_name ) | (c= class_name ) )* )
            // BON.g:350:3: c1= class_name ( ( ',' c= class_name ) | (c= class_name ) )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_class_name_in_class_name_list2119);
            c1=class_name();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               if(isOk()) list.add((c1!=null?c1.name:null)); 
            }
            // BON.g:353:3: ( ( ',' c= class_name ) | (c= class_name ) )*
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
            	    // BON.g:353:6: ( ',' c= class_name )
            	    {
            	    // BON.g:353:6: ( ',' c= class_name )
            	    // BON.g:353:8: ',' c= class_name
            	    {
            	    match(input,35,FOLLOW_35_in_class_name_list2133); if (state.failed) return list;
            	    pushFollow(FOLLOW_class_name_in_class_name_list2137);
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
            	    // BON.g:356:6: (c= class_name )
            	    {
            	    // BON.g:356:6: (c= class_name )
            	    // BON.g:356:8: c= class_name
            	    {
            	    pushFollow(FOLLOW_class_name_in_class_name_list2166);
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
    // BON.g:363:1: cluster_name_list returns [List<String> list] : c1= cluster_name ( ( ',' c= cluster_name ) | (c= cluster_name ) )* ;
    public final List<String> cluster_name_list() throws RecognitionException {
        List<String> list = null;

        BONParser.cluster_name_return c1 = null;

        BONParser.cluster_name_return c = null;


        try {
            // BON.g:363:47: (c1= cluster_name ( ( ',' c= cluster_name ) | (c= cluster_name ) )* )
            // BON.g:364:3: c1= cluster_name ( ( ',' c= cluster_name ) | (c= cluster_name ) )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_cluster_name_in_cluster_name_list2235);
            c1=cluster_name();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               if(isOk()) list.add((c1!=null?input.toString(c1.start,c1.stop):null)); 
            }
            // BON.g:367:3: ( ( ',' c= cluster_name ) | (c= cluster_name ) )*
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
            	    // BON.g:367:6: ( ',' c= cluster_name )
            	    {
            	    // BON.g:367:6: ( ',' c= cluster_name )
            	    // BON.g:367:8: ',' c= cluster_name
            	    {
            	    match(input,35,FOLLOW_35_in_cluster_name_list2248); if (state.failed) return list;
            	    pushFollow(FOLLOW_cluster_name_in_cluster_name_list2252);
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
            	    // BON.g:370:6: (c= cluster_name )
            	    {
            	    // BON.g:370:6: (c= cluster_name )
            	    // BON.g:370:8: c= cluster_name
            	    {
            	    pushFollow(FOLLOW_cluster_name_in_cluster_name_list2280);
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
    // BON.g:377:1: class_or_cluster_name_list returns [List<String> list] : c1= class_or_bracketed_cluster_name ( ',' c= class_or_bracketed_cluster_name )* ;
    public final BONParser.class_or_cluster_name_list_return class_or_cluster_name_list() throws RecognitionException {
        BONParser.class_or_cluster_name_list_return retval = new BONParser.class_or_cluster_name_list_return();
        retval.start = input.LT(1);

        String c1 = null;

        String c = null;


        try {
            // BON.g:377:56: (c1= class_or_bracketed_cluster_name ( ',' c= class_or_bracketed_cluster_name )* )
            // BON.g:378:3: c1= class_or_bracketed_cluster_name ( ',' c= class_or_bracketed_cluster_name )*
            {
            if ( state.backtracking==0 ) {
               retval.list = createList(); 
            }
            pushFollow(FOLLOW_class_or_bracketed_cluster_name_in_class_or_cluster_name_list2377);
            c1=class_or_bracketed_cluster_name();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.list.add(c1); 
            }
            // BON.g:381:3: ( ',' c= class_or_bracketed_cluster_name )*
            loop43:
            do {
                int alt43=2;
                int LA43_0 = input.LA(1);

                if ( (LA43_0==35) ) {
                    alt43=1;
                }


                switch (alt43) {
            	case 1 :
            	    // BON.g:381:5: ',' c= class_or_bracketed_cluster_name
            	    {
            	    match(input,35,FOLLOW_35_in_class_or_cluster_name_list2387); if (state.failed) return retval;
            	    pushFollow(FOLLOW_class_or_bracketed_cluster_name_in_class_or_cluster_name_list2391);
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
    // BON.g:386:1: class_or_bracketed_cluster_name returns [String name] : ( class_name | '(' cluster_name ')' );
    public final String class_or_bracketed_cluster_name() throws RecognitionException {
        String name = null;

        BONParser.class_name_return class_name41 = null;

        BONParser.cluster_name_return cluster_name42 = null;


        try {
            // BON.g:386:55: ( class_name | '(' cluster_name ')' )
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
                    // BON.g:387:4: class_name
                    {
                    pushFollow(FOLLOW_class_name_in_class_or_bracketed_cluster_name2419);
                    class_name41=class_name();

                    state._fsp--;
                    if (state.failed) return name;
                    if ( state.backtracking==0 ) {
                       if(isOk()) name = (class_name41!=null?class_name41.name:null).getName(); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:390:4: '(' cluster_name ')'
                    {
                    match(input,42,FOLLOW_42_in_class_or_bracketed_cluster_name2433); if (state.failed) return name;
                    pushFollow(FOLLOW_cluster_name_in_class_or_bracketed_cluster_name2435);
                    cluster_name42=cluster_name();

                    state._fsp--;
                    if (state.failed) return name;
                    match(input,43,FOLLOW_43_in_class_or_bracketed_cluster_name2437); if (state.failed) return name;
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
    // BON.g:394:1: class_name returns [ClassName name] : i= IDENTIFIER ;
    public final BONParser.class_name_return class_name() throws RecognitionException {
        BONParser.class_name_return retval = new BONParser.class_name_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // BON.g:394:37: (i= IDENTIFIER )
            // BON.g:395:3: i= IDENTIFIER
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_class_name2459); if (state.failed) return retval;
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
    // BON.g:399:1: event_chart returns [EventChart ec] : e= 'event_chart' system_name ( 'incoming' | 'outgoing' )? ( indexing )? ( explanation )? ( part )? (ee= event_entries | ) end= 'end' ;
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
            // BON.g:404:1: (e= 'event_chart' system_name ( 'incoming' | 'outgoing' )? ( indexing )? ( explanation )? ( part )? (ee= event_entries | ) end= 'end' )
            // BON.g:405:3: e= 'event_chart' system_name ( 'incoming' | 'outgoing' )? ( indexing )? ( explanation )? ( part )? (ee= event_entries | ) end= 'end'
            {
            e=(Token)match(input,44,FOLLOW_44_in_event_chart2490); if (state.failed) return ec;
            pushFollow(FOLLOW_system_name_in_event_chart2492);
            system_name46=system_name();

            state._fsp--;
            if (state.failed) return ec;
            // BON.g:406:3: ( 'incoming' | 'outgoing' )?
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
                    // BON.g:406:6: 'incoming'
                    {
                    match(input,45,FOLLOW_45_in_event_chart2500); if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       incoming = true; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:407:6: 'outgoing'
                    {
                    match(input,46,FOLLOW_46_in_event_chart2510); if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       outgoing = true; 
                    }

                    }
                    break;

            }

            // BON.g:409:3: ( indexing )?
            int alt46=2;
            int LA46_0 = input.LA(1);

            if ( (LA46_0==30) ) {
                alt46=1;
            }
            switch (alt46) {
                case 1 :
                    // BON.g:409:4: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_event_chart2522);
                    indexing43=indexing();

                    state._fsp--;
                    if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) indexing = (indexing43!=null?indexing43.indexing:null); 
                    }

                    }
                    break;

            }

            // BON.g:410:3: ( explanation )?
            int alt47=2;
            int LA47_0 = input.LA(1);

            if ( (LA47_0==29) ) {
                alt47=1;
            }
            switch (alt47) {
                case 1 :
                    // BON.g:410:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_event_chart2531);
                    explanation44=explanation();

                    state._fsp--;
                    if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) explanation = explanation44; 
                    }

                    }
                    break;

            }

            // BON.g:411:3: ( part )?
            int alt48=2;
            int LA48_0 = input.LA(1);

            if ( (LA48_0==31) ) {
                alt48=1;
            }
            switch (alt48) {
                case 1 :
                    // BON.g:411:4: part
                    {
                    pushFollow(FOLLOW_part_in_event_chart2541);
                    part45=part();

                    state._fsp--;
                    if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) part = part45; 
                    }

                    }
                    break;

            }

            // BON.g:412:3: (ee= event_entries | )
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
                    // BON.g:412:5: ee= event_entries
                    {
                    pushFollow(FOLLOW_event_entries_in_event_chart2554);
                    ee=event_entries();

                    state._fsp--;
                    if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) eventEntries = ee; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:415:5: 
                    {
                    if ( state.backtracking==0 ) {
                       eventEntries = createList(); 
                    }

                    }
                    break;

            }

            end=(Token)match(input,25,FOLLOW_25_in_event_chart2581); if (state.failed) return ec;
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
    // BON.g:421:1: event_entries returns [List<EventEntry> entries] : ( event_entry )+ ;
    public final List<EventEntry> event_entries() throws RecognitionException {
        List<EventEntry> entries = null;

        EventEntry event_entry47 = null;


        try {
            // BON.g:421:50: ( ( event_entry )+ )
            // BON.g:422:3: ( event_entry )+
            {
            if ( state.backtracking==0 ) {
               entries = createList(); 
            }
            // BON.g:423:3: ( event_entry )+
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
            	    // BON.g:423:4: event_entry
            	    {
            	    pushFollow(FOLLOW_event_entry_in_event_entries2618);
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
    // BON.g:426:1: event_entry returns [EventEntry entry] : e= 'event' ( (m= manifest_textblock ) | ) i= 'involves' ( (ccns= class_or_cluster_name_list ) | ) ;
    public final EventEntry event_entry() throws RecognitionException {
        EventEntry entry = null;

        Token e=null;
        Token i=null;
        BONParser.manifest_textblock_return m = null;

        BONParser.class_or_cluster_name_list_return ccns = null;


         boolean mok=false; boolean cok=false; List<String> ccnl = null; String description = null; Token stop=null; 
        try {
            // BON.g:427:119: (e= 'event' ( (m= manifest_textblock ) | ) i= 'involves' ( (ccns= class_or_cluster_name_list ) | ) )
            // BON.g:428:3: e= 'event' ( (m= manifest_textblock ) | ) i= 'involves' ( (ccns= class_or_cluster_name_list ) | )
            {
            e=(Token)match(input,47,FOLLOW_47_in_event_entry2661); if (state.failed) return entry;
            // BON.g:429:3: ( (m= manifest_textblock ) | )
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
                    // BON.g:429:6: (m= manifest_textblock )
                    {
                    // BON.g:429:6: (m= manifest_textblock )
                    // BON.g:429:8: m= manifest_textblock
                    {
                    pushFollow(FOLLOW_manifest_textblock_in_event_entry2672);
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
                    // BON.g:433:4: 
                    {
                    if ( state.backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(e), "event name", "in event entry clause", true)); 
                    }

                    }
                    break;

            }

            i=(Token)match(input,48,FOLLOW_48_in_event_entry2712); if (state.failed) return entry;
            // BON.g:436:3: ( (ccns= class_or_cluster_name_list ) | )
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
                    // BON.g:436:6: (ccns= class_or_cluster_name_list )
                    {
                    // BON.g:436:6: (ccns= class_or_cluster_name_list )
                    // BON.g:436:7: ccns= class_or_cluster_name_list
                    {
                    pushFollow(FOLLOW_class_or_cluster_name_list_in_event_entry2722);
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
                    // BON.g:441:6: 
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
    // BON.g:447:1: scenario_chart returns [ScenarioChart sc] : s= 'scenario_chart' system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries | ) e= 'end' ;
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
            // BON.g:451:1: (s= 'scenario_chart' system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries | ) e= 'end' )
            // BON.g:452:3: s= 'scenario_chart' system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries | ) e= 'end'
            {
            s=(Token)match(input,49,FOLLOW_49_in_scenario_chart2802); if (state.failed) return sc;
            pushFollow(FOLLOW_system_name_in_scenario_chart2804);
            system_name52=system_name();

            state._fsp--;
            if (state.failed) return sc;
            // BON.g:453:3: ( indexing )?
            int alt53=2;
            int LA53_0 = input.LA(1);

            if ( (LA53_0==30) ) {
                alt53=1;
            }
            switch (alt53) {
                case 1 :
                    // BON.g:453:4: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_scenario_chart2809);
                    indexing48=indexing();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) indexing = (indexing48!=null?indexing48.indexing:null); 
                    }

                    }
                    break;

            }

            // BON.g:454:3: ( explanation )?
            int alt54=2;
            int LA54_0 = input.LA(1);

            if ( (LA54_0==29) ) {
                alt54=1;
            }
            switch (alt54) {
                case 1 :
                    // BON.g:454:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_scenario_chart2819);
                    explanation49=explanation();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) explanation = explanation49; 
                    }

                    }
                    break;

            }

            // BON.g:455:3: ( part )?
            int alt55=2;
            int LA55_0 = input.LA(1);

            if ( (LA55_0==31) ) {
                alt55=1;
            }
            switch (alt55) {
                case 1 :
                    // BON.g:455:4: part
                    {
                    pushFollow(FOLLOW_part_in_scenario_chart2829);
                    part50=part();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) part = part50; 
                    }

                    }
                    break;

            }

            // BON.g:456:3: ( scenario_entries | )
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
                    // BON.g:456:5: scenario_entries
                    {
                    pushFollow(FOLLOW_scenario_entries_in_scenario_chart2840);
                    scenario_entries51=scenario_entries();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       if(isOk()) entries = scenario_entries51; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:457:6: 
                    {
                    if ( state.backtracking==0 ) {
                       if(isOk()) entries = emptyList(); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_scenario_chart2861); if (state.failed) return sc;
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
    // BON.g:463:1: scenario_entries returns [List<ScenarioEntry> entries] : ( scenario_entry )+ ;
    public final List<ScenarioEntry> scenario_entries() throws RecognitionException {
        List<ScenarioEntry> entries = null;

        ScenarioEntry scenario_entry53 = null;


        try {
            // BON.g:463:56: ( ( scenario_entry )+ )
            // BON.g:464:3: ( scenario_entry )+
            {
            if ( state.backtracking==0 ) {
               entries = createList(); 
            }
            // BON.g:465:3: ( scenario_entry )+
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
            	    // BON.g:465:4: scenario_entry
            	    {
            	    pushFollow(FOLLOW_scenario_entry_in_scenario_entries2901);
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
    // BON.g:468:1: scenario_entry returns [ScenarioEntry entry] : s= 'scenario' m= MANIFEST_STRING d= description ;
    public final ScenarioEntry scenario_entry() throws RecognitionException {
        ScenarioEntry entry = null;

        Token s=null;
        Token m=null;
        BONParser.description_return d = null;


        try {
            // BON.g:468:46: (s= 'scenario' m= MANIFEST_STRING d= description )
            // BON.g:469:3: s= 'scenario' m= MANIFEST_STRING d= description
            {
            s=(Token)match(input,50,FOLLOW_50_in_scenario_entry2942); if (state.failed) return entry;
            m=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_scenario_entry2946); if (state.failed) return entry;
            pushFollow(FOLLOW_description_in_scenario_entry2950);
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
    // BON.g:473:1: creation_chart returns [CreationChart cc] : start= 'creation_chart' system_name ( indexing )? ( explanation )? ( part )? ( creation_entries | ) end= 'end' ;
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
            // BON.g:477:1: (start= 'creation_chart' system_name ( indexing )? ( explanation )? ( part )? ( creation_entries | ) end= 'end' )
            // BON.g:478:3: start= 'creation_chart' system_name ( indexing )? ( explanation )? ( part )? ( creation_entries | ) end= 'end'
            {
            start=(Token)match(input,51,FOLLOW_51_in_creation_chart2979); if (state.failed) return retval;
            pushFollow(FOLLOW_system_name_in_creation_chart2981);
            system_name58=system_name();

            state._fsp--;
            if (state.failed) return retval;
            // BON.g:479:3: ( indexing )?
            int alt58=2;
            int LA58_0 = input.LA(1);

            if ( (LA58_0==30) ) {
                alt58=1;
            }
            switch (alt58) {
                case 1 :
                    // BON.g:479:4: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_creation_chart2986);
                    indexing54=indexing();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) indexing = (indexing54!=null?indexing54.indexing:null); 
                    }

                    }
                    break;

            }

            // BON.g:480:3: ( explanation )?
            int alt59=2;
            int LA59_0 = input.LA(1);

            if ( (LA59_0==29) ) {
                alt59=1;
            }
            switch (alt59) {
                case 1 :
                    // BON.g:480:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_creation_chart2996);
                    explanation55=explanation();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) explanation = explanation55; 
                    }

                    }
                    break;

            }

            // BON.g:481:3: ( part )?
            int alt60=2;
            int LA60_0 = input.LA(1);

            if ( (LA60_0==31) ) {
                alt60=1;
            }
            switch (alt60) {
                case 1 :
                    // BON.g:481:4: part
                    {
                    pushFollow(FOLLOW_part_in_creation_chart3006);
                    part56=part();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) part = part56; 
                    }

                    }
                    break;

            }

            // BON.g:482:3: ( creation_entries | )
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
                    // BON.g:482:5: creation_entries
                    {
                    pushFollow(FOLLOW_creation_entries_in_creation_chart3017);
                    creation_entries57=creation_entries();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) entries = creation_entries57; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:483:6: 
                    {
                    if ( state.backtracking==0 ) {
                       entries = emptyList(); 
                    }

                    }
                    break;

            }

            end=(Token)match(input,25,FOLLOW_25_in_creation_chart3034); if (state.failed) return retval;
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
    // BON.g:488:1: creation_entries returns [List<CreationEntry> entries] : ( creation_entry )+ ;
    public final List<CreationEntry> creation_entries() throws RecognitionException {
        List<CreationEntry> entries = null;

        CreationEntry creation_entry59 = null;


        try {
            // BON.g:488:56: ( ( creation_entry )+ )
            // BON.g:489:3: ( creation_entry )+
            {
            if ( state.backtracking==0 ) {
               entries = createList(); 
            }
            // BON.g:490:3: ( creation_entry )+
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
            	    // BON.g:490:4: creation_entry
            	    {
            	    pushFollow(FOLLOW_creation_entry_in_creation_entries3075);
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
    // BON.g:493:1: creation_entry returns [CreationEntry entry] : c= 'creator' class_name 'creates' ccnl= class_or_cluster_name_list ;
    public final CreationEntry creation_entry() throws RecognitionException {
        CreationEntry entry = null;

        Token c=null;
        BONParser.class_or_cluster_name_list_return ccnl = null;

        BONParser.class_name_return class_name60 = null;


        try {
            // BON.g:493:46: (c= 'creator' class_name 'creates' ccnl= class_or_cluster_name_list )
            // BON.g:494:3: c= 'creator' class_name 'creates' ccnl= class_or_cluster_name_list
            {
            c=(Token)match(input,52,FOLLOW_52_in_creation_entry3115); if (state.failed) return entry;
            pushFollow(FOLLOW_class_name_in_creation_entry3117);
            class_name60=class_name();

            state._fsp--;
            if (state.failed) return entry;
            match(input,53,FOLLOW_53_in_creation_entry3122); if (state.failed) return entry;
            pushFollow(FOLLOW_class_or_cluster_name_list_in_creation_entry3126);
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
    // BON.g:499:1: static_diagram returns [StaticDiagram sd] : s= 'static_diagram' ( extended_id )? (c= COMMENT )? 'component' sb= static_block e= 'end' ;
    public final StaticDiagram static_diagram() throws RecognitionException {
        StaticDiagram sd = null;

        Token s=null;
        Token c=null;
        Token e=null;
        List<StaticComponent> sb = null;

        BONParser.extended_id_return extended_id61 = null;


         String eid = null; String comment = null; 
        try {
            // BON.g:505:1: (s= 'static_diagram' ( extended_id )? (c= COMMENT )? 'component' sb= static_block e= 'end' )
            // BON.g:506:3: s= 'static_diagram' ( extended_id )? (c= COMMENT )? 'component' sb= static_block e= 'end'
            {
            s=(Token)match(input,54,FOLLOW_54_in_static_diagram3159); if (state.failed) return sd;
            // BON.g:507:3: ( extended_id )?
            int alt63=2;
            int LA63_0 = input.LA(1);

            if ( (LA63_0==IDENTIFIER||LA63_0==INTEGER) ) {
                alt63=1;
            }
            switch (alt63) {
                case 1 :
                    // BON.g:507:4: extended_id
                    {
                    pushFollow(FOLLOW_extended_id_in_static_diagram3165);
                    extended_id61=extended_id();

                    state._fsp--;
                    if (state.failed) return sd;
                    if ( state.backtracking==0 ) {
                       if(isOk()) eid=(extended_id61!=null?extended_id61.eid:null); 
                    }

                    }
                    break;

            }

            // BON.g:508:3: (c= COMMENT )?
            int alt64=2;
            int LA64_0 = input.LA(1);

            if ( (LA64_0==COMMENT) ) {
                alt64=1;
            }
            switch (alt64) {
                case 1 :
                    // BON.g:508:4: c= COMMENT
                    {
                    c=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_static_diagram3178); if (state.failed) return sd;
                    if ( state.backtracking==0 ) {
                       if(isOk()) comment=(c!=null?c.getText():null); 
                    }

                    }
                    break;

            }

            match(input,55,FOLLOW_55_in_static_diagram3188); if (state.failed) return sd;
            pushFollow(FOLLOW_static_block_in_static_diagram3195);
            sb=static_block();

            state._fsp--;
            if (state.failed) return sd;
            e=(Token)match(input,25,FOLLOW_25_in_static_diagram3202); if (state.failed) return sd;
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
    // BON.g:515:1: extended_id returns [String eid] : (i= IDENTIFIER | i= INTEGER );
    public final BONParser.extended_id_return extended_id() throws RecognitionException {
        BONParser.extended_id_return retval = new BONParser.extended_id_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // BON.g:515:34: (i= IDENTIFIER | i= INTEGER )
            int alt65=2;
            int LA65_0 = input.LA(1);

            if ( (LA65_0==IDENTIFIER) ) {
                alt65=1;
            }
            else if ( (LA65_0==INTEGER) ) {
                alt65=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 65, 0, input);

                throw nvae;
            }
            switch (alt65) {
                case 1 :
                    // BON.g:516:4: i= IDENTIFIER
                    {
                    i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_extended_id3258); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.eid = (i!=null?i.getText():null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:518:4: i= INTEGER
                    {
                    i=(Token)match(input,INTEGER,FOLLOW_INTEGER_in_extended_id3271); if (state.failed) return retval;
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
    // BON.g:522:1: static_block returns [List<StaticComponent> components] : (sc= static_component )* ;
    public final List<StaticComponent> static_block() throws RecognitionException {
        List<StaticComponent> components = null;

        StaticComponent sc = null;


        try {
            // BON.g:522:57: ( (sc= static_component )* )
            // BON.g:523:3: (sc= static_component )*
            {
            if ( state.backtracking==0 ) {
               components = createList(); 
            }
            // BON.g:524:3: (sc= static_component )*
            loop66:
            do {
                int alt66=2;
                int LA66_0 = input.LA(1);

                if ( (LA66_0==IDENTIFIER||(LA66_0>=26 && LA66_0<=27)||(LA66_0>=57 && LA66_0<=59)) ) {
                    alt66=1;
                }


                switch (alt66) {
            	case 1 :
            	    // BON.g:524:4: sc= static_component
            	    {
            	    pushFollow(FOLLOW_static_component_in_static_block3312);
            	    sc=static_component();

            	    state._fsp--;
            	    if (state.failed) return components;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) components.add(sc); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop66;
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
    // BON.g:527:1: static_component returns [StaticComponent component] : (c1= cluster | c2= clazz | s= static_relation );
    public final StaticComponent static_component() throws RecognitionException {
        StaticComponent component = null;

        Cluster c1 = null;

        Clazz c2 = null;

        StaticRelation s = null;


        try {
            // BON.g:527:54: (c1= cluster | c2= clazz | s= static_relation )
            int alt67=3;
            switch ( input.LA(1) ) {
            case 27:
                {
                alt67=1;
                }
                break;
            case 26:
            case 57:
            case 58:
            case 59:
                {
                alt67=2;
                }
                break;
            case IDENTIFIER:
                {
                alt67=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return component;}
                NoViableAltException nvae =
                    new NoViableAltException("", 67, 0, input);

                throw nvae;
            }

            switch (alt67) {
                case 1 :
                    // BON.g:528:4: c1= cluster
                    {
                    pushFollow(FOLLOW_cluster_in_static_component3347);
                    c1=cluster();

                    state._fsp--;
                    if (state.failed) return component;
                    if ( state.backtracking==0 ) {
                       if(isOk()) component = c1; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:530:4: c2= clazz
                    {
                    pushFollow(FOLLOW_clazz_in_static_component3360);
                    c2=clazz();

                    state._fsp--;
                    if (state.failed) return component;
                    if ( state.backtracking==0 ) {
                       if(isOk()) component = c2; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:532:4: s= static_relation
                    {
                    pushFollow(FOLLOW_static_relation_in_static_component3373);
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
    // BON.g:536:1: cluster returns [Cluster cluster] : c= 'cluster' cluster_name (r= 'reused' )? (co= COMMENT )? (cc= cluster_components | ) ;
    public final Cluster cluster() throws RecognitionException {
        Cluster cluster = null;

        Token c=null;
        Token r=null;
        Token co=null;
        BONParser.cluster_components_return cc = null;

        BONParser.cluster_name_return cluster_name62 = null;


         boolean reused = false; String comment = null; List<StaticComponent> components = null; Token end = null; 
        try {
            // BON.g:540:1: (c= 'cluster' cluster_name (r= 'reused' )? (co= COMMENT )? (cc= cluster_components | ) )
            // BON.g:541:3: c= 'cluster' cluster_name (r= 'reused' )? (co= COMMENT )? (cc= cluster_components | )
            {
            c=(Token)match(input,27,FOLLOW_27_in_cluster3405); if (state.failed) return cluster;
            pushFollow(FOLLOW_cluster_name_in_cluster3407);
            cluster_name62=cluster_name();

            state._fsp--;
            if (state.failed) return cluster;
            if ( state.backtracking==0 ) {
               end = (cluster_name62!=null?((Token)cluster_name62.stop):null); 
            }
            // BON.g:542:3: (r= 'reused' )?
            int alt68=2;
            int LA68_0 = input.LA(1);

            if ( (LA68_0==56) ) {
                alt68=1;
            }
            switch (alt68) {
                case 1 :
                    // BON.g:542:4: r= 'reused'
                    {
                    r=(Token)match(input,56,FOLLOW_56_in_cluster3416); if (state.failed) return cluster;
                    if ( state.backtracking==0 ) {
                       if(isOk()) reused = true; end = r; 
                    }

                    }
                    break;

            }

            // BON.g:543:3: (co= COMMENT )?
            int alt69=2;
            int LA69_0 = input.LA(1);

            if ( (LA69_0==COMMENT) ) {
                alt69=1;
            }
            switch (alt69) {
                case 1 :
                    // BON.g:543:4: co= COMMENT
                    {
                    co=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_cluster3429); if (state.failed) return cluster;
                    if ( state.backtracking==0 ) {
                       if(isOk()) comment = (co!=null?co.getText():null); end = co;
                    }

                    }
                    break;

            }

            // BON.g:544:3: (cc= cluster_components | )
            int alt70=2;
            int LA70_0 = input.LA(1);

            if ( (LA70_0==55) ) {
                alt70=1;
            }
            else if ( (LA70_0==IDENTIFIER||(LA70_0>=25 && LA70_0<=27)||(LA70_0>=57 && LA70_0<=59)) ) {
                alt70=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return cluster;}
                NoViableAltException nvae =
                    new NoViableAltException("", 70, 0, input);

                throw nvae;
            }
            switch (alt70) {
                case 1 :
                    // BON.g:544:6: cc= cluster_components
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
                    // BON.g:547:6: 
                    {
                    if ( state.backtracking==0 ) {
                       components = emptyList(); 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               if(isOk()) cluster = Cluster.mk((cluster_name62!=null?cluster_name62.name:null), components, reused, comment, getSLoc(c,end)); 
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
    // BON.g:552:1: cluster_components returns [List<StaticComponent> components] : 'component' static_block 'end' ;
    public final BONParser.cluster_components_return cluster_components() throws RecognitionException {
        BONParser.cluster_components_return retval = new BONParser.cluster_components_return();
        retval.start = input.LT(1);

        List<StaticComponent> static_block63 = null;


        try {
            // BON.g:552:63: ( 'component' static_block 'end' )
            // BON.g:553:3: 'component' static_block 'end'
            {
            match(input,55,FOLLOW_55_in_cluster_components3502); if (state.failed) return retval;
            pushFollow(FOLLOW_static_block_in_cluster_components3504);
            static_block63=static_block();

            state._fsp--;
            if (state.failed) return retval;
            match(input,25,FOLLOW_25_in_cluster_components3506); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.components = static_block63; 
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
    // BON.g:557:1: clazz returns [Clazz clazz] : (r= 'root' | d= 'deferred' | e= 'effective' | ) c= 'class' cn= class_name (fg= formal_generics | ) (ru= 'reused' )? (p= 'persistent' )? (i= 'interfaced' )? (co= COMMENT )? (ci= class_interface )? ;
    public final Clazz clazz() throws RecognitionException {
        Clazz clazz = null;

        Token r=null;
        Token d=null;
        Token e=null;
        Token c=null;
        Token ru=null;
        Token p=null;
        Token i=null;
        Token co=null;
        BONParser.class_name_return cn = null;

        BONParser.formal_generics_return fg = null;

        BONParser.class_interface_return ci = null;


         Clazz.Mod mod = null; List<FormalGeneric> generics = null; Token start = null; Token end = null;
                boolean reused = false; boolean persistent = false; boolean interfaced = false; 
                String comment = null; ClassInterface classInterface = null; 
        try {
            // BON.g:561:1: ( (r= 'root' | d= 'deferred' | e= 'effective' | ) c= 'class' cn= class_name (fg= formal_generics | ) (ru= 'reused' )? (p= 'persistent' )? (i= 'interfaced' )? (co= COMMENT )? (ci= class_interface )? )
            // BON.g:562:3: (r= 'root' | d= 'deferred' | e= 'effective' | ) c= 'class' cn= class_name (fg= formal_generics | ) (ru= 'reused' )? (p= 'persistent' )? (i= 'interfaced' )? (co= COMMENT )? (ci= class_interface )?
            {
            // BON.g:562:3: (r= 'root' | d= 'deferred' | e= 'effective' | )
            int alt71=4;
            switch ( input.LA(1) ) {
            case 57:
                {
                alt71=1;
                }
                break;
            case 58:
                {
                alt71=2;
                }
                break;
            case 59:
                {
                alt71=3;
                }
                break;
            case 26:
                {
                alt71=4;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return clazz;}
                NoViableAltException nvae =
                    new NoViableAltException("", 71, 0, input);

                throw nvae;
            }

            switch (alt71) {
                case 1 :
                    // BON.g:562:7: r= 'root'
                    {
                    r=(Token)match(input,57,FOLLOW_57_in_clazz3557); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       mod = Clazz.Mod.ROOT; start = r; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:563:7: d= 'deferred'
                    {
                    d=(Token)match(input,58,FOLLOW_58_in_clazz3574); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       mod = Clazz.Mod.DEFERRED; start = d; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:564:7: e= 'effective'
                    {
                    e=(Token)match(input,59,FOLLOW_59_in_clazz3587); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       mod = Clazz.Mod.EFFECTIVE; start = e; 
                    }

                    }
                    break;
                case 4 :
                    // BON.g:565:21: 
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
            // BON.g:571:3: (fg= formal_generics | )
            int alt72=2;
            int LA72_0 = input.LA(1);

            if ( (LA72_0==66) ) {
                alt72=1;
            }
            else if ( ((LA72_0>=IDENTIFIER && LA72_0<=COMMENT)||(LA72_0>=25 && LA72_0<=27)||LA72_0==30||LA72_0==38||(LA72_0>=56 && LA72_0<=61)||(LA72_0>=71 && LA72_0<=72)) ) {
                alt72=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return clazz;}
                NoViableAltException nvae =
                    new NoViableAltException("", 72, 0, input);

                throw nvae;
            }
            switch (alt72) {
                case 1 :
                    // BON.g:571:6: fg= formal_generics
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
                    // BON.g:572:6: 
                    {
                    if ( state.backtracking==0 ) {
                       generics = emptyList(); 
                    }

                    }
                    break;

            }

            // BON.g:574:3: (ru= 'reused' )?
            int alt73=2;
            int LA73_0 = input.LA(1);

            if ( (LA73_0==56) ) {
                alt73=1;
            }
            switch (alt73) {
                case 1 :
                    // BON.g:574:4: ru= 'reused'
                    {
                    ru=(Token)match(input,56,FOLLOW_56_in_clazz3667); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       reused = true; end = ru; 
                    }

                    }
                    break;

            }

            // BON.g:575:3: (p= 'persistent' )?
            int alt74=2;
            int LA74_0 = input.LA(1);

            if ( (LA74_0==60) ) {
                alt74=1;
            }
            switch (alt74) {
                case 1 :
                    // BON.g:575:4: p= 'persistent'
                    {
                    p=(Token)match(input,60,FOLLOW_60_in_clazz3680); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       persistent = true; end = p; 
                    }

                    }
                    break;

            }

            // BON.g:576:3: (i= 'interfaced' )?
            int alt75=2;
            int LA75_0 = input.LA(1);

            if ( (LA75_0==61) ) {
                alt75=1;
            }
            switch (alt75) {
                case 1 :
                    // BON.g:576:4: i= 'interfaced'
                    {
                    i=(Token)match(input,61,FOLLOW_61_in_clazz3694); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       interfaced = true; end = i; 
                    }

                    }
                    break;

            }

            // BON.g:577:3: (co= COMMENT )?
            int alt76=2;
            int LA76_0 = input.LA(1);

            if ( (LA76_0==COMMENT) ) {
                alt76=1;
            }
            switch (alt76) {
                case 1 :
                    // BON.g:577:4: co= COMMENT
                    {
                    co=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_clazz3706); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       comment = (co!=null?co.getText():null); end = co; 
                    }

                    }
                    break;

            }

            // BON.g:579:3: (ci= class_interface )?
            int alt77=2;
            int LA77_0 = input.LA(1);

            if ( (LA77_0==30||LA77_0==38||(LA77_0>=71 && LA77_0<=72)) ) {
                alt77=1;
            }
            switch (alt77) {
                case 1 :
                    // BON.g:579:4: ci= class_interface
                    {
                    pushFollow(FOLLOW_class_interface_in_clazz3721);
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


    // $ANTLR start "static_relation"
    // BON.g:584:1: static_relation returns [StaticRelation relation] : (ir= inheritance_relation | cr= client_relation );
    public final StaticRelation static_relation() throws RecognitionException {
        StaticRelation relation = null;

        InheritanceRelation ir = null;

        ClientRelation cr = null;


        try {
            // BON.g:584:51: (ir= inheritance_relation | cr= client_relation )
            int alt78=2;
            alt78 = dfa78.predict(input);
            switch (alt78) {
                case 1 :
                    // BON.g:585:4: ir= inheritance_relation
                    {
                    pushFollow(FOLLOW_inheritance_relation_in_static_relation3763);
                    ir=inheritance_relation();

                    state._fsp--;
                    if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       if(isOk()) relation = ir; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:587:4: cr= client_relation
                    {
                    pushFollow(FOLLOW_client_relation_in_static_relation3775);
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
    // BON.g:591:1: inheritance_relation returns [InheritanceRelation relation] : c= child 'inherit' (a= '{' multiplicity b= '}' )? p= parent ( semantic_label )? ;
    public final InheritanceRelation inheritance_relation() throws RecognitionException {
        InheritanceRelation relation = null;

        Token a=null;
        Token b=null;
        BONParser.child_return c = null;

        BONParser.parent_return p = null;

        BONParser.multiplicity_return multiplicity64 = null;

        BONParser.semantic_label_return semantic_label65 = null;


         Multiplicity multiplicity = null; String semanticLabel = null; Token end = null; 
        try {
            // BON.g:595:1: (c= child 'inherit' (a= '{' multiplicity b= '}' )? p= parent ( semantic_label )? )
            // BON.g:596:3: c= child 'inherit' (a= '{' multiplicity b= '}' )? p= parent ( semantic_label )?
            {
            pushFollow(FOLLOW_child_in_inheritance_relation3806);
            c=child();

            state._fsp--;
            if (state.failed) return relation;
            match(input,38,FOLLOW_38_in_inheritance_relation3808); if (state.failed) return relation;
            // BON.g:597:3: (a= '{' multiplicity b= '}' )?
            int alt79=2;
            int LA79_0 = input.LA(1);

            if ( (LA79_0==62) ) {
                alt79=1;
            }
            switch (alt79) {
                case 1 :
                    // BON.g:597:4: a= '{' multiplicity b= '}'
                    {
                    a=(Token)match(input,62,FOLLOW_62_in_inheritance_relation3816); if (state.failed) return relation;
                    pushFollow(FOLLOW_multiplicity_in_inheritance_relation3818);
                    multiplicity64=multiplicity();

                    state._fsp--;
                    if (state.failed) return relation;
                    b=(Token)match(input,63,FOLLOW_63_in_inheritance_relation3822); if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       if(isOk()) multiplicity = Multiplicity.mk((multiplicity64!=null?multiplicity64.num:null), getSLoc(a,b)); 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_parent_in_inheritance_relation3839);
            p=parent();

            state._fsp--;
            if (state.failed) return relation;
            if ( state.backtracking==0 ) {
               end = (p!=null?((Token)p.stop):null); 
            }
            // BON.g:602:3: ( semantic_label )?
            int alt80=2;
            int LA80_0 = input.LA(1);

            if ( (LA80_0==MANIFEST_STRING) ) {
                alt80=1;
            }
            switch (alt80) {
                case 1 :
                    // BON.g:602:5: semantic_label
                    {
                    pushFollow(FOLLOW_semantic_label_in_inheritance_relation3850);
                    semantic_label65=semantic_label();

                    state._fsp--;
                    if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       if(isOk()) semanticLabel = (semantic_label65!=null?semantic_label65.label:null); end = (semantic_label65!=null?((Token)semantic_label65.stop):null); 
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
    // BON.g:608:1: client_relation returns [ClientRelation relation] : c= client 'client' ( client_entities )? ( type_mark | ) s= supplier ( semantic_label )? ;
    public final ClientRelation client_relation() throws RecognitionException {
        ClientRelation relation = null;

        BONParser.client_return c = null;

        BONParser.supplier_return s = null;

        ClientEntityExpression client_entities66 = null;

        BONParser.type_mark_return type_mark67 = null;

        BONParser.semantic_label_return semantic_label68 = null;


         ClientEntityExpression entities = null; TypeMark mark = null; String semanticLabel = null; Token end = null; 
        try {
            // BON.g:610:1: (c= client 'client' ( client_entities )? ( type_mark | ) s= supplier ( semantic_label )? )
            // BON.g:611:3: c= client 'client' ( client_entities )? ( type_mark | ) s= supplier ( semantic_label )?
            {
            pushFollow(FOLLOW_client_in_client_relation3909);
            c=client();

            state._fsp--;
            if (state.failed) return relation;
            match(input,64,FOLLOW_64_in_client_relation3911); if (state.failed) return relation;
            // BON.g:612:3: ( client_entities )?
            int alt81=2;
            int LA81_0 = input.LA(1);

            if ( (LA81_0==62) ) {
                alt81=1;
            }
            switch (alt81) {
                case 1 :
                    // BON.g:612:4: client_entities
                    {
                    pushFollow(FOLLOW_client_entities_in_client_relation3916);
                    client_entities66=client_entities();

                    state._fsp--;
                    if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       if(isOk()) entities = client_entities66; 
                    }

                    }
                    break;

            }

            // BON.g:613:3: ( type_mark | )
            int alt82=2;
            int LA82_0 = input.LA(1);

            if ( (LA82_0==34||LA82_0==69) ) {
                alt82=1;
            }
            else if ( (LA82_0==IDENTIFIER) ) {
                alt82=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return relation;}
                NoViableAltException nvae =
                    new NoViableAltException("", 82, 0, input);

                throw nvae;
            }
            switch (alt82) {
                case 1 :
                    // BON.g:613:5: type_mark
                    {
                    pushFollow(FOLLOW_type_mark_in_client_relation3928);
                    type_mark67=type_mark();

                    state._fsp--;
                    if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       if(isOk()) mark = (type_mark67!=null?type_mark67.mark:null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:616:4: 
                    {
                    if ( state.backtracking==0 ) {
                       mark = Constants.NO_TYPE_MARK; 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_supplier_in_client_relation3954);
            s=supplier();

            state._fsp--;
            if (state.failed) return relation;
            if ( state.backtracking==0 ) {
               end = (s!=null?((Token)s.stop):null); 
            }
            // BON.g:620:3: ( semantic_label )?
            int alt83=2;
            int LA83_0 = input.LA(1);

            if ( (LA83_0==MANIFEST_STRING) ) {
                alt83=1;
            }
            switch (alt83) {
                case 1 :
                    // BON.g:620:4: semantic_label
                    {
                    pushFollow(FOLLOW_semantic_label_in_client_relation3964);
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
    // BON.g:624:1: client_entities returns [ClientEntityExpression entities] : '{' cee= client_entity_expression '}' ;
    public final ClientEntityExpression client_entities() throws RecognitionException {
        ClientEntityExpression entities = null;

        ClientEntityExpression cee = null;


        try {
            // BON.g:624:59: ( '{' cee= client_entity_expression '}' )
            // BON.g:625:3: '{' cee= client_entity_expression '}'
            {
            match(input,62,FOLLOW_62_in_client_entities4005); if (state.failed) return entities;
            pushFollow(FOLLOW_client_entity_expression_in_client_entities4009);
            cee=client_entity_expression();

            state._fsp--;
            if (state.failed) return entities;
            match(input,63,FOLLOW_63_in_client_entities4011); if (state.failed) return entities;
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
    // BON.g:629:1: client_entity_expression returns [ClientEntityExpression entities] : (cel= client_entity_list | m= multiplicity );
    public final ClientEntityExpression client_entity_expression() throws RecognitionException {
        ClientEntityExpression entities = null;

        BONParser.client_entity_list_return cel = null;

        BONParser.multiplicity_return m = null;


        try {
            // BON.g:629:68: (cel= client_entity_list | m= multiplicity )
            int alt84=2;
            int LA84_0 = input.LA(1);

            if ( (LA84_0==IDENTIFIER||LA84_0==42||(LA84_0>=65 && LA84_0<=66)||LA84_0==68||LA84_0==79||LA84_0==81) ) {
                alt84=1;
            }
            else if ( (LA84_0==INTEGER) ) {
                alt84=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return entities;}
                NoViableAltException nvae =
                    new NoViableAltException("", 84, 0, input);

                throw nvae;
            }
            switch (alt84) {
                case 1 :
                    // BON.g:630:4: cel= client_entity_list
                    {
                    pushFollow(FOLLOW_client_entity_list_in_client_entity_expression4050);
                    cel=client_entity_list();

                    state._fsp--;
                    if (state.failed) return entities;
                    if ( state.backtracking==0 ) {
                       if(isOk()) entities = ClientEntityList.mk((cel!=null?cel.entities:null),getSLoc((cel!=null?((Token)cel.start):null),(cel!=null?((Token)cel.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:632:4: m= multiplicity
                    {
                    pushFollow(FOLLOW_multiplicity_in_client_entity_expression4063);
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
    // BON.g:636:1: client_entity_list returns [List<ClientEntity> entities] : ce= client_entity ( ',' c= client_entity )* ;
    public final BONParser.client_entity_list_return client_entity_list() throws RecognitionException {
        BONParser.client_entity_list_return retval = new BONParser.client_entity_list_return();
        retval.start = input.LT(1);

        ClientEntity ce = null;

        ClientEntity c = null;


        try {
            // BON.g:636:58: (ce= client_entity ( ',' c= client_entity )* )
            // BON.g:637:3: ce= client_entity ( ',' c= client_entity )*
            {
            if ( state.backtracking==0 ) {
               retval.entities = createList(); 
            }
            pushFollow(FOLLOW_client_entity_in_client_entity_list4116);
            ce=client_entity();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.entities.add(ce); 
            }
            // BON.g:640:3: ( ',' c= client_entity )*
            loop85:
            do {
                int alt85=2;
                int LA85_0 = input.LA(1);

                if ( (LA85_0==35) ) {
                    alt85=1;
                }


                switch (alt85) {
            	case 1 :
            	    // BON.g:640:4: ',' c= client_entity
            	    {
            	    match(input,35,FOLLOW_35_in_client_entity_list4125); if (state.failed) return retval;
            	    pushFollow(FOLLOW_client_entity_in_client_entity_list4129);
            	    c=client_entity();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.entities.add(c); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop85;
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
    // BON.g:649:1: client_entity returns [ClientEntity entity] : ( prefix | infix | supplier_indirection | parent_indirection );
    public final ClientEntity client_entity() throws RecognitionException {
        ClientEntity entity = null;

        SupplierIndirection supplier_indirection69 = null;

        ParentIndirection parent_indirection70 = null;


        try {
            // BON.g:649:45: ( prefix | infix | supplier_indirection | parent_indirection )
            int alt86=4;
            alt86 = dfa86.predict(input);
            switch (alt86) {
                case 1 :
                    // BON.g:650:4: prefix
                    {
                    pushFollow(FOLLOW_prefix_in_client_entity4180);
                    prefix();

                    state._fsp--;
                    if (state.failed) return entity;

                    }
                    break;
                case 2 :
                    // BON.g:651:4: infix
                    {
                    pushFollow(FOLLOW_infix_in_client_entity4185);
                    infix();

                    state._fsp--;
                    if (state.failed) return entity;

                    }
                    break;
                case 3 :
                    // BON.g:652:4: supplier_indirection
                    {
                    pushFollow(FOLLOW_supplier_indirection_in_client_entity4190);
                    supplier_indirection69=supplier_indirection();

                    state._fsp--;
                    if (state.failed) return entity;
                    if ( state.backtracking==0 ) {
                       if(isOk()) entity = supplier_indirection69; 
                    }

                    }
                    break;
                case 4 :
                    // BON.g:654:4: parent_indirection
                    {
                    pushFollow(FOLLOW_parent_indirection_in_client_entity4201);
                    parent_indirection70=parent_indirection();

                    state._fsp--;
                    if (state.failed) return entity;
                    if ( state.backtracking==0 ) {
                       if(isOk()) entity = parent_indirection70; 
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
    // BON.g:658:1: supplier_indirection returns [SupplierIndirection indirection] : (ifp= indirection_feature_part ':' )? gi= generic_indirection ;
    public final SupplierIndirection supplier_indirection() throws RecognitionException {
        SupplierIndirection indirection = null;

        BONParser.indirection_feature_part_return ifp = null;

        BONParser.generic_indirection_return gi = null;


        IndirectionFeaturePart part = null; Token start = null; 
        try {
            // BON.g:660:1: ( (ifp= indirection_feature_part ':' )? gi= generic_indirection )
            // BON.g:661:3: (ifp= indirection_feature_part ':' )? gi= generic_indirection
            {
            // BON.g:661:3: (ifp= indirection_feature_part ':' )?
            int alt87=2;
            int LA87_0 = input.LA(1);

            if ( (LA87_0==IDENTIFIER) ) {
                int LA87_1 = input.LA(2);

                if ( (LA87_1==34) ) {
                    alt87=1;
                }
            }
            else if ( (LA87_0==42||LA87_0==79||LA87_0==81) ) {
                alt87=1;
            }
            switch (alt87) {
                case 1 :
                    // BON.g:661:4: ifp= indirection_feature_part ':'
                    {
                    pushFollow(FOLLOW_indirection_feature_part_in_supplier_indirection4247);
                    ifp=indirection_feature_part();

                    state._fsp--;
                    if (state.failed) return indirection;
                    if ( state.backtracking==0 ) {
                       start = (ifp!=null?((Token)ifp.start):null); 
                    }
                    match(input,34,FOLLOW_34_in_supplier_indirection4251); if (state.failed) return indirection;

                    }
                    break;

            }

            pushFollow(FOLLOW_generic_indirection_in_supplier_indirection4260);
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
    // BON.g:667:1: indirection_feature_part returns [IndirectionFeaturePart part] : ( feature_name | indirection_feature_list );
    public final BONParser.indirection_feature_part_return indirection_feature_part() throws RecognitionException {
        BONParser.indirection_feature_part_return retval = new BONParser.indirection_feature_part_return();
        retval.start = input.LT(1);

        BONParser.feature_name_return feature_name71 = null;

        IndirectionFeatureList indirection_feature_list72 = null;


        try {
            // BON.g:667:64: ( feature_name | indirection_feature_list )
            int alt88=2;
            int LA88_0 = input.LA(1);

            if ( (LA88_0==IDENTIFIER||LA88_0==79||LA88_0==81) ) {
                alt88=1;
            }
            else if ( (LA88_0==42) ) {
                alt88=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 88, 0, input);

                throw nvae;
            }
            switch (alt88) {
                case 1 :
                    // BON.g:668:4: feature_name
                    {
                    pushFollow(FOLLOW_feature_name_in_indirection_feature_part4309);
                    feature_name71=feature_name();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.part = (feature_name71!=null?feature_name71.name:null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:670:4: indirection_feature_list
                    {
                    pushFollow(FOLLOW_indirection_feature_list_in_indirection_feature_part4320);
                    indirection_feature_list72=indirection_feature_list();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.part = indirection_feature_list72; 
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
    // BON.g:674:1: indirection_feature_list returns [IndirectionFeatureList list] : s= '(' fnl= feature_name_list e= ')' ;
    public final IndirectionFeatureList indirection_feature_list() throws RecognitionException {
        IndirectionFeatureList list = null;

        Token s=null;
        Token e=null;
        BONParser.feature_name_list_return fnl = null;


        try {
            // BON.g:674:64: (s= '(' fnl= feature_name_list e= ')' )
            // BON.g:675:3: s= '(' fnl= feature_name_list e= ')'
            {
            s=(Token)match(input,42,FOLLOW_42_in_indirection_feature_list4370); if (state.failed) return list;
            pushFollow(FOLLOW_feature_name_list_in_indirection_feature_list4374);
            fnl=feature_name_list();

            state._fsp--;
            if (state.failed) return list;
            e=(Token)match(input,43,FOLLOW_43_in_indirection_feature_list4378); if (state.failed) return list;
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
    // BON.g:679:1: parent_indirection returns [ParentIndirection indirection] : '->' gi= generic_indirection ;
    public final ParentIndirection parent_indirection() throws RecognitionException {
        ParentIndirection indirection = null;

        BONParser.generic_indirection_return gi = null;


        try {
            // BON.g:679:60: ( '->' gi= generic_indirection )
            // BON.g:680:3: '->' gi= generic_indirection
            {
            match(input,65,FOLLOW_65_in_parent_indirection4426); if (state.failed) return indirection;
            pushFollow(FOLLOW_generic_indirection_in_parent_indirection4430);
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
    // BON.g:684:1: generic_indirection returns [GenericIndirection indirection] : ie= indirection_element ;
    public final BONParser.generic_indirection_return generic_indirection() throws RecognitionException {
        BONParser.generic_indirection_return retval = new BONParser.generic_indirection_return();
        retval.start = input.LT(1);

        BONParser.indirection_element_return ie = null;


        try {
            // BON.g:686:62: (ie= indirection_element )
            // BON.g:690:5: ie= indirection_element
            {
            pushFollow(FOLLOW_indirection_element_in_generic_indirection4482);
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
    // BON.g:694:1: named_indirection returns [NamedIndirection indirection] : (cn= class_name '[' il= indirection_list e= ']' | s= '[' indirection_list ']' );
    public final NamedIndirection named_indirection() throws RecognitionException {
        NamedIndirection indirection = null;

        Token e=null;
        Token s=null;
        BONParser.class_name_return cn = null;

        List<IndirectionElement> il = null;


        try {
            // BON.g:694:58: (cn= class_name '[' il= indirection_list e= ']' | s= '[' indirection_list ']' )
            int alt89=2;
            int LA89_0 = input.LA(1);

            if ( (LA89_0==IDENTIFIER) ) {
                alt89=1;
            }
            else if ( (LA89_0==66) ) {
                alt89=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return indirection;}
                NoViableAltException nvae =
                    new NoViableAltException("", 89, 0, input);

                throw nvae;
            }
            switch (alt89) {
                case 1 :
                    // BON.g:695:4: cn= class_name '[' il= indirection_list e= ']'
                    {
                    pushFollow(FOLLOW_class_name_in_named_indirection4527);
                    cn=class_name();

                    state._fsp--;
                    if (state.failed) return indirection;
                    match(input,66,FOLLOW_66_in_named_indirection4529); if (state.failed) return indirection;
                    pushFollow(FOLLOW_indirection_list_in_named_indirection4533);
                    il=indirection_list();

                    state._fsp--;
                    if (state.failed) return indirection;
                    e=(Token)match(input,67,FOLLOW_67_in_named_indirection4537); if (state.failed) return indirection;
                    if ( state.backtracking==0 ) {
                       if(isOk()) indirection = NamedIndirection.mk((cn!=null?cn.name:null), il, getSLoc((cn!=null?((Token)cn.start):null),e)); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:698:4: s= '[' indirection_list ']'
                    {
                    s=(Token)match(input,66,FOLLOW_66_in_named_indirection4552); if (state.failed) return indirection;
                    pushFollow(FOLLOW_indirection_list_in_named_indirection4554);
                    indirection_list();

                    state._fsp--;
                    if (state.failed) return indirection;
                    match(input,67,FOLLOW_67_in_named_indirection4556); if (state.failed) return indirection;
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
    // BON.g:702:1: indirection_list returns [List<IndirectionElement> list] : i1= indirection_element ( ',' i= indirection_element )* ;
    public final List<IndirectionElement> indirection_list() throws RecognitionException {
        List<IndirectionElement> list = null;

        BONParser.indirection_element_return i1 = null;

        BONParser.indirection_element_return i = null;


        try {
            // BON.g:702:58: (i1= indirection_element ( ',' i= indirection_element )* )
            // BON.g:703:3: i1= indirection_element ( ',' i= indirection_element )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_indirection_element_in_indirection_list4603);
            i1=indirection_element();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               if(isOk()) list.add((i1!=null?i1.el:null)); 
            }
            // BON.g:706:3: ( ',' i= indirection_element )*
            loop90:
            do {
                int alt90=2;
                int LA90_0 = input.LA(1);

                if ( (LA90_0==35) ) {
                    alt90=1;
                }


                switch (alt90) {
            	case 1 :
            	    // BON.g:706:4: ',' i= indirection_element
            	    {
            	    match(input,35,FOLLOW_35_in_indirection_list4613); if (state.failed) return list;
            	    pushFollow(FOLLOW_indirection_element_in_indirection_list4617);
            	    i=indirection_element();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) list.add((i!=null?i.el:null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop90;
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
    // BON.g:711:1: indirection_element returns [IndirectionElement el] : (t= '...' | named_indirection | class_name );
    public final BONParser.indirection_element_return indirection_element() throws RecognitionException {
        BONParser.indirection_element_return retval = new BONParser.indirection_element_return();
        retval.start = input.LT(1);

        Token t=null;
        NamedIndirection named_indirection73 = null;

        BONParser.class_name_return class_name74 = null;


        try {
            // BON.g:711:53: (t= '...' | named_indirection | class_name )
            int alt91=3;
            switch ( input.LA(1) ) {
            case 68:
                {
                alt91=1;
                }
                break;
            case IDENTIFIER:
                {
                int LA91_2 = input.LA(2);

                if ( (LA91_2==35||LA91_2==63||LA91_2==67) ) {
                    alt91=3;
                }
                else if ( (LA91_2==66) ) {
                    alt91=2;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 91, 2, input);

                    throw nvae;
                }
                }
                break;
            case 66:
                {
                alt91=2;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 91, 0, input);

                throw nvae;
            }

            switch (alt91) {
                case 1 :
                    // BON.g:712:4: t= '...'
                    {
                    t=(Token)match(input,68,FOLLOW_68_in_indirection_element4671); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.el = CompactedIndirectionElementImpl.mk(getSLoc(t)); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:714:4: named_indirection
                    {
                    pushFollow(FOLLOW_named_indirection_in_indirection_element4681);
                    named_indirection73=named_indirection();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.el = named_indirection73; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:716:4: class_name
                    {
                    pushFollow(FOLLOW_class_name_in_indirection_element4692);
                    class_name74=class_name();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.el = (class_name74!=null?class_name74.name:null); 
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
    // BON.g:721:1: type_mark returns [TypeMark mark] : (m= ':' | m= ':{' | sm= shared_mark );
    public final BONParser.type_mark_return type_mark() throws RecognitionException {
        BONParser.type_mark_return retval = new BONParser.type_mark_return();
        retval.start = input.LT(1);

        Token m=null;
        TypeMark sm = null;


        try {
            // BON.g:721:35: (m= ':' | m= ':{' | sm= shared_mark )
            int alt92=3;
            int LA92_0 = input.LA(1);

            if ( (LA92_0==34) ) {
                int LA92_1 = input.LA(2);

                if ( (LA92_1==42) ) {
                    alt92=3;
                }
                else if ( (LA92_1==IDENTIFIER||LA92_1==74) ) {
                    alt92=1;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 92, 1, input);

                    throw nvae;
                }
            }
            else if ( (LA92_0==69) ) {
                alt92=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 92, 0, input);

                throw nvae;
            }
            switch (alt92) {
                case 1 :
                    // BON.g:722:4: m= ':'
                    {
                    m=(Token)match(input,34,FOLLOW_34_in_type_mark4737); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.mark = TypeMark.mk(TypeMark.Mark.HASTYPE, null, getSLoc(m)); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:724:4: m= ':{'
                    {
                    m=(Token)match(input,69,FOLLOW_69_in_type_mark4750); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.mark = TypeMark.mk(TypeMark.Mark.AGGREGATE, null, getSLoc(m)); 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:726:4: sm= shared_mark
                    {
                    pushFollow(FOLLOW_shared_mark_in_type_mark4763);
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
    // BON.g:730:1: shared_mark returns [TypeMark mark] : a= ':' '(' m= multiplicity b= ')' ;
    public final TypeMark shared_mark() throws RecognitionException {
        TypeMark mark = null;

        Token a=null;
        Token b=null;
        BONParser.multiplicity_return m = null;


        try {
            // BON.g:730:37: (a= ':' '(' m= multiplicity b= ')' )
            // BON.g:731:3: a= ':' '(' m= multiplicity b= ')'
            {
            a=(Token)match(input,34,FOLLOW_34_in_shared_mark4809); if (state.failed) return mark;
            match(input,42,FOLLOW_42_in_shared_mark4811); if (state.failed) return mark;
            pushFollow(FOLLOW_multiplicity_in_shared_mark4815);
            m=multiplicity();

            state._fsp--;
            if (state.failed) return mark;
            b=(Token)match(input,43,FOLLOW_43_in_shared_mark4819); if (state.failed) return mark;
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
    // BON.g:735:1: child returns [StaticRef ref] : s= static_ref ;
    public final BONParser.child_return child() throws RecognitionException {
        BONParser.child_return retval = new BONParser.child_return();
        retval.start = input.LT(1);

        StaticRef s = null;


        try {
            // BON.g:737:31: (s= static_ref )
            // BON.g:738:3: s= static_ref
            {
            pushFollow(FOLLOW_static_ref_in_child4843);
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
    // BON.g:742:1: parent returns [StaticRef ref] : s= static_ref ;
    public final BONParser.parent_return parent() throws RecognitionException {
        BONParser.parent_return retval = new BONParser.parent_return();
        retval.start = input.LT(1);

        StaticRef s = null;


        try {
            // BON.g:742:32: (s= static_ref )
            // BON.g:743:3: s= static_ref
            {
            pushFollow(FOLLOW_static_ref_in_parent4871);
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
    // BON.g:747:1: client returns [StaticRef ref] : s= static_ref ;
    public final BONParser.client_return client() throws RecognitionException {
        BONParser.client_return retval = new BONParser.client_return();
        retval.start = input.LT(1);

        StaticRef s = null;


        try {
            // BON.g:747:32: (s= static_ref )
            // BON.g:748:3: s= static_ref
            {
            pushFollow(FOLLOW_static_ref_in_client4909);
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
    // BON.g:752:1: supplier returns [StaticRef ref] : s= static_ref ;
    public final BONParser.supplier_return supplier() throws RecognitionException {
        BONParser.supplier_return retval = new BONParser.supplier_return();
        retval.start = input.LT(1);

        StaticRef s = null;


        try {
            // BON.g:752:34: (s= static_ref )
            // BON.g:753:3: s= static_ref
            {
            pushFollow(FOLLOW_static_ref_in_supplier4939);
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
    // BON.g:757:1: static_ref returns [StaticRef ref] : (s= static_component_name | cp= cluster_prefix s= static_component_name );
    public final StaticRef static_ref() throws RecognitionException {
        StaticRef ref = null;

        BONParser.static_component_name_return s = null;

        BONParser.cluster_prefix_return cp = null;


        try {
            // BON.g:757:36: (s= static_component_name | cp= cluster_prefix s= static_component_name )
            int alt93=2;
            int LA93_0 = input.LA(1);

            if ( (LA93_0==IDENTIFIER) ) {
                int LA93_1 = input.LA(2);

                if ( (LA93_1==70) ) {
                    alt93=2;
                }
                else if ( ((LA93_1>=MANIFEST_STRING && LA93_1<=IDENTIFIER)||(LA93_1>=25 && LA93_1<=27)||LA93_1==38||(LA93_1>=57 && LA93_1<=59)||LA93_1==64) ) {
                    alt93=1;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return ref;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 93, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return ref;}
                NoViableAltException nvae =
                    new NoViableAltException("", 93, 0, input);

                throw nvae;
            }
            switch (alt93) {
                case 1 :
                    // BON.g:758:4: s= static_component_name
                    {
                    pushFollow(FOLLOW_static_component_name_in_static_ref4973);
                    s=static_component_name();

                    state._fsp--;
                    if (state.failed) return ref;
                    if ( state.backtracking==0 ) {
                       List<StaticRefPart> empty = emptyList(); if(isOk()) ref = StaticRef.mk(empty, (s!=null?s.ref:null), getSLoc((s!=null?((Token)s.start):null),(s!=null?((Token)s.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:761:4: cp= cluster_prefix s= static_component_name
                    {
                    pushFollow(FOLLOW_cluster_prefix_in_static_ref4989);
                    cp=cluster_prefix();

                    state._fsp--;
                    if (state.failed) return ref;
                    pushFollow(FOLLOW_static_component_name_in_static_ref4993);
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
    // BON.g:765:1: cluster_prefix returns [List<StaticRefPart> prefix] : c1= cluster_name '.' (c= cluster_name '.' )* ;
    public final BONParser.cluster_prefix_return cluster_prefix() throws RecognitionException {
        BONParser.cluster_prefix_return retval = new BONParser.cluster_prefix_return();
        retval.start = input.LT(1);

        BONParser.cluster_name_return c1 = null;

        BONParser.cluster_name_return c = null;


        try {
            // BON.g:765:53: (c1= cluster_name '.' (c= cluster_name '.' )* )
            // BON.g:766:3: c1= cluster_name '.' (c= cluster_name '.' )*
            {
            if ( state.backtracking==0 ) {
               retval.prefix = createList(); 
            }
            pushFollow(FOLLOW_cluster_name_in_cluster_prefix5032);
            c1=cluster_name();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.prefix.add(StaticRefPart.mk((c1!=null?c1.name:null), getSLoc((c1!=null?((Token)c1.start):null),(c1!=null?((Token)c1.stop):null)))); 
            }
            match(input,70,FOLLOW_70_in_cluster_prefix5041); if (state.failed) return retval;
            // BON.g:770:3: (c= cluster_name '.' )*
            loop94:
            do {
                int alt94=2;
                int LA94_0 = input.LA(1);

                if ( (LA94_0==IDENTIFIER) ) {
                    int LA94_1 = input.LA(2);

                    if ( (LA94_1==70) ) {
                        alt94=1;
                    }


                }


                switch (alt94) {
            	case 1 :
            	    // BON.g:770:5: c= cluster_name '.'
            	    {
            	    pushFollow(FOLLOW_cluster_name_in_cluster_prefix5050);
            	    c=cluster_name();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    match(input,70,FOLLOW_70_in_cluster_prefix5052); if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.prefix.add(StaticRefPart.mk((c!=null?c.name:null), getSLoc((c!=null?((Token)c.start):null),(c!=null?((Token)c.stop):null)))); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop94;
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
    // BON.g:777:1: static_component_name returns [StaticRefPart ref] : i= IDENTIFIER ;
    public final BONParser.static_component_name_return static_component_name() throws RecognitionException {
        BONParser.static_component_name_return retval = new BONParser.static_component_name_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // BON.g:777:51: (i= IDENTIFIER )
            // BON.g:778:3: i= IDENTIFIER
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_static_component_name5084); if (state.failed) return retval;
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
    // BON.g:782:1: multiplicity returns [Integer num] : i= INTEGER ;
    public final BONParser.multiplicity_return multiplicity() throws RecognitionException {
        BONParser.multiplicity_return retval = new BONParser.multiplicity_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // BON.g:782:36: (i= INTEGER )
            // BON.g:783:3: i= INTEGER
            {
            i=(Token)match(input,INTEGER,FOLLOW_INTEGER_in_multiplicity5128); if (state.failed) return retval;
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
    // BON.g:787:1: semantic_label returns [String label] : m= MANIFEST_STRING ;
    public final BONParser.semantic_label_return semantic_label() throws RecognitionException {
        BONParser.semantic_label_return retval = new BONParser.semantic_label_return();
        retval.start = input.LT(1);

        Token m=null;

        try {
            // BON.g:787:39: (m= MANIFEST_STRING )
            // BON.g:788:3: m= MANIFEST_STRING
            {
            m=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_semantic_label5164); if (state.failed) return retval;
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
    // BON.g:792:1: class_interface returns [ClassInterface ci] : (cisi= class_interface_start_indexing | cisp= class_interface_start_inherit | cisf= class_interface_start_features | cisv= class_interface_start_invariant );
    public final BONParser.class_interface_return class_interface() throws RecognitionException {
        BONParser.class_interface_return retval = new BONParser.class_interface_return();
        retval.start = input.LT(1);

        ClassInterface cisi = null;

        ClassInterface cisp = null;

        ClassInterface cisf = null;

        ClassInterface cisv = null;


        try {
            // BON.g:796:45: (cisi= class_interface_start_indexing | cisp= class_interface_start_inherit | cisf= class_interface_start_features | cisv= class_interface_start_invariant )
            int alt95=4;
            switch ( input.LA(1) ) {
            case 30:
                {
                alt95=1;
                }
                break;
            case 38:
                {
                alt95=2;
                }
                break;
            case 72:
                {
                alt95=3;
                }
                break;
            case 71:
                {
                alt95=4;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 95, 0, input);

                throw nvae;
            }

            switch (alt95) {
                case 1 :
                    // BON.g:797:5: cisi= class_interface_start_indexing
                    {
                    pushFollow(FOLLOW_class_interface_start_indexing_in_class_interface5190);
                    cisi=class_interface_start_indexing();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                      if(isOk()) retval.ci =cisi;
                    }

                    }
                    break;
                case 2 :
                    // BON.g:798:5: cisp= class_interface_start_inherit
                    {
                    pushFollow(FOLLOW_class_interface_start_inherit_in_class_interface5200);
                    cisp=class_interface_start_inherit();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                      if(isOk()) retval.ci =cisp;
                    }

                    }
                    break;
                case 3 :
                    // BON.g:799:5: cisf= class_interface_start_features
                    {
                    pushFollow(FOLLOW_class_interface_start_features_in_class_interface5210);
                    cisf=class_interface_start_features();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                      if(isOk()) retval.ci =cisf;
                    }

                    }
                    break;
                case 4 :
                    // BON.g:800:5: cisv= class_interface_start_invariant
                    {
                    pushFollow(FOLLOW_class_interface_start_invariant_in_class_interface5220);
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
    // BON.g:803:1: class_interface_start_indexing returns [ClassInterface ci] : indexing (pcl= parent_class_list )? ( features )? (inv= class_invariant )? e= 'end' ;
    public final ClassInterface class_interface_start_indexing() throws RecognitionException {
        ClassInterface ci = null;

        Token e=null;
        BONParser.parent_class_list_return pcl = null;

        BONParser.class_invariant_return inv = null;

        BONParser.indexing_return indexing75 = null;

        BONParser.features_return features76 = null;


         Indexing indexing = null; List<Type> parents = emptyList(); 
                List<Expression> invariant = emptyList(); Token start = null; 
                List<Feature> features = emptyList(); 
        try {
            // BON.g:807:1: ( indexing (pcl= parent_class_list )? ( features )? (inv= class_invariant )? e= 'end' )
            // BON.g:808:3: indexing (pcl= parent_class_list )? ( features )? (inv= class_invariant )? e= 'end'
            {
            pushFollow(FOLLOW_indexing_in_class_interface_start_indexing5242);
            indexing75=indexing();

            state._fsp--;
            if (state.failed) return ci;
            if ( state.backtracking==0 ) {
               if(isOk()) indexing = (indexing75!=null?indexing75.indexing:null); start = (indexing75!=null?((Token)indexing75.start):null); 
            }
            // BON.g:809:3: (pcl= parent_class_list )?
            int alt96=2;
            int LA96_0 = input.LA(1);

            if ( (LA96_0==38) ) {
                alt96=1;
            }
            switch (alt96) {
                case 1 :
                    // BON.g:809:6: pcl= parent_class_list
                    {
                    pushFollow(FOLLOW_parent_class_list_in_class_interface_start_indexing5254);
                    pcl=parent_class_list();

                    state._fsp--;
                    if (state.failed) return ci;
                    if ( state.backtracking==0 ) {
                       if(isOk()) parents = (pcl!=null?pcl.parents:null); if (start == null) start = (pcl!=null?((Token)pcl.start):null); 
                    }

                    }
                    break;

            }

            // BON.g:810:3: ( features )?
            int alt97=2;
            int LA97_0 = input.LA(1);

            if ( (LA97_0==72) ) {
                alt97=1;
            }
            switch (alt97) {
                case 1 :
                    // BON.g:810:7: features
                    {
                    pushFollow(FOLLOW_features_in_class_interface_start_indexing5267);
                    features76=features();

                    state._fsp--;
                    if (state.failed) return ci;
                    if ( state.backtracking==0 ) {
                       if(isOk()) features = (features76!=null?features76.features:null); 
                    }

                    }
                    break;

            }

            // BON.g:811:3: (inv= class_invariant )?
            int alt98=2;
            int LA98_0 = input.LA(1);

            if ( (LA98_0==71) ) {
                alt98=1;
            }
            switch (alt98) {
                case 1 :
                    // BON.g:811:6: inv= class_invariant
                    {
                    pushFollow(FOLLOW_class_invariant_in_class_interface_start_indexing5281);
                    inv=class_invariant();

                    state._fsp--;
                    if (state.failed) return ci;
                    if ( state.backtracking==0 ) {
                       if(isOk()) invariant = (inv!=null?inv.invariant:null); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_class_interface_start_indexing5292); if (state.failed) return ci;
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
    // BON.g:816:1: class_interface_start_inherit returns [ClassInterface ci] : pcl= parent_class_list ( features )? (inv= class_invariant )? e= 'end' ;
    public final ClassInterface class_interface_start_inherit() throws RecognitionException {
        ClassInterface ci = null;

        Token e=null;
        BONParser.parent_class_list_return pcl = null;

        BONParser.class_invariant_return inv = null;

        BONParser.features_return features77 = null;


         Indexing indexing = null; List<Type> parents = emptyList(); 
                List<Expression> invariant = emptyList(); Token start = null; 
                List<Feature> features = emptyList(); 
        try {
            // BON.g:820:1: (pcl= parent_class_list ( features )? (inv= class_invariant )? e= 'end' )
            // BON.g:821:3: pcl= parent_class_list ( features )? (inv= class_invariant )? e= 'end'
            {
            pushFollow(FOLLOW_parent_class_list_in_class_interface_start_inherit5318);
            pcl=parent_class_list();

            state._fsp--;
            if (state.failed) return ci;
            if ( state.backtracking==0 ) {
               start = (pcl!=null?((Token)pcl.start):null); 
            }
            // BON.g:822:3: ( features )?
            int alt99=2;
            int LA99_0 = input.LA(1);

            if ( (LA99_0==72) ) {
                alt99=1;
            }
            switch (alt99) {
                case 1 :
                    // BON.g:822:7: features
                    {
                    pushFollow(FOLLOW_features_in_class_interface_start_inherit5328);
                    features77=features();

                    state._fsp--;
                    if (state.failed) return ci;
                    if ( state.backtracking==0 ) {
                       if(isOk()) features = (features77!=null?features77.features:null); 
                    }

                    }
                    break;

            }

            // BON.g:823:3: (inv= class_invariant )?
            int alt100=2;
            int LA100_0 = input.LA(1);

            if ( (LA100_0==71) ) {
                alt100=1;
            }
            switch (alt100) {
                case 1 :
                    // BON.g:823:6: inv= class_invariant
                    {
                    pushFollow(FOLLOW_class_invariant_in_class_interface_start_inherit5342);
                    inv=class_invariant();

                    state._fsp--;
                    if (state.failed) return ci;
                    if ( state.backtracking==0 ) {
                       if(isOk()) invariant = (inv!=null?inv.invariant:null); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_class_interface_start_inherit5353); if (state.failed) return ci;
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
    // BON.g:828:1: class_interface_start_features returns [ClassInterface ci] : features (inv= class_invariant )? e= 'end' ;
    public final ClassInterface class_interface_start_features() throws RecognitionException {
        ClassInterface ci = null;

        Token e=null;
        BONParser.class_invariant_return inv = null;

        BONParser.features_return features78 = null;


         Indexing indexing = null; List<Type> parents = emptyList(); 
                List<Expression> invariant = emptyList(); Token start = null; 
        try {
            // BON.g:831:1: ( features (inv= class_invariant )? e= 'end' )
            // BON.g:832:3: features (inv= class_invariant )? e= 'end'
            {
            pushFollow(FOLLOW_features_in_class_interface_start_features5377);
            features78=features();

            state._fsp--;
            if (state.failed) return ci;
            if ( state.backtracking==0 ) {
               start = (features78!=null?((Token)features78.start):null); 
            }
            // BON.g:833:3: (inv= class_invariant )?
            int alt101=2;
            int LA101_0 = input.LA(1);

            if ( (LA101_0==71) ) {
                alt101=1;
            }
            switch (alt101) {
                case 1 :
                    // BON.g:833:6: inv= class_invariant
                    {
                    pushFollow(FOLLOW_class_invariant_in_class_interface_start_features5388);
                    inv=class_invariant();

                    state._fsp--;
                    if (state.failed) return ci;
                    if ( state.backtracking==0 ) {
                       if(isOk()) invariant = (inv!=null?inv.invariant:null); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_class_interface_start_features5399); if (state.failed) return ci;
            if ( state.backtracking==0 ) {
               if(isOk()) ci = ClassInterface.mk((features78!=null?features78.features:null), parents, invariant, indexing, getSLoc(start, e)); 
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
    // BON.g:838:1: class_interface_start_invariant returns [ClassInterface ci] : inv= class_invariant e= 'end' ;
    public final ClassInterface class_interface_start_invariant() throws RecognitionException {
        ClassInterface ci = null;

        Token e=null;
        BONParser.class_invariant_return inv = null;


         Indexing indexing = null; List<Type> parents = emptyList(); 
                Token start = null; List<Feature> features = emptyList(); 
        try {
            // BON.g:841:1: (inv= class_invariant e= 'end' )
            // BON.g:842:3: inv= class_invariant e= 'end'
            {
            pushFollow(FOLLOW_class_invariant_in_class_interface_start_invariant5425);
            inv=class_invariant();

            state._fsp--;
            if (state.failed) return ci;
            if ( state.backtracking==0 ) {
               start = (inv!=null?((Token)inv.start):null); 
            }
            e=(Token)match(input,25,FOLLOW_25_in_class_interface_start_invariant5433); if (state.failed) return ci;
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
    // BON.g:847:1: class_invariant returns [List<Expression> invariant] : 'invariant' assertion ;
    public final BONParser.class_invariant_return class_invariant() throws RecognitionException {
        BONParser.class_invariant_return retval = new BONParser.class_invariant_return();
        retval.start = input.LT(1);

        List<Expression> assertion79 = null;


        try {
            // BON.g:847:54: ( 'invariant' assertion )
            // BON.g:848:3: 'invariant' assertion
            {
            match(input,71,FOLLOW_71_in_class_invariant5452); if (state.failed) return retval;
            pushFollow(FOLLOW_assertion_in_class_invariant5454);
            assertion79=assertion();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.invariant = assertion79; 
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
    // BON.g:852:1: parent_class_list returns [List<Type> parents] : ( 'inherit' c1= class_type ( ';' c= class_type )* ( ';' )? | i= 'inherit' );
    public final BONParser.parent_class_list_return parent_class_list() throws RecognitionException {
        BONParser.parent_class_list_return retval = new BONParser.parent_class_list_return();
        retval.start = input.LT(1);

        Token i=null;
        BONParser.class_type_return c1 = null;

        BONParser.class_type_return c = null;


        try {
            // BON.g:852:48: ( 'inherit' c1= class_type ( ';' c= class_type )* ( ';' )? | i= 'inherit' )
            int alt104=2;
            int LA104_0 = input.LA(1);

            if ( (LA104_0==38) ) {
                int LA104_1 = input.LA(2);

                if ( (LA104_1==25||(LA104_1>=71 && LA104_1<=72)) ) {
                    alt104=2;
                }
                else if ( (LA104_1==IDENTIFIER) ) {
                    alt104=1;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 104, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 104, 0, input);

                throw nvae;
            }
            switch (alt104) {
                case 1 :
                    // BON.g:853:3: 'inherit' c1= class_type ( ';' c= class_type )* ( ';' )?
                    {
                    if ( state.backtracking==0 ) {
                       retval.parents = createList(); 
                    }
                    match(input,38,FOLLOW_38_in_parent_class_list5495); if (state.failed) return retval;
                    pushFollow(FOLLOW_class_type_in_parent_class_list5499);
                    c1=class_type();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.parents.add((c1!=null?c1.type:null)); 
                    }
                    // BON.g:856:3: ( ';' c= class_type )*
                    loop102:
                    do {
                        int alt102=2;
                        int LA102_0 = input.LA(1);

                        if ( (LA102_0==33) ) {
                            int LA102_1 = input.LA(2);

                            if ( (LA102_1==IDENTIFIER) ) {
                                alt102=1;
                            }


                        }


                        switch (alt102) {
                    	case 1 :
                    	    // BON.g:856:4: ';' c= class_type
                    	    {
                    	    match(input,33,FOLLOW_33_in_parent_class_list5510); if (state.failed) return retval;
                    	    pushFollow(FOLLOW_class_type_in_parent_class_list5514);
                    	    c=class_type();

                    	    state._fsp--;
                    	    if (state.failed) return retval;
                    	    if ( state.backtracking==0 ) {
                    	       if(isOk()) retval.parents.add((c!=null?c.type:null)); 
                    	    }

                    	    }
                    	    break;

                    	default :
                    	    break loop102;
                        }
                    } while (true);

                    // BON.g:859:3: ( ';' )?
                    int alt103=2;
                    int LA103_0 = input.LA(1);

                    if ( (LA103_0==33) ) {
                        alt103=1;
                    }
                    switch (alt103) {
                        case 1 :
                            // BON.g:859:3: ';'
                            {
                            match(input,33,FOLLOW_33_in_parent_class_list5531); if (state.failed) return retval;

                            }
                            break;

                    }


                    }
                    break;
                case 2 :
                    // BON.g:861:3: i= 'inherit'
                    {
                    i=(Token)match(input,38,FOLLOW_38_in_parent_class_list5542); if (state.failed) return retval;
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
    // BON.g:865:1: features returns [List<Feature> features] : ( feature_clause )+ ;
    public final BONParser.features_return features() throws RecognitionException {
        BONParser.features_return retval = new BONParser.features_return();
        retval.start = input.LT(1);

        Feature feature_clause80 = null;


        try {
            // BON.g:865:43: ( ( feature_clause )+ )
            // BON.g:866:3: ( feature_clause )+
            {
            if ( state.backtracking==0 ) {
               retval.features = createList(); 
            }
            // BON.g:867:3: ( feature_clause )+
            int cnt105=0;
            loop105:
            do {
                int alt105=2;
                int LA105_0 = input.LA(1);

                if ( (LA105_0==72) ) {
                    alt105=1;
                }


                switch (alt105) {
            	case 1 :
            	    // BON.g:867:4: feature_clause
            	    {
            	    pushFollow(FOLLOW_feature_clause_in_features5586);
            	    feature_clause80=feature_clause();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.features.add(feature_clause80); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt105 >= 1 ) break loop105;
            	    if (state.backtracking>0) {state.failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(105, input);
                        throw eee;
                }
                cnt105++;
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
    // BON.g:870:1: feature_clause returns [Feature feature] : f= 'feature' (se= selective_export | ) (c= COMMENT )? fs= feature_specifications ;
    public final Feature feature_clause() throws RecognitionException {
        Feature feature = null;

        Token f=null;
        Token c=null;
        List<ClassName> se = null;

        BONParser.feature_specifications_return fs = null;


         String comment = null; List<ClassName> selectiveExport = null; 
        try {
            // BON.g:874:1: (f= 'feature' (se= selective_export | ) (c= COMMENT )? fs= feature_specifications )
            // BON.g:875:3: f= 'feature' (se= selective_export | ) (c= COMMENT )? fs= feature_specifications
            {
            f=(Token)match(input,72,FOLLOW_72_in_feature_clause5627); if (state.failed) return feature;
            // BON.g:876:3: (se= selective_export | )
            int alt106=2;
            int LA106_0 = input.LA(1);

            if ( (LA106_0==62) ) {
                alt106=1;
            }
            else if ( ((LA106_0>=IDENTIFIER && LA106_0<=COMMENT)||(LA106_0>=58 && LA106_0<=59)||LA106_0==73||LA106_0==79||LA106_0==81) ) {
                alt106=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return feature;}
                NoViableAltException nvae =
                    new NoViableAltException("", 106, 0, input);

                throw nvae;
            }
            switch (alt106) {
                case 1 :
                    // BON.g:876:6: se= selective_export
                    {
                    pushFollow(FOLLOW_selective_export_in_feature_clause5637);
                    se=selective_export();

                    state._fsp--;
                    if (state.failed) return feature;
                    if ( state.backtracking==0 ) {
                       if(isOk()) selectiveExport = se; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:877:6: 
                    {
                    if ( state.backtracking==0 ) {
                       selectiveExport = emptyList(); 
                    }

                    }
                    break;

            }

            // BON.g:879:3: (c= COMMENT )?
            int alt107=2;
            int LA107_0 = input.LA(1);

            if ( (LA107_0==COMMENT) ) {
                alt107=1;
            }
            switch (alt107) {
                case 1 :
                    // BON.g:879:4: c= COMMENT
                    {
                    c=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_feature_clause5659); if (state.failed) return feature;
                    if ( state.backtracking==0 ) {
                       if(isOk()) comment = (c!=null?c.getText():null); 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_feature_specifications_in_feature_clause5671);
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
    // BON.g:884:1: feature_specifications returns [List<FeatureSpecification> specs] : (fs= feature_specification )+ ;
    public final BONParser.feature_specifications_return feature_specifications() throws RecognitionException {
        BONParser.feature_specifications_return retval = new BONParser.feature_specifications_return();
        retval.start = input.LT(1);

        FeatureSpecification fs = null;


        try {
            // BON.g:884:67: ( (fs= feature_specification )+ )
            // BON.g:885:3: (fs= feature_specification )+
            {
            if ( state.backtracking==0 ) {
               retval.specs = createList(); 
            }
            // BON.g:886:3: (fs= feature_specification )+
            int cnt108=0;
            loop108:
            do {
                int alt108=2;
                int LA108_0 = input.LA(1);

                if ( (LA108_0==IDENTIFIER||(LA108_0>=58 && LA108_0<=59)||LA108_0==73||LA108_0==79||LA108_0==81) ) {
                    alt108=1;
                }


                switch (alt108) {
            	case 1 :
            	    // BON.g:886:4: fs= feature_specification
            	    {
            	    pushFollow(FOLLOW_feature_specification_in_feature_specifications5714);
            	    fs=feature_specification();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.specs.add(fs); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt108 >= 1 ) break loop108;
            	    if (state.backtracking>0) {state.failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(108, input);
                        throw eee;
                }
                cnt108++;
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
    // BON.g:889:1: feature_specification returns [FeatureSpecification spec] : (d= 'deferred' | e= 'effective' | r= 'redefined' | ) fnl= feature_name_list ( has_type )? (rc= rename_clause )? (c= COMMENT )? (fa= feature_arguments | ) (cc= contract_clause | ) ;
    public final FeatureSpecification feature_specification() throws RecognitionException {
        FeatureSpecification spec = null;

        Token d=null;
        Token e=null;
        Token r=null;
        Token c=null;
        BONParser.feature_name_list_return fnl = null;

        BONParser.rename_clause_return rc = null;

        BONParser.feature_arguments_return fa = null;

        BONParser.contract_clause_return cc = null;

        BONParser.has_type_return has_type81 = null;


         FeatureSpecification.Modifier modifier = FeatureSpecification.Modifier.NONE; 
                List<FeatureArgument> args = null; HasType hasType = null; Token start = null; Token end = null;
                RenameClause renaming = null; String comment = null; ContractClause contracts = null;
        try {
            // BON.g:893:1: ( (d= 'deferred' | e= 'effective' | r= 'redefined' | ) fnl= feature_name_list ( has_type )? (rc= rename_clause )? (c= COMMENT )? (fa= feature_arguments | ) (cc= contract_clause | ) )
            // BON.g:894:3: (d= 'deferred' | e= 'effective' | r= 'redefined' | ) fnl= feature_name_list ( has_type )? (rc= rename_clause )? (c= COMMENT )? (fa= feature_arguments | ) (cc= contract_clause | )
            {
            // BON.g:894:3: (d= 'deferred' | e= 'effective' | r= 'redefined' | )
            int alt109=4;
            switch ( input.LA(1) ) {
            case 58:
                {
                alt109=1;
                }
                break;
            case 59:
                {
                alt109=2;
                }
                break;
            case 73:
                {
                alt109=3;
                }
                break;
            case IDENTIFIER:
            case 79:
            case 81:
                {
                alt109=4;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return spec;}
                NoViableAltException nvae =
                    new NoViableAltException("", 109, 0, input);

                throw nvae;
            }

            switch (alt109) {
                case 1 :
                    // BON.g:894:6: d= 'deferred'
                    {
                    d=(Token)match(input,58,FOLLOW_58_in_feature_specification5769); if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       modifier = FeatureSpecification.Modifier.DEFERRED; start = d; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:895:6: e= 'effective'
                    {
                    e=(Token)match(input,59,FOLLOW_59_in_feature_specification5782); if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       modifier = FeatureSpecification.Modifier.EFFECTIVE; start = e; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:896:6: r= 'redefined'
                    {
                    r=(Token)match(input,73,FOLLOW_73_in_feature_specification5793); if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       modifier = FeatureSpecification.Modifier.REDEFINED; start = r; 
                    }

                    }
                    break;
                case 4 :
                    // BON.g:897:18: 
                    {
                    if ( state.backtracking==0 ) {
                       modifier = FeatureSpecification.Modifier.NONE; 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_feature_name_list_in_feature_specification5824);
            fnl=feature_name_list();

            state._fsp--;
            if (state.failed) return spec;
            if ( state.backtracking==0 ) {
               end=(fnl!=null?((Token)fnl.stop):null); if (start==null) start=(fnl!=null?((Token)fnl.start):null); 
            }
            // BON.g:901:3: ( has_type )?
            int alt110=2;
            int LA110_0 = input.LA(1);

            if ( (LA110_0==34||LA110_0==69) ) {
                alt110=1;
            }
            switch (alt110) {
                case 1 :
                    // BON.g:901:4: has_type
                    {
                    pushFollow(FOLLOW_has_type_in_feature_specification5833);
                    has_type81=has_type();

                    state._fsp--;
                    if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) hasType = (has_type81!=null?has_type81.htype:null); end=(has_type81!=null?((Token)has_type81.stop):null); 
                    }

                    }
                    break;

            }

            // BON.g:902:3: (rc= rename_clause )?
            int alt111=2;
            int LA111_0 = input.LA(1);

            if ( (LA111_0==62) ) {
                alt111=1;
            }
            switch (alt111) {
                case 1 :
                    // BON.g:902:4: rc= rename_clause
                    {
                    pushFollow(FOLLOW_rename_clause_in_feature_specification5845);
                    rc=rename_clause();

                    state._fsp--;
                    if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) renaming = (rc!=null?rc.rename:null); end=(rc!=null?((Token)rc.stop):null); 
                    }

                    }
                    break;

            }

            // BON.g:903:3: (c= COMMENT )?
            int alt112=2;
            int LA112_0 = input.LA(1);

            if ( (LA112_0==COMMENT) ) {
                alt112=1;
            }
            switch (alt112) {
                case 1 :
                    // BON.g:903:4: c= COMMENT
                    {
                    c=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_feature_specification5857); if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) comment = (c!=null?c.getText():null); end=c; 
                    }

                    }
                    break;

            }

            // BON.g:904:3: (fa= feature_arguments | )
            int alt113=2;
            int LA113_0 = input.LA(1);

            if ( (LA113_0==65||LA113_0==78) ) {
                alt113=1;
            }
            else if ( (LA113_0==IDENTIFIER||LA113_0==25||(LA113_0>=58 && LA113_0<=59)||(LA113_0>=71 && LA113_0<=73)||(LA113_0>=75 && LA113_0<=76)||LA113_0==79||LA113_0==81) ) {
                alt113=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return spec;}
                NoViableAltException nvae =
                    new NoViableAltException("", 113, 0, input);

                throw nvae;
            }
            switch (alt113) {
                case 1 :
                    // BON.g:904:6: fa= feature_arguments
                    {
                    pushFollow(FOLLOW_feature_arguments_in_feature_specification5871);
                    fa=feature_arguments();

                    state._fsp--;
                    if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) args = (fa!=null?fa.args:null); end=(fa!=null?((Token)fa.stop):null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:906:6: 
                    {
                    if ( state.backtracking==0 ) {
                       args = emptyList(); 
                    }

                    }
                    break;

            }

            // BON.g:908:3: (cc= contract_clause | )
            int alt114=2;
            int LA114_0 = input.LA(1);

            if ( ((LA114_0>=75 && LA114_0<=76)) ) {
                alt114=1;
            }
            else if ( (LA114_0==IDENTIFIER||LA114_0==25||(LA114_0>=58 && LA114_0<=59)||(LA114_0>=71 && LA114_0<=73)||LA114_0==79||LA114_0==81) ) {
                alt114=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return spec;}
                NoViableAltException nvae =
                    new NoViableAltException("", 114, 0, input);

                throw nvae;
            }
            switch (alt114) {
                case 1 :
                    // BON.g:908:6: cc= contract_clause
                    {
                    pushFollow(FOLLOW_contract_clause_in_feature_specification5898);
                    cc=contract_clause();

                    state._fsp--;
                    if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       if(isOk()) contracts = (cc!=null?cc.contracts:null); end=(cc!=null?((Token)cc.stop):null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:910:6: 
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
    // BON.g:915:1: has_type returns [HasType htype] : type_mark ( type | v= 'Void' ) ;
    public final BONParser.has_type_return has_type() throws RecognitionException {
        BONParser.has_type_return retval = new BONParser.has_type_return();
        retval.start = input.LT(1);

        Token v=null;
        BONParser.type_mark_return type_mark82 = null;

        BONParser.type_return type83 = null;


        try {
            // BON.g:915:34: ( type_mark ( type | v= 'Void' ) )
            // BON.g:916:3: type_mark ( type | v= 'Void' )
            {
            pushFollow(FOLLOW_type_mark_in_has_type5961);
            type_mark82=type_mark();

            state._fsp--;
            if (state.failed) return retval;
            // BON.g:917:3: ( type | v= 'Void' )
            int alt115=2;
            int LA115_0 = input.LA(1);

            if ( (LA115_0==IDENTIFIER) ) {
                alt115=1;
            }
            else if ( (LA115_0==74) ) {
                alt115=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 115, 0, input);

                throw nvae;
            }
            switch (alt115) {
                case 1 :
                    // BON.g:917:6: type
                    {
                    pushFollow(FOLLOW_type_in_has_type5969);
                    type83=type();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.htype = HasType.mk((type_mark82!=null?type_mark82.mark:null), (type83!=null?type83.type:null), getSLoc((type_mark82!=null?((Token)type_mark82.start):null),(type83!=null?((Token)type83.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:919:6: v= 'Void'
                    {
                    v=(Token)match(input,74,FOLLOW_74_in_has_type5986); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.htype = HasType.mk((type_mark82!=null?type_mark82.mark:null), BONType.voidType(getSLoc(v)), getSLoc(v)); 
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
    // BON.g:924:1: contract_clause returns [ContractClause contracts] : cc= contracting_conditions 'end' ;
    public final BONParser.contract_clause_return contract_clause() throws RecognitionException {
        BONParser.contract_clause_return retval = new BONParser.contract_clause_return();
        retval.start = input.LT(1);

        ContractClause cc = null;


        try {
            // BON.g:926:52: (cc= contracting_conditions 'end' )
            // BON.g:927:3: cc= contracting_conditions 'end'
            {
            pushFollow(FOLLOW_contracting_conditions_in_contract_clause6017);
            cc=contracting_conditions();

            state._fsp--;
            if (state.failed) return retval;
            match(input,25,FOLLOW_25_in_contract_clause6019); if (state.failed) return retval;
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
    // BON.g:932:1: contracting_conditions returns [ContractClause contracts] : ( (pre= precondition (post= postcondition )? ) | post= postcondition ) ;
    public final ContractClause contracting_conditions() throws RecognitionException {
        ContractClause contracts = null;

        BONParser.precondition_return pre = null;

        BONParser.postcondition_return post = null;


         List<Expression> postC = null; 
        try {
            // BON.g:934:1: ( ( (pre= precondition (post= postcondition )? ) | post= postcondition ) )
            // BON.g:935:3: ( (pre= precondition (post= postcondition )? ) | post= postcondition )
            {
            // BON.g:935:3: ( (pre= precondition (post= postcondition )? ) | post= postcondition )
            int alt117=2;
            int LA117_0 = input.LA(1);

            if ( (LA117_0==75) ) {
                alt117=1;
            }
            else if ( (LA117_0==76) ) {
                alt117=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return contracts;}
                NoViableAltException nvae =
                    new NoViableAltException("", 117, 0, input);

                throw nvae;
            }
            switch (alt117) {
                case 1 :
                    // BON.g:935:6: (pre= precondition (post= postcondition )? )
                    {
                    // BON.g:935:6: (pre= precondition (post= postcondition )? )
                    // BON.g:935:7: pre= precondition (post= postcondition )?
                    {
                    pushFollow(FOLLOW_precondition_in_contracting_conditions6051);
                    pre=precondition();

                    state._fsp--;
                    if (state.failed) return contracts;
                    // BON.g:935:24: (post= postcondition )?
                    int alt116=2;
                    int LA116_0 = input.LA(1);

                    if ( (LA116_0==76) ) {
                        alt116=1;
                    }
                    switch (alt116) {
                        case 1 :
                            // BON.g:935:25: post= postcondition
                            {
                            pushFollow(FOLLOW_postcondition_in_contracting_conditions6056);
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
                    // BON.g:938:6: post= postcondition
                    {
                    pushFollow(FOLLOW_postcondition_in_contracting_conditions6080);
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
    // BON.g:943:1: precondition returns [List<Expression> assertions] : 'require' assertion ;
    public final BONParser.precondition_return precondition() throws RecognitionException {
        BONParser.precondition_return retval = new BONParser.precondition_return();
        retval.start = input.LT(1);

        List<Expression> assertion84 = null;


        try {
            // BON.g:943:52: ( 'require' assertion )
            // BON.g:944:3: 'require' assertion
            {
            match(input,75,FOLLOW_75_in_precondition6106); if (state.failed) return retval;
            pushFollow(FOLLOW_assertion_in_precondition6108);
            assertion84=assertion();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.assertions = assertion84; 
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
    // BON.g:948:1: postcondition returns [List<Expression> assertions] : 'ensure' assertion ;
    public final BONParser.postcondition_return postcondition() throws RecognitionException {
        BONParser.postcondition_return retval = new BONParser.postcondition_return();
        retval.start = input.LT(1);

        List<Expression> assertion85 = null;


        try {
            // BON.g:948:53: ( 'ensure' assertion )
            // BON.g:949:3: 'ensure' assertion
            {
            match(input,76,FOLLOW_76_in_postcondition6142); if (state.failed) return retval;
            pushFollow(FOLLOW_assertion_in_postcondition6144);
            assertion85=assertion();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.assertions = assertion85; 
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
    // BON.g:953:1: selective_export returns [List<ClassName> exports] : '{' cnl= class_name_list '}' ;
    public final List<ClassName> selective_export() throws RecognitionException {
        List<ClassName> exports = null;

        List<ClassName> cnl = null;


        try {
            // BON.g:955:52: ( '{' cnl= class_name_list '}' )
            // BON.g:956:3: '{' cnl= class_name_list '}'
            {
            match(input,62,FOLLOW_62_in_selective_export6167); if (state.failed) return exports;
            pushFollow(FOLLOW_class_name_list_in_selective_export6171);
            cnl=class_name_list();

            state._fsp--;
            if (state.failed) return exports;
            match(input,63,FOLLOW_63_in_selective_export6173); if (state.failed) return exports;
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
    // BON.g:960:1: feature_name_list returns [List<FeatureName> list] : f1= feature_name ( ',' f= feature_name )* ;
    public final BONParser.feature_name_list_return feature_name_list() throws RecognitionException {
        BONParser.feature_name_list_return retval = new BONParser.feature_name_list_return();
        retval.start = input.LT(1);

        BONParser.feature_name_return f1 = null;

        BONParser.feature_name_return f = null;


        try {
            // BON.g:960:52: (f1= feature_name ( ',' f= feature_name )* )
            // BON.g:961:3: f1= feature_name ( ',' f= feature_name )*
            {
            if ( state.backtracking==0 ) {
               retval.list = createList(); 
            }
            pushFollow(FOLLOW_feature_name_in_feature_name_list6218);
            f1=feature_name();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.list.add((f1!=null?f1.name:null)); 
            }
            // BON.g:964:3: ( ',' f= feature_name )*
            loop118:
            do {
                int alt118=2;
                int LA118_0 = input.LA(1);

                if ( (LA118_0==35) ) {
                    alt118=1;
                }


                switch (alt118) {
            	case 1 :
            	    // BON.g:964:4: ',' f= feature_name
            	    {
            	    match(input,35,FOLLOW_35_in_feature_name_list6228); if (state.failed) return retval;
            	    pushFollow(FOLLOW_feature_name_in_feature_name_list6232);
            	    f=feature_name();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.list.add((f!=null?f.name:null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop118;
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
    // BON.g:969:1: feature_name returns [FeatureName name] : (i= IDENTIFIER | prefix | infix );
    public final BONParser.feature_name_return feature_name() throws RecognitionException {
        BONParser.feature_name_return retval = new BONParser.feature_name_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // BON.g:969:41: (i= IDENTIFIER | prefix | infix )
            int alt119=3;
            switch ( input.LA(1) ) {
            case IDENTIFIER:
                {
                alt119=1;
                }
                break;
            case 79:
                {
                alt119=2;
                }
                break;
            case 81:
                {
                alt119=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 119, 0, input);

                throw nvae;
            }

            switch (alt119) {
                case 1 :
                    // BON.g:970:4: i= IDENTIFIER
                    {
                    i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_feature_name6281); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.name = FeatureName.mk((i!=null?i.getText():null), getSLoc(i)); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:972:4: prefix
                    {
                    pushFollow(FOLLOW_prefix_in_feature_name6291);
                    prefix();

                    state._fsp--;
                    if (state.failed) return retval;

                    }
                    break;
                case 3 :
                    // BON.g:973:4: infix
                    {
                    pushFollow(FOLLOW_infix_in_feature_name6297);
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
    // BON.g:976:1: rename_clause returns [RenameClause rename] : '{' renaming '}' ;
    public final BONParser.rename_clause_return rename_clause() throws RecognitionException {
        BONParser.rename_clause_return retval = new BONParser.rename_clause_return();
        retval.start = input.LT(1);

        RenameClause renaming86 = null;


        try {
            // BON.g:976:45: ( '{' renaming '}' )
            // BON.g:977:3: '{' renaming '}'
            {
            match(input,62,FOLLOW_62_in_rename_clause6327); if (state.failed) return retval;
            pushFollow(FOLLOW_renaming_in_rename_clause6329);
            renaming86=renaming();

            state._fsp--;
            if (state.failed) return retval;
            match(input,63,FOLLOW_63_in_rename_clause6331); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.rename = renaming86; 
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
    // BON.g:981:1: renaming returns [RenameClause renaming] : s= '^' class_name '.' feature_name ;
    public final RenameClause renaming() throws RecognitionException {
        RenameClause renaming = null;

        Token s=null;
        BONParser.class_name_return class_name87 = null;

        BONParser.feature_name_return feature_name88 = null;


        try {
            // BON.g:981:42: (s= '^' class_name '.' feature_name )
            // BON.g:982:3: s= '^' class_name '.' feature_name
            {
            s=(Token)match(input,77,FOLLOW_77_in_renaming6367); if (state.failed) return renaming;
            pushFollow(FOLLOW_class_name_in_renaming6369);
            class_name87=class_name();

            state._fsp--;
            if (state.failed) return renaming;
            match(input,70,FOLLOW_70_in_renaming6371); if (state.failed) return renaming;
            pushFollow(FOLLOW_feature_name_in_renaming6373);
            feature_name88=feature_name();

            state._fsp--;
            if (state.failed) return renaming;
            if ( state.backtracking==0 ) {
               if(isOk()) renaming = RenameClause.mk((class_name87!=null?class_name87.name:null), (feature_name88!=null?feature_name88.name:null), getSLoc(s,(feature_name88!=null?((Token)feature_name88.stop):null))); 
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
    // BON.g:986:1: feature_arguments returns [List<FeatureArgument> args] : ( feature_argument )+ ;
    public final BONParser.feature_arguments_return feature_arguments() throws RecognitionException {
        BONParser.feature_arguments_return retval = new BONParser.feature_arguments_return();
        retval.start = input.LT(1);

        List<FeatureArgument> feature_argument89 = null;


        try {
            // BON.g:986:56: ( ( feature_argument )+ )
            // BON.g:987:3: ( feature_argument )+
            {
            if ( state.backtracking==0 ) {
               retval.args = createList(); 
            }
            // BON.g:988:3: ( feature_argument )+
            int cnt120=0;
            loop120:
            do {
                int alt120=2;
                int LA120_0 = input.LA(1);

                if ( (LA120_0==65||LA120_0==78) ) {
                    alt120=1;
                }


                switch (alt120) {
            	case 1 :
            	    // BON.g:988:4: feature_argument
            	    {
            	    pushFollow(FOLLOW_feature_argument_in_feature_arguments6408);
            	    feature_argument89=feature_argument();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.args.addAll(feature_argument89); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt120 >= 1 ) break loop120;
            	    if (state.backtracking>0) {state.failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(120, input);
                        throw eee;
                }
                cnt120++;
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
    // BON.g:991:1: feature_argument returns [List<FeatureArgument> args] : ( '->' | '<-' ) ( ( identifier_list ':' t1= type ) | (t2= type ) ) ;
    public final List<FeatureArgument> feature_argument() throws RecognitionException {
        List<FeatureArgument> args = null;

        BONParser.type_return t1 = null;

        BONParser.type_return t2 = null;

        BONParser.identifier_list_return identifier_list90 = null;


        try {
            // BON.g:991:55: ( ( '->' | '<-' ) ( ( identifier_list ':' t1= type ) | (t2= type ) ) )
            // BON.g:992:3: ( '->' | '<-' ) ( ( identifier_list ':' t1= type ) | (t2= type ) )
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

            // BON.g:993:3: ( ( identifier_list ':' t1= type ) | (t2= type ) )
            int alt121=2;
            int LA121_0 = input.LA(1);

            if ( (LA121_0==IDENTIFIER) ) {
                int LA121_1 = input.LA(2);

                if ( (LA121_1==IDENTIFIER||LA121_1==25||(LA121_1>=58 && LA121_1<=59)||(LA121_1>=65 && LA121_1<=66)||(LA121_1>=71 && LA121_1<=73)||(LA121_1>=75 && LA121_1<=76)||(LA121_1>=78 && LA121_1<=79)||LA121_1==81) ) {
                    alt121=2;
                }
                else if ( ((LA121_1>=34 && LA121_1<=35)) ) {
                    alt121=1;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return args;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 121, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return args;}
                NoViableAltException nvae =
                    new NoViableAltException("", 121, 0, input);

                throw nvae;
            }
            switch (alt121) {
                case 1 :
                    // BON.g:994:6: ( identifier_list ':' t1= type )
                    {
                    // BON.g:994:6: ( identifier_list ':' t1= type )
                    // BON.g:994:8: identifier_list ':' t1= type
                    {
                    pushFollow(FOLLOW_identifier_list_in_feature_argument6472);
                    identifier_list90=identifier_list();

                    state._fsp--;
                    if (state.failed) return args;
                    match(input,34,FOLLOW_34_in_feature_argument6474); if (state.failed) return args;
                    pushFollow(FOLLOW_type_in_feature_argument6478);
                    t1=type();

                    state._fsp--;
                    if (state.failed) return args;
                    if ( state.backtracking==0 ) {
                       if(isOk()) { List<String> ids = (identifier_list90!=null?identifier_list90.list:null); args = new ArrayList<FeatureArgument>(ids.size()); for (String id : (identifier_list90!=null?identifier_list90.list:null)) args.add(FeatureArgument.mk(id, (t1!=null?t1.type:null), getSLoc((identifier_list90!=null?((Token)identifier_list90.start):null), (t1!=null?((Token)t1.stop):null)))); } 
                    }

                    }


                    }
                    break;
                case 2 :
                    // BON.g:997:6: (t2= type )
                    {
                    // BON.g:997:6: (t2= type )
                    // BON.g:997:8: t2= type
                    {
                    pushFollow(FOLLOW_type_in_feature_argument6510);
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
    // BON.g:1003:1: identifier_list returns [List<String> list] : i1= IDENTIFIER ( ',' i= IDENTIFIER )* ;
    public final BONParser.identifier_list_return identifier_list() throws RecognitionException {
        BONParser.identifier_list_return retval = new BONParser.identifier_list_return();
        retval.start = input.LT(1);

        Token i1=null;
        Token i=null;

        try {
            // BON.g:1003:45: (i1= IDENTIFIER ( ',' i= IDENTIFIER )* )
            // BON.g:1004:3: i1= IDENTIFIER ( ',' i= IDENTIFIER )*
            {
            if ( state.backtracking==0 ) {
               retval.list = createList(); 
            }
            i1=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_identifier_list6570); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.list.add((i1!=null?i1.getText():null)); 
            }
            // BON.g:1007:3: ( ',' i= IDENTIFIER )*
            loop122:
            do {
                int alt122=2;
                int LA122_0 = input.LA(1);

                if ( (LA122_0==35) ) {
                    alt122=1;
                }


                switch (alt122) {
            	case 1 :
            	    // BON.g:1007:4: ',' i= IDENTIFIER
            	    {
            	    match(input,35,FOLLOW_35_in_identifier_list6580); if (state.failed) return retval;
            	    i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_identifier_list6584); if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.list.add((i!=null?i.getText():null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop122;
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
    // BON.g:1011:1: prefix : 'prefix' '\"' prefix_operator '\"' ;
    public final void prefix() throws RecognitionException {
        try {
            // BON.g:1011:9: ( 'prefix' '\"' prefix_operator '\"' )
            // BON.g:1011:12: 'prefix' '\"' prefix_operator '\"'
            {
            match(input,79,FOLLOW_79_in_prefix6601); if (state.failed) return ;
            match(input,80,FOLLOW_80_in_prefix6603); if (state.failed) return ;
            pushFollow(FOLLOW_prefix_operator_in_prefix6605);
            prefix_operator();

            state._fsp--;
            if (state.failed) return ;
            match(input,80,FOLLOW_80_in_prefix6607); if (state.failed) return ;

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
    // BON.g:1014:1: infix : 'infix' '\"' infix_operator '\"' ;
    public final void infix() throws RecognitionException {
        try {
            // BON.g:1014:8: ( 'infix' '\"' infix_operator '\"' )
            // BON.g:1014:11: 'infix' '\"' infix_operator '\"'
            {
            match(input,81,FOLLOW_81_in_infix6626); if (state.failed) return ;
            match(input,80,FOLLOW_80_in_infix6628); if (state.failed) return ;
            pushFollow(FOLLOW_infix_operator_in_infix6630);
            infix_operator();

            state._fsp--;
            if (state.failed) return ;
            match(input,80,FOLLOW_80_in_infix6632); if (state.failed) return ;

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
    // BON.g:1018:1: prefix_operator : unary ;
    public final void prefix_operator() throws RecognitionException {
        try {
            // BON.g:1018:18: ( unary )
            // BON.g:1018:21: unary
            {
            pushFollow(FOLLOW_unary_in_prefix_operator6652);
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
    // BON.g:1022:1: infix_operator : binary ;
    public final void infix_operator() throws RecognitionException {
        try {
            // BON.g:1022:17: ( binary )
            // BON.g:1023:3: binary
            {
            pushFollow(FOLLOW_binary_in_infix_operator6667);
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
    // BON.g:1027:1: formal_generics returns [List<FormalGeneric> generics] : '[' fgl= formal_generic_list ']' ;
    public final BONParser.formal_generics_return formal_generics() throws RecognitionException {
        BONParser.formal_generics_return retval = new BONParser.formal_generics_return();
        retval.start = input.LT(1);

        List<FormalGeneric> fgl = null;


        try {
            // BON.g:1029:56: ( '[' fgl= formal_generic_list ']' )
            // BON.g:1030:3: '[' fgl= formal_generic_list ']'
            {
            match(input,66,FOLLOW_66_in_formal_generics6686); if (state.failed) return retval;
            pushFollow(FOLLOW_formal_generic_list_in_formal_generics6690);
            fgl=formal_generic_list();

            state._fsp--;
            if (state.failed) return retval;
            match(input,67,FOLLOW_67_in_formal_generics6692); if (state.failed) return retval;
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
    // BON.g:1034:1: formal_generic_list returns [List<FormalGeneric> list] : fg1= formal_generic ( ',' fg= formal_generic )* ;
    public final List<FormalGeneric> formal_generic_list() throws RecognitionException {
        List<FormalGeneric> list = null;

        FormalGeneric fg1 = null;

        FormalGeneric fg = null;


        try {
            // BON.g:1034:56: (fg1= formal_generic ( ',' fg= formal_generic )* )
            // BON.g:1035:3: fg1= formal_generic ( ',' fg= formal_generic )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_formal_generic_in_formal_generic_list6735);
            fg1=formal_generic();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               if(isOk()) list.add(fg1); 
            }
            // BON.g:1038:3: ( ',' fg= formal_generic )*
            loop123:
            do {
                int alt123=2;
                int LA123_0 = input.LA(1);

                if ( (LA123_0==35) ) {
                    alt123=1;
                }


                switch (alt123) {
            	case 1 :
            	    // BON.g:1038:4: ',' fg= formal_generic
            	    {
            	    match(input,35,FOLLOW_35_in_formal_generic_list6744); if (state.failed) return list;
            	    pushFollow(FOLLOW_formal_generic_in_formal_generic_list6748);
            	    fg=formal_generic();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) list.add(fg); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop123;
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
    // BON.g:1043:1: formal_generic returns [FormalGeneric generic] : (f= formal_generic_name | f= formal_generic_name '->' ct= class_type );
    public final FormalGeneric formal_generic() throws RecognitionException {
        FormalGeneric generic = null;

        BONParser.formal_generic_name_return f = null;

        BONParser.class_type_return ct = null;


        try {
            // BON.g:1043:48: (f= formal_generic_name | f= formal_generic_name '->' ct= class_type )
            int alt124=2;
            int LA124_0 = input.LA(1);

            if ( (LA124_0==IDENTIFIER) ) {
                int LA124_1 = input.LA(2);

                if ( (LA124_1==65) ) {
                    alt124=2;
                }
                else if ( (LA124_1==35||LA124_1==67) ) {
                    alt124=1;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return generic;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 124, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return generic;}
                NoViableAltException nvae =
                    new NoViableAltException("", 124, 0, input);

                throw nvae;
            }
            switch (alt124) {
                case 1 :
                    // BON.g:1044:4: f= formal_generic_name
                    {
                    pushFollow(FOLLOW_formal_generic_name_in_formal_generic6798);
                    f=formal_generic_name();

                    state._fsp--;
                    if (state.failed) return generic;
                    if ( state.backtracking==0 ) {
                       if(isOk()) generic = FormalGeneric.mk((f!=null?f.name:null), null, getSLoc((f!=null?((Token)f.start):null),(f!=null?((Token)f.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1046:4: f= formal_generic_name '->' ct= class_type
                    {
                    pushFollow(FOLLOW_formal_generic_name_in_formal_generic6810);
                    f=formal_generic_name();

                    state._fsp--;
                    if (state.failed) return generic;
                    match(input,65,FOLLOW_65_in_formal_generic6812); if (state.failed) return generic;
                    pushFollow(FOLLOW_class_type_in_formal_generic6816);
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
    // BON.g:1050:1: formal_generic_name returns [String name] : i= IDENTIFIER ;
    public final BONParser.formal_generic_name_return formal_generic_name() throws RecognitionException {
        BONParser.formal_generic_name_return retval = new BONParser.formal_generic_name_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // BON.g:1050:43: (i= IDENTIFIER )
            // BON.g:1051:3: i= IDENTIFIER
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_formal_generic_name6855); if (state.failed) return retval;
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
    // BON.g:1055:1: class_type returns [Type type] : c= class_name ( actual_generics | ) ;
    public final BONParser.class_type_return class_type() throws RecognitionException {
        BONParser.class_type_return retval = new BONParser.class_type_return();
        retval.start = input.LT(1);

        BONParser.class_name_return c = null;

        BONParser.actual_generics_return actual_generics91 = null;


        try {
            // BON.g:1055:32: (c= class_name ( actual_generics | ) )
            // BON.g:1056:3: c= class_name ( actual_generics | )
            {
            pushFollow(FOLLOW_class_name_in_class_type6900);
            c=class_name();

            state._fsp--;
            if (state.failed) return retval;
            // BON.g:1057:3: ( actual_generics | )
            int alt125=2;
            int LA125_0 = input.LA(1);

            if ( (LA125_0==66) ) {
                alt125=1;
            }
            else if ( (LA125_0==25||LA125_0==33||LA125_0==35||LA125_0==67||(LA125_0>=71 && LA125_0<=72)) ) {
                alt125=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 125, 0, input);

                throw nvae;
            }
            switch (alt125) {
                case 1 :
                    // BON.g:1057:6: actual_generics
                    {
                    pushFollow(FOLLOW_actual_generics_in_class_type6908);
                    actual_generics91=actual_generics();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.type = BONType.mk((c!=null?input.toString(c.start,c.stop):null), (actual_generics91!=null?actual_generics91.types:null), (c!=null?input.toString(c.start,c.stop):null).concat((actual_generics91!=null?input.toString(actual_generics91.start,actual_generics91.stop):null)), getSLoc((c!=null?((Token)c.start):null), (actual_generics91!=null?((Token)actual_generics91.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1060:6: 
                    {
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.type = BONType.mk((c!=null?input.toString(c.start,c.stop):null), Constants.EMPTY_TYPE_LIST, (c!=null?input.toString(c.start,c.stop):null), getSLoc((c!=null?((Token)c.start):null),(c!=null?((Token)c.stop):null))); 
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
    // BON.g:1064:1: actual_generics returns [List<Type> types] : '[' type_list ']' ;
    public final BONParser.actual_generics_return actual_generics() throws RecognitionException {
        BONParser.actual_generics_return retval = new BONParser.actual_generics_return();
        retval.start = input.LT(1);

        List<Type> type_list92 = null;


        try {
            // BON.g:1064:44: ( '[' type_list ']' )
            // BON.g:1065:19: '[' type_list ']'
            {
            match(input,66,FOLLOW_66_in_actual_generics6979); if (state.failed) return retval;
            pushFollow(FOLLOW_type_list_in_actual_generics6981);
            type_list92=type_list();

            state._fsp--;
            if (state.failed) return retval;
            match(input,67,FOLLOW_67_in_actual_generics6983); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.types = type_list92; 
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
    // BON.g:1069:1: type_list returns [List<Type> types] : t1= type ( ',' t= type )* ;
    public final List<Type> type_list() throws RecognitionException {
        List<Type> types = null;

        BONParser.type_return t1 = null;

        BONParser.type_return t = null;


        try {
            // BON.g:1069:39: (t1= type ( ',' t= type )* )
            // BON.g:1070:12: t1= type ( ',' t= type )*
            {
            pushFollow(FOLLOW_type_in_type_list7047);
            t1=type();

            state._fsp--;
            if (state.failed) return types;
            if ( state.backtracking==0 ) {
               types = createList(); if(isOk()) types.add((t1!=null?t1.type:null)); 
            }
            // BON.g:1072:12: ( ',' t= type )*
            loop126:
            do {
                int alt126=2;
                int LA126_0 = input.LA(1);

                if ( (LA126_0==35) ) {
                    alt126=1;
                }


                switch (alt126) {
            	case 1 :
            	    // BON.g:1072:13: ',' t= type
            	    {
            	    match(input,35,FOLLOW_35_in_type_list7075); if (state.failed) return types;
            	    pushFollow(FOLLOW_type_in_type_list7079);
            	    t=type();

            	    state._fsp--;
            	    if (state.failed) return types;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) types.add((t!=null?t.type:null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop126;
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
    // BON.g:1080:1: type returns [Type type] : i= IDENTIFIER ( ( actual_generics ) | ) ;
    public final BONParser.type_return type() throws RecognitionException {
        BONParser.type_return retval = new BONParser.type_return();
        retval.start = input.LT(1);

        Token i=null;
        BONParser.actual_generics_return actual_generics93 = null;


        try {
            // BON.g:1080:26: (i= IDENTIFIER ( ( actual_generics ) | ) )
            // BON.g:1081:8: i= IDENTIFIER ( ( actual_generics ) | )
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_type7134); if (state.failed) return retval;
            // BON.g:1082:8: ( ( actual_generics ) | )
            int alt127=2;
            int LA127_0 = input.LA(1);

            if ( (LA127_0==66) ) {
                alt127=1;
            }
            else if ( ((LA127_0>=IDENTIFIER && LA127_0<=COMMENT)||LA127_0==25||LA127_0==33||LA127_0==35||(LA127_0>=58 && LA127_0<=59)||LA127_0==62||LA127_0==65||LA127_0==67||(LA127_0>=71 && LA127_0<=73)||(LA127_0>=75 && LA127_0<=76)||(LA127_0>=78 && LA127_0<=79)||LA127_0==81||(LA127_0>=84 && LA127_0<=85)) ) {
                alt127=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 127, 0, input);

                throw nvae;
            }
            switch (alt127) {
                case 1 :
                    // BON.g:1083:9: ( actual_generics )
                    {
                    // BON.g:1083:9: ( actual_generics )
                    // BON.g:1083:11: actual_generics
                    {
                    pushFollow(FOLLOW_actual_generics_in_type7156);
                    actual_generics93=actual_generics();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       String fullText = (actual_generics93!=null?input.toString(actual_generics93.start,actual_generics93.stop):null)==null? (i!=null?i.getText():null) : (i!=null?i.getText():null).concat((actual_generics93!=null?input.toString(actual_generics93.start,actual_generics93.stop):null));
                                  if(isOk()) retval.type = BONType.mk((i!=null?i.getText():null), (actual_generics93!=null?actual_generics93.types:null), fullText, getSLoc(i,(actual_generics93!=null?((Token)actual_generics93.stop):null))); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // BON.g:1088:9: 
                    {
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.type = BONType.mk((i!=null?i.getText():null), Constants.EMPTY_TYPE_LIST, (i!=null?i.getText():null),getSLoc(i)); 
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
    // BON.g:1092:1: assertion returns [List<Expression> clauses] : a1= assertion_clause ( ';' a= assertion_clause )* ( ';' )? ;
    public final List<Expression> assertion() throws RecognitionException {
        List<Expression> clauses = null;

        Expression a1 = null;

        Expression a = null;


        try {
            // BON.g:1097:46: (a1= assertion_clause ( ';' a= assertion_clause )* ( ';' )? )
            // BON.g:1098:3: a1= assertion_clause ( ';' a= assertion_clause )* ( ';' )?
            {
            if ( state.backtracking==0 ) {
               clauses = createList(); 
            }
            pushFollow(FOLLOW_assertion_clause_in_assertion7235);
            a1=assertion_clause();

            state._fsp--;
            if (state.failed) return clauses;
            if ( state.backtracking==0 ) {
               if(isOk()) clauses.add(a1); 
            }
            // BON.g:1101:3: ( ';' a= assertion_clause )*
            loop128:
            do {
                int alt128=2;
                int LA128_0 = input.LA(1);

                if ( (LA128_0==33) ) {
                    int LA128_1 = input.LA(2);

                    if ( ((LA128_1>=MANIFEST_STRING && LA128_1<=IDENTIFIER)||(LA128_1>=INTEGER && LA128_1<=REAL)||LA128_1==42||LA128_1==62||LA128_1==74||(LA128_1>=82 && LA128_1<=83)||(LA128_1>=88 && LA128_1<=91)||(LA128_1>=103 && LA128_1<=104)||(LA128_1>=108 && LA128_1<=110)) ) {
                        alt128=1;
                    }


                }


                switch (alt128) {
            	case 1 :
            	    // BON.g:1101:4: ';' a= assertion_clause
            	    {
            	    match(input,33,FOLLOW_33_in_assertion7244); if (state.failed) return clauses;
            	    pushFollow(FOLLOW_assertion_clause_in_assertion7248);
            	    a=assertion_clause();

            	    state._fsp--;
            	    if (state.failed) return clauses;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) clauses.add(a); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop128;
                }
            } while (true);

            // BON.g:1104:3: ( ';' )?
            int alt129=2;
            int LA129_0 = input.LA(1);

            if ( (LA129_0==33) ) {
                alt129=1;
            }
            switch (alt129) {
                case 1 :
                    // BON.g:1104:3: ';'
                    {
                    match(input,33,FOLLOW_33_in_assertion7265); if (state.failed) return clauses;

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
    // BON.g:1107:1: assertion_clause returns [Expression clause] : be= boolean_expression ;
    public final Expression assertion_clause() throws RecognitionException {
        Expression clause = null;

        Expression be = null;


        try {
            // BON.g:1107:46: (be= boolean_expression )
            // BON.g:1108:3: be= boolean_expression
            {
            pushFollow(FOLLOW_boolean_expression_in_assertion_clause7294);
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
    // BON.g:1115:1: boolean_expression returns [Expression exp] : expression ;
    public final Expression boolean_expression() throws RecognitionException {
        Expression exp = null;

        BONParser.expression_return expression94 = null;


        try {
            // BON.g:1115:45: ( expression )
            // BON.g:1116:3: expression
            {
            pushFollow(FOLLOW_expression_in_boolean_expression7316);
            expression94=expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp = (expression94!=null?expression94.exp:null); 
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
    // BON.g:1120:1: quantification returns [Quantification quantification] : q= quantifier rexp= range_expression (r= restriction )? p= proposition ;
    public final Quantification quantification() throws RecognitionException {
        Quantification quantification = null;

        BONParser.quantifier_return q = null;

        List<VariableRange> rexp = null;

        Expression r = null;

        BONParser.proposition_return p = null;


         Expression restrict = null; 
        try {
            // BON.g:1122:1: (q= quantifier rexp= range_expression (r= restriction )? p= proposition )
            // BON.g:1123:3: q= quantifier rexp= range_expression (r= restriction )? p= proposition
            {
            pushFollow(FOLLOW_quantifier_in_quantification7356);
            q=quantifier();

            state._fsp--;
            if (state.failed) return quantification;
            pushFollow(FOLLOW_range_expression_in_quantification7363);
            rexp=range_expression();

            state._fsp--;
            if (state.failed) return quantification;
            // BON.g:1125:3: (r= restriction )?
            int alt130=2;
            int LA130_0 = input.LA(1);

            if ( (LA130_0==84) ) {
                alt130=1;
            }
            switch (alt130) {
                case 1 :
                    // BON.g:1125:4: r= restriction
                    {
                    pushFollow(FOLLOW_restriction_in_quantification7371);
                    r=restriction();

                    state._fsp--;
                    if (state.failed) return quantification;
                    if ( state.backtracking==0 ) {
                       if(isOk()) restrict = r; 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_proposition_in_quantification7383);
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
    // BON.g:1130:1: quantifier returns [Quantification.Quantifier q] : (f= 'for_all' | e= 'exists' );
    public final BONParser.quantifier_return quantifier() throws RecognitionException {
        BONParser.quantifier_return retval = new BONParser.quantifier_return();
        retval.start = input.LT(1);

        Token f=null;
        Token e=null;

        try {
            // BON.g:1130:50: (f= 'for_all' | e= 'exists' )
            int alt131=2;
            int LA131_0 = input.LA(1);

            if ( (LA131_0==82) ) {
                alt131=1;
            }
            else if ( (LA131_0==83) ) {
                alt131=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 131, 0, input);

                throw nvae;
            }
            switch (alt131) {
                case 1 :
                    // BON.g:1131:4: f= 'for_all'
                    {
                    f=(Token)match(input,82,FOLLOW_82_in_quantifier7422); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.q = Quantification.Quantifier.FORALL; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1133:4: e= 'exists'
                    {
                    e=(Token)match(input,83,FOLLOW_83_in_quantifier7435); if (state.failed) return retval;
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
    // BON.g:1137:1: range_expression returns [List<VariableRange> ranges] : vr1= variable_range ( ';' vr= variable_range )* ( ';' )? ;
    public final List<VariableRange> range_expression() throws RecognitionException {
        List<VariableRange> ranges = null;

        VariableRange vr1 = null;

        VariableRange vr = null;


        try {
            // BON.g:1137:55: (vr1= variable_range ( ';' vr= variable_range )* ( ';' )? )
            // BON.g:1138:3: vr1= variable_range ( ';' vr= variable_range )* ( ';' )?
            {
            if ( state.backtracking==0 ) {
               ranges = createList(); 
            }
            pushFollow(FOLLOW_variable_range_in_range_expression7473);
            vr1=variable_range();

            state._fsp--;
            if (state.failed) return ranges;
            if ( state.backtracking==0 ) {
               if(isOk()) ranges.add(vr); 
            }
            // BON.g:1141:3: ( ';' vr= variable_range )*
            loop132:
            do {
                int alt132=2;
                int LA132_0 = input.LA(1);

                if ( (LA132_0==33) ) {
                    int LA132_1 = input.LA(2);

                    if ( (LA132_1==IDENTIFIER) ) {
                        alt132=1;
                    }


                }


                switch (alt132) {
            	case 1 :
            	    // BON.g:1141:4: ';' vr= variable_range
            	    {
            	    match(input,33,FOLLOW_33_in_range_expression7483); if (state.failed) return ranges;
            	    pushFollow(FOLLOW_variable_range_in_range_expression7487);
            	    vr=variable_range();

            	    state._fsp--;
            	    if (state.failed) return ranges;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) ranges.add(vr); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop132;
                }
            } while (true);

            // BON.g:1144:3: ( ';' )?
            int alt133=2;
            int LA133_0 = input.LA(1);

            if ( (LA133_0==33) ) {
                alt133=1;
            }
            switch (alt133) {
                case 1 :
                    // BON.g:1144:3: ';'
                    {
                    match(input,33,FOLLOW_33_in_range_expression7502); if (state.failed) return ranges;

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
    // BON.g:1147:1: restriction returns [Expression exp] : st= 'such_that' be= boolean_expression ;
    public final Expression restriction() throws RecognitionException {
        Expression exp = null;

        Token st=null;
        Expression be = null;


        try {
            // BON.g:1147:38: (st= 'such_that' be= boolean_expression )
            // BON.g:1148:3: st= 'such_that' be= boolean_expression
            {
            st=(Token)match(input,84,FOLLOW_84_in_restriction7539); if (state.failed) return exp;
            pushFollow(FOLLOW_boolean_expression_in_restriction7543);
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
    // BON.g:1152:1: proposition returns [Expression exp] : ih= 'it_holds' be= boolean_expression ;
    public final BONParser.proposition_return proposition() throws RecognitionException {
        BONParser.proposition_return retval = new BONParser.proposition_return();
        retval.start = input.LT(1);

        Token ih=null;
        Expression be = null;


        try {
            // BON.g:1152:38: (ih= 'it_holds' be= boolean_expression )
            // BON.g:1153:3: ih= 'it_holds' be= boolean_expression
            {
            ih=(Token)match(input,85,FOLLOW_85_in_proposition7577); if (state.failed) return retval;
            pushFollow(FOLLOW_boolean_expression_in_proposition7581);
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
    // BON.g:1157:1: variable_range returns [VariableRange range] : (mr= member_range | tr= type_range );
    public final VariableRange variable_range() throws RecognitionException {
        VariableRange range = null;

        MemberRange mr = null;

        TypeRange tr = null;


        try {
            // BON.g:1157:46: (mr= member_range | tr= type_range )
            int alt134=2;
            alt134 = dfa134.predict(input);
            switch (alt134) {
                case 1 :
                    // BON.g:1158:4: mr= member_range
                    {
                    pushFollow(FOLLOW_member_range_in_variable_range7617);
                    mr=member_range();

                    state._fsp--;
                    if (state.failed) return range;
                    if ( state.backtracking==0 ) {
                       if(isOk()) range = mr; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1160:4: tr= type_range
                    {
                    pushFollow(FOLLOW_type_range_in_variable_range7629);
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
    // BON.g:1164:1: member_range returns [MemberRange range] : il= identifier_list 'member_of' e= expression ;
    public final MemberRange member_range() throws RecognitionException {
        MemberRange range = null;

        BONParser.identifier_list_return il = null;

        BONParser.expression_return e = null;


        try {
            // BON.g:1164:42: (il= identifier_list 'member_of' e= expression )
            // BON.g:1165:3: il= identifier_list 'member_of' e= expression
            {
            pushFollow(FOLLOW_identifier_list_in_member_range7669);
            il=identifier_list();

            state._fsp--;
            if (state.failed) return range;
            match(input,86,FOLLOW_86_in_member_range7671); if (state.failed) return range;
            pushFollow(FOLLOW_expression_in_member_range7675);
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
    // BON.g:1169:1: type_range returns [TypeRange range] : il= identifier_list ':' t= type ;
    public final TypeRange type_range() throws RecognitionException {
        TypeRange range = null;

        BONParser.identifier_list_return il = null;

        BONParser.type_return t = null;


        try {
            // BON.g:1169:38: (il= identifier_list ':' t= type )
            // BON.g:1170:3: il= identifier_list ':' t= type
            {
            pushFollow(FOLLOW_identifier_list_in_type_range7711);
            il=identifier_list();

            state._fsp--;
            if (state.failed) return range;
            match(input,34,FOLLOW_34_in_type_range7713); if (state.failed) return range;
            pushFollow(FOLLOW_type_in_type_range7717);
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
    // BON.g:1174:1: call_chain returns [List<UnqualifiedCall> calls] : uc1= unqualified_call ( '.' uc= unqualified_call )* ;
    public final BONParser.call_chain_return call_chain() throws RecognitionException {
        BONParser.call_chain_return retval = new BONParser.call_chain_return();
        retval.start = input.LT(1);

        UnqualifiedCall uc1 = null;

        UnqualifiedCall uc = null;


        try {
            // BON.g:1176:50: (uc1= unqualified_call ( '.' uc= unqualified_call )* )
            // BON.g:1177:3: uc1= unqualified_call ( '.' uc= unqualified_call )*
            {
            if ( state.backtracking==0 ) {
               if(isOk()) retval.calls = createList(); 
            }
            pushFollow(FOLLOW_unqualified_call_in_call_chain7777);
            uc1=unqualified_call();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if(isOk()) retval.calls.add(uc1); 
            }
            // BON.g:1180:3: ( '.' uc= unqualified_call )*
            loop135:
            do {
                int alt135=2;
                int LA135_0 = input.LA(1);

                if ( (LA135_0==70) ) {
                    alt135=1;
                }


                switch (alt135) {
            	case 1 :
            	    // BON.g:1180:4: '.' uc= unqualified_call
            	    {
            	    match(input,70,FOLLOW_70_in_call_chain7786); if (state.failed) return retval;
            	    pushFollow(FOLLOW_unqualified_call_in_call_chain7790);
            	    uc=unqualified_call();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) retval.calls.add(uc); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop135;
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
    // BON.g:1183:1: unqualified_call returns [UnqualifiedCall call] : i= IDENTIFIER (aa= actual_arguments | ) ;
    public final UnqualifiedCall unqualified_call() throws RecognitionException {
        UnqualifiedCall call = null;

        Token i=null;
        BONParser.actual_arguments_return aa = null;


         List<Expression> args = null; Token end = null;
        try {
            // BON.g:1185:1: (i= IDENTIFIER (aa= actual_arguments | ) )
            // BON.g:1186:3: i= IDENTIFIER (aa= actual_arguments | )
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_unqualified_call7831); if (state.failed) return call;
            if ( state.backtracking==0 ) {
               end = i; 
            }
            // BON.g:1188:3: (aa= actual_arguments | )
            int alt136=2;
            int LA136_0 = input.LA(1);

            if ( (LA136_0==42) ) {
                alt136=1;
            }
            else if ( (LA136_0==25||(LA136_0>=33 && LA136_0<=35)||LA136_0==43||LA136_0==63||LA136_0==65||LA136_0==70||(LA136_0>=76 && LA136_0<=77)||(LA136_0>=84 && LA136_0<=86)||(LA136_0>=102 && LA136_0<=107)||(LA136_0>=110 && LA136_0<=120)) ) {
                alt136=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return call;}
                NoViableAltException nvae =
                    new NoViableAltException("", 136, 0, input);

                throw nvae;
            }
            switch (alt136) {
                case 1 :
                    // BON.g:1188:6: aa= actual_arguments
                    {
                    pushFollow(FOLLOW_actual_arguments_in_unqualified_call7845);
                    aa=actual_arguments();

                    state._fsp--;
                    if (state.failed) return call;
                    if ( state.backtracking==0 ) {
                       if(isOk()) args = (aa!=null?aa.args:null); end = (aa!=null?((Token)aa.stop):null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1190:6: 
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
    // BON.g:1195:1: actual_arguments returns [List<Expression> args] : '(' (el= expression_list | ) ')' ;
    public final BONParser.actual_arguments_return actual_arguments() throws RecognitionException {
        BONParser.actual_arguments_return retval = new BONParser.actual_arguments_return();
        retval.start = input.LT(1);

        List<Expression> el = null;


        try {
            // BON.g:1196:1: ( '(' (el= expression_list | ) ')' )
            // BON.g:1197:3: '(' (el= expression_list | ) ')'
            {
            match(input,42,FOLLOW_42_in_actual_arguments7884); if (state.failed) return retval;
            // BON.g:1198:3: (el= expression_list | )
            int alt137=2;
            int LA137_0 = input.LA(1);

            if ( ((LA137_0>=MANIFEST_STRING && LA137_0<=IDENTIFIER)||(LA137_0>=INTEGER && LA137_0<=REAL)||LA137_0==42||LA137_0==62||LA137_0==74||(LA137_0>=82 && LA137_0<=83)||(LA137_0>=88 && LA137_0<=91)||(LA137_0>=103 && LA137_0<=104)||(LA137_0>=108 && LA137_0<=110)) ) {
                alt137=1;
            }
            else if ( (LA137_0==43) ) {
                alt137=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 137, 0, input);

                throw nvae;
            }
            switch (alt137) {
                case 1 :
                    // BON.g:1198:6: el= expression_list
                    {
                    pushFollow(FOLLOW_expression_list_in_actual_arguments7894);
                    el=expression_list();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.args = el; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1200:6: 
                    {
                    if ( state.backtracking==0 ) {
                       retval.args = emptyList(); 
                    }

                    }
                    break;

            }

            match(input,43,FOLLOW_43_in_actual_arguments7917); if (state.failed) return retval;

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
    // BON.g:1205:1: expression_list returns [List<Expression> list] : e1= expression ( ',' e= expression )* ;
    public final List<Expression> expression_list() throws RecognitionException {
        List<Expression> list = null;

        BONParser.expression_return e1 = null;

        BONParser.expression_return e = null;


        try {
            // BON.g:1205:49: (e1= expression ( ',' e= expression )* )
            // BON.g:1206:3: e1= expression ( ',' e= expression )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_expression_in_expression_list7953);
            e1=expression();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               if(isOk()) list.add((e1!=null?e1.exp:null)); 
            }
            // BON.g:1209:3: ( ',' e= expression )*
            loop138:
            do {
                int alt138=2;
                int LA138_0 = input.LA(1);

                if ( (LA138_0==35) ) {
                    alt138=1;
                }


                switch (alt138) {
            	case 1 :
            	    // BON.g:1209:4: ',' e= expression
            	    {
            	    match(input,35,FOLLOW_35_in_expression_list7963); if (state.failed) return list;
            	    pushFollow(FOLLOW_expression_in_expression_list7967);
            	    e=expression();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) list.add((e!=null?e.exp:null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop138;
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
    // BON.g:1212:1: enumerated_set returns [List<EnumerationElement> list] : '{' el= enumeration_list '}' ;
    public final BONParser.enumerated_set_return enumerated_set() throws RecognitionException {
        BONParser.enumerated_set_return retval = new BONParser.enumerated_set_return();
        retval.start = input.LT(1);

        List<EnumerationElement> el = null;


        try {
            // BON.g:1220:56: ( '{' el= enumeration_list '}' )
            // BON.g:1221:3: '{' el= enumeration_list '}'
            {
            match(input,62,FOLLOW_62_in_enumerated_set8013); if (state.failed) return retval;
            pushFollow(FOLLOW_enumeration_list_in_enumerated_set8017);
            el=enumeration_list();

            state._fsp--;
            if (state.failed) return retval;
            match(input,63,FOLLOW_63_in_enumerated_set8019); if (state.failed) return retval;
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
    // BON.g:1225:1: enumeration_list returns [List<EnumerationElement> list] : el1= enumeration_element ( ',' el= enumeration_element )* ;
    public final List<EnumerationElement> enumeration_list() throws RecognitionException {
        List<EnumerationElement> list = null;

        EnumerationElement el1 = null;

        EnumerationElement el = null;


        try {
            // BON.g:1225:58: (el1= enumeration_element ( ',' el= enumeration_element )* )
            // BON.g:1226:3: el1= enumeration_element ( ',' el= enumeration_element )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_enumeration_element_in_enumeration_list8061);
            el1=enumeration_element();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               if(isOk()) list.add(el1); 
            }
            // BON.g:1229:3: ( ',' el= enumeration_element )*
            loop139:
            do {
                int alt139=2;
                int LA139_0 = input.LA(1);

                if ( (LA139_0==35) ) {
                    alt139=1;
                }


                switch (alt139) {
            	case 1 :
            	    // BON.g:1229:4: ',' el= enumeration_element
            	    {
            	    match(input,35,FOLLOW_35_in_enumeration_list8071); if (state.failed) return list;
            	    pushFollow(FOLLOW_enumeration_element_in_enumeration_list8075);
            	    el=enumeration_element();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) list.add(el); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop139;
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
    // BON.g:1232:1: enumeration_element returns [EnumerationElement el] : (e= expression | i= interval );
    public final EnumerationElement enumeration_element() throws RecognitionException {
        EnumerationElement el = null;

        BONParser.expression_return e = null;

        Interval i = null;


        try {
            // BON.g:1232:53: (e= expression | i= interval )
            int alt140=2;
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
                alt140=1;
                }
                break;
            case CHARACTER_CONSTANT:
                {
                int LA140_2 = input.LA(2);

                if ( (LA140_2==87) ) {
                    alt140=2;
                }
                else if ( ((LA140_2>=34 && LA140_2<=35)||LA140_2==63||LA140_2==65||LA140_2==70||LA140_2==77||LA140_2==86||(LA140_2>=102 && LA140_2<=107)||(LA140_2>=110 && LA140_2<=120)) ) {
                    alt140=1;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return el;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 140, 2, input);

                    throw nvae;
                }
                }
                break;
            case 103:
                {
                int LA140_3 = input.LA(2);

                if ( (LA140_3==INTEGER) ) {
                    int LA140_7 = input.LA(3);

                    if ( (LA140_7==87) ) {
                        alt140=2;
                    }
                    else if ( ((LA140_7>=34 && LA140_7<=35)||LA140_7==63||LA140_7==65||LA140_7==70||LA140_7==77||LA140_7==86||(LA140_7>=102 && LA140_7<=107)||(LA140_7>=110 && LA140_7<=120)) ) {
                        alt140=1;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return el;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 140, 7, input);

                        throw nvae;
                    }
                }
                else if ( ((LA140_3>=MANIFEST_STRING && LA140_3<=IDENTIFIER)||(LA140_3>=CHARACTER_CONSTANT && LA140_3<=REAL)||LA140_3==42||LA140_3==62||LA140_3==74||(LA140_3>=88 && LA140_3<=91)||(LA140_3>=103 && LA140_3<=104)||(LA140_3>=108 && LA140_3<=110)) ) {
                    alt140=1;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return el;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 140, 3, input);

                    throw nvae;
                }
                }
                break;
            case 104:
                {
                int LA140_4 = input.LA(2);

                if ( (LA140_4==INTEGER) ) {
                    int LA140_7 = input.LA(3);

                    if ( (LA140_7==87) ) {
                        alt140=2;
                    }
                    else if ( ((LA140_7>=34 && LA140_7<=35)||LA140_7==63||LA140_7==65||LA140_7==70||LA140_7==77||LA140_7==86||(LA140_7>=102 && LA140_7<=107)||(LA140_7>=110 && LA140_7<=120)) ) {
                        alt140=1;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return el;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 140, 7, input);

                        throw nvae;
                    }
                }
                else if ( ((LA140_4>=MANIFEST_STRING && LA140_4<=IDENTIFIER)||(LA140_4>=CHARACTER_CONSTANT && LA140_4<=REAL)||LA140_4==42||LA140_4==62||LA140_4==74||(LA140_4>=88 && LA140_4<=91)||(LA140_4>=103 && LA140_4<=104)||(LA140_4>=108 && LA140_4<=110)) ) {
                    alt140=1;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return el;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 140, 4, input);

                    throw nvae;
                }
                }
                break;
            case INTEGER:
                {
                int LA140_5 = input.LA(2);

                if ( (LA140_5==87) ) {
                    alt140=2;
                }
                else if ( ((LA140_5>=34 && LA140_5<=35)||LA140_5==63||LA140_5==65||LA140_5==70||LA140_5==77||LA140_5==86||(LA140_5>=102 && LA140_5<=107)||(LA140_5>=110 && LA140_5<=120)) ) {
                    alt140=1;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return el;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 140, 5, input);

                    throw nvae;
                }
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return el;}
                NoViableAltException nvae =
                    new NoViableAltException("", 140, 0, input);

                throw nvae;
            }

            switch (alt140) {
                case 1 :
                    // BON.g:1233:4: e= expression
                    {
                    pushFollow(FOLLOW_expression_in_enumeration_element8107);
                    e=expression();

                    state._fsp--;
                    if (state.failed) return el;
                    if ( state.backtracking==0 ) {
                       if(isOk()) el = (e!=null?e.exp:null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1235:4: i= interval
                    {
                    pushFollow(FOLLOW_interval_in_enumeration_element8121);
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
    // BON.g:1239:1: interval returns [Interval interval] : (ii= integer_interval | ci= character_interval );
    public final Interval interval() throws RecognitionException {
        Interval interval = null;

        IntegerInterval ii = null;

        CharacterInterval ci = null;


        try {
            // BON.g:1239:39: (ii= integer_interval | ci= character_interval )
            int alt141=2;
            int LA141_0 = input.LA(1);

            if ( (LA141_0==INTEGER||(LA141_0>=103 && LA141_0<=104)) ) {
                alt141=1;
            }
            else if ( (LA141_0==CHARACTER_CONSTANT) ) {
                alt141=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return interval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 141, 0, input);

                throw nvae;
            }
            switch (alt141) {
                case 1 :
                    // BON.g:1240:4: ii= integer_interval
                    {
                    pushFollow(FOLLOW_integer_interval_in_interval8168);
                    ii=integer_interval();

                    state._fsp--;
                    if (state.failed) return interval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) interval = ii; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1242:4: ci= character_interval
                    {
                    pushFollow(FOLLOW_character_interval_in_interval8180);
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
    // BON.g:1246:1: integer_interval returns [IntegerInterval interval] : i1= integer_constant '..' i2= integer_constant ;
    public final IntegerInterval integer_interval() throws RecognitionException {
        IntegerInterval interval = null;

        BONParser.integer_constant_return i1 = null;

        BONParser.integer_constant_return i2 = null;


        try {
            // BON.g:1246:53: (i1= integer_constant '..' i2= integer_constant )
            // BON.g:1247:3: i1= integer_constant '..' i2= integer_constant
            {
            pushFollow(FOLLOW_integer_constant_in_integer_interval8213);
            i1=integer_constant();

            state._fsp--;
            if (state.failed) return interval;
            match(input,87,FOLLOW_87_in_integer_interval8215); if (state.failed) return interval;
            pushFollow(FOLLOW_integer_constant_in_integer_interval8219);
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
    // BON.g:1251:1: character_interval returns [CharacterInterval interval] : c1= character_constant '..' c2= character_constant ;
    public final CharacterInterval character_interval() throws RecognitionException {
        CharacterInterval interval = null;

        BONParser.character_constant_return c1 = null;

        BONParser.character_constant_return c2 = null;


        try {
            // BON.g:1251:57: (c1= character_constant '..' c2= character_constant )
            // BON.g:1252:3: c1= character_constant '..' c2= character_constant
            {
            pushFollow(FOLLOW_character_constant_in_character_interval8261);
            c1=character_constant();

            state._fsp--;
            if (state.failed) return interval;
            match(input,87,FOLLOW_87_in_character_interval8263); if (state.failed) return interval;
            pushFollow(FOLLOW_character_constant_in_character_interval8267);
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
    // BON.g:1256:1: constant returns [Constant constant] : (mc= manifest_constant | c= 'Current' | v= 'Void' | v= 'Result' );
    public final BONParser.constant_return constant() throws RecognitionException {
        BONParser.constant_return retval = new BONParser.constant_return();
        retval.start = input.LT(1);

        Token c=null;
        Token v=null;
        ManifestConstant mc = null;


        try {
            // BON.g:1258:38: (mc= manifest_constant | c= 'Current' | v= 'Void' | v= 'Result' )
            int alt142=4;
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
                alt142=1;
                }
                break;
            case 88:
                {
                alt142=2;
                }
                break;
            case 74:
                {
                alt142=3;
                }
                break;
            case 89:
                {
                alt142=4;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 142, 0, input);

                throw nvae;
            }

            switch (alt142) {
                case 1 :
                    // BON.g:1259:4: mc= manifest_constant
                    {
                    pushFollow(FOLLOW_manifest_constant_in_constant8293);
                    mc=manifest_constant();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.constant = mc; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1261:4: c= 'Current'
                    {
                    c=(Token)match(input,88,FOLLOW_88_in_constant8306); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.constant = KeywordConstant.mk(KeywordConstant.Constant.CURRENT, getSLoc(c)); 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:1263:4: v= 'Void'
                    {
                    v=(Token)match(input,74,FOLLOW_74_in_constant8319); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.constant = KeywordConstant.mk(KeywordConstant.Constant.VOID, getSLoc(v)); 
                    }

                    }
                    break;
                case 4 :
                    // BON.g:1265:4: v= 'Result'
                    {
                    v=(Token)match(input,89,FOLLOW_89_in_constant8343); if (state.failed) return retval;
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
    // BON.g:1269:1: manifest_constant returns [ManifestConstant constant] : (bc= boolean_constant | cc= character_constant | ic= integer_constant | rc= real_constant | ms= MANIFEST_STRING | es= enumerated_set );
    public final ManifestConstant manifest_constant() throws RecognitionException {
        ManifestConstant constant = null;

        Token ms=null;
        BONParser.boolean_constant_return bc = null;

        BONParser.character_constant_return cc = null;

        BONParser.integer_constant_return ic = null;

        BONParser.real_constant_return rc = null;

        BONParser.enumerated_set_return es = null;


        try {
            // BON.g:1269:55: (bc= boolean_constant | cc= character_constant | ic= integer_constant | rc= real_constant | ms= MANIFEST_STRING | es= enumerated_set )
            int alt143=6;
            switch ( input.LA(1) ) {
            case 90:
            case 91:
                {
                alt143=1;
                }
                break;
            case CHARACTER_CONSTANT:
                {
                alt143=2;
                }
                break;
            case 103:
                {
                int LA143_3 = input.LA(2);

                if ( (LA143_3==REAL) ) {
                    alt143=4;
                }
                else if ( (LA143_3==INTEGER) ) {
                    alt143=3;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return constant;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 143, 3, input);

                    throw nvae;
                }
                }
                break;
            case 104:
                {
                int LA143_4 = input.LA(2);

                if ( (LA143_4==REAL) ) {
                    alt143=4;
                }
                else if ( (LA143_4==INTEGER) ) {
                    alt143=3;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return constant;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 143, 4, input);

                    throw nvae;
                }
                }
                break;
            case INTEGER:
                {
                alt143=3;
                }
                break;
            case REAL:
                {
                alt143=4;
                }
                break;
            case MANIFEST_STRING:
                {
                alt143=5;
                }
                break;
            case 62:
                {
                alt143=6;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return constant;}
                NoViableAltException nvae =
                    new NoViableAltException("", 143, 0, input);

                throw nvae;
            }

            switch (alt143) {
                case 1 :
                    // BON.g:1270:4: bc= boolean_constant
                    {
                    pushFollow(FOLLOW_boolean_constant_in_manifest_constant8366);
                    bc=boolean_constant();

                    state._fsp--;
                    if (state.failed) return constant;
                    if ( state.backtracking==0 ) {
                       constant = BooleanConstant.mk((bc!=null?bc.value:null),getSLoc((bc!=null?((Token)bc.start):null),(bc!=null?((Token)bc.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1272:4: cc= character_constant
                    {
                    pushFollow(FOLLOW_character_constant_in_manifest_constant8379);
                    cc=character_constant();

                    state._fsp--;
                    if (state.failed) return constant;
                    if ( state.backtracking==0 ) {
                       constant = CharacterConstant.mk((cc!=null?cc.value:null),getSLoc((cc!=null?((Token)cc.start):null),(cc!=null?((Token)cc.stop):null))); 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:1274:4: ic= integer_constant
                    {
                    pushFollow(FOLLOW_integer_constant_in_manifest_constant8392);
                    ic=integer_constant();

                    state._fsp--;
                    if (state.failed) return constant;
                    if ( state.backtracking==0 ) {
                       constant = IntegerConstant.mk((ic!=null?ic.value:null),getSLoc((ic!=null?((Token)ic.start):null),(ic!=null?((Token)ic.stop):null))); 
                    }

                    }
                    break;
                case 4 :
                    // BON.g:1276:4: rc= real_constant
                    {
                    pushFollow(FOLLOW_real_constant_in_manifest_constant8405);
                    rc=real_constant();

                    state._fsp--;
                    if (state.failed) return constant;
                    if ( state.backtracking==0 ) {
                       constant = RealConstant.mk((rc!=null?rc.value:null),getSLoc((rc!=null?((Token)rc.start):null),(rc!=null?((Token)rc.stop):null))); 
                    }

                    }
                    break;
                case 5 :
                    // BON.g:1278:4: ms= MANIFEST_STRING
                    {
                    ms=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_manifest_constant8418); if (state.failed) return constant;
                    if ( state.backtracking==0 ) {
                       constant = StringConstant.mk((ms!=null?ms.getText():null),getSLoc(ms)); 
                    }

                    }
                    break;
                case 6 :
                    // BON.g:1280:4: es= enumerated_set
                    {
                    pushFollow(FOLLOW_enumerated_set_in_manifest_constant8431);
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
    // BON.g:1284:1: sign returns [BinaryExp.Op op] : add_sub_op ;
    public final BinaryExp.Op sign() throws RecognitionException {
        BinaryExp.Op op = null;

        BinaryExp.Op add_sub_op95 = null;


        try {
            // BON.g:1284:32: ( add_sub_op )
            // BON.g:1285:3: add_sub_op
            {
            pushFollow(FOLLOW_add_sub_op_in_sign8470);
            add_sub_op95=add_sub_op();

            state._fsp--;
            if (state.failed) return op;
            if ( state.backtracking==0 ) {
               if(isOk()) op = add_sub_op95; 
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
    // BON.g:1289:1: boolean_constant returns [Boolean value] : ( 'true' | 'false' );
    public final BONParser.boolean_constant_return boolean_constant() throws RecognitionException {
        BONParser.boolean_constant_return retval = new BONParser.boolean_constant_return();
        retval.start = input.LT(1);

        try {
            // BON.g:1289:42: ( 'true' | 'false' )
            int alt144=2;
            int LA144_0 = input.LA(1);

            if ( (LA144_0==90) ) {
                alt144=1;
            }
            else if ( (LA144_0==91) ) {
                alt144=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 144, 0, input);

                throw nvae;
            }
            switch (alt144) {
                case 1 :
                    // BON.g:1290:4: 'true'
                    {
                    match(input,90,FOLLOW_90_in_boolean_constant8496); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.value = true; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1292:4: 'false'
                    {
                    match(input,91,FOLLOW_91_in_boolean_constant8507); if (state.failed) return retval;
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
    // BON.g:1298:1: character_constant returns [Character value] : cc= CHARACTER_CONSTANT ;
    public final BONParser.character_constant_return character_constant() throws RecognitionException {
        BONParser.character_constant_return retval = new BONParser.character_constant_return();
        retval.start = input.LT(1);

        Token cc=null;

        try {
            // BON.g:1298:46: (cc= CHARACTER_CONSTANT )
            // BON.g:1299:2: cc= CHARACTER_CONSTANT
            {
            cc=(Token)match(input,CHARACTER_CONSTANT,FOLLOW_CHARACTER_CONSTANT_in_character_constant8531); if (state.failed) return retval;
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
    // BON.g:1307:1: integer_constant returns [Integer value] : ( sign )? i= INTEGER ;
    public final BONParser.integer_constant_return integer_constant() throws RecognitionException {
        BONParser.integer_constant_return retval = new BONParser.integer_constant_return();
        retval.start = input.LT(1);

        Token i=null;
        BinaryExp.Op sign96 = null;


         boolean negative = false; 
        try {
            // BON.g:1309:1: ( ( sign )? i= INTEGER )
            // BON.g:1310:3: ( sign )? i= INTEGER
            {
            // BON.g:1310:3: ( sign )?
            int alt145=2;
            int LA145_0 = input.LA(1);

            if ( ((LA145_0>=103 && LA145_0<=104)) ) {
                alt145=1;
            }
            switch (alt145) {
                case 1 :
                    // BON.g:1310:4: sign
                    {
                    pushFollow(FOLLOW_sign_in_integer_constant8597);
                    sign96=sign();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if (sign96 == BinaryExp.Op.SUB) negative = true; 
                    }

                    }
                    break;

            }

            i=(Token)match(input,INTEGER,FOLLOW_INTEGER_in_integer_constant8608); if (state.failed) return retval;
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
    // BON.g:1315:1: real_constant returns [Double value] : ( sign )? r= REAL ;
    public final BONParser.real_constant_return real_constant() throws RecognitionException {
        BONParser.real_constant_return retval = new BONParser.real_constant_return();
        retval.start = input.LT(1);

        Token r=null;
        BinaryExp.Op sign97 = null;


         boolean negative = false; 
        try {
            // BON.g:1317:1: ( ( sign )? r= REAL )
            // BON.g:1318:3: ( sign )? r= REAL
            {
            // BON.g:1318:3: ( sign )?
            int alt146=2;
            int LA146_0 = input.LA(1);

            if ( ((LA146_0>=103 && LA146_0<=104)) ) {
                alt146=1;
            }
            switch (alt146) {
                case 1 :
                    // BON.g:1318:4: sign
                    {
                    pushFollow(FOLLOW_sign_in_real_constant8653);
                    sign97=sign();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if (sign97 == BinaryExp.Op.SUB) negative = true; 
                    }

                    }
                    break;

            }

            r=(Token)match(input,REAL,FOLLOW_REAL_in_real_constant8665); if (state.failed) return retval;
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
    // BON.g:1323:1: dynamic_diagram returns [DynamicDiagram dd] : s= 'dynamic_diagram' (eid= extended_id )? (c= COMMENT )? 'component' (db= dynamic_block | ) e= 'end' ;
    public final DynamicDiagram dynamic_diagram() throws RecognitionException {
        DynamicDiagram dd = null;

        Token s=null;
        Token c=null;
        Token e=null;
        BONParser.extended_id_return eid = null;

        List<DynamicComponent> db = null;


         String id = null; String comment = null; List<DynamicComponent> components = null; 
        try {
            // BON.g:1329:1: (s= 'dynamic_diagram' (eid= extended_id )? (c= COMMENT )? 'component' (db= dynamic_block | ) e= 'end' )
            // BON.g:1330:3: s= 'dynamic_diagram' (eid= extended_id )? (c= COMMENT )? 'component' (db= dynamic_block | ) e= 'end'
            {
            s=(Token)match(input,92,FOLLOW_92_in_dynamic_diagram8696); if (state.failed) return dd;
            // BON.g:1331:3: (eid= extended_id )?
            int alt147=2;
            int LA147_0 = input.LA(1);

            if ( (LA147_0==IDENTIFIER||LA147_0==INTEGER) ) {
                alt147=1;
            }
            switch (alt147) {
                case 1 :
                    // BON.g:1331:4: eid= extended_id
                    {
                    pushFollow(FOLLOW_extended_id_in_dynamic_diagram8704);
                    eid=extended_id();

                    state._fsp--;
                    if (state.failed) return dd;
                    if ( state.backtracking==0 ) {
                       if(isOk()) id = (eid!=null?eid.eid:null); 
                    }

                    }
                    break;

            }

            // BON.g:1332:3: (c= COMMENT )?
            int alt148=2;
            int LA148_0 = input.LA(1);

            if ( (LA148_0==COMMENT) ) {
                alt148=1;
            }
            switch (alt148) {
                case 1 :
                    // BON.g:1332:4: c= COMMENT
                    {
                    c=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_dynamic_diagram8717); if (state.failed) return dd;
                    if ( state.backtracking==0 ) {
                       if(isOk()) comment = (c!=null?c.getText():null); 
                    }

                    }
                    break;

            }

            match(input,55,FOLLOW_55_in_dynamic_diagram8726); if (state.failed) return dd;
            // BON.g:1334:3: (db= dynamic_block | )
            int alt149=2;
            int LA149_0 = input.LA(1);

            if ( (LA149_0==IDENTIFIER||LA149_0==INTEGER||LA149_0==50||(LA149_0>=94 && LA149_0<=97)) ) {
                alt149=1;
            }
            else if ( (LA149_0==25) ) {
                alt149=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return dd;}
                NoViableAltException nvae =
                    new NoViableAltException("", 149, 0, input);

                throw nvae;
            }
            switch (alt149) {
                case 1 :
                    // BON.g:1334:5: db= dynamic_block
                    {
                    pushFollow(FOLLOW_dynamic_block_in_dynamic_diagram8735);
                    db=dynamic_block();

                    state._fsp--;
                    if (state.failed) return dd;
                    if ( state.backtracking==0 ) {
                       if(isOk()) components = db; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1336:6: 
                    {
                    if ( state.backtracking==0 ) {
                       components = emptyList(); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_dynamic_diagram8759); if (state.failed) return dd;
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
    // BON.g:1342:1: dynamic_block returns [List<DynamicComponent> components] : (dc= dynamic_component )+ ;
    public final List<DynamicComponent> dynamic_block() throws RecognitionException {
        List<DynamicComponent> components = null;

        DynamicComponent dc = null;


        try {
            // BON.g:1342:59: ( (dc= dynamic_component )+ )
            // BON.g:1343:3: (dc= dynamic_component )+
            {
            if ( state.backtracking==0 ) {
               components = createList(); 
            }
            // BON.g:1344:3: (dc= dynamic_component )+
            int cnt150=0;
            loop150:
            do {
                int alt150=2;
                int LA150_0 = input.LA(1);

                if ( (LA150_0==IDENTIFIER||LA150_0==INTEGER||LA150_0==50||(LA150_0>=94 && LA150_0<=97)) ) {
                    alt150=1;
                }


                switch (alt150) {
            	case 1 :
            	    // BON.g:1344:4: dc= dynamic_component
            	    {
            	    pushFollow(FOLLOW_dynamic_component_in_dynamic_block8802);
            	    dc=dynamic_component();

            	    state._fsp--;
            	    if (state.failed) return components;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) components.add(dc); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt150 >= 1 ) break loop150;
            	    if (state.backtracking>0) {state.failed=true; return components;}
                        EarlyExitException eee =
                            new EarlyExitException(150, input);
                        throw eee;
                }
                cnt150++;
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
    // BON.g:1347:1: dynamic_component returns [DynamicComponent component] : ( scenario_description | object_group | object_stack | object | message_relation );
    public final DynamicComponent dynamic_component() throws RecognitionException {
        DynamicComponent component = null;

        try {
            // BON.g:1347:56: ( scenario_description | object_group | object_stack | object | message_relation )
            int alt151=5;
            switch ( input.LA(1) ) {
            case 50:
                {
                alt151=1;
                }
                break;
            case 94:
            case 95:
                {
                alt151=2;
                }
                break;
            case 96:
                {
                alt151=3;
                }
                break;
            case 97:
                {
                alt151=4;
                }
                break;
            case IDENTIFIER:
            case INTEGER:
                {
                alt151=5;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return component;}
                NoViableAltException nvae =
                    new NoViableAltException("", 151, 0, input);

                throw nvae;
            }

            switch (alt151) {
                case 1 :
                    // BON.g:1348:4: scenario_description
                    {
                    pushFollow(FOLLOW_scenario_description_in_dynamic_component8839);
                    scenario_description();

                    state._fsp--;
                    if (state.failed) return component;

                    }
                    break;
                case 2 :
                    // BON.g:1349:4: object_group
                    {
                    pushFollow(FOLLOW_object_group_in_dynamic_component8844);
                    object_group();

                    state._fsp--;
                    if (state.failed) return component;

                    }
                    break;
                case 3 :
                    // BON.g:1350:4: object_stack
                    {
                    pushFollow(FOLLOW_object_stack_in_dynamic_component8850);
                    object_stack();

                    state._fsp--;
                    if (state.failed) return component;

                    }
                    break;
                case 4 :
                    // BON.g:1351:4: object
                    {
                    pushFollow(FOLLOW_object_in_dynamic_component8855);
                    object();

                    state._fsp--;
                    if (state.failed) return component;

                    }
                    break;
                case 5 :
                    // BON.g:1352:4: message_relation
                    {
                    pushFollow(FOLLOW_message_relation_in_dynamic_component8860);
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
    // BON.g:1355:1: scenario_description returns [ScenarioDescription description] : s= 'scenario' scenario_name (c= COMMENT )? 'action' la= labelled_actions e= 'end' ;
    public final ScenarioDescription scenario_description() throws RecognitionException {
        ScenarioDescription description = null;

        Token s=null;
        Token c=null;
        Token e=null;
        List<LabelledAction> la = null;

        String scenario_name98 = null;


         String comment = null; 
        try {
            // BON.g:1359:1: (s= 'scenario' scenario_name (c= COMMENT )? 'action' la= labelled_actions e= 'end' )
            // BON.g:1360:3: s= 'scenario' scenario_name (c= COMMENT )? 'action' la= labelled_actions e= 'end'
            {
            s=(Token)match(input,50,FOLLOW_50_in_scenario_description8888); if (state.failed) return description;
            pushFollow(FOLLOW_scenario_name_in_scenario_description8890);
            scenario_name98=scenario_name();

            state._fsp--;
            if (state.failed) return description;
            // BON.g:1361:3: (c= COMMENT )?
            int alt152=2;
            int LA152_0 = input.LA(1);

            if ( (LA152_0==COMMENT) ) {
                alt152=1;
            }
            switch (alt152) {
                case 1 :
                    // BON.g:1361:4: c= COMMENT
                    {
                    c=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_scenario_description8898); if (state.failed) return description;
                    if ( state.backtracking==0 ) {
                       if(isOk()) comment = (c!=null?c.getText():null); 
                    }

                    }
                    break;

            }

            match(input,93,FOLLOW_93_in_scenario_description8907); if (state.failed) return description;
            pushFollow(FOLLOW_labelled_actions_in_scenario_description8914);
            la=labelled_actions();

            state._fsp--;
            if (state.failed) return description;
            e=(Token)match(input,25,FOLLOW_25_in_scenario_description8921); if (state.failed) return description;
            if ( state.backtracking==0 ) {
               if(isOk()) description = ScenarioDescription.mk(scenario_name98, la, comment, getSLoc(s,c)); 
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
    // BON.g:1368:1: labelled_actions returns [List<LabelledAction> actions] : (la= labelled_action )+ ;
    public final List<LabelledAction> labelled_actions() throws RecognitionException {
        List<LabelledAction> actions = null;

        LabelledAction la = null;


        try {
            // BON.g:1368:57: ( (la= labelled_action )+ )
            // BON.g:1369:3: (la= labelled_action )+
            {
            if ( state.backtracking==0 ) {
               actions = createList(); 
            }
            // BON.g:1370:3: (la= labelled_action )+
            int cnt153=0;
            loop153:
            do {
                int alt153=2;
                int LA153_0 = input.LA(1);

                if ( (LA153_0==MANIFEST_STRING) ) {
                    alt153=1;
                }


                switch (alt153) {
            	case 1 :
            	    // BON.g:1370:4: la= labelled_action
            	    {
            	    pushFollow(FOLLOW_labelled_action_in_labelled_actions8969);
            	    la=labelled_action();

            	    state._fsp--;
            	    if (state.failed) return actions;
            	    if ( state.backtracking==0 ) {
            	       if(isOk()) actions.add(la); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt153 >= 1 ) break loop153;
            	    if (state.backtracking>0) {state.failed=true; return actions;}
                        EarlyExitException eee =
                            new EarlyExitException(153, input);
                        throw eee;
                }
                cnt153++;
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
    // BON.g:1373:1: labelled_action returns [LabelledAction action] : al= action_label ad= action_description ;
    public final LabelledAction labelled_action() throws RecognitionException {
        LabelledAction action = null;

        BONParser.action_label_return al = null;

        BONParser.action_description_return ad = null;


        try {
            // BON.g:1373:49: (al= action_label ad= action_description )
            // BON.g:1374:3: al= action_label ad= action_description
            {
            pushFollow(FOLLOW_action_label_in_labelled_action9010);
            al=action_label();

            state._fsp--;
            if (state.failed) return action;
            pushFollow(FOLLOW_action_description_in_labelled_action9014);
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
    // BON.g:1378:1: action_label returns [String label] : m= MANIFEST_STRING ;
    public final BONParser.action_label_return action_label() throws RecognitionException {
        BONParser.action_label_return retval = new BONParser.action_label_return();
        retval.start = input.LT(1);

        Token m=null;

        try {
            // BON.g:1378:37: (m= MANIFEST_STRING )
            // BON.g:1379:3: m= MANIFEST_STRING
            {
            m=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_action_label9053); if (state.failed) return retval;
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
    // BON.g:1383:1: action_description returns [String description] : m= manifest_textblock ;
    public final BONParser.action_description_return action_description() throws RecognitionException {
        BONParser.action_description_return retval = new BONParser.action_description_return();
        retval.start = input.LT(1);

        BONParser.manifest_textblock_return m = null;


        try {
            // BON.g:1383:49: (m= manifest_textblock )
            // BON.g:1384:3: m= manifest_textblock
            {
            pushFollow(FOLLOW_manifest_textblock_in_action_description9088);
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
    // BON.g:1388:1: scenario_name returns [String name] : m= manifest_textblock ;
    public final String scenario_name() throws RecognitionException {
        String name = null;

        BONParser.manifest_textblock_return m = null;


        try {
            // BON.g:1388:37: (m= manifest_textblock )
            // BON.g:1389:3: m= manifest_textblock
            {
            pushFollow(FOLLOW_manifest_textblock_in_scenario_name9129);
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
    // BON.g:1393:1: object_group returns [ObjectGroup group] : (n= 'nameless' | ) s= 'object_group' group_name (c= COMMENT )? (gc= group_components | ) ;
    public final ObjectGroup object_group() throws RecognitionException {
        ObjectGroup group = null;

        Token n=null;
        Token s=null;
        Token c=null;
        List<DynamicComponent> gc = null;

        BONParser.group_name_return group_name99 = null;


         String comment = null; List<DynamicComponent> components = null; 
                ObjectGroup.Nameless nameless = ObjectGroup.Nameless.NOTNAMELESS; 
                Token start = null; Token end = null; 
        try {
            // BON.g:1399:1: ( (n= 'nameless' | ) s= 'object_group' group_name (c= COMMENT )? (gc= group_components | ) )
            // BON.g:1400:3: (n= 'nameless' | ) s= 'object_group' group_name (c= COMMENT )? (gc= group_components | )
            {
            // BON.g:1400:3: (n= 'nameless' | )
            int alt154=2;
            int LA154_0 = input.LA(1);

            if ( (LA154_0==94) ) {
                alt154=1;
            }
            else if ( (LA154_0==95) ) {
                alt154=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return group;}
                NoViableAltException nvae =
                    new NoViableAltException("", 154, 0, input);

                throw nvae;
            }
            switch (alt154) {
                case 1 :
                    // BON.g:1400:6: n= 'nameless'
                    {
                    n=(Token)match(input,94,FOLLOW_94_in_object_group9162); if (state.failed) return group;
                    if ( state.backtracking==0 ) {
                       nameless = ObjectGroup.Nameless.NAMELESS; start = n; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1402:6: 
                    {
                    if ( state.backtracking==0 ) {
                       nameless = ObjectGroup.Nameless.NOTNAMELESS; 
                    }

                    }
                    break;

            }

            s=(Token)match(input,95,FOLLOW_95_in_object_group9187); if (state.failed) return group;
            if ( state.backtracking==0 ) {
               if (start==null) start=s; 
            }
            pushFollow(FOLLOW_group_name_in_object_group9193);
            group_name99=group_name();

            state._fsp--;
            if (state.failed) return group;
            if ( state.backtracking==0 ) {
               end = (group_name99!=null?((Token)group_name99.stop):null); 
            }
            // BON.g:1407:3: (c= COMMENT )?
            int alt155=2;
            int LA155_0 = input.LA(1);

            if ( (LA155_0==COMMENT) ) {
                alt155=1;
            }
            switch (alt155) {
                case 1 :
                    // BON.g:1407:4: c= COMMENT
                    {
                    c=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_object_group9205); if (state.failed) return group;
                    if ( state.backtracking==0 ) {
                       comment = (c!=null?c.getText():null); end = c; 
                    }

                    }
                    break;

            }

            // BON.g:1408:3: (gc= group_components | )
            int alt156=2;
            int LA156_0 = input.LA(1);

            if ( (LA156_0==55) ) {
                alt156=1;
            }
            else if ( (LA156_0==IDENTIFIER||LA156_0==INTEGER||LA156_0==25||LA156_0==50||(LA156_0>=94 && LA156_0<=97)) ) {
                alt156=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return group;}
                NoViableAltException nvae =
                    new NoViableAltException("", 156, 0, input);

                throw nvae;
            }
            switch (alt156) {
                case 1 :
                    // BON.g:1408:6: gc= group_components
                    {
                    pushFollow(FOLLOW_group_components_in_object_group9220);
                    gc=group_components();

                    state._fsp--;
                    if (state.failed) return group;
                    if ( state.backtracking==0 ) {
                       if(isOk()) components = gc; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1410:6: 
                    {
                    if ( state.backtracking==0 ) {
                       components = emptyList(); 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               if(isOk()) group = ObjectGroup.mk(nameless, (group_name99!=null?input.toString(group_name99.start,group_name99.stop):null), components, comment, getSLoc(start,end)); 
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
    // BON.g:1415:1: group_components returns [List<DynamicComponent> components] : 'component' dynamic_block 'end' ;
    public final List<DynamicComponent> group_components() throws RecognitionException {
        List<DynamicComponent> components = null;

        List<DynamicComponent> dynamic_block100 = null;


        try {
            // BON.g:1415:62: ( 'component' dynamic_block 'end' )
            // BON.g:1416:3: 'component' dynamic_block 'end'
            {
            match(input,55,FOLLOW_55_in_group_components9271); if (state.failed) return components;
            pushFollow(FOLLOW_dynamic_block_in_group_components9273);
            dynamic_block100=dynamic_block();

            state._fsp--;
            if (state.failed) return components;
            match(input,25,FOLLOW_25_in_group_components9275); if (state.failed) return components;
            if ( state.backtracking==0 ) {
               if(isOk()) components = dynamic_block100; 
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
    // BON.g:1420:1: object_stack returns [ObjectStack stack] : s= 'object_stack' n= object_name (c= COMMENT )? ;
    public final ObjectStack object_stack() throws RecognitionException {
        ObjectStack stack = null;

        Token s=null;
        Token c=null;
        BONParser.object_name_return n = null;


         String comment = null; Token end = null; 
        try {
            // BON.g:1422:1: (s= 'object_stack' n= object_name (c= COMMENT )? )
            // BON.g:1423:3: s= 'object_stack' n= object_name (c= COMMENT )?
            {
            s=(Token)match(input,96,FOLLOW_96_in_object_stack9320); if (state.failed) return stack;
            pushFollow(FOLLOW_object_name_in_object_stack9327);
            n=object_name();

            state._fsp--;
            if (state.failed) return stack;
            if ( state.backtracking==0 ) {
               end = (n!=null?((Token)n.stop):null); 
            }
            // BON.g:1426:3: (c= COMMENT )?
            int alt157=2;
            int LA157_0 = input.LA(1);

            if ( (LA157_0==COMMENT) ) {
                alt157=1;
            }
            switch (alt157) {
                case 1 :
                    // BON.g:1426:4: c= COMMENT
                    {
                    c=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_object_stack9339); if (state.failed) return stack;
                    if ( state.backtracking==0 ) {
                       if(isOk()) comment = (c!=null?c.getText():null); end = c; 
                    }

                    }
                    break;

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
    // BON.g:1430:1: object returns [ObjectInstance object] : s= 'object' n= object_name (c= COMMENT )? ;
    public final ObjectInstance object() throws RecognitionException {
        ObjectInstance object = null;

        Token s=null;
        Token c=null;
        BONParser.object_name_return n = null;


         String comment = null; Token end = null; 
        try {
            // BON.g:1432:1: (s= 'object' n= object_name (c= COMMENT )? )
            // BON.g:1433:3: s= 'object' n= object_name (c= COMMENT )?
            {
            s=(Token)match(input,97,FOLLOW_97_in_object9387); if (state.failed) return object;
            pushFollow(FOLLOW_object_name_in_object9394);
            n=object_name();

            state._fsp--;
            if (state.failed) return object;
            if ( state.backtracking==0 ) {
               end = (n!=null?((Token)n.stop):null); 
            }
            // BON.g:1436:3: (c= COMMENT )?
            int alt158=2;
            int LA158_0 = input.LA(1);

            if ( (LA158_0==COMMENT) ) {
                alt158=1;
            }
            switch (alt158) {
                case 1 :
                    // BON.g:1436:4: c= COMMENT
                    {
                    c=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_object9406); if (state.failed) return object;
                    if ( state.backtracking==0 ) {
                       if(isOk()) comment = (c!=null?c.getText():null); end = c; 
                    }

                    }
                    break;

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
    // BON.g:1440:1: message_relation : caller 'calls' receiver ( message_label )? ;
    public final void message_relation() throws RecognitionException {
        try {
            // BON.g:1442:19: ( caller 'calls' receiver ( message_label )? )
            // BON.g:1442:22: caller 'calls' receiver ( message_label )?
            {
            pushFollow(FOLLOW_caller_in_message_relation9430);
            caller();

            state._fsp--;
            if (state.failed) return ;
            match(input,98,FOLLOW_98_in_message_relation9432); if (state.failed) return ;
            pushFollow(FOLLOW_receiver_in_message_relation9434);
            receiver();

            state._fsp--;
            if (state.failed) return ;
            // BON.g:1442:46: ( message_label )?
            int alt159=2;
            int LA159_0 = input.LA(1);

            if ( (LA159_0==MANIFEST_STRING) ) {
                alt159=1;
            }
            switch (alt159) {
                case 1 :
                    // BON.g:1442:47: message_label
                    {
                    pushFollow(FOLLOW_message_label_in_message_relation9437);
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
    // BON.g:1445:1: caller : dynamic_ref ;
    public final void caller() throws RecognitionException {
        try {
            // BON.g:1445:9: ( dynamic_ref )
            // BON.g:1445:12: dynamic_ref
            {
            pushFollow(FOLLOW_dynamic_ref_in_caller9469);
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
    // BON.g:1448:1: receiver : dynamic_ref ;
    public final void receiver() throws RecognitionException {
        try {
            // BON.g:1448:11: ( dynamic_ref )
            // BON.g:1448:14: dynamic_ref
            {
            pushFollow(FOLLOW_dynamic_ref_in_receiver9489);
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
    // BON.g:1455:1: dynamic_ref : extended_id ( '.' extended_id )* ;
    public final void dynamic_ref() throws RecognitionException {
        try {
            // BON.g:1455:14: ( extended_id ( '.' extended_id )* )
            // BON.g:1455:17: extended_id ( '.' extended_id )*
            {
            pushFollow(FOLLOW_extended_id_in_dynamic_ref9515);
            extended_id();

            state._fsp--;
            if (state.failed) return ;
            // BON.g:1455:29: ( '.' extended_id )*
            loop160:
            do {
                int alt160=2;
                int LA160_0 = input.LA(1);

                if ( (LA160_0==70) ) {
                    alt160=1;
                }


                switch (alt160) {
            	case 1 :
            	    // BON.g:1455:30: '.' extended_id
            	    {
            	    match(input,70,FOLLOW_70_in_dynamic_ref9518); if (state.failed) return ;
            	    pushFollow(FOLLOW_extended_id_in_dynamic_ref9520);
            	    extended_id();

            	    state._fsp--;
            	    if (state.failed) return ;

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
        return ;
    }
    // $ANTLR end "dynamic_ref"


    // $ANTLR start "dynamic_component_name"
    // BON.g:1464:1: dynamic_component_name : ( ( IDENTIFIER ( '.' extended_id )? ) | INTEGER );
    public final void dynamic_component_name() throws RecognitionException {
        try {
            // BON.g:1464:25: ( ( IDENTIFIER ( '.' extended_id )? ) | INTEGER )
            int alt162=2;
            int LA162_0 = input.LA(1);

            if ( (LA162_0==IDENTIFIER) ) {
                alt162=1;
            }
            else if ( (LA162_0==INTEGER) ) {
                alt162=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 162, 0, input);

                throw nvae;
            }
            switch (alt162) {
                case 1 :
                    // BON.g:1465:4: ( IDENTIFIER ( '.' extended_id )? )
                    {
                    // BON.g:1465:4: ( IDENTIFIER ( '.' extended_id )? )
                    // BON.g:1465:5: IDENTIFIER ( '.' extended_id )?
                    {
                    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_dynamic_component_name9551); if (state.failed) return ;
                    // BON.g:1465:16: ( '.' extended_id )?
                    int alt161=2;
                    int LA161_0 = input.LA(1);

                    if ( (LA161_0==70) ) {
                        alt161=1;
                    }
                    switch (alt161) {
                        case 1 :
                            // BON.g:1465:17: '.' extended_id
                            {
                            match(input,70,FOLLOW_70_in_dynamic_component_name9554); if (state.failed) return ;
                            pushFollow(FOLLOW_extended_id_in_dynamic_component_name9556);
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
                    // BON.g:1466:4: INTEGER
                    {
                    match(input,INTEGER,FOLLOW_INTEGER_in_dynamic_component_name9565); if (state.failed) return ;

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
    // BON.g:1469:1: object_name returns [ObjectName name] : n= class_name ( '.' e= extended_id )? ;
    public final BONParser.object_name_return object_name() throws RecognitionException {
        BONParser.object_name_return retval = new BONParser.object_name_return();
        retval.start = input.LT(1);

        BONParser.class_name_return n = null;

        BONParser.extended_id_return e = null;


         String id = null; Token end = null; 
        try {
            // BON.g:1471:1: (n= class_name ( '.' e= extended_id )? )
            // BON.g:1472:3: n= class_name ( '.' e= extended_id )?
            {
            pushFollow(FOLLOW_class_name_in_object_name9588);
            n=class_name();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               end = (n!=null?((Token)n.stop):null); 
            }
            // BON.g:1474:3: ( '.' e= extended_id )?
            int alt163=2;
            int LA163_0 = input.LA(1);

            if ( (LA163_0==70) ) {
                alt163=1;
            }
            switch (alt163) {
                case 1 :
                    // BON.g:1474:4: '.' e= extended_id
                    {
                    match(input,70,FOLLOW_70_in_object_name9598); if (state.failed) return retval;
                    pushFollow(FOLLOW_extended_id_in_object_name9602);
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
    // BON.g:1478:1: group_name returns [String name] : e= extended_id ;
    public final BONParser.group_name_return group_name() throws RecognitionException {
        BONParser.group_name_return retval = new BONParser.group_name_return();
        retval.start = input.LT(1);

        BONParser.extended_id_return e = null;


        try {
            // BON.g:1478:34: (e= extended_id )
            // BON.g:1479:3: e= extended_id
            {
            pushFollow(FOLLOW_extended_id_in_group_name9642);
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
    // BON.g:1483:1: message_label returns [String label] : m= MANIFEST_STRING ;
    public final String message_label() throws RecognitionException {
        String label = null;

        Token m=null;

        try {
            // BON.g:1483:38: (m= MANIFEST_STRING )
            // BON.g:1484:3: m= MANIFEST_STRING
            {
            m=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_message_label9675); if (state.failed) return label;
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
    // BON.g:1488:1: notational_tuning : ( change_string_marks | change_concatenator | change_prefix );
    public final void notational_tuning() throws RecognitionException {
        try {
            // BON.g:1492:19: ( change_string_marks | change_concatenator | change_prefix )
            int alt164=3;
            switch ( input.LA(1) ) {
            case 99:
                {
                alt164=1;
                }
                break;
            case 100:
                {
                alt164=2;
                }
                break;
            case 101:
                {
                alt164=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 164, 0, input);

                throw nvae;
            }

            switch (alt164) {
                case 1 :
                    // BON.g:1493:4: change_string_marks
                    {
                    pushFollow(FOLLOW_change_string_marks_in_notational_tuning9699);
                    change_string_marks();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 2 :
                    // BON.g:1494:4: change_concatenator
                    {
                    pushFollow(FOLLOW_change_concatenator_in_notational_tuning9705);
                    change_concatenator();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 3 :
                    // BON.g:1495:4: change_prefix
                    {
                    pushFollow(FOLLOW_change_prefix_in_notational_tuning9710);
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
    // BON.g:1498:1: change_string_marks : 'string_marks' MANIFEST_STRING MANIFEST_STRING ;
    public final void change_string_marks() throws RecognitionException {
        try {
            // BON.g:1498:22: ( 'string_marks' MANIFEST_STRING MANIFEST_STRING )
            // BON.g:1499:3: 'string_marks' MANIFEST_STRING MANIFEST_STRING
            {
            match(input,99,FOLLOW_99_in_change_string_marks9725); if (state.failed) return ;
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_string_marks9727); if (state.failed) return ;
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_string_marks9729); if (state.failed) return ;

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
    // BON.g:1502:1: change_concatenator : 'concatenator' MANIFEST_STRING ;
    public final void change_concatenator() throws RecognitionException {
        try {
            // BON.g:1502:22: ( 'concatenator' MANIFEST_STRING )
            // BON.g:1503:3: 'concatenator' MANIFEST_STRING
            {
            match(input,100,FOLLOW_100_in_change_concatenator9763); if (state.failed) return ;
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_concatenator9765); if (state.failed) return ;

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
    // BON.g:1506:1: change_prefix : 'keyword_prefix' MANIFEST_STRING ;
    public final void change_prefix() throws RecognitionException {
        try {
            // BON.g:1506:16: ( 'keyword_prefix' MANIFEST_STRING )
            // BON.g:1507:3: 'keyword_prefix' MANIFEST_STRING
            {
            match(input,101,FOLLOW_101_in_change_prefix9799); if (state.failed) return ;
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_prefix9801); if (state.failed) return ;

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
    // BON.g:1510:1: expression returns [Expression exp] : (e= equivalence_expression | q= quantification );
    public final BONParser.expression_return expression() throws RecognitionException {
        BONParser.expression_return retval = new BONParser.expression_return();
        retval.start = input.LT(1);

        Expression e = null;

        Quantification q = null;


        try {
            // BON.g:1514:37: (e= equivalence_expression | q= quantification )
            int alt165=2;
            int LA165_0 = input.LA(1);

            if ( ((LA165_0>=MANIFEST_STRING && LA165_0<=IDENTIFIER)||(LA165_0>=INTEGER && LA165_0<=REAL)||LA165_0==42||LA165_0==62||LA165_0==74||(LA165_0>=88 && LA165_0<=91)||(LA165_0>=103 && LA165_0<=104)||(LA165_0>=108 && LA165_0<=110)) ) {
                alt165=1;
            }
            else if ( ((LA165_0>=82 && LA165_0<=83)) ) {
                alt165=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 165, 0, input);

                throw nvae;
            }
            switch (alt165) {
                case 1 :
                    // BON.g:1515:4: e= equivalence_expression
                    {
                    pushFollow(FOLLOW_equivalence_expression_in_expression9827);
                    e=equivalence_expression();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.exp = e; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1517:4: q= quantification
                    {
                    pushFollow(FOLLOW_quantification_in_expression9841);
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
    // BON.g:1521:1: equivalence_expression returns [Expression exp] : l= implies_expression ( '<->' r= implies_expression )* ;
    public final Expression equivalence_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        Expression r = null;


        try {
            // BON.g:1521:49: (l= implies_expression ( '<->' r= implies_expression )* )
            // BON.g:1522:3: l= implies_expression ( '<->' r= implies_expression )*
            {
            pushFollow(FOLLOW_implies_expression_in_equivalence_expression9863);
            l=implies_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp = l; 
            }
            // BON.g:1524:3: ( '<->' r= implies_expression )*
            loop166:
            do {
                int alt166=2;
                int LA166_0 = input.LA(1);

                if ( (LA166_0==102) ) {
                    alt166=1;
                }


                switch (alt166) {
            	case 1 :
            	    // BON.g:1524:4: '<->' r= implies_expression
            	    {
            	    match(input,102,FOLLOW_102_in_equivalence_expression9873); if (state.failed) return exp;
            	    pushFollow(FOLLOW_implies_expression_in_equivalence_expression9877);
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
            	    break loop166;
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
    // BON.g:1531:1: implies_expression returns [Expression exp] : l= and_or_xor_expression ( '->' r= implies_expression )? ;
    public final Expression implies_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        Expression r = null;


        try {
            // BON.g:1531:45: (l= and_or_xor_expression ( '->' r= implies_expression )? )
            // BON.g:1532:3: l= and_or_xor_expression ( '->' r= implies_expression )?
            {
            pushFollow(FOLLOW_and_or_xor_expression_in_implies_expression9905);
            l=and_or_xor_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp = l; 
            }
            // BON.g:1534:3: ( '->' r= implies_expression )?
            int alt167=2;
            int LA167_0 = input.LA(1);

            if ( (LA167_0==65) ) {
                alt167=1;
            }
            switch (alt167) {
                case 1 :
                    // BON.g:1534:4: '->' r= implies_expression
                    {
                    match(input,65,FOLLOW_65_in_implies_expression9915); if (state.failed) return exp;
                    pushFollow(FOLLOW_implies_expression_in_implies_expression9919);
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
    // BON.g:1540:1: and_or_xor_expression returns [Expression exp] : l= comparison_expression (op= and_or_xor_op r= comparison_expression )* ;
    public final Expression and_or_xor_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        BinaryExp.Op op = null;

        Expression r = null;


        try {
            // BON.g:1540:48: (l= comparison_expression (op= and_or_xor_op r= comparison_expression )* )
            // BON.g:1541:3: l= comparison_expression (op= and_or_xor_op r= comparison_expression )*
            {
            pushFollow(FOLLOW_comparison_expression_in_and_or_xor_expression9946);
            l=comparison_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp = l; 
            }
            // BON.g:1543:3: (op= and_or_xor_op r= comparison_expression )*
            loop168:
            do {
                int alt168=2;
                int LA168_0 = input.LA(1);

                if ( ((LA168_0>=105 && LA168_0<=107)) ) {
                    alt168=1;
                }


                switch (alt168) {
            	case 1 :
            	    // BON.g:1543:5: op= and_or_xor_op r= comparison_expression
            	    {
            	    pushFollow(FOLLOW_and_or_xor_op_in_and_or_xor_expression9959);
            	    op=and_or_xor_op();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    pushFollow(FOLLOW_comparison_expression_in_and_or_xor_expression9963);
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
            	    break loop168;
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
    // BON.g:1549:1: comparison_expression returns [Expression exp] : l= add_sub_expression (op= comparison_op r= add_sub_expression )* ;
    public final Expression comparison_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        BinaryExp.Op op = null;

        Expression r = null;


        try {
            // BON.g:1549:48: (l= add_sub_expression (op= comparison_op r= add_sub_expression )* )
            // BON.g:1550:3: l= add_sub_expression (op= comparison_op r= add_sub_expression )*
            {
            pushFollow(FOLLOW_add_sub_expression_in_comparison_expression9991);
            l=add_sub_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp = l; 
            }
            // BON.g:1552:3: (op= comparison_op r= add_sub_expression )*
            loop169:
            do {
                int alt169=2;
                int LA169_0 = input.LA(1);

                if ( (LA169_0==34||LA169_0==86||(LA169_0>=110 && LA169_0<=116)) ) {
                    alt169=1;
                }


                switch (alt169) {
            	case 1 :
            	    // BON.g:1552:4: op= comparison_op r= add_sub_expression
            	    {
            	    pushFollow(FOLLOW_comparison_op_in_comparison_expression10003);
            	    op=comparison_op();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    pushFollow(FOLLOW_add_sub_expression_in_comparison_expression10008);
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
            	    break loop169;
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
    // BON.g:1559:1: add_sub_expression returns [Expression exp] : l= mul_div_expression (op= add_sub_op r= mul_div_expression )* ;
    public final Expression add_sub_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        BinaryExp.Op op = null;

        Expression r = null;


        try {
            // BON.g:1559:45: (l= mul_div_expression (op= add_sub_op r= mul_div_expression )* )
            // BON.g:1560:3: l= mul_div_expression (op= add_sub_op r= mul_div_expression )*
            {
            pushFollow(FOLLOW_mul_div_expression_in_add_sub_expression10036);
            l=mul_div_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp = l; 
            }
            // BON.g:1562:3: (op= add_sub_op r= mul_div_expression )*
            loop170:
            do {
                int alt170=2;
                int LA170_0 = input.LA(1);

                if ( ((LA170_0>=103 && LA170_0<=104)) ) {
                    alt170=1;
                }


                switch (alt170) {
            	case 1 :
            	    // BON.g:1562:4: op= add_sub_op r= mul_div_expression
            	    {
            	    pushFollow(FOLLOW_add_sub_op_in_add_sub_expression10048);
            	    op=add_sub_op();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    pushFollow(FOLLOW_mul_div_expression_in_add_sub_expression10052);
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
            	    break loop170;
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
    // BON.g:1568:1: mul_div_expression returns [Expression exp] : l= mod_pow_expression (op= mul_div_op r= mod_pow_expression )* ;
    public final Expression mul_div_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        BinaryExp.Op op = null;

        Expression r = null;


        try {
            // BON.g:1568:45: (l= mod_pow_expression (op= mul_div_op r= mod_pow_expression )* )
            // BON.g:1569:3: l= mod_pow_expression (op= mul_div_op r= mod_pow_expression )*
            {
            pushFollow(FOLLOW_mod_pow_expression_in_mul_div_expression10080);
            l=mod_pow_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp = l; 
            }
            // BON.g:1571:3: (op= mul_div_op r= mod_pow_expression )*
            loop171:
            do {
                int alt171=2;
                int LA171_0 = input.LA(1);

                if ( ((LA171_0>=117 && LA171_0<=119)) ) {
                    alt171=1;
                }


                switch (alt171) {
            	case 1 :
            	    // BON.g:1571:4: op= mul_div_op r= mod_pow_expression
            	    {
            	    pushFollow(FOLLOW_mul_div_op_in_mul_div_expression10092);
            	    op=mul_div_op();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    pushFollow(FOLLOW_mod_pow_expression_in_mul_div_expression10096);
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
            	    break loop171;
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
    // BON.g:1578:1: mod_pow_expression returns [Expression exp] : l= lowest_expression (op= mod_pow_op r= mod_pow_expression )? ;
    public final Expression mod_pow_expression() throws RecognitionException {
        Expression exp = null;

        BONParser.lowest_expression_return l = null;

        BinaryExp.Op op = null;

        Expression r = null;


        try {
            // BON.g:1578:45: (l= lowest_expression (op= mod_pow_op r= mod_pow_expression )? )
            // BON.g:1579:3: l= lowest_expression (op= mod_pow_op r= mod_pow_expression )?
            {
            pushFollow(FOLLOW_lowest_expression_in_mod_pow_expression10125);
            l=lowest_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               if(isOk()) exp = (l!=null?l.exp:null); 
            }
            // BON.g:1581:3: (op= mod_pow_op r= mod_pow_expression )?
            int alt172=2;
            int LA172_0 = input.LA(1);

            if ( (LA172_0==77||LA172_0==120) ) {
                alt172=1;
            }
            switch (alt172) {
                case 1 :
                    // BON.g:1581:4: op= mod_pow_op r= mod_pow_expression
                    {
                    pushFollow(FOLLOW_mod_pow_op_in_mod_pow_expression10137);
                    op=mod_pow_op();

                    state._fsp--;
                    if (state.failed) return exp;
                    pushFollow(FOLLOW_mod_pow_expression_in_mod_pow_expression10141);
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
    // BON.g:1587:1: lowest_expression returns [Expression exp] : ( ( constant )=> constant ( ( '.' cc= call_chain ) | ) | unary le= lowest_expression | s= '(' e= expression ')' ( ( '.' cc= call_chain ) | ) | cc= call_chain );
    public final BONParser.lowest_expression_return lowest_expression() throws RecognitionException {
        BONParser.lowest_expression_return retval = new BONParser.lowest_expression_return();
        retval.start = input.LT(1);

        Token s=null;
        BONParser.call_chain_return cc = null;

        BONParser.lowest_expression_return le = null;

        BONParser.expression_return e = null;

        BONParser.constant_return constant101 = null;

        BONParser.unary_return unary102 = null;


        try {
            // BON.g:1587:44: ( ( constant )=> constant ( ( '.' cc= call_chain ) | ) | unary le= lowest_expression | s= '(' e= expression ')' ( ( '.' cc= call_chain ) | ) | cc= call_chain )
            int alt175=4;
            alt175 = dfa175.predict(input);
            switch (alt175) {
                case 1 :
                    // BON.g:1588:5: ( constant )=> constant ( ( '.' cc= call_chain ) | )
                    {
                    pushFollow(FOLLOW_constant_in_lowest_expression10174);
                    constant101=constant();

                    state._fsp--;
                    if (state.failed) return retval;
                    // BON.g:1589:5: ( ( '.' cc= call_chain ) | )
                    int alt173=2;
                    int LA173_0 = input.LA(1);

                    if ( (LA173_0==70) ) {
                        alt173=1;
                    }
                    else if ( (LA173_0==25||(LA173_0>=33 && LA173_0<=35)||LA173_0==43||LA173_0==63||LA173_0==65||(LA173_0>=76 && LA173_0<=77)||(LA173_0>=84 && LA173_0<=86)||(LA173_0>=102 && LA173_0<=107)||(LA173_0>=110 && LA173_0<=120)) ) {
                        alt173=2;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return retval;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 173, 0, input);

                        throw nvae;
                    }
                    switch (alt173) {
                        case 1 :
                            // BON.g:1589:7: ( '.' cc= call_chain )
                            {
                            // BON.g:1589:7: ( '.' cc= call_chain )
                            // BON.g:1589:8: '.' cc= call_chain
                            {
                            match(input,70,FOLLOW_70_in_lowest_expression10183); if (state.failed) return retval;
                            pushFollow(FOLLOW_call_chain_in_lowest_expression10187);
                            cc=call_chain();

                            state._fsp--;
                            if (state.failed) return retval;
                            if ( state.backtracking==0 ) {
                               if(isOk()) retval.exp = CallExp.mk((constant101!=null?constant101.constant:null), (cc!=null?cc.calls:null), getSLoc((constant101!=null?((Token)constant101.start):null),(cc!=null?((Token)cc.stop):null))); 
                            }

                            }


                            }
                            break;
                        case 2 :
                            // BON.g:1593:7: 
                            {
                            if ( state.backtracking==0 ) {
                               if(isOk()) retval.exp = (constant101!=null?constant101.constant:null); 
                            }

                            }
                            break;

                    }


                    }
                    break;
                case 2 :
                    // BON.g:1595:4: unary le= lowest_expression
                    {
                    pushFollow(FOLLOW_unary_in_lowest_expression10237);
                    unary102=unary();

                    state._fsp--;
                    if (state.failed) return retval;
                    pushFollow(FOLLOW_lowest_expression_in_lowest_expression10241);
                    le=lowest_expression();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if(isOk()) retval.exp = UnaryExp.mk((unary102!=null?unary102.op:null), (le!=null?le.exp:null), getSLoc((unary102!=null?((Token)unary102.start):null),(le!=null?((Token)le.stop):null))); 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:1597:4: s= '(' e= expression ')' ( ( '.' cc= call_chain ) | )
                    {
                    s=(Token)match(input,42,FOLLOW_42_in_lowest_expression10254); if (state.failed) return retval;
                    pushFollow(FOLLOW_expression_in_lowest_expression10258);
                    e=expression();

                    state._fsp--;
                    if (state.failed) return retval;
                    match(input,43,FOLLOW_43_in_lowest_expression10260); if (state.failed) return retval;
                    // BON.g:1598:4: ( ( '.' cc= call_chain ) | )
                    int alt174=2;
                    int LA174_0 = input.LA(1);

                    if ( (LA174_0==70) ) {
                        alt174=1;
                    }
                    else if ( (LA174_0==25||(LA174_0>=33 && LA174_0<=35)||LA174_0==43||LA174_0==63||LA174_0==65||(LA174_0>=76 && LA174_0<=77)||(LA174_0>=84 && LA174_0<=86)||(LA174_0>=102 && LA174_0<=107)||(LA174_0>=110 && LA174_0<=120)) ) {
                        alt174=2;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return retval;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 174, 0, input);

                        throw nvae;
                    }
                    switch (alt174) {
                        case 1 :
                            // BON.g:1598:6: ( '.' cc= call_chain )
                            {
                            // BON.g:1598:6: ( '.' cc= call_chain )
                            // BON.g:1598:7: '.' cc= call_chain
                            {
                            match(input,70,FOLLOW_70_in_lowest_expression10270); if (state.failed) return retval;
                            pushFollow(FOLLOW_call_chain_in_lowest_expression10274);
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
                            // BON.g:1601:7: 
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
                    // BON.g:1603:4: cc= call_chain
                    {
                    pushFollow(FOLLOW_call_chain_in_lowest_expression10310);
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
    // BON.g:1607:1: add_sub_op returns [BinaryExp.Op op] : ( '+' | '-' );
    public final BinaryExp.Op add_sub_op() throws RecognitionException {
        BinaryExp.Op op = null;

        try {
            // BON.g:1611:38: ( '+' | '-' )
            int alt176=2;
            int LA176_0 = input.LA(1);

            if ( (LA176_0==103) ) {
                alt176=1;
            }
            else if ( (LA176_0==104) ) {
                alt176=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 176, 0, input);

                throw nvae;
            }
            switch (alt176) {
                case 1 :
                    // BON.g:1612:4: '+'
                    {
                    match(input,103,FOLLOW_103_in_add_sub_op10334); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.ADD; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1613:4: '-'
                    {
                    match(input,104,FOLLOW_104_in_add_sub_op10342); if (state.failed) return op;
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
    // BON.g:1616:1: add_sub_op_unary returns [UnaryExp.Op op] : ( '+' | '-' );
    public final UnaryExp.Op add_sub_op_unary() throws RecognitionException {
        UnaryExp.Op op = null;

        try {
            // BON.g:1616:43: ( '+' | '-' )
            int alt177=2;
            int LA177_0 = input.LA(1);

            if ( (LA177_0==103) ) {
                alt177=1;
            }
            else if ( (LA177_0==104) ) {
                alt177=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 177, 0, input);

                throw nvae;
            }
            switch (alt177) {
                case 1 :
                    // BON.g:1617:4: '+'
                    {
                    match(input,103,FOLLOW_103_in_add_sub_op_unary10360); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = UnaryExp.Op.ADD; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1618:4: '-'
                    {
                    match(input,104,FOLLOW_104_in_add_sub_op_unary10368); if (state.failed) return op;
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
    // BON.g:1621:1: and_or_xor_op returns [BinaryExp.Op op] : ( 'and' | 'or' | 'xor' );
    public final BinaryExp.Op and_or_xor_op() throws RecognitionException {
        BinaryExp.Op op = null;

        try {
            // BON.g:1621:41: ( 'and' | 'or' | 'xor' )
            int alt178=3;
            switch ( input.LA(1) ) {
            case 105:
                {
                alt178=1;
                }
                break;
            case 106:
                {
                alt178=2;
                }
                break;
            case 107:
                {
                alt178=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 178, 0, input);

                throw nvae;
            }

            switch (alt178) {
                case 1 :
                    // BON.g:1622:4: 'and'
                    {
                    match(input,105,FOLLOW_105_in_and_or_xor_op10386); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.AND; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1623:4: 'or'
                    {
                    match(input,106,FOLLOW_106_in_and_or_xor_op10393); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.OR; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:1624:4: 'xor'
                    {
                    match(input,107,FOLLOW_107_in_and_or_xor_op10401); if (state.failed) return op;
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
    // BON.g:1627:1: unary returns [UnaryExp.Op op] : ( other_unary | add_sub_op_unary );
    public final BONParser.unary_return unary() throws RecognitionException {
        BONParser.unary_return retval = new BONParser.unary_return();
        retval.start = input.LT(1);

        UnaryExp.Op other_unary103 = null;

        UnaryExp.Op add_sub_op_unary104 = null;


        try {
            // BON.g:1627:33: ( other_unary | add_sub_op_unary )
            int alt179=2;
            int LA179_0 = input.LA(1);

            if ( ((LA179_0>=108 && LA179_0<=110)) ) {
                alt179=1;
            }
            else if ( ((LA179_0>=103 && LA179_0<=104)) ) {
                alt179=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 179, 0, input);

                throw nvae;
            }
            switch (alt179) {
                case 1 :
                    // BON.g:1628:4: other_unary
                    {
                    pushFollow(FOLLOW_other_unary_in_unary10421);
                    other_unary103=other_unary();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.op = other_unary103; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1629:4: add_sub_op_unary
                    {
                    pushFollow(FOLLOW_add_sub_op_unary_in_unary10435);
                    add_sub_op_unary104=add_sub_op_unary();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.op = add_sub_op_unary104; 
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
    // BON.g:1632:1: other_unary returns [UnaryExp.Op op] : ( 'delta' | 'old' | 'not' );
    public final UnaryExp.Op other_unary() throws RecognitionException {
        UnaryExp.Op op = null;

        try {
            // BON.g:1632:39: ( 'delta' | 'old' | 'not' )
            int alt180=3;
            switch ( input.LA(1) ) {
            case 108:
                {
                alt180=1;
                }
                break;
            case 109:
                {
                alt180=2;
                }
                break;
            case 110:
                {
                alt180=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 180, 0, input);

                throw nvae;
            }

            switch (alt180) {
                case 1 :
                    // BON.g:1633:4: 'delta'
                    {
                    match(input,108,FOLLOW_108_in_other_unary10455); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = UnaryExp.Op.DELTA; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1634:4: 'old'
                    {
                    match(input,109,FOLLOW_109_in_other_unary10463); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = UnaryExp.Op.OLD; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:1635:4: 'not'
                    {
                    match(input,110,FOLLOW_110_in_other_unary10472); if (state.failed) return op;
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
    // BON.g:1638:1: binary : ( add_sub_op | mul_div_op | comparison_op | mod_pow_op | and_or_xor_op | '->' | '<->' );
    public final void binary() throws RecognitionException {
        try {
            // BON.g:1638:9: ( add_sub_op | mul_div_op | comparison_op | mod_pow_op | and_or_xor_op | '->' | '<->' )
            int alt181=7;
            switch ( input.LA(1) ) {
            case 103:
            case 104:
                {
                alt181=1;
                }
                break;
            case 117:
            case 118:
            case 119:
                {
                alt181=2;
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
                alt181=3;
                }
                break;
            case 77:
            case 120:
                {
                alt181=4;
                }
                break;
            case 105:
            case 106:
            case 107:
                {
                alt181=5;
                }
                break;
            case 65:
                {
                alt181=6;
                }
                break;
            case 102:
                {
                alt181=7;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 181, 0, input);

                throw nvae;
            }

            switch (alt181) {
                case 1 :
                    // BON.g:1638:13: add_sub_op
                    {
                    pushFollow(FOLLOW_add_sub_op_in_binary10503);
                    add_sub_op();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 2 :
                    // BON.g:1638:26: mul_div_op
                    {
                    pushFollow(FOLLOW_mul_div_op_in_binary10507);
                    mul_div_op();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 3 :
                    // BON.g:1638:39: comparison_op
                    {
                    pushFollow(FOLLOW_comparison_op_in_binary10511);
                    comparison_op();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 4 :
                    // BON.g:1639:13: mod_pow_op
                    {
                    pushFollow(FOLLOW_mod_pow_op_in_binary10526);
                    mod_pow_op();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 5 :
                    // BON.g:1639:26: and_or_xor_op
                    {
                    pushFollow(FOLLOW_and_or_xor_op_in_binary10530);
                    and_or_xor_op();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 6 :
                    // BON.g:1640:13: '->'
                    {
                    match(input,65,FOLLOW_65_in_binary10545); if (state.failed) return ;

                    }
                    break;
                case 7 :
                    // BON.g:1640:20: '<->'
                    {
                    match(input,102,FOLLOW_102_in_binary10549); if (state.failed) return ;

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
    // BON.g:1642:1: comparison_op returns [BinaryExp.Op op] : ( '<' | '>' | '<=' | '>=' | '=' | '/=' | 'member_of' | 'not' 'member_of' | ':' );
    public final BinaryExp.Op comparison_op() throws RecognitionException {
        BinaryExp.Op op = null;

        try {
            // BON.g:1642:41: ( '<' | '>' | '<=' | '>=' | '=' | '/=' | 'member_of' | 'not' 'member_of' | ':' )
            int alt182=9;
            switch ( input.LA(1) ) {
            case 111:
                {
                alt182=1;
                }
                break;
            case 112:
                {
                alt182=2;
                }
                break;
            case 113:
                {
                alt182=3;
                }
                break;
            case 114:
                {
                alt182=4;
                }
                break;
            case 115:
                {
                alt182=5;
                }
                break;
            case 116:
                {
                alt182=6;
                }
                break;
            case 86:
                {
                alt182=7;
                }
                break;
            case 110:
                {
                alt182=8;
                }
                break;
            case 34:
                {
                alt182=9;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 182, 0, input);

                throw nvae;
            }

            switch (alt182) {
                case 1 :
                    // BON.g:1643:4: '<'
                    {
                    match(input,111,FOLLOW_111_in_comparison_op10565); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.LT; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1644:4: '>'
                    {
                    match(input,112,FOLLOW_112_in_comparison_op10573); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.GT; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:1645:4: '<='
                    {
                    match(input,113,FOLLOW_113_in_comparison_op10581); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.LE; 
                    }

                    }
                    break;
                case 4 :
                    // BON.g:1646:4: '>='
                    {
                    match(input,114,FOLLOW_114_in_comparison_op10588); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.GE; 
                    }

                    }
                    break;
                case 5 :
                    // BON.g:1647:4: '='
                    {
                    match(input,115,FOLLOW_115_in_comparison_op10595); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.EQ; 
                    }

                    }
                    break;
                case 6 :
                    // BON.g:1648:4: '/='
                    {
                    match(input,116,FOLLOW_116_in_comparison_op10603); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.NEQ; 
                    }

                    }
                    break;
                case 7 :
                    // BON.g:1649:4: 'member_of'
                    {
                    match(input,86,FOLLOW_86_in_comparison_op10610); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.MEMBEROF; 
                    }

                    }
                    break;
                case 8 :
                    // BON.g:1650:4: 'not' 'member_of'
                    {
                    match(input,110,FOLLOW_110_in_comparison_op10617); if (state.failed) return op;
                    match(input,86,FOLLOW_86_in_comparison_op10619); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.NOTMEMBEROF; 
                    }

                    }
                    break;
                case 9 :
                    // BON.g:1651:4: ':'
                    {
                    match(input,34,FOLLOW_34_in_comparison_op10626); if (state.failed) return op;
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
    // BON.g:1655:1: mul_div_op returns [BinaryExp.Op op] : ( '*' | '/' | '//' );
    public final BinaryExp.Op mul_div_op() throws RecognitionException {
        BinaryExp.Op op = null;

        try {
            // BON.g:1655:38: ( '*' | '/' | '//' )
            int alt183=3;
            switch ( input.LA(1) ) {
            case 117:
                {
                alt183=1;
                }
                break;
            case 118:
                {
                alt183=2;
                }
                break;
            case 119:
                {
                alt183=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 183, 0, input);

                throw nvae;
            }

            switch (alt183) {
                case 1 :
                    // BON.g:1656:4: '*'
                    {
                    match(input,117,FOLLOW_117_in_mul_div_op10653); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.MUL; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1657:4: '/'
                    {
                    match(input,118,FOLLOW_118_in_mul_div_op10661); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.DIV; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:1658:4: '//'
                    {
                    match(input,119,FOLLOW_119_in_mul_div_op10669); if (state.failed) return op;
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
    // BON.g:1661:1: mod_pow_op returns [BinaryExp.Op op] : ( '\\\\\\\\' | '^' );
    public final BinaryExp.Op mod_pow_op() throws RecognitionException {
        BinaryExp.Op op = null;

        try {
            // BON.g:1661:38: ( '\\\\\\\\' | '^' )
            int alt184=2;
            int LA184_0 = input.LA(1);

            if ( (LA184_0==120) ) {
                alt184=1;
            }
            else if ( (LA184_0==77) ) {
                alt184=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 184, 0, input);

                throw nvae;
            }
            switch (alt184) {
                case 1 :
                    // BON.g:1662:4: '\\\\\\\\'
                    {
                    match(input,120,FOLLOW_120_in_mod_pow_op10702); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.MOD; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1663:4: '^'
                    {
                    match(input,77,FOLLOW_77_in_mod_pow_op10710); if (state.failed) return op;
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
    // BON.g:1705:1: manifest_textblock : ( MANIFEST_STRING | MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END );
    public final BONParser.manifest_textblock_return manifest_textblock() throws RecognitionException {
        BONParser.manifest_textblock_return retval = new BONParser.manifest_textblock_return();
        retval.start = input.LT(1);

        try {
            // BON.g:1706:1: ( MANIFEST_STRING | MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END )
            int alt186=2;
            int LA186_0 = input.LA(1);

            if ( (LA186_0==MANIFEST_STRING) ) {
                alt186=1;
            }
            else if ( (LA186_0==MANIFEST_TEXTBLOCK_START) ) {
                alt186=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 186, 0, input);

                throw nvae;
            }
            switch (alt186) {
                case 1 :
                    // BON.g:1707:3: MANIFEST_STRING
                    {
                    if ( state.backtracking==0 ) {
                       //TODO warn when not MANIFEST_STRING where we desire a single block. 
                        
                    }
                    match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_manifest_textblock11022); if (state.failed) return retval;

                    }
                    break;
                case 2 :
                    // BON.g:1710:4: MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END
                    {
                    match(input,MANIFEST_TEXTBLOCK_START,FOLLOW_MANIFEST_TEXTBLOCK_START_in_manifest_textblock11028); if (state.failed) return retval;
                    // BON.g:1710:29: ( MANIFEST_TEXTBLOCK_MIDDLE )*
                    loop185:
                    do {
                        int alt185=2;
                        int LA185_0 = input.LA(1);

                        if ( (LA185_0==MANIFEST_TEXTBLOCK_MIDDLE) ) {
                            alt185=1;
                        }


                        switch (alt185) {
                    	case 1 :
                    	    // BON.g:1710:29: MANIFEST_TEXTBLOCK_MIDDLE
                    	    {
                    	    match(input,MANIFEST_TEXTBLOCK_MIDDLE,FOLLOW_MANIFEST_TEXTBLOCK_MIDDLE_in_manifest_textblock11030); if (state.failed) return retval;

                    	    }
                    	    break;

                    	default :
                    	    break loop185;
                        }
                    } while (true);

                    match(input,MANIFEST_TEXTBLOCK_END,FOLLOW_MANIFEST_TEXTBLOCK_END_in_manifest_textblock11033); if (state.failed) return retval;

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
        // BON.g:1588:5: ( constant )
        // BON.g:1588:6: constant
        {
        pushFollow(FOLLOW_constant_in_synpred1_BON10170);
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
    protected DFA78 dfa78 = new DFA78(this);
    protected DFA86 dfa86 = new DFA86(this);
    protected DFA134 dfa134 = new DFA134(this);
    protected DFA175 dfa175 = new DFA175(this);
    static final String DFA1_eotS =
        "\50\uffff";
    static final String DFA1_eofS =
        "\1\3\1\uffff\1\6\4\uffff\2\6\1\uffff\1\6\2\uffff\1\6\2\uffff\3\6"+
        "\1\uffff\1\6\1\uffff\1\6\3\uffff\1\6\1\uffff\1\6\2\uffff\2\6\1\uffff"+
        "\1\6\2\uffff\1\6\1\uffff\1\6";
    static final String DFA1_minS =
        "\1\30\1\uffff\1\5\1\uffff\1\42\2\uffff\1\4\1\5\1\42\1\5\1\14\1\42"+
        "\2\4\1\14\1\5\1\4\1\5\1\14\1\5\1\14\1\5\1\14\1\4\1\14\1\5\1\14\1"+
        "\5\1\4\1\14\2\5\1\14\1\5\2\14\1\5\1\14\1\5";
    static final String DFA1_maxS =
        "\1\134\1\uffff\1\134\1\uffff\1\42\2\uffff\2\134\1\42\1\134\1\15"+
        "\1\42\1\134\1\13\1\15\3\134\1\15\1\134\1\15\1\134\1\15\1\13\1\15"+
        "\1\134\1\15\1\134\1\13\1\15\2\134\1\15\1\134\2\15\1\134\1\15\1\134";
    static final String DFA1_acceptS =
        "\1\uffff\1\1\1\uffff\1\3\1\uffff\1\2\1\4\41\uffff";
    static final String DFA1_specialS =
        "\50\uffff}>";
    static final String[] DFA1_transitionS = {
            "\1\1\3\uffff\1\1\1\uffff\1\2\5\uffff\2\1\6\uffff\1\1\4\uffff"+
            "\1\1\1\uffff\1\1\2\uffff\1\1\45\uffff\1\1",
            "",
            "\1\4\22\uffff\1\5\3\uffff\1\5\7\uffff\2\5\6\uffff\1\5\4\uffff"+
            "\1\5\1\uffff\1\5\2\uffff\1\5\45\uffff\1\5",
            "",
            "\1\7",
            "",
            "",
            "\1\12\1\11\5\uffff\1\13\14\uffff\1\5\3\uffff\1\5\4\uffff\1"+
            "\10\2\uffff\2\5\6\uffff\1\5\4\uffff\1\5\1\uffff\1\5\2\uffff"+
            "\1\5\45\uffff\1\5",
            "\1\14\22\uffff\1\5\3\uffff\1\5\7\uffff\2\5\6\uffff\1\5\4\uffff"+
            "\1\5\1\uffff\1\5\2\uffff\1\5\45\uffff\1\5",
            "\1\15",
            "\1\11\22\uffff\1\5\3\uffff\1\5\4\uffff\1\10\1\uffff\1\16\2"+
            "\5\6\uffff\1\5\4\uffff\1\5\1\uffff\1\5\2\uffff\1\5\45\uffff"+
            "\1\5",
            "\1\17\1\20",
            "\1\21",
            "\1\22\1\11\5\uffff\1\23\14\uffff\1\5\3\uffff\1\5\4\uffff\1"+
            "\10\2\uffff\2\5\6\uffff\1\5\4\uffff\1\5\1\uffff\1\5\2\uffff"+
            "\1\5\45\uffff\1\5",
            "\1\24\6\uffff\1\25",
            "\1\17\1\20",
            "\1\11\22\uffff\1\5\3\uffff\1\5\4\uffff\1\10\1\uffff\1\16\2"+
            "\5\6\uffff\1\5\4\uffff\1\5\1\uffff\1\5\2\uffff\1\5\45\uffff"+
            "\1\5",
            "\1\26\1\11\5\uffff\1\27\14\uffff\1\5\3\uffff\1\5\4\uffff\1"+
            "\10\2\uffff\2\5\6\uffff\1\5\4\uffff\1\5\1\uffff\1\5\2\uffff"+
            "\1\5\45\uffff\1\5",
            "\1\11\22\uffff\1\5\3\uffff\1\5\4\uffff\1\10\1\uffff\1\30\2"+
            "\5\6\uffff\1\5\4\uffff\1\5\1\uffff\1\5\2\uffff\1\5\45\uffff"+
            "\1\5",
            "\1\31\1\32",
            "\1\11\22\uffff\1\5\3\uffff\1\5\4\uffff\1\10\1\uffff\1\16\2"+
            "\5\6\uffff\1\5\4\uffff\1\5\1\uffff\1\5\2\uffff\1\5\45\uffff"+
            "\1\5",
            "\1\33\1\34",
            "\1\11\22\uffff\1\5\3\uffff\1\5\4\uffff\1\10\1\uffff\1\35\2"+
            "\5\6\uffff\1\5\4\uffff\1\5\1\uffff\1\5\2\uffff\1\5\45\uffff"+
            "\1\5",
            "\1\36\1\37",
            "\1\40\6\uffff\1\41",
            "\1\31\1\32",
            "\1\11\22\uffff\1\5\3\uffff\1\5\4\uffff\1\10\1\uffff\1\30\2"+
            "\5\6\uffff\1\5\4\uffff\1\5\1\uffff\1\5\2\uffff\1\5\45\uffff"+
            "\1\5",
            "\1\33\1\34",
            "\1\11\22\uffff\1\5\3\uffff\1\5\4\uffff\1\10\1\uffff\1\16\2"+
            "\5\6\uffff\1\5\4\uffff\1\5\1\uffff\1\5\2\uffff\1\5\45\uffff"+
            "\1\5",
            "\1\42\6\uffff\1\43",
            "\1\36\1\37",
            "\1\11\22\uffff\1\5\3\uffff\1\5\4\uffff\1\10\1\uffff\1\35\2"+
            "\5\6\uffff\1\5\4\uffff\1\5\1\uffff\1\5\2\uffff\1\5\45\uffff"+
            "\1\5",
            "\1\11\22\uffff\1\5\3\uffff\1\5\4\uffff\1\10\1\uffff\1\30\2"+
            "\5\6\uffff\1\5\4\uffff\1\5\1\uffff\1\5\2\uffff\1\5\45\uffff"+
            "\1\5",
            "\1\44\1\45",
            "\1\11\22\uffff\1\5\3\uffff\1\5\4\uffff\1\10\1\uffff\1\35\2"+
            "\5\6\uffff\1\5\4\uffff\1\5\1\uffff\1\5\2\uffff\1\5\45\uffff"+
            "\1\5",
            "\1\46\1\47",
            "\1\44\1\45",
            "\1\11\22\uffff\1\5\3\uffff\1\5\4\uffff\1\10\1\uffff\1\30\2"+
            "\5\6\uffff\1\5\4\uffff\1\5\1\uffff\1\5\2\uffff\1\5\45\uffff"+
            "\1\5",
            "\1\46\1\47",
            "\1\11\22\uffff\1\5\3\uffff\1\5\4\uffff\1\10\1\uffff\1\35\2"+
            "\5\6\uffff\1\5\4\uffff\1\5\1\uffff\1\5\2\uffff\1\5\45\uffff"+
            "\1\5"
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
    static final String DFA78_eotS =
        "\7\uffff";
    static final String DFA78_eofS =
        "\7\uffff";
    static final String DFA78_minS =
        "\1\5\1\46\1\5\2\uffff\1\46\1\5";
    static final String DFA78_maxS =
        "\1\5\1\106\1\5\2\uffff\1\106\1\5";
    static final String DFA78_acceptS =
        "\3\uffff\1\1\1\2\2\uffff";
    static final String DFA78_specialS =
        "\7\uffff}>";
    static final String[] DFA78_transitionS = {
            "\1\1",
            "\1\3\31\uffff\1\4\5\uffff\1\2",
            "\1\5",
            "",
            "",
            "\1\3\31\uffff\1\4\5\uffff\1\6",
            "\1\5"
    };

    static final short[] DFA78_eot = DFA.unpackEncodedString(DFA78_eotS);
    static final short[] DFA78_eof = DFA.unpackEncodedString(DFA78_eofS);
    static final char[] DFA78_min = DFA.unpackEncodedStringToUnsignedChars(DFA78_minS);
    static final char[] DFA78_max = DFA.unpackEncodedStringToUnsignedChars(DFA78_maxS);
    static final short[] DFA78_accept = DFA.unpackEncodedString(DFA78_acceptS);
    static final short[] DFA78_special = DFA.unpackEncodedString(DFA78_specialS);
    static final short[][] DFA78_transition;

    static {
        int numStates = DFA78_transitionS.length;
        DFA78_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA78_transition[i] = DFA.unpackEncodedString(DFA78_transitionS[i]);
        }
    }

    class DFA78 extends DFA {

        public DFA78(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 78;
            this.eot = DFA78_eot;
            this.eof = DFA78_eof;
            this.min = DFA78_min;
            this.max = DFA78_max;
            this.accept = DFA78_accept;
            this.special = DFA78_special;
            this.transition = DFA78_transition;
        }
        public String getDescription() {
            return "584:1: static_relation returns [StaticRelation relation] : (ir= inheritance_relation | cr= client_relation );";
        }
    }
    static final String DFA86_eotS =
        "\46\uffff";
    static final String DFA86_eofS =
        "\46\uffff";
    static final String DFA86_minS =
        "\1\5\2\120\2\uffff\1\147\1\42\21\120\1\126\10\120\2\42\1\120\2\uffff";
    static final String DFA86_maxS =
        "\1\121\2\120\2\uffff\1\156\1\170\21\120\1\126\10\120\2\77\1\120"+
        "\2\uffff";
    static final String DFA86_acceptS =
        "\3\uffff\1\3\1\4\37\uffff\1\1\1\2";
    static final String DFA86_specialS =
        "\46\uffff}>";
    static final String[] DFA86_transitionS = {
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

    static final short[] DFA86_eot = DFA.unpackEncodedString(DFA86_eotS);
    static final short[] DFA86_eof = DFA.unpackEncodedString(DFA86_eofS);
    static final char[] DFA86_min = DFA.unpackEncodedStringToUnsignedChars(DFA86_minS);
    static final char[] DFA86_max = DFA.unpackEncodedStringToUnsignedChars(DFA86_maxS);
    static final short[] DFA86_accept = DFA.unpackEncodedString(DFA86_acceptS);
    static final short[] DFA86_special = DFA.unpackEncodedString(DFA86_specialS);
    static final short[][] DFA86_transition;

    static {
        int numStates = DFA86_transitionS.length;
        DFA86_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA86_transition[i] = DFA.unpackEncodedString(DFA86_transitionS[i]);
        }
    }

    class DFA86 extends DFA {

        public DFA86(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 86;
            this.eot = DFA86_eot;
            this.eof = DFA86_eof;
            this.min = DFA86_min;
            this.max = DFA86_max;
            this.accept = DFA86_accept;
            this.special = DFA86_special;
            this.transition = DFA86_transition;
        }
        public String getDescription() {
            return "649:1: client_entity returns [ClientEntity entity] : ( prefix | infix | supplier_indirection | parent_indirection );";
        }
    }
    static final String DFA134_eotS =
        "\6\uffff";
    static final String DFA134_eofS =
        "\6\uffff";
    static final String DFA134_minS =
        "\1\5\1\42\1\5\2\uffff\1\42";
    static final String DFA134_maxS =
        "\1\5\1\126\1\5\2\uffff\1\126";
    static final String DFA134_acceptS =
        "\3\uffff\1\1\1\2\1\uffff";
    static final String DFA134_specialS =
        "\6\uffff}>";
    static final String[] DFA134_transitionS = {
            "\1\1",
            "\1\4\1\2\62\uffff\1\3",
            "\1\5",
            "",
            "",
            "\1\4\1\2\62\uffff\1\3"
    };

    static final short[] DFA134_eot = DFA.unpackEncodedString(DFA134_eotS);
    static final short[] DFA134_eof = DFA.unpackEncodedString(DFA134_eofS);
    static final char[] DFA134_min = DFA.unpackEncodedStringToUnsignedChars(DFA134_minS);
    static final char[] DFA134_max = DFA.unpackEncodedStringToUnsignedChars(DFA134_maxS);
    static final short[] DFA134_accept = DFA.unpackEncodedString(DFA134_acceptS);
    static final short[] DFA134_special = DFA.unpackEncodedString(DFA134_specialS);
    static final short[][] DFA134_transition;

    static {
        int numStates = DFA134_transitionS.length;
        DFA134_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA134_transition[i] = DFA.unpackEncodedString(DFA134_transitionS[i]);
        }
    }

    class DFA134 extends DFA {

        public DFA134(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 134;
            this.eot = DFA134_eot;
            this.eof = DFA134_eof;
            this.min = DFA134_min;
            this.max = DFA134_max;
            this.accept = DFA134_accept;
            this.special = DFA134_special;
            this.transition = DFA134_transition;
        }
        public String getDescription() {
            return "1157:1: variable_range returns [VariableRange range] : (mr= member_range | tr= type_range );";
        }
    }
    static final String DFA175_eotS =
        "\20\uffff";
    static final String DFA175_eofS =
        "\20\uffff";
    static final String DFA175_minS =
        "\1\4\3\uffff\2\0\12\uffff";
    static final String DFA175_maxS =
        "\1\156\3\uffff\2\0\12\uffff";
    static final String DFA175_acceptS =
        "\1\uffff\3\1\2\uffff\7\1\1\2\1\3\1\4";
    static final String DFA175_specialS =
        "\1\0\3\uffff\1\1\1\2\12\uffff}>";
    static final String[] DFA175_transitionS = {
            "\1\10\1\17\1\uffff\1\6\1\3\1\7\40\uffff\1\16\23\uffff\1\11\13"+
            "\uffff\1\13\15\uffff\1\12\1\14\1\1\1\2\13\uffff\1\4\1\5\3\uffff"+
            "\3\15",
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

    static final short[] DFA175_eot = DFA.unpackEncodedString(DFA175_eotS);
    static final short[] DFA175_eof = DFA.unpackEncodedString(DFA175_eofS);
    static final char[] DFA175_min = DFA.unpackEncodedStringToUnsignedChars(DFA175_minS);
    static final char[] DFA175_max = DFA.unpackEncodedStringToUnsignedChars(DFA175_maxS);
    static final short[] DFA175_accept = DFA.unpackEncodedString(DFA175_acceptS);
    static final short[] DFA175_special = DFA.unpackEncodedString(DFA175_specialS);
    static final short[][] DFA175_transition;

    static {
        int numStates = DFA175_transitionS.length;
        DFA175_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA175_transition[i] = DFA.unpackEncodedString(DFA175_transitionS[i]);
        }
    }

    class DFA175 extends DFA {

        public DFA175(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 175;
            this.eot = DFA175_eot;
            this.eof = DFA175_eof;
            this.min = DFA175_min;
            this.max = DFA175_max;
            this.accept = DFA175_accept;
            this.special = DFA175_special;
            this.transition = DFA175_transition;
        }
        public String getDescription() {
            return "1587:1: lowest_expression returns [Expression exp] : ( ( constant )=> constant ( ( '.' cc= call_chain ) | ) | unary le= lowest_expression | s= '(' e= expression ')' ( ( '.' cc= call_chain ) | ) | cc= call_chain );";
        }
        public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
            TokenStream input = (TokenStream)_input;
        	int _s = s;
            switch ( s ) {
                    case 0 : 
                        int LA175_0 = input.LA(1);

                         
                        int index175_0 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (LA175_0==90) && (synpred1_BON())) {s = 1;}

                        else if ( (LA175_0==91) && (synpred1_BON())) {s = 2;}

                        else if ( (LA175_0==CHARACTER_CONSTANT) && (synpred1_BON())) {s = 3;}

                        else if ( (LA175_0==103) ) {s = 4;}

                        else if ( (LA175_0==104) ) {s = 5;}

                        else if ( (LA175_0==INTEGER) && (synpred1_BON())) {s = 6;}

                        else if ( (LA175_0==REAL) && (synpred1_BON())) {s = 7;}

                        else if ( (LA175_0==MANIFEST_STRING) && (synpred1_BON())) {s = 8;}

                        else if ( (LA175_0==62) && (synpred1_BON())) {s = 9;}

                        else if ( (LA175_0==88) && (synpred1_BON())) {s = 10;}

                        else if ( (LA175_0==74) && (synpred1_BON())) {s = 11;}

                        else if ( (LA175_0==89) && (synpred1_BON())) {s = 12;}

                        else if ( ((LA175_0>=108 && LA175_0<=110)) ) {s = 13;}

                        else if ( (LA175_0==42) ) {s = 14;}

                        else if ( (LA175_0==IDENTIFIER) ) {s = 15;}

                         
                        input.seek(index175_0);
                        if ( s>=0 ) return s;
                        break;
                    case 1 : 
                        int LA175_4 = input.LA(1);

                         
                        int index175_4 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred1_BON()) ) {s = 12;}

                        else if ( (true) ) {s = 13;}

                         
                        input.seek(index175_4);
                        if ( s>=0 ) return s;
                        break;
                    case 2 : 
                        int LA175_5 = input.LA(1);

                         
                        int index175_5 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred1_BON()) ) {s = 12;}

                        else if ( (true) ) {s = 13;}

                         
                        input.seek(index175_5);
                        if ( s>=0 ) return s;
                        break;
            }
            if (state.backtracking>0) {state.failed=true; return -1;}
            NoViableAltException nvae =
                new NoViableAltException(getDescription(), 175, _s, input);
            error(nvae);
            throw nvae;
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
    public static final BitSet FOLLOW_29_in_explanation665 = new BitSet(new long[]{0x0000000000000810L});
    public static final BitSet FOLLOW_manifest_textblock_in_explanation669 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_29_in_explanation682 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_30_in_indexing707 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_index_list_in_indexing709 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_30_in_indexing725 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_31_in_part755 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_part759 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_31_in_part777 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_32_in_description807 = new BitSet(new long[]{0x0000000000000810L});
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
    public static final BitSet FOLLOW_34_in_index_clause1152 = new BitSet(new long[]{0x0000000000000810L});
    public static final BitSet FOLLOW_index_term_list_in_index_clause1154 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_index_clause1168 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_34_in_index_clause1170 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_index_string_in_index_term_list1212 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_index_term_list1222 = new BitSet(new long[]{0x0000000000000810L});
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
    public static final BitSet FOLLOW_39_in_queries1738 = new BitSet(new long[]{0x0000000000000810L});
    public static final BitSet FOLLOW_query_list_in_queries1740 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_40_in_commands1770 = new BitSet(new long[]{0x0000000000000810L});
    public static final BitSet FOLLOW_command_list_in_commands1772 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_41_in_constraints1791 = new BitSet(new long[]{0x0000000000000810L});
    public static final BitSet FOLLOW_constraint_list_in_constraints1793 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_query_list1819 = new BitSet(new long[]{0x0000000800000812L});
    public static final BitSet FOLLOW_35_in_query_list1832 = new BitSet(new long[]{0x0000000000000810L});
    public static final BitSet FOLLOW_manifest_textblock_in_query_list1836 = new BitSet(new long[]{0x0000000800000812L});
    public static final BitSet FOLLOW_manifest_textblock_in_query_list1868 = new BitSet(new long[]{0x0000000800000812L});
    public static final BitSet FOLLOW_35_in_query_list1894 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_command_list1941 = new BitSet(new long[]{0x0000000800000812L});
    public static final BitSet FOLLOW_35_in_command_list1954 = new BitSet(new long[]{0x0000000000000810L});
    public static final BitSet FOLLOW_manifest_textblock_in_command_list1958 = new BitSet(new long[]{0x0000000800000812L});
    public static final BitSet FOLLOW_manifest_textblock_in_command_list1984 = new BitSet(new long[]{0x0000000800000812L});
    public static final BitSet FOLLOW_35_in_command_list2009 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_constraint_list2045 = new BitSet(new long[]{0x0000000800000812L});
    public static final BitSet FOLLOW_35_in_constraint_list2058 = new BitSet(new long[]{0x0000000000000810L});
    public static final BitSet FOLLOW_manifest_textblock_in_constraint_list2062 = new BitSet(new long[]{0x0000000800000812L});
    public static final BitSet FOLLOW_manifest_textblock_in_constraint_list2073 = new BitSet(new long[]{0x0000000800000812L});
    public static final BitSet FOLLOW_35_in_constraint_list2097 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_class_name_list2119 = new BitSet(new long[]{0x0000000800000022L});
    public static final BitSet FOLLOW_35_in_class_name_list2133 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_in_class_name_list2137 = new BitSet(new long[]{0x0000000800000022L});
    public static final BitSet FOLLOW_class_name_in_class_name_list2166 = new BitSet(new long[]{0x0000000800000022L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_name_list2235 = new BitSet(new long[]{0x0000000800000022L});
    public static final BitSet FOLLOW_35_in_cluster_name_list2248 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_name_list2252 = new BitSet(new long[]{0x0000000800000022L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_name_list2280 = new BitSet(new long[]{0x0000000800000022L});
    public static final BitSet FOLLOW_class_or_bracketed_cluster_name_in_class_or_cluster_name_list2377 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_class_or_cluster_name_list2387 = new BitSet(new long[]{0x0000040000000020L});
    public static final BitSet FOLLOW_class_or_bracketed_cluster_name_in_class_or_cluster_name_list2391 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_class_name_in_class_or_bracketed_cluster_name2419 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_42_in_class_or_bracketed_cluster_name2433 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_cluster_name_in_class_or_bracketed_cluster_name2435 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_43_in_class_or_bracketed_cluster_name2437 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_class_name2459 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_44_in_event_chart2490 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_system_name_in_event_chart2492 = new BitSet(new long[]{0x0000E000E2000000L});
    public static final BitSet FOLLOW_45_in_event_chart2500 = new BitSet(new long[]{0x00008000E2000000L});
    public static final BitSet FOLLOW_46_in_event_chart2510 = new BitSet(new long[]{0x00008000E2000000L});
    public static final BitSet FOLLOW_indexing_in_event_chart2522 = new BitSet(new long[]{0x00008000A2000000L});
    public static final BitSet FOLLOW_explanation_in_event_chart2531 = new BitSet(new long[]{0x0000800082000000L});
    public static final BitSet FOLLOW_part_in_event_chart2541 = new BitSet(new long[]{0x0000800002000000L});
    public static final BitSet FOLLOW_event_entries_in_event_chart2554 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_event_chart2581 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_event_entry_in_event_entries2618 = new BitSet(new long[]{0x0000800000000002L});
    public static final BitSet FOLLOW_47_in_event_entry2661 = new BitSet(new long[]{0x0001000000000810L});
    public static final BitSet FOLLOW_manifest_textblock_in_event_entry2672 = new BitSet(new long[]{0x0001000000000000L});
    public static final BitSet FOLLOW_48_in_event_entry2712 = new BitSet(new long[]{0x0000040000000022L});
    public static final BitSet FOLLOW_class_or_cluster_name_list_in_event_entry2722 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_49_in_scenario_chart2802 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_system_name_in_scenario_chart2804 = new BitSet(new long[]{0x00040000E2000000L});
    public static final BitSet FOLLOW_indexing_in_scenario_chart2809 = new BitSet(new long[]{0x00040000A2000000L});
    public static final BitSet FOLLOW_explanation_in_scenario_chart2819 = new BitSet(new long[]{0x0004000082000000L});
    public static final BitSet FOLLOW_part_in_scenario_chart2829 = new BitSet(new long[]{0x0004000002000000L});
    public static final BitSet FOLLOW_scenario_entries_in_scenario_chart2840 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_scenario_chart2861 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_scenario_entry_in_scenario_entries2901 = new BitSet(new long[]{0x0004000000000002L});
    public static final BitSet FOLLOW_50_in_scenario_entry2942 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_scenario_entry2946 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_description_in_scenario_entry2950 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_51_in_creation_chart2979 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_system_name_in_creation_chart2981 = new BitSet(new long[]{0x00100000E2000000L});
    public static final BitSet FOLLOW_indexing_in_creation_chart2986 = new BitSet(new long[]{0x00100000A2000000L});
    public static final BitSet FOLLOW_explanation_in_creation_chart2996 = new BitSet(new long[]{0x0010000082000000L});
    public static final BitSet FOLLOW_part_in_creation_chart3006 = new BitSet(new long[]{0x0010000002000000L});
    public static final BitSet FOLLOW_creation_entries_in_creation_chart3017 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_creation_chart3034 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_creation_entry_in_creation_entries3075 = new BitSet(new long[]{0x0010000000000002L});
    public static final BitSet FOLLOW_52_in_creation_entry3115 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_in_creation_entry3117 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_53_in_creation_entry3122 = new BitSet(new long[]{0x0000040000000020L});
    public static final BitSet FOLLOW_class_or_cluster_name_list_in_creation_entry3126 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_54_in_static_diagram3159 = new BitSet(new long[]{0x00800000000000E0L});
    public static final BitSet FOLLOW_extended_id_in_static_diagram3165 = new BitSet(new long[]{0x0080000000000040L});
    public static final BitSet FOLLOW_COMMENT_in_static_diagram3178 = new BitSet(new long[]{0x0080000000000000L});
    public static final BitSet FOLLOW_55_in_static_diagram3188 = new BitSet(new long[]{0x0E0000000E000020L});
    public static final BitSet FOLLOW_static_block_in_static_diagram3195 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_static_diagram3202 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_extended_id3258 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_INTEGER_in_extended_id3271 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_component_in_static_block3312 = new BitSet(new long[]{0x0E0000000C000022L});
    public static final BitSet FOLLOW_cluster_in_static_component3347 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_clazz_in_static_component3360 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_relation_in_static_component3373 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_27_in_cluster3405 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_cluster_name_in_cluster3407 = new BitSet(new long[]{0x0180000000000042L});
    public static final BitSet FOLLOW_56_in_cluster3416 = new BitSet(new long[]{0x0080000000000042L});
    public static final BitSet FOLLOW_COMMENT_in_cluster3429 = new BitSet(new long[]{0x0080000000000002L});
    public static final BitSet FOLLOW_cluster_components_in_cluster3447 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_55_in_cluster_components3502 = new BitSet(new long[]{0x0E0000000E000020L});
    public static final BitSet FOLLOW_static_block_in_cluster_components3504 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_cluster_components3506 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_57_in_clazz3557 = new BitSet(new long[]{0x0000000004000000L});
    public static final BitSet FOLLOW_58_in_clazz3574 = new BitSet(new long[]{0x0000000004000000L});
    public static final BitSet FOLLOW_59_in_clazz3587 = new BitSet(new long[]{0x0000000004000000L});
    public static final BitSet FOLLOW_26_in_clazz3621 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_in_clazz3632 = new BitSet(new long[]{0x3100004040000042L,0x0000000000000184L});
    public static final BitSet FOLLOW_formal_generics_in_clazz3645 = new BitSet(new long[]{0x3100004040000042L,0x0000000000000180L});
    public static final BitSet FOLLOW_56_in_clazz3667 = new BitSet(new long[]{0x3000004040000042L,0x0000000000000180L});
    public static final BitSet FOLLOW_60_in_clazz3680 = new BitSet(new long[]{0x2000004040000042L,0x0000000000000180L});
    public static final BitSet FOLLOW_61_in_clazz3694 = new BitSet(new long[]{0x0000004040000042L,0x0000000000000180L});
    public static final BitSet FOLLOW_COMMENT_in_clazz3706 = new BitSet(new long[]{0x0000004040000002L,0x0000000000000180L});
    public static final BitSet FOLLOW_class_interface_in_clazz3721 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_inheritance_relation_in_static_relation3763 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_client_relation_in_static_relation3775 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_child_in_inheritance_relation3806 = new BitSet(new long[]{0x0000004000000000L});
    public static final BitSet FOLLOW_38_in_inheritance_relation3808 = new BitSet(new long[]{0x4000000000000020L});
    public static final BitSet FOLLOW_62_in_inheritance_relation3816 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_multiplicity_in_inheritance_relation3818 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_63_in_inheritance_relation3822 = new BitSet(new long[]{0x4000000000000020L});
    public static final BitSet FOLLOW_parent_in_inheritance_relation3839 = new BitSet(new long[]{0x0000000000000012L});
    public static final BitSet FOLLOW_semantic_label_in_inheritance_relation3850 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_client_in_client_relation3909 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000001L});
    public static final BitSet FOLLOW_64_in_client_relation3911 = new BitSet(new long[]{0x4000000400000020L,0x0000000000000020L});
    public static final BitSet FOLLOW_client_entities_in_client_relation3916 = new BitSet(new long[]{0x4000000400000020L,0x0000000000000020L});
    public static final BitSet FOLLOW_type_mark_in_client_relation3928 = new BitSet(new long[]{0x4000000400000020L,0x0000000000000020L});
    public static final BitSet FOLLOW_supplier_in_client_relation3954 = new BitSet(new long[]{0x0000000000000012L});
    public static final BitSet FOLLOW_semantic_label_in_client_relation3964 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_62_in_client_entities4005 = new BitSet(new long[]{0x00000400000000A0L,0x0000000000028016L});
    public static final BitSet FOLLOW_client_entity_expression_in_client_entities4009 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_63_in_client_entities4011 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_client_entity_list_in_client_entity_expression4050 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_multiplicity_in_client_entity_expression4063 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_client_entity_in_client_entity_list4116 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_client_entity_list4125 = new BitSet(new long[]{0x0000040000000020L,0x0000000000028016L});
    public static final BitSet FOLLOW_client_entity_in_client_entity_list4129 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_prefix_in_client_entity4180 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_infix_in_client_entity4185 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_supplier_indirection_in_client_entity4190 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_parent_indirection_in_client_entity4201 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indirection_feature_part_in_supplier_indirection4247 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_34_in_supplier_indirection4251 = new BitSet(new long[]{0x0000040000000020L,0x0000000000028014L});
    public static final BitSet FOLLOW_generic_indirection_in_supplier_indirection4260 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_name_in_indirection_feature_part4309 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indirection_feature_list_in_indirection_feature_part4320 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_42_in_indirection_feature_list4370 = new BitSet(new long[]{0x0000000000000020L,0x0000000000028000L});
    public static final BitSet FOLLOW_feature_name_list_in_indirection_feature_list4374 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_43_in_indirection_feature_list4378 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_65_in_parent_indirection4426 = new BitSet(new long[]{0x0000040000000020L,0x0000000000028014L});
    public static final BitSet FOLLOW_generic_indirection_in_parent_indirection4430 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indirection_element_in_generic_indirection4482 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_named_indirection4527 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000004L});
    public static final BitSet FOLLOW_66_in_named_indirection4529 = new BitSet(new long[]{0x0000040000000020L,0x0000000000028014L});
    public static final BitSet FOLLOW_indirection_list_in_named_indirection4533 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_67_in_named_indirection4537 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_66_in_named_indirection4552 = new BitSet(new long[]{0x0000040000000020L,0x0000000000028014L});
    public static final BitSet FOLLOW_indirection_list_in_named_indirection4554 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_67_in_named_indirection4556 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indirection_element_in_indirection_list4603 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_indirection_list4613 = new BitSet(new long[]{0x0000040000000020L,0x0000000000028014L});
    public static final BitSet FOLLOW_indirection_element_in_indirection_list4617 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_68_in_indirection_element4671 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_named_indirection_in_indirection_element4681 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_indirection_element4692 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_34_in_type_mark4737 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_69_in_type_mark4750 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_shared_mark_in_type_mark4763 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_34_in_shared_mark4809 = new BitSet(new long[]{0x0000040000000000L});
    public static final BitSet FOLLOW_42_in_shared_mark4811 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_multiplicity_in_shared_mark4815 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_43_in_shared_mark4819 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_ref_in_child4843 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_ref_in_parent4871 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_ref_in_client4909 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_ref_in_supplier4939 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_component_name_in_static_ref4973 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cluster_prefix_in_static_ref4989 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_static_component_name_in_static_ref4993 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_prefix5032 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_cluster_prefix5041 = new BitSet(new long[]{0x0000000000000022L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_prefix5050 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_cluster_prefix5052 = new BitSet(new long[]{0x0000000000000022L});
    public static final BitSet FOLLOW_IDENTIFIER_in_static_component_name5084 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_INTEGER_in_multiplicity5128 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_semantic_label5164 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_interface_start_indexing_in_class_interface5190 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_interface_start_inherit_in_class_interface5200 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_interface_start_features_in_class_interface5210 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_interface_start_invariant_in_class_interface5220 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indexing_in_class_interface_start_indexing5242 = new BitSet(new long[]{0x0000004042000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_parent_class_list_in_class_interface_start_indexing5254 = new BitSet(new long[]{0x0000004042000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_features_in_class_interface_start_indexing5267 = new BitSet(new long[]{0x0000004042000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_class_invariant_in_class_interface_start_indexing5281 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_class_interface_start_indexing5292 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_parent_class_list_in_class_interface_start_inherit5318 = new BitSet(new long[]{0x0000004042000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_features_in_class_interface_start_inherit5328 = new BitSet(new long[]{0x0000004042000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_class_invariant_in_class_interface_start_inherit5342 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_class_interface_start_inherit5353 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_features_in_class_interface_start_features5377 = new BitSet(new long[]{0x0000004042000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_class_invariant_in_class_interface_start_features5388 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_class_interface_start_features5399 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_invariant_in_class_interface_start_invariant5425 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_class_interface_start_invariant5433 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_71_in_class_invariant5452 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_assertion_in_class_invariant5454 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_38_in_parent_class_list5495 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_type_in_parent_class_list5499 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_parent_class_list5510 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_type_in_parent_class_list5514 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_parent_class_list5531 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_38_in_parent_class_list5542 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_clause_in_features5586 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000100L});
    public static final BitSet FOLLOW_72_in_feature_clause5627 = new BitSet(new long[]{0x4C00000000000060L,0x0000000000028200L});
    public static final BitSet FOLLOW_selective_export_in_feature_clause5637 = new BitSet(new long[]{0x4C00000000000060L,0x0000000000028200L});
    public static final BitSet FOLLOW_COMMENT_in_feature_clause5659 = new BitSet(new long[]{0x4C00000000000060L,0x0000000000028200L});
    public static final BitSet FOLLOW_feature_specifications_in_feature_clause5671 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_specification_in_feature_specifications5714 = new BitSet(new long[]{0x4C00000000000062L,0x0000000000028200L});
    public static final BitSet FOLLOW_58_in_feature_specification5769 = new BitSet(new long[]{0x0000000000000020L,0x0000000000028000L});
    public static final BitSet FOLLOW_59_in_feature_specification5782 = new BitSet(new long[]{0x0000000000000020L,0x0000000000028000L});
    public static final BitSet FOLLOW_73_in_feature_specification5793 = new BitSet(new long[]{0x0000000000000020L,0x0000000000028000L});
    public static final BitSet FOLLOW_feature_name_list_in_feature_specification5824 = new BitSet(new long[]{0x4000000400000042L,0x0000000000005822L});
    public static final BitSet FOLLOW_has_type_in_feature_specification5833 = new BitSet(new long[]{0x4000000000000042L,0x0000000000005802L});
    public static final BitSet FOLLOW_rename_clause_in_feature_specification5845 = new BitSet(new long[]{0x0000000000000042L,0x0000000000005802L});
    public static final BitSet FOLLOW_COMMENT_in_feature_specification5857 = new BitSet(new long[]{0x0000000000000002L,0x0000000000005802L});
    public static final BitSet FOLLOW_feature_arguments_in_feature_specification5871 = new BitSet(new long[]{0x0000000000000002L,0x0000000000001800L});
    public static final BitSet FOLLOW_contract_clause_in_feature_specification5898 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_type_mark_in_has_type5961 = new BitSet(new long[]{0x0000000000000020L,0x0000000000000400L});
    public static final BitSet FOLLOW_type_in_has_type5969 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_74_in_has_type5986 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_contracting_conditions_in_contract_clause6017 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_contract_clause6019 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_precondition_in_contracting_conditions6051 = new BitSet(new long[]{0x0000000000000002L,0x0000000000001800L});
    public static final BitSet FOLLOW_postcondition_in_contracting_conditions6056 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_postcondition_in_contracting_conditions6080 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_75_in_precondition6106 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_assertion_in_precondition6108 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_76_in_postcondition6142 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_assertion_in_postcondition6144 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_62_in_selective_export6167 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_list_in_selective_export6171 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_63_in_selective_export6173 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_name_in_feature_name_list6218 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_feature_name_list6228 = new BitSet(new long[]{0x0000000000000020L,0x0000000000028000L});
    public static final BitSet FOLLOW_feature_name_in_feature_name_list6232 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_feature_name6281 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_prefix_in_feature_name6291 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_infix_in_feature_name6297 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_62_in_rename_clause6327 = new BitSet(new long[]{0x0000000000000000L,0x0000000000002000L});
    public static final BitSet FOLLOW_renaming_in_rename_clause6329 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_63_in_rename_clause6331 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_77_in_renaming6367 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_in_renaming6369 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_renaming6371 = new BitSet(new long[]{0x0000000000000020L,0x0000000000028000L});
    public static final BitSet FOLLOW_feature_name_in_renaming6373 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_argument_in_feature_arguments6408 = new BitSet(new long[]{0x0000000000000002L,0x0000000000004002L});
    public static final BitSet FOLLOW_set_in_feature_argument6448 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_identifier_list_in_feature_argument6472 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_34_in_feature_argument6474 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_type_in_feature_argument6478 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_type_in_feature_argument6510 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_identifier_list6570 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_identifier_list6580 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_IDENTIFIER_in_identifier_list6584 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_79_in_prefix6601 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010000L});
    public static final BitSet FOLLOW_80_in_prefix6603 = new BitSet(new long[]{0x0000000000000000L,0x0000718000000000L});
    public static final BitSet FOLLOW_prefix_operator_in_prefix6605 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010000L});
    public static final BitSet FOLLOW_80_in_prefix6607 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_81_in_infix6626 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010000L});
    public static final BitSet FOLLOW_80_in_infix6628 = new BitSet(new long[]{0x0000000400000000L,0x01FFCFC000402002L});
    public static final BitSet FOLLOW_infix_operator_in_infix6630 = new BitSet(new long[]{0x0000000000000000L,0x0000000000010000L});
    public static final BitSet FOLLOW_80_in_infix6632 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unary_in_prefix_operator6652 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_binary_in_infix_operator6667 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_66_in_formal_generics6686 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_formal_generic_list_in_formal_generics6690 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_67_in_formal_generics6692 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_formal_generic_in_formal_generic_list6735 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_formal_generic_list6744 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_formal_generic_in_formal_generic_list6748 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_formal_generic_name_in_formal_generic6798 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_formal_generic_name_in_formal_generic6810 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000002L});
    public static final BitSet FOLLOW_65_in_formal_generic6812 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_type_in_formal_generic6816 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_formal_generic_name6855 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_class_type6900 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000004L});
    public static final BitSet FOLLOW_actual_generics_in_class_type6908 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_66_in_actual_generics6979 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_type_list_in_actual_generics6981 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_67_in_actual_generics6983 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_type_in_type_list7047 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_type_list7075 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_type_in_type_list7079 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_type7134 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000004L});
    public static final BitSet FOLLOW_actual_generics_in_type7156 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_assertion_clause_in_assertion7235 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_assertion7244 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_assertion_clause_in_assertion7248 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_assertion7265 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_boolean_expression_in_assertion_clause7294 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_expression_in_boolean_expression7316 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_quantifier_in_quantification7356 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_range_expression_in_quantification7363 = new BitSet(new long[]{0x0000000000000000L,0x0000000000300000L});
    public static final BitSet FOLLOW_restriction_in_quantification7371 = new BitSet(new long[]{0x0000000000000000L,0x0000000000300000L});
    public static final BitSet FOLLOW_proposition_in_quantification7383 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_82_in_quantifier7422 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_83_in_quantifier7435 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_variable_range_in_range_expression7473 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_range_expression7483 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_variable_range_in_range_expression7487 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_range_expression7502 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_84_in_restriction7539 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_boolean_expression_in_restriction7543 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_85_in_proposition7577 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_boolean_expression_in_proposition7581 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_member_range_in_variable_range7617 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_type_range_in_variable_range7629 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_identifier_list_in_member_range7669 = new BitSet(new long[]{0x0000000000000000L,0x0000000000400000L});
    public static final BitSet FOLLOW_86_in_member_range7671 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_expression_in_member_range7675 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_identifier_list_in_type_range7711 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_34_in_type_range7713 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_type_in_type_range7717 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unqualified_call_in_call_chain7777 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_call_chain7786 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F000400L});
    public static final BitSet FOLLOW_unqualified_call_in_call_chain7790 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_IDENTIFIER_in_unqualified_call7831 = new BitSet(new long[]{0x0000040000000002L});
    public static final BitSet FOLLOW_actual_arguments_in_unqualified_call7845 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_42_in_actual_arguments7884 = new BitSet(new long[]{0x40000C00000003B0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_expression_list_in_actual_arguments7894 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_43_in_actual_arguments7917 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_expression_in_expression_list7953 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_expression_list7963 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_expression_in_expression_list7967 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_62_in_enumerated_set8013 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_enumeration_list_in_enumerated_set8017 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_63_in_enumerated_set8019 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_enumeration_element_in_enumeration_list8061 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_enumeration_list8071 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_enumeration_element_in_enumeration_list8075 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_expression_in_enumeration_element8107 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_interval_in_enumeration_element8121 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_integer_interval_in_interval8168 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_character_interval_in_interval8180 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_integer_constant_in_integer_interval8213 = new BitSet(new long[]{0x0000000000000000L,0x0000000000800000L});
    public static final BitSet FOLLOW_87_in_integer_interval8215 = new BitSet(new long[]{0x0000000000000080L,0x0000018000000000L});
    public static final BitSet FOLLOW_integer_constant_in_integer_interval8219 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_character_constant_in_character_interval8261 = new BitSet(new long[]{0x0000000000000000L,0x0000000000800000L});
    public static final BitSet FOLLOW_87_in_character_interval8263 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_character_constant_in_character_interval8267 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_constant_in_constant8293 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_88_in_constant8306 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_74_in_constant8319 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_89_in_constant8343 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_boolean_constant_in_manifest_constant8366 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_character_constant_in_manifest_constant8379 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_integer_constant_in_manifest_constant8392 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_real_constant_in_manifest_constant8405 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_manifest_constant8418 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_enumerated_set_in_manifest_constant8431 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_in_sign8470 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_90_in_boolean_constant8496 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_91_in_boolean_constant8507 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CHARACTER_CONSTANT_in_character_constant8531 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_integer_constant8597 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_INTEGER_in_integer_constant8608 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_real_constant8653 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_REAL_in_real_constant8665 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_92_in_dynamic_diagram8696 = new BitSet(new long[]{0x00800000000000E0L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_diagram8704 = new BitSet(new long[]{0x0080000000000040L});
    public static final BitSet FOLLOW_COMMENT_in_dynamic_diagram8717 = new BitSet(new long[]{0x0080000000000000L});
    public static final BitSet FOLLOW_55_in_dynamic_diagram8726 = new BitSet(new long[]{0x00040000020000A0L,0x00000003C0000000L});
    public static final BitSet FOLLOW_dynamic_block_in_dynamic_diagram8735 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_dynamic_diagram8759 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_dynamic_component_in_dynamic_block8802 = new BitSet(new long[]{0x00040000000000A2L,0x00000003C0000000L});
    public static final BitSet FOLLOW_scenario_description_in_dynamic_component8839 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_object_group_in_dynamic_component8844 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_object_stack_in_dynamic_component8850 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_object_in_dynamic_component8855 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_message_relation_in_dynamic_component8860 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_50_in_scenario_description8888 = new BitSet(new long[]{0x0000000000000810L});
    public static final BitSet FOLLOW_scenario_name_in_scenario_description8890 = new BitSet(new long[]{0x0000000000000040L,0x0000000020000000L});
    public static final BitSet FOLLOW_COMMENT_in_scenario_description8898 = new BitSet(new long[]{0x0000000000000000L,0x0000000020000000L});
    public static final BitSet FOLLOW_93_in_scenario_description8907 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_labelled_actions_in_scenario_description8914 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_scenario_description8921 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_labelled_action_in_labelled_actions8969 = new BitSet(new long[]{0x0000000000000012L});
    public static final BitSet FOLLOW_action_label_in_labelled_action9010 = new BitSet(new long[]{0x0000000000000810L});
    public static final BitSet FOLLOW_action_description_in_labelled_action9014 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_action_label9053 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_action_description9088 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_scenario_name9129 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_94_in_object_group9162 = new BitSet(new long[]{0x0000000000000000L,0x0000000080000000L});
    public static final BitSet FOLLOW_95_in_object_group9187 = new BitSet(new long[]{0x00000000000000A0L});
    public static final BitSet FOLLOW_group_name_in_object_group9193 = new BitSet(new long[]{0x0080000000000042L});
    public static final BitSet FOLLOW_COMMENT_in_object_group9205 = new BitSet(new long[]{0x0080000000000002L});
    public static final BitSet FOLLOW_group_components_in_object_group9220 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_55_in_group_components9271 = new BitSet(new long[]{0x00040000000000A0L,0x00000003C0000000L});
    public static final BitSet FOLLOW_dynamic_block_in_group_components9273 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_group_components9275 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_96_in_object_stack9320 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_object_name_in_object_stack9327 = new BitSet(new long[]{0x0000000000000042L});
    public static final BitSet FOLLOW_COMMENT_in_object_stack9339 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_97_in_object9387 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_object_name_in_object9394 = new BitSet(new long[]{0x0000000000000042L});
    public static final BitSet FOLLOW_COMMENT_in_object9406 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_caller_in_message_relation9430 = new BitSet(new long[]{0x0000000000000000L,0x0000000400000000L});
    public static final BitSet FOLLOW_98_in_message_relation9432 = new BitSet(new long[]{0x00040000000000A0L,0x00000003C0000000L});
    public static final BitSet FOLLOW_receiver_in_message_relation9434 = new BitSet(new long[]{0x0000000000000012L});
    public static final BitSet FOLLOW_message_label_in_message_relation9437 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_dynamic_ref_in_caller9469 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_dynamic_ref_in_receiver9489 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_ref9515 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_dynamic_ref9518 = new BitSet(new long[]{0x00000000000000A0L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_ref9520 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_IDENTIFIER_in_dynamic_component_name9551 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_dynamic_component_name9554 = new BitSet(new long[]{0x00000000000000A0L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_component_name9556 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_INTEGER_in_dynamic_component_name9565 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_object_name9588 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_object_name9598 = new BitSet(new long[]{0x00000000000000A0L});
    public static final BitSet FOLLOW_extended_id_in_object_name9602 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_extended_id_in_group_name9642 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_message_label9675 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_change_string_marks_in_notational_tuning9699 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_change_concatenator_in_notational_tuning9705 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_change_prefix_in_notational_tuning9710 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_99_in_change_string_marks9725 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_string_marks9727 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_string_marks9729 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_100_in_change_concatenator9763 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_concatenator9765 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_101_in_change_prefix9799 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_prefix9801 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_equivalence_expression_in_expression9827 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_quantification_in_expression9841 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_implies_expression_in_equivalence_expression9863 = new BitSet(new long[]{0x0000000000000002L,0x0000004000000000L});
    public static final BitSet FOLLOW_102_in_equivalence_expression9873 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F000400L});
    public static final BitSet FOLLOW_implies_expression_in_equivalence_expression9877 = new BitSet(new long[]{0x0000000000000002L,0x0000004000000000L});
    public static final BitSet FOLLOW_and_or_xor_expression_in_implies_expression9905 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000002L});
    public static final BitSet FOLLOW_65_in_implies_expression9915 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F000400L});
    public static final BitSet FOLLOW_implies_expression_in_implies_expression9919 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_comparison_expression_in_and_or_xor_expression9946 = new BitSet(new long[]{0x0000000000000002L,0x00000E0000000000L});
    public static final BitSet FOLLOW_and_or_xor_op_in_and_or_xor_expression9959 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F000400L});
    public static final BitSet FOLLOW_comparison_expression_in_and_or_xor_expression9963 = new BitSet(new long[]{0x0000000000000002L,0x00000E0000000000L});
    public static final BitSet FOLLOW_add_sub_expression_in_comparison_expression9991 = new BitSet(new long[]{0x0000000400000002L,0x001FC00000400000L});
    public static final BitSet FOLLOW_comparison_op_in_comparison_expression10003 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F000400L});
    public static final BitSet FOLLOW_add_sub_expression_in_comparison_expression10008 = new BitSet(new long[]{0x0000000400000002L,0x001FC00000400000L});
    public static final BitSet FOLLOW_mul_div_expression_in_add_sub_expression10036 = new BitSet(new long[]{0x0000000000000002L,0x0000018000000000L});
    public static final BitSet FOLLOW_add_sub_op_in_add_sub_expression10048 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F000400L});
    public static final BitSet FOLLOW_mul_div_expression_in_add_sub_expression10052 = new BitSet(new long[]{0x0000000000000002L,0x0000018000000000L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mul_div_expression10080 = new BitSet(new long[]{0x0000000000000002L,0x00E0000000000000L});
    public static final BitSet FOLLOW_mul_div_op_in_mul_div_expression10092 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F000400L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mul_div_expression10096 = new BitSet(new long[]{0x0000000000000002L,0x00E0000000000000L});
    public static final BitSet FOLLOW_lowest_expression_in_mod_pow_expression10125 = new BitSet(new long[]{0x0000000000000002L,0x0100000000002000L});
    public static final BitSet FOLLOW_mod_pow_op_in_mod_pow_expression10137 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F000400L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mod_pow_expression10141 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constant_in_lowest_expression10174 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_lowest_expression10183 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F000400L});
    public static final BitSet FOLLOW_call_chain_in_lowest_expression10187 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unary_in_lowest_expression10237 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F000400L});
    public static final BitSet FOLLOW_lowest_expression_in_lowest_expression10241 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_42_in_lowest_expression10254 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F0C0400L});
    public static final BitSet FOLLOW_expression_in_lowest_expression10258 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_43_in_lowest_expression10260 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_lowest_expression10270 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F000400L});
    public static final BitSet FOLLOW_call_chain_in_lowest_expression10274 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_call_chain_in_lowest_expression10310 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_103_in_add_sub_op10334 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_104_in_add_sub_op10342 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_103_in_add_sub_op_unary10360 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_104_in_add_sub_op_unary10368 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_105_in_and_or_xor_op10386 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_106_in_and_or_xor_op10393 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_107_in_and_or_xor_op10401 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_other_unary_in_unary10421 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_unary_in_unary10435 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_108_in_other_unary10455 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_109_in_other_unary10463 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_110_in_other_unary10472 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_in_binary10503 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_mul_div_op_in_binary10507 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_comparison_op_in_binary10511 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_mod_pow_op_in_binary10526 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_and_or_xor_op_in_binary10530 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_65_in_binary10545 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_102_in_binary10549 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_111_in_comparison_op10565 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_112_in_comparison_op10573 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_113_in_comparison_op10581 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_114_in_comparison_op10588 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_115_in_comparison_op10595 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_116_in_comparison_op10603 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_86_in_comparison_op10610 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_110_in_comparison_op10617 = new BitSet(new long[]{0x0000000000000000L,0x0000000000400000L});
    public static final BitSet FOLLOW_86_in_comparison_op10619 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_34_in_comparison_op10626 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_117_in_mul_div_op10653 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_118_in_mul_div_op10661 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_119_in_mul_div_op10669 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_120_in_mod_pow_op10702 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_77_in_mod_pow_op10710 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_manifest_textblock11022 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_START_in_manifest_textblock11028 = new BitSet(new long[]{0x0000000000003000L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_MIDDLE_in_manifest_textblock11030 = new BitSet(new long[]{0x0000000000003000L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_END_in_manifest_textblock11033 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constant_in_synpred1_BON10170 = new BitSet(new long[]{0x0000000000000002L});

}