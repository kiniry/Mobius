// $ANTLR 3.1.3 Apr 15, 2009 15:48:38 BON.g 2009-09-01 13:59:51

  package ie.ucd.bon.parser; 
  
  import ie.ucd.bon.parser.errors.MissingElementParseError;
  import ie.ucd.bon.ast.*;


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
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "MANIFEST_STRING", "IDENTIFIER", "COMMENT", "INTEGER", "CHARACTER_CONSTANT", "REAL", "NEWLINE", "MANIFEST_TEXTBLOCK_START", "MANIFEST_TEXTBLOCK_MIDDLE", "MANIFEST_TEXTBLOCK_END", "LINE_COMMENT", "COMMENT_START", "DIGIT", "ALPHA", "ALPHANUMERIC_OR_UNDERSCORE", "ALPHANUMERIC", "UNDERSCORE", "LOWER", "UPPER", "WHITESPACE", "'dictionary'", "'end'", "'class'", "'cluster'", "'system_chart'", "'explanation'", "'indexing'", "'part'", "'description'", "';'", "':'", "','", "'cluster_chart'", "'class_chart'", "'inherit'", "'query'", "'command'", "'constraint'", "'('", "')'", "'event_chart'", "'incoming'", "'outgoing'", "'event'", "'involves'", "'scenario_chart'", "'scenario'", "'creation_chart'", "'creator'", "'creates'", "'static_diagram'", "'component'", "'reused'", "'root'", "'deferred'", "'effective'", "'persistent'", "'interfaced'", "'{'", "'}'", "'client'", "'->'", "'['", "']'", "'...'", "':{'", "'.'", "'invariant'", "'feature'", "'redefined'", "'require'", "'ensure'", "'^'", "'<-'", "'prefix'", "'\"'", "'infix'", "'for_all'", "'exists'", "'such_that'", "'it_holds'", "'member_of'", "'..'", "'Current'", "'Void'", "'Result'", "'true'", "'false'", "'dynamic_diagram'", "'action'", "'nameless'", "'object_group'", "'object_stack'", "'object'", "'calls'", "'string_marks'", "'concatenator'", "'keyword_prefix'", "'<->'", "'+'", "'-'", "'and'", "'or'", "'xor'", "'delta'", "'old'", "'not'", "'<'", "'>'", "'<='", "'>='", "'='", "'/='", "'*'", "'/'", "'//'", "'\\\\\\\\'"
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


    //Currently nothing, everything in BONAbstractParser	



    // $ANTLR start "prog"
    // BON.g:31:1: prog returns [BonSourceFile bonSource] : (bs= bon_specification EOF | i= indexing bs= bon_specification EOF | e= EOF | indexing e= EOF );
    public final BonSourceFile prog() throws RecognitionException {
        BonSourceFile bonSource = null;

        Token e=null;
        BONParser.bon_specification_return bs = null;

        BONParser.indexing_return i = null;


        try {
            // BON.g:37:40: (bs= bon_specification EOF | i= indexing bs= bon_specification EOF | e= EOF | indexing e= EOF )
            int alt1=4;
            alt1 = dfa1.predict(input);
            switch (alt1) {
                case 1 :
                    // BON.g:38:10: bs= bon_specification EOF
                    {
                    pushFollow(FOLLOW_bon_specification_in_prog70);
                    bs=bon_specification();

                    state._fsp--;
                    if (state.failed) return bonSource;
                    match(input,EOF,FOLLOW_EOF_in_prog72); if (state.failed) return bonSource;
                    if ( state.backtracking==0 ) {
                       bonSource = BonSourceFile.mk((bs!=null?bs.spec_els:null), null, getSLoc((bs!=null?((Token)bs.start):null), (bs!=null?((Token)bs.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:41:10: i= indexing bs= bon_specification EOF
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
                       bonSource = BonSourceFile.mk((bs!=null?bs.spec_els:null), (i!=null?i.indexing:null), getSLoc((i!=null?((Token)i.start):null), (bs!=null?((Token)bs.stop):null))); 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:44:10: e= EOF
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
                    // BON.g:48:10: indexing e= EOF
                    {
                    pushFollow(FOLLOW_indexing_in_prog188);
                    indexing();

                    state._fsp--;
                    if (state.failed) return bonSource;
                    e=(Token)match(input,EOF,FOLLOW_EOF_in_prog192); if (state.failed) return bonSource;
                    if ( state.backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(e), "at least one specification entry", "in source file", true)); 
                    }
                    if ( state.backtracking==0 ) {
                       bonSource = BonSourceFile.mk(Constants.NO_SPEC_ELEMS, (i!=null?i.indexing:null), getSLoc((i!=null?((Token)i.start):null),(i!=null?((Token)i.stop):null))); 
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
    // BON.g:53:1: bon_specification returns [List<SpecificationElement> spec_els] : (se= specification_element )+ ;
    public final BONParser.bon_specification_return bon_specification() throws RecognitionException {
        BONParser.bon_specification_return retval = new BONParser.bon_specification_return();
        retval.start = input.LT(1);

        SpecificationElement se = null;


        try {
            // BON.g:57:65: ( (se= specification_element )+ )
            // BON.g:58:3: (se= specification_element )+
            {
            if ( state.backtracking==0 ) {
               retval.spec_els = createList(); 
            }
            // BON.g:59:3: (se= specification_element )+
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
            	    // BON.g:59:5: se= specification_element
            	    {
            	    pushFollow(FOLLOW_specification_element_in_bon_specification241);
            	    se=specification_element();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       retval.spec_els.add(se); 
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
    // BON.g:64:1: specification_element returns [SpecificationElement se] : (ic= informal_chart | cd= class_dictionary | sd= static_diagram | dd= dynamic_diagram );
    public final SpecificationElement specification_element() throws RecognitionException {
        SpecificationElement se = null;

        InformalChart ic = null;

        ClassDictionary cd = null;

        StaticDiagram sd = null;

        DynamicDiagram dd = null;


        try {
            // BON.g:64:57: (ic= informal_chart | cd= class_dictionary | sd= static_diagram | dd= dynamic_diagram )
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
                    // BON.g:65:5: ic= informal_chart
                    {
                    pushFollow(FOLLOW_informal_chart_in_specification_element272);
                    ic=informal_chart();

                    state._fsp--;
                    if (state.failed) return se;
                    if ( state.backtracking==0 ) {
                       se = ic; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:67:5: cd= class_dictionary
                    {
                    pushFollow(FOLLOW_class_dictionary_in_specification_element286);
                    cd=class_dictionary();

                    state._fsp--;
                    if (state.failed) return se;
                    if ( state.backtracking==0 ) {
                       se = cd; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:69:5: sd= static_diagram
                    {
                    pushFollow(FOLLOW_static_diagram_in_specification_element300);
                    sd=static_diagram();

                    state._fsp--;
                    if (state.failed) return se;
                    if ( state.backtracking==0 ) {
                       se = sd; 
                    }

                    }
                    break;
                case 4 :
                    // BON.g:71:5: dd= dynamic_diagram
                    {
                    pushFollow(FOLLOW_dynamic_diagram_in_specification_element314);
                    dd=dynamic_diagram();

                    state._fsp--;
                    if (state.failed) return se;
                    if ( state.backtracking==0 ) {
                       se = dd; 
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
    // BON.g:77:1: informal_chart returns [InformalChart ic] : ( system_chart | cluster_chart | class_chart | event_chart | scenario_chart | creation_chart );
    public final InformalChart informal_chart() throws RecognitionException {
        InformalChart ic = null;

        ClusterChart system_chart1 = null;

        ClusterChart cluster_chart2 = null;

        ClassChart class_chart3 = null;

        EventChart event_chart4 = null;

        ScenarioChart scenario_chart5 = null;

        BONParser.creation_chart_return creation_chart6 = null;


        try {
            // BON.g:81:43: ( system_chart | cluster_chart | class_chart | event_chart | scenario_chart | creation_chart )
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
                    // BON.g:82:5: system_chart
                    {
                    pushFollow(FOLLOW_system_chart_in_informal_chart342);
                    system_chart1=system_chart();

                    state._fsp--;
                    if (state.failed) return ic;
                    if ( state.backtracking==0 ) {
                       ic = system_chart1; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:84:5: cluster_chart
                    {
                    pushFollow(FOLLOW_cluster_chart_in_informal_chart354);
                    cluster_chart2=cluster_chart();

                    state._fsp--;
                    if (state.failed) return ic;
                    if ( state.backtracking==0 ) {
                       ic = cluster_chart2; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:86:5: class_chart
                    {
                    pushFollow(FOLLOW_class_chart_in_informal_chart366);
                    class_chart3=class_chart();

                    state._fsp--;
                    if (state.failed) return ic;
                    if ( state.backtracking==0 ) {
                       ic = class_chart3; 
                    }

                    }
                    break;
                case 4 :
                    // BON.g:88:5: event_chart
                    {
                    pushFollow(FOLLOW_event_chart_in_informal_chart378);
                    event_chart4=event_chart();

                    state._fsp--;
                    if (state.failed) return ic;
                    if ( state.backtracking==0 ) {
                       ic = event_chart4; 
                    }

                    }
                    break;
                case 5 :
                    // BON.g:90:5: scenario_chart
                    {
                    pushFollow(FOLLOW_scenario_chart_in_informal_chart390);
                    scenario_chart5=scenario_chart();

                    state._fsp--;
                    if (state.failed) return ic;
                    if ( state.backtracking==0 ) {
                       ic = scenario_chart5; 
                    }

                    }
                    break;
                case 6 :
                    // BON.g:92:5: creation_chart
                    {
                    pushFollow(FOLLOW_creation_chart_in_informal_chart402);
                    creation_chart6=creation_chart();

                    state._fsp--;
                    if (state.failed) return ic;
                    if ( state.backtracking==0 ) {
                       ic = (creation_chart6!=null?creation_chart6.cc:null); 
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
    // BON.g:96:1: class_dictionary returns [ClassDictionary cd] : d= 'dictionary' system_name ( indexing )? ( explanation )? ( part )? (de= dictionary_entry )+ e= 'end' ;
    public final ClassDictionary class_dictionary() throws RecognitionException {
        ClassDictionary cd = null;

        Token d=null;
        Token e=null;
        DictionaryEntry de = null;

        BONParser.indexing_return indexing7 = null;

        String explanation8 = null;

        String part9 = null;

        String system_name10 = null;


         Indexing index = null; String expl = null; String p = null; 
                List<DictionaryEntry> entries = createList(); 
        try {
            // BON.g:99:1: (d= 'dictionary' system_name ( indexing )? ( explanation )? ( part )? (de= dictionary_entry )+ e= 'end' )
            // BON.g:100:3: d= 'dictionary' system_name ( indexing )? ( explanation )? ( part )? (de= dictionary_entry )+ e= 'end'
            {
            d=(Token)match(input,24,FOLLOW_24_in_class_dictionary437); if (state.failed) return cd;
            pushFollow(FOLLOW_system_name_in_class_dictionary442);
            system_name10=system_name();

            state._fsp--;
            if (state.failed) return cd;
            // BON.g:102:3: ( indexing )?
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0==30) ) {
                alt5=1;
            }
            switch (alt5) {
                case 1 :
                    // BON.g:102:4: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_class_dictionary448);
                    indexing7=indexing();

                    state._fsp--;
                    if (state.failed) return cd;
                    if ( state.backtracking==0 ) {
                       index = (indexing7!=null?indexing7.indexing:null); 
                    }

                    }
                    break;

            }

            // BON.g:103:3: ( explanation )?
            int alt6=2;
            int LA6_0 = input.LA(1);

            if ( (LA6_0==29) ) {
                alt6=1;
            }
            switch (alt6) {
                case 1 :
                    // BON.g:103:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_class_dictionary458);
                    explanation8=explanation();

                    state._fsp--;
                    if (state.failed) return cd;
                    if ( state.backtracking==0 ) {
                       expl = explanation8; 
                    }

                    }
                    break;

            }

            // BON.g:104:3: ( part )?
            int alt7=2;
            int LA7_0 = input.LA(1);

            if ( (LA7_0==31) ) {
                alt7=1;
            }
            switch (alt7) {
                case 1 :
                    // BON.g:104:4: part
                    {
                    pushFollow(FOLLOW_part_in_class_dictionary469);
                    part9=part();

                    state._fsp--;
                    if (state.failed) return cd;
                    if ( state.backtracking==0 ) {
                       p = part9; 
                    }

                    }
                    break;

            }

            // BON.g:105:3: (de= dictionary_entry )+
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
            	    // BON.g:105:4: de= dictionary_entry
            	    {
            	    pushFollow(FOLLOW_dictionary_entry_in_class_dictionary482);
            	    de=dictionary_entry();

            	    state._fsp--;
            	    if (state.failed) return cd;
            	    if ( state.backtracking==0 ) {
            	       entries.add(de); 
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
               cd = ClassDictionary.mk(system_name10, entries, index, expl, p, getSLoc(d,e)); 
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
    // BON.g:112:1: dictionary_entry returns [DictionaryEntry entry] : c= 'class' class_name 'cluster' cluster_name_list description ;
    public final DictionaryEntry dictionary_entry() throws RecognitionException {
        DictionaryEntry entry = null;

        Token c=null;
        BONParser.class_name_return class_name11 = null;

        List<String> cluster_name_list12 = null;

        BONParser.description_return description13 = null;


        try {
            // BON.g:112:50: (c= 'class' class_name 'cluster' cluster_name_list description )
            // BON.g:113:3: c= 'class' class_name 'cluster' cluster_name_list description
            {
            c=(Token)match(input,26,FOLLOW_26_in_dictionary_entry525); if (state.failed) return entry;
            pushFollow(FOLLOW_class_name_in_dictionary_entry527);
            class_name11=class_name();

            state._fsp--;
            if (state.failed) return entry;
            match(input,27,FOLLOW_27_in_dictionary_entry532); if (state.failed) return entry;
            pushFollow(FOLLOW_cluster_name_list_in_dictionary_entry534);
            cluster_name_list12=cluster_name_list();

            state._fsp--;
            if (state.failed) return entry;
            pushFollow(FOLLOW_description_in_dictionary_entry539);
            description13=description();

            state._fsp--;
            if (state.failed) return entry;
            if ( state.backtracking==0 ) {
               entry = DictionaryEntry.mk((class_name11!=null?input.toString(class_name11.start,class_name11.stop):null), cluster_name_list12, (description13!=null?input.toString(description13.start,description13.stop):null), getSLoc(c, (description13!=null?((Token)description13.stop):null))); 
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
    // BON.g:119:1: system_chart returns [ClusterChart sc] : s= 'system_chart' system_name ( indexing )? ( explanation )? ( part )? (ce= cluster_entries | ) e= 'end' ;
    public final ClusterChart system_chart() throws RecognitionException {
        ClusterChart sc = null;

        Token s=null;
        Token e=null;
        List<ClusterEntry> ce = null;

        BONParser.indexing_return indexing14 = null;

        String explanation15 = null;

        String part16 = null;

        String system_name17 = null;


         Indexing index = null; String expl = null; String p = null; 
                List<ClusterEntry> entries = null; 
        try {
            // BON.g:124:1: (s= 'system_chart' system_name ( indexing )? ( explanation )? ( part )? (ce= cluster_entries | ) e= 'end' )
            // BON.g:125:3: s= 'system_chart' system_name ( indexing )? ( explanation )? ( part )? (ce= cluster_entries | ) e= 'end'
            {
            s=(Token)match(input,28,FOLLOW_28_in_system_chart570); if (state.failed) return sc;
            pushFollow(FOLLOW_system_name_in_system_chart575);
            system_name17=system_name();

            state._fsp--;
            if (state.failed) return sc;
            // BON.g:127:3: ( indexing )?
            int alt9=2;
            int LA9_0 = input.LA(1);

            if ( (LA9_0==30) ) {
                alt9=1;
            }
            switch (alt9) {
                case 1 :
                    // BON.g:127:4: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_system_chart581);
                    indexing14=indexing();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       index = (indexing14!=null?indexing14.indexing:null); 
                    }

                    }
                    break;

            }

            // BON.g:128:3: ( explanation )?
            int alt10=2;
            int LA10_0 = input.LA(1);

            if ( (LA10_0==29) ) {
                alt10=1;
            }
            switch (alt10) {
                case 1 :
                    // BON.g:128:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_system_chart591);
                    explanation15=explanation();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       expl = explanation15; 
                    }

                    }
                    break;

            }

            // BON.g:129:3: ( part )?
            int alt11=2;
            int LA11_0 = input.LA(1);

            if ( (LA11_0==31) ) {
                alt11=1;
            }
            switch (alt11) {
                case 1 :
                    // BON.g:129:4: part
                    {
                    pushFollow(FOLLOW_part_in_system_chart602);
                    part16=part();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       p = part16; 
                    }

                    }
                    break;

            }

            // BON.g:130:3: (ce= cluster_entries | )
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
                    // BON.g:130:6: ce= cluster_entries
                    {
                    pushFollow(FOLLOW_cluster_entries_in_system_chart617);
                    ce=cluster_entries();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       entries = ce; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:132:6: 
                    {
                    if ( state.backtracking==0 ) {
                       entries = emptyList(); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_system_chart644); if (state.failed) return sc;
            if ( state.backtracking==0 ) {
               sc = ClusterChart.mk(system_name17, true, Constants.NO_CLASS_ENTRIES, entries, index, expl, p, getSLoc(s,e)); 
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
    // BON.g:138:1: explanation returns [String explanation] : (e= 'explanation' m= manifest_textblock | e= 'explanation' );
    public final String explanation() throws RecognitionException {
        String explanation = null;

        Token e=null;
        BONParser.manifest_textblock_return m = null;


        try {
            // BON.g:138:42: (e= 'explanation' m= manifest_textblock | e= 'explanation' )
            int alt13=2;
            int LA13_0 = input.LA(1);

            if ( (LA13_0==29) ) {
                int LA13_1 = input.LA(2);

                if ( ((LA13_1>=25 && LA13_1<=27)||LA13_1==31||(LA13_1>=38 && LA13_1<=41)||LA13_1==47||LA13_1==50||LA13_1==52) ) {
                    alt13=2;
                }
                else if ( (LA13_1==MANIFEST_STRING||LA13_1==MANIFEST_TEXTBLOCK_START) ) {
                    alt13=1;
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
                    // BON.g:139:3: e= 'explanation' m= manifest_textblock
                    {
                    e=(Token)match(input,29,FOLLOW_29_in_explanation665); if (state.failed) return explanation;
                    pushFollow(FOLLOW_manifest_textblock_in_explanation669);
                    m=manifest_textblock();

                    state._fsp--;
                    if (state.failed) return explanation;
                    if ( state.backtracking==0 ) {
                       explanation = (m!=null?input.toString(m.start,m.stop):null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:142:3: e= 'explanation'
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
    // BON.g:146:1: indexing returns [Indexing indexing] : (i= 'indexing' index_list | i= 'indexing' );
    public final BONParser.indexing_return indexing() throws RecognitionException {
        BONParser.indexing_return retval = new BONParser.indexing_return();
        retval.start = input.LT(1);

        Token i=null;
        BONParser.index_list_return index_list18 = null;


        try {
            // BON.g:146:38: (i= 'indexing' index_list | i= 'indexing' )
            int alt14=2;
            int LA14_0 = input.LA(1);

            if ( (LA14_0==30) ) {
                int LA14_1 = input.LA(2);

                if ( (LA14_1==EOF||(LA14_1>=24 && LA14_1<=29)||LA14_1==31||(LA14_1>=36 && LA14_1<=41)||LA14_1==44||LA14_1==47||(LA14_1>=49 && LA14_1<=52)||LA14_1==54||LA14_1==72||LA14_1==92) ) {
                    alt14=2;
                }
                else if ( (LA14_1==IDENTIFIER) ) {
                    alt14=1;
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
                    // BON.g:147:4: i= 'indexing' index_list
                    {
                    i=(Token)match(input,30,FOLLOW_30_in_indexing707); if (state.failed) return retval;
                    pushFollow(FOLLOW_index_list_in_indexing709);
                    index_list18=index_list();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.indexing = Indexing.mk((index_list18!=null?index_list18.list:null), getSLoc(i,(index_list18!=null?((Token)index_list18.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:150:4: i= 'indexing'
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
    // BON.g:155:1: part returns [String part] : (p= 'part' m= MANIFEST_STRING | p= 'part' );
    public final String part() throws RecognitionException {
        String part = null;

        Token p=null;
        Token m=null;

        try {
            // BON.g:155:28: (p= 'part' m= MANIFEST_STRING | p= 'part' )
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
                    // BON.g:156:5: p= 'part' m= MANIFEST_STRING
                    {
                    p=(Token)match(input,31,FOLLOW_31_in_part755); if (state.failed) return part;
                    m=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_part759); if (state.failed) return part;
                    if ( state.backtracking==0 ) {
                       part = (m!=null?m.getText():null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:159:5: p= 'part'
                    {
                    p=(Token)match(input,31,FOLLOW_31_in_part777); if (state.failed) return part;
                    if ( state.backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(p), "part text", "after 'part'", false)); 
                    }
                    if ( state.backtracking==0 ) {
                       part = ""; 
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
    // BON.g:164:1: description returns [String description] : d= 'description' m= manifest_textblock ;
    public final BONParser.description_return description() throws RecognitionException {
        BONParser.description_return retval = new BONParser.description_return();
        retval.start = input.LT(1);

        Token d=null;
        BONParser.manifest_textblock_return m = null;


        try {
            // BON.g:164:42: (d= 'description' m= manifest_textblock )
            // BON.g:165:3: d= 'description' m= manifest_textblock
            {
            d=(Token)match(input,32,FOLLOW_32_in_description807); if (state.failed) return retval;
            pushFollow(FOLLOW_manifest_textblock_in_description811);
            m=manifest_textblock();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.description = (m!=null?input.toString(m.start,m.stop):null); 
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
    // BON.g:169:1: cluster_entries returns [List<ClusterEntry> entries] : ( cluster_entry )+ ;
    public final List<ClusterEntry> cluster_entries() throws RecognitionException {
        List<ClusterEntry> entries = null;

        ClusterEntry cluster_entry19 = null;


        try {
            // BON.g:169:54: ( ( cluster_entry )+ )
            // BON.g:170:3: ( cluster_entry )+
            {
            if ( state.backtracking==0 ) {
               entries = createList(); 
            }
            // BON.g:171:3: ( cluster_entry )+
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
            	    // BON.g:171:4: cluster_entry
            	    {
            	    pushFollow(FOLLOW_cluster_entry_in_cluster_entries836);
            	    cluster_entry19=cluster_entry();

            	    state._fsp--;
            	    if (state.failed) return entries;
            	    if ( state.backtracking==0 ) {
            	       entries.add(cluster_entry19); 
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
    // BON.g:174:1: cluster_entry returns [ClusterEntry ce] : c= 'cluster' cluster_name description ;
    public final ClusterEntry cluster_entry() throws RecognitionException {
        ClusterEntry ce = null;

        Token c=null;
        BONParser.cluster_name_return cluster_name20 = null;

        BONParser.description_return description21 = null;


        try {
            // BON.g:174:41: (c= 'cluster' cluster_name description )
            // BON.g:175:3: c= 'cluster' cluster_name description
            {
            c=(Token)match(input,27,FOLLOW_27_in_cluster_entry875); if (state.failed) return ce;
            pushFollow(FOLLOW_cluster_name_in_cluster_entry877);
            cluster_name20=cluster_name();

            state._fsp--;
            if (state.failed) return ce;
            pushFollow(FOLLOW_description_in_cluster_entry879);
            description21=description();

            state._fsp--;
            if (state.failed) return ce;
            if ( state.backtracking==0 ) {
               ce = ClusterEntry.mk((cluster_name20!=null?input.toString(cluster_name20.start,cluster_name20.stop):null), (description21!=null?description21.description:null), getSLoc(c, (description21!=null?((Token)description21.stop):null))); 
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
    // BON.g:179:1: system_name returns [String name] : i= IDENTIFIER ;
    public final String system_name() throws RecognitionException {
        String name = null;

        Token i=null;

        try {
            // BON.g:179:35: (i= IDENTIFIER )
            // BON.g:180:3: i= IDENTIFIER
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_system_name916); if (state.failed) return name;
            if ( state.backtracking==0 ) {
               name = (i!=null?i.getText():null); 
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
    // BON.g:184:1: index_list returns [List<IndexClause> list] : i1= index_clause ( ( ';' i2= index_clause ) | i= index_clause )* ( ';' )? ;
    public final BONParser.index_list_return index_list() throws RecognitionException {
        BONParser.index_list_return retval = new BONParser.index_list_return();
        retval.start = input.LT(1);

        BONParser.index_clause_return i1 = null;

        BONParser.index_clause_return i2 = null;

        BONParser.index_clause_return i = null;


        try {
            // BON.g:186:45: (i1= index_clause ( ( ';' i2= index_clause ) | i= index_clause )* ( ';' )? )
            // BON.g:187:16: i1= index_clause ( ( ';' i2= index_clause ) | i= index_clause )* ( ';' )?
            {
            if ( state.backtracking==0 ) {
               retval.list = createList(); 
            }
            pushFollow(FOLLOW_index_clause_in_index_list973);
            i1=index_clause();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.list.add((i1!=null?i1.clause:null)); 
            }
            // BON.g:190:16: ( ( ';' i2= index_clause ) | i= index_clause )*
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
            	    // BON.g:190:19: ( ';' i2= index_clause )
            	    {
            	    // BON.g:190:19: ( ';' i2= index_clause )
            	    // BON.g:190:20: ';' i2= index_clause
            	    {
            	    match(input,33,FOLLOW_33_in_index_list1012); if (state.failed) return retval;
            	    pushFollow(FOLLOW_index_clause_in_index_list1016);
            	    i2=index_clause();

            	    state._fsp--;
            	    if (state.failed) return retval;

            	    }

            	    if ( state.backtracking==0 ) {
            	       retval.list.add((i2!=null?i2.clause:null)); 
            	    }

            	    }
            	    break;
            	case 2 :
            	    // BON.g:192:19: i= index_clause
            	    {
            	    pushFollow(FOLLOW_index_clause_in_index_list1059);
            	    i=index_clause();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       addParseProblem(new MissingElementParseError(getSourceLocation((i!=null?((Token)i.start):null)), "semi-colon", "before additional index clause", false)); 
            	    }
            	    if ( state.backtracking==0 ) {
            	       retval.list.add((i!=null?i.clause:null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop17;
                }
            } while (true);

            // BON.g:195:16: ( ';' )?
            int alt18=2;
            int LA18_0 = input.LA(1);

            if ( (LA18_0==33) ) {
                alt18=1;
            }
            switch (alt18) {
                case 1 :
                    // BON.g:195:16: ';'
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
    // BON.g:198:1: index_clause returns [IndexClause clause] : (i= IDENTIFIER ':' index_term_list | i= IDENTIFIER ':' );
    public final BONParser.index_clause_return index_clause() throws RecognitionException {
        BONParser.index_clause_return retval = new BONParser.index_clause_return();
        retval.start = input.LT(1);

        Token i=null;
        BONParser.index_term_list_return index_term_list22 = null;


        try {
            // BON.g:198:43: (i= IDENTIFIER ':' index_term_list | i= IDENTIFIER ':' )
            int alt19=2;
            int LA19_0 = input.LA(1);

            if ( (LA19_0==IDENTIFIER) ) {
                int LA19_1 = input.LA(2);

                if ( (LA19_1==34) ) {
                    int LA19_2 = input.LA(3);

                    if ( (LA19_2==MANIFEST_STRING) ) {
                        alt19=1;
                    }
                    else if ( (LA19_2==EOF||LA19_2==IDENTIFIER||(LA19_2>=24 && LA19_2<=29)||LA19_2==31||LA19_2==33||(LA19_2>=36 && LA19_2<=41)||LA19_2==44||LA19_2==47||(LA19_2>=49 && LA19_2<=52)||LA19_2==54||LA19_2==72||LA19_2==92) ) {
                        alt19=2;
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
                    // BON.g:199:3: i= IDENTIFIER ':' index_term_list
                    {
                    i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_index_clause1150); if (state.failed) return retval;
                    match(input,34,FOLLOW_34_in_index_clause1152); if (state.failed) return retval;
                    pushFollow(FOLLOW_index_term_list_in_index_clause1154);
                    index_term_list22=index_term_list();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.clause = IndexClause.mk((i!=null?i.getText():null), (index_term_list22!=null?index_term_list22.strings:null), getSLoc(i, (index_term_list22!=null?((Token)index_term_list22.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:202:3: i= IDENTIFIER ':'
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
    // BON.g:206:1: index_term_list returns [List<String> strings] : i1= index_string ( ',' i= index_string )* ;
    public final BONParser.index_term_list_return index_term_list() throws RecognitionException {
        BONParser.index_term_list_return retval = new BONParser.index_term_list_return();
        retval.start = input.LT(1);

        BONParser.index_string_return i1 = null;

        BONParser.index_string_return i = null;


        try {
            // BON.g:206:48: (i1= index_string ( ',' i= index_string )* )
            // BON.g:207:3: i1= index_string ( ',' i= index_string )*
            {
            if ( state.backtracking==0 ) {
               retval.strings = createList(); 
            }
            pushFollow(FOLLOW_index_string_in_index_term_list1212);
            i1=index_string();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.strings.add((i1!=null?input.toString(i1.start,i1.stop):null)); 
            }
            // BON.g:210:3: ( ',' i= index_string )*
            loop20:
            do {
                int alt20=2;
                int LA20_0 = input.LA(1);

                if ( (LA20_0==35) ) {
                    alt20=1;
                }


                switch (alt20) {
            	case 1 :
            	    // BON.g:210:4: ',' i= index_string
            	    {
            	    match(input,35,FOLLOW_35_in_index_term_list1222); if (state.failed) return retval;
            	    pushFollow(FOLLOW_index_string_in_index_term_list1226);
            	    i=index_string();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       retval.strings.add((i!=null?input.toString(i.start,i.stop):null)); 
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
    // BON.g:215:1: index_string returns [String s] : m= MANIFEST_STRING ;
    public final BONParser.index_string_return index_string() throws RecognitionException {
        BONParser.index_string_return retval = new BONParser.index_string_return();
        retval.start = input.LT(1);

        Token m=null;

        try {
            // BON.g:215:33: (m= MANIFEST_STRING )
            // BON.g:216:3: m= MANIFEST_STRING
            {
            m=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_index_string1271); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.s = (m!=null?m.getText():null); 
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
    // BON.g:220:1: cluster_chart returns [ClusterChart cc] : c= 'cluster_chart' cluster_name (i= indexing )? ( explanation )? ( part )? (ce= class_entries | ) (cle= cluster_entries | ) e= 'end' ;
    public final ClusterChart cluster_chart() throws RecognitionException {
        ClusterChart cc = null;

        Token c=null;
        Token e=null;
        BONParser.indexing_return i = null;

        List<ClassEntry> ce = null;

        List<ClusterEntry> cle = null;

        String explanation23 = null;

        String part24 = null;

        BONParser.cluster_name_return cluster_name25 = null;


         List<ClassEntry> classes = null; List<ClusterEntry> clusters = null; 
                Indexing indexing = null; String explanation = null; String part = null;  
        try {
            // BON.g:225:1: (c= 'cluster_chart' cluster_name (i= indexing )? ( explanation )? ( part )? (ce= class_entries | ) (cle= cluster_entries | ) e= 'end' )
            // BON.g:226:3: c= 'cluster_chart' cluster_name (i= indexing )? ( explanation )? ( part )? (ce= class_entries | ) (cle= cluster_entries | ) e= 'end'
            {
            c=(Token)match(input,36,FOLLOW_36_in_cluster_chart1305); if (state.failed) return cc;
            pushFollow(FOLLOW_cluster_name_in_cluster_chart1307);
            cluster_name25=cluster_name();

            state._fsp--;
            if (state.failed) return cc;
            // BON.g:227:3: (i= indexing )?
            int alt21=2;
            int LA21_0 = input.LA(1);

            if ( (LA21_0==30) ) {
                alt21=1;
            }
            switch (alt21) {
                case 1 :
                    // BON.g:227:4: i= indexing
                    {
                    pushFollow(FOLLOW_indexing_in_cluster_chart1315);
                    i=indexing();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       indexing = (i!=null?i.indexing:null); 
                    }

                    }
                    break;

            }

            // BON.g:228:3: ( explanation )?
            int alt22=2;
            int LA22_0 = input.LA(1);

            if ( (LA22_0==29) ) {
                alt22=1;
            }
            switch (alt22) {
                case 1 :
                    // BON.g:228:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_cluster_chart1326);
                    explanation23=explanation();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       explanation = explanation23; 
                    }

                    }
                    break;

            }

            // BON.g:229:3: ( part )?
            int alt23=2;
            int LA23_0 = input.LA(1);

            if ( (LA23_0==31) ) {
                alt23=1;
            }
            switch (alt23) {
                case 1 :
                    // BON.g:229:4: part
                    {
                    pushFollow(FOLLOW_part_in_cluster_chart1337);
                    part24=part();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       part = part24; 
                    }

                    }
                    break;

            }

            // BON.g:230:3: (ce= class_entries | )
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
                    // BON.g:230:6: ce= class_entries
                    {
                    pushFollow(FOLLOW_class_entries_in_cluster_chart1352);
                    ce=class_entries();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       classes = ce; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:231:6: 
                    {
                    if ( state.backtracking==0 ) {
                       classes = emptyList(); 
                    }

                    }
                    break;

            }

            // BON.g:233:3: (cle= cluster_entries | )
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
                    // BON.g:233:6: cle= cluster_entries
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
                    // BON.g:234:6: 
                    {
                    if ( state.backtracking==0 ) {
                       clusters = emptyList(); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_cluster_chart1397); if (state.failed) return cc;
            if ( state.backtracking==0 ) {
               cc = ClusterChart.mk((cluster_name25!=null?cluster_name25.name:null), false, classes, clusters, indexing, explanation, part, getSLoc(c,e)); 
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
    // BON.g:240:1: class_entries returns [List<ClassEntry> entries] : ( class_entry )+ ;
    public final List<ClassEntry> class_entries() throws RecognitionException {
        List<ClassEntry> entries = null;

        ClassEntry class_entry26 = null;


        try {
            // BON.g:240:50: ( ( class_entry )+ )
            // BON.g:241:3: ( class_entry )+
            {
            if ( state.backtracking==0 ) {
               entries = createList(); 
            }
            // BON.g:242:3: ( class_entry )+
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
            	    // BON.g:242:4: class_entry
            	    {
            	    pushFollow(FOLLOW_class_entry_in_class_entries1436);
            	    class_entry26=class_entry();

            	    state._fsp--;
            	    if (state.failed) return entries;
            	    if ( state.backtracking==0 ) {
            	       entries.add(class_entry26); 
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
    // BON.g:245:1: class_entry returns [ClassEntry entry] : c= 'class' class_name description ;
    public final ClassEntry class_entry() throws RecognitionException {
        ClassEntry entry = null;

        Token c=null;
        BONParser.class_name_return class_name27 = null;

        BONParser.description_return description28 = null;


        try {
            // BON.g:245:40: (c= 'class' class_name description )
            // BON.g:246:3: c= 'class' class_name description
            {
            c=(Token)match(input,26,FOLLOW_26_in_class_entry1474); if (state.failed) return entry;
            pushFollow(FOLLOW_class_name_in_class_entry1476);
            class_name27=class_name();

            state._fsp--;
            if (state.failed) return entry;
            pushFollow(FOLLOW_description_in_class_entry1480);
            description28=description();

            state._fsp--;
            if (state.failed) return entry;
            if ( state.backtracking==0 ) {
               entry = ClassEntry.mk((class_name27!=null?input.toString(class_name27.start,class_name27.stop):null), (description28!=null?description28.description:null), getSLoc(c, (description28!=null?((Token)description28.stop):null))); 
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
    // BON.g:251:1: cluster_name returns [String name] : i= IDENTIFIER ;
    public final BONParser.cluster_name_return cluster_name() throws RecognitionException {
        BONParser.cluster_name_return retval = new BONParser.cluster_name_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // BON.g:251:36: (i= IDENTIFIER )
            // BON.g:252:3: i= IDENTIFIER
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_cluster_name1514); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.name = (i!=null?i.getText():null); 
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
    // BON.g:256:1: class_chart returns [ClassChart cc] : c= 'class_chart' class_name (i= indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? e= 'end' ;
    public final ClassChart class_chart() throws RecognitionException {
        ClassChart cc = null;

        Token c=null;
        Token e=null;
        BONParser.indexing_return i = null;

        String explanation29 = null;

        String part30 = null;

        List<ClassName> inherits31 = null;

        List<String> queries32 = null;

        List<String> commands33 = null;

        List<String> constraints34 = null;

        BONParser.class_name_return class_name35 = null;


         Indexing indexing = null; String explanation = null; String part = null;
                List<ClassName> inherits = emptyList(); List<String> commands = emptyList(); List<String> queries = emptyList(); 
                List<String> constraints = emptyList();  
        try {
            // BON.g:262:1: (c= 'class_chart' class_name (i= indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? e= 'end' )
            // BON.g:263:3: c= 'class_chart' class_name (i= indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? e= 'end'
            {
            c=(Token)match(input,37,FOLLOW_37_in_class_chart1545); if (state.failed) return cc;
            pushFollow(FOLLOW_class_name_in_class_chart1547);
            class_name35=class_name();

            state._fsp--;
            if (state.failed) return cc;
            // BON.g:264:3: (i= indexing )?
            int alt27=2;
            int LA27_0 = input.LA(1);

            if ( (LA27_0==30) ) {
                alt27=1;
            }
            switch (alt27) {
                case 1 :
                    // BON.g:264:4: i= indexing
                    {
                    pushFollow(FOLLOW_indexing_in_class_chart1555);
                    i=indexing();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       indexing = (i!=null?i.indexing:null); 
                    }

                    }
                    break;

            }

            // BON.g:265:3: ( explanation )?
            int alt28=2;
            int LA28_0 = input.LA(1);

            if ( (LA28_0==29) ) {
                alt28=1;
            }
            switch (alt28) {
                case 1 :
                    // BON.g:265:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_class_chart1566);
                    explanation29=explanation();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       explanation = explanation29; 
                    }

                    }
                    break;

            }

            // BON.g:266:3: ( part )?
            int alt29=2;
            int LA29_0 = input.LA(1);

            if ( (LA29_0==31) ) {
                alt29=1;
            }
            switch (alt29) {
                case 1 :
                    // BON.g:266:4: part
                    {
                    pushFollow(FOLLOW_part_in_class_chart1577);
                    part30=part();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       part = part30; 
                    }

                    }
                    break;

            }

            // BON.g:267:3: ( inherits )?
            int alt30=2;
            int LA30_0 = input.LA(1);

            if ( (LA30_0==38) ) {
                alt30=1;
            }
            switch (alt30) {
                case 1 :
                    // BON.g:267:6: inherits
                    {
                    pushFollow(FOLLOW_inherits_in_class_chart1590);
                    inherits31=inherits();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       inherits = inherits31; 
                    }

                    }
                    break;

            }

            // BON.g:270:3: ( queries )?
            int alt31=2;
            int LA31_0 = input.LA(1);

            if ( (LA31_0==39) ) {
                alt31=1;
            }
            switch (alt31) {
                case 1 :
                    // BON.g:270:6: queries
                    {
                    pushFollow(FOLLOW_queries_in_class_chart1609);
                    queries32=queries();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       queries = queries32; 
                    }

                    }
                    break;

            }

            // BON.g:273:3: ( commands )?
            int alt32=2;
            int LA32_0 = input.LA(1);

            if ( (LA32_0==40) ) {
                alt32=1;
            }
            switch (alt32) {
                case 1 :
                    // BON.g:273:6: commands
                    {
                    pushFollow(FOLLOW_commands_in_class_chart1628);
                    commands33=commands();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       commands = commands33; 
                    }

                    }
                    break;

            }

            // BON.g:276:3: ( constraints )?
            int alt33=2;
            int LA33_0 = input.LA(1);

            if ( (LA33_0==41) ) {
                alt33=1;
            }
            switch (alt33) {
                case 1 :
                    // BON.g:276:6: constraints
                    {
                    pushFollow(FOLLOW_constraints_in_class_chart1647);
                    constraints34=constraints();

                    state._fsp--;
                    if (state.failed) return cc;
                    if ( state.backtracking==0 ) {
                       constraints = constraints34; 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_class_chart1665); if (state.failed) return cc;
            if ( state.backtracking==0 ) {
               cc = ClassChart.mk((class_name35!=null?class_name35.name:null), inherits, queries, commands, constraints, indexing, explanation, part, getSLoc(c,e)); 
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
    // BON.g:283:1: inherits returns [List<ClassName> inherits] : (i= 'inherit' class_name_list | i= 'inherit' );
    public final List<ClassName> inherits() throws RecognitionException {
        List<ClassName> inherits = null;

        Token i=null;
        List<ClassName> class_name_list36 = null;


        try {
            // BON.g:283:45: (i= 'inherit' class_name_list | i= 'inherit' )
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
                    // BON.g:284:3: i= 'inherit' class_name_list
                    {
                    i=(Token)match(input,38,FOLLOW_38_in_inherits1699); if (state.failed) return inherits;
                    pushFollow(FOLLOW_class_name_list_in_inherits1704);
                    class_name_list36=class_name_list();

                    state._fsp--;
                    if (state.failed) return inherits;
                    if ( state.backtracking==0 ) {
                       inherits = class_name_list36; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:288:3: i= 'inherit'
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
    // BON.g:292:1: queries returns [List<String> queries] : 'query' query_list ;
    public final List<String> queries() throws RecognitionException {
        List<String> queries = null;

        List<String> query_list37 = null;


        try {
            // BON.g:292:40: ( 'query' query_list )
            // BON.g:293:3: 'query' query_list
            {
            match(input,39,FOLLOW_39_in_queries1738); if (state.failed) return queries;
            pushFollow(FOLLOW_query_list_in_queries1740);
            query_list37=query_list();

            state._fsp--;
            if (state.failed) return queries;
            if ( state.backtracking==0 ) {
               queries = query_list37; 
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
    // BON.g:297:1: commands returns [List<String> commands] : 'command' command_list ;
    public final List<String> commands() throws RecognitionException {
        List<String> commands = null;

        List<String> command_list38 = null;


        try {
            // BON.g:297:42: ( 'command' command_list )
            // BON.g:298:3: 'command' command_list
            {
            match(input,40,FOLLOW_40_in_commands1770); if (state.failed) return commands;
            pushFollow(FOLLOW_command_list_in_commands1772);
            command_list38=command_list();

            state._fsp--;
            if (state.failed) return commands;
            if ( state.backtracking==0 ) {
               commands = command_list38; 
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
    // BON.g:302:1: constraints returns [List<String> constraints] : 'constraint' constraint_list ;
    public final List<String> constraints() throws RecognitionException {
        List<String> constraints = null;

        List<String> constraint_list39 = null;


        try {
            // BON.g:302:48: ( 'constraint' constraint_list )
            // BON.g:303:3: 'constraint' constraint_list
            {
            match(input,41,FOLLOW_41_in_constraints1791); if (state.failed) return constraints;
            pushFollow(FOLLOW_constraint_list_in_constraints1793);
            constraint_list39=constraint_list();

            state._fsp--;
            if (state.failed) return constraints;
            if ( state.backtracking==0 ) {
               constraints = constraint_list39; 
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
    // BON.g:308:1: query_list returns [List<String> queries] : m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? ;
    public final List<String> query_list() throws RecognitionException {
        List<String> queries = null;

        BONParser.manifest_textblock_return m1 = null;

        BONParser.manifest_textblock_return m = null;


        try {
            // BON.g:308:43: (m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? )
            // BON.g:309:3: m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )?
            {
            if ( state.backtracking==0 ) {
               queries = createList(); 
            }
            pushFollow(FOLLOW_manifest_textblock_in_query_list1819);
            m1=manifest_textblock();

            state._fsp--;
            if (state.failed) return queries;
            if ( state.backtracking==0 ) {
               queries.add((m1!=null?input.toString(m1.start,m1.stop):null)); 
            }
            // BON.g:312:3: ( ( ',' m= manifest_textblock ) | m= manifest_textblock )*
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
            	    // BON.g:312:6: ( ',' m= manifest_textblock )
            	    {
            	    // BON.g:312:6: ( ',' m= manifest_textblock )
            	    // BON.g:312:7: ',' m= manifest_textblock
            	    {
            	    match(input,35,FOLLOW_35_in_query_list1832); if (state.failed) return queries;
            	    pushFollow(FOLLOW_manifest_textblock_in_query_list1836);
            	    m=manifest_textblock();

            	    state._fsp--;
            	    if (state.failed) return queries;
            	    if ( state.backtracking==0 ) {
            	       queries.add((m!=null?input.toString(m.start,m.stop):null)); 
            	    }

            	    }


            	    }
            	    break;
            	case 2 :
            	    // BON.g:315:6: m= manifest_textblock
            	    {
            	    pushFollow(FOLLOW_manifest_textblock_in_query_list1868);
            	    m=manifest_textblock();

            	    state._fsp--;
            	    if (state.failed) return queries;
            	    if ( state.backtracking==0 ) {
            	       addParseProblem(new MissingElementParseError(getSourceLocation((m!=null?((Token)m.start):null)), "comma", "before additional query item", false)); 
            	    }
            	    if ( state.backtracking==0 ) {
            	       queries.add((m!=null?input.toString(m.start,m.stop):null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop35;
                }
            } while (true);

            // BON.g:319:3: ( ',' )?
            int alt36=2;
            int LA36_0 = input.LA(1);

            if ( (LA36_0==35) ) {
                alt36=1;
            }
            switch (alt36) {
                case 1 :
                    // BON.g:319:3: ','
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
    // BON.g:322:1: command_list returns [List<String> commands] : m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? ;
    public final List<String> command_list() throws RecognitionException {
        List<String> commands = null;

        BONParser.manifest_textblock_return m1 = null;

        BONParser.manifest_textblock_return m = null;


        try {
            // BON.g:322:46: (m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? )
            // BON.g:323:3: m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )?
            {
            if ( state.backtracking==0 ) {
               commands = createList(); 
            }
            pushFollow(FOLLOW_manifest_textblock_in_command_list1941);
            m1=manifest_textblock();

            state._fsp--;
            if (state.failed) return commands;
            if ( state.backtracking==0 ) {
               commands.add((m1!=null?input.toString(m1.start,m1.stop):null)); 
            }
            // BON.g:326:3: ( ( ',' m= manifest_textblock ) | m= manifest_textblock )*
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
            	    // BON.g:326:6: ( ',' m= manifest_textblock )
            	    {
            	    // BON.g:326:6: ( ',' m= manifest_textblock )
            	    // BON.g:326:7: ',' m= manifest_textblock
            	    {
            	    match(input,35,FOLLOW_35_in_command_list1954); if (state.failed) return commands;
            	    pushFollow(FOLLOW_manifest_textblock_in_command_list1958);
            	    m=manifest_textblock();

            	    state._fsp--;
            	    if (state.failed) return commands;
            	    if ( state.backtracking==0 ) {
            	       commands.add((m!=null?input.toString(m.start,m.stop):null)); 
            	    }

            	    }


            	    }
            	    break;
            	case 2 :
            	    // BON.g:329:6: m= manifest_textblock
            	    {
            	    pushFollow(FOLLOW_manifest_textblock_in_command_list1984);
            	    m=manifest_textblock();

            	    state._fsp--;
            	    if (state.failed) return commands;
            	    if ( state.backtracking==0 ) {
            	       addParseProblem(new MissingElementParseError(getSourceLocation((m!=null?((Token)m.start):null)), "comma", "before additional command item", false)); 
            	    }
            	    if ( state.backtracking==0 ) {
            	       commands.add((m!=null?input.toString(m.start,m.stop):null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop37;
                }
            } while (true);

            // BON.g:333:3: ( ',' )?
            int alt38=2;
            int LA38_0 = input.LA(1);

            if ( (LA38_0==35) ) {
                alt38=1;
            }
            switch (alt38) {
                case 1 :
                    // BON.g:333:3: ','
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
    // BON.g:336:1: constraint_list returns [List<String> constraints] : m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? ;
    public final List<String> constraint_list() throws RecognitionException {
        List<String> constraints = null;

        BONParser.manifest_textblock_return m1 = null;

        BONParser.manifest_textblock_return m = null;


        try {
            // BON.g:336:52: (m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )? )
            // BON.g:337:3: m1= manifest_textblock ( ( ',' m= manifest_textblock ) | m= manifest_textblock )* ( ',' )?
            {
            if ( state.backtracking==0 ) {
               constraints = createList(); 
            }
            pushFollow(FOLLOW_manifest_textblock_in_constraint_list2045);
            m1=manifest_textblock();

            state._fsp--;
            if (state.failed) return constraints;
            if ( state.backtracking==0 ) {
               constraints.add((m1!=null?input.toString(m1.start,m1.stop):null)); 
            }
            // BON.g:340:3: ( ( ',' m= manifest_textblock ) | m= manifest_textblock )*
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
            	    // BON.g:340:6: ( ',' m= manifest_textblock )
            	    {
            	    // BON.g:340:6: ( ',' m= manifest_textblock )
            	    // BON.g:340:7: ',' m= manifest_textblock
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
            	    // BON.g:341:6: m= manifest_textblock
            	    {
            	    pushFollow(FOLLOW_manifest_textblock_in_constraint_list2073);
            	    m=manifest_textblock();

            	    state._fsp--;
            	    if (state.failed) return constraints;
            	    if ( state.backtracking==0 ) {
            	       addParseProblem(new MissingElementParseError(getSourceLocation((m!=null?((Token)m.start):null)), "comma", "before additional constraint item", false)); 
            	    }
            	    if ( state.backtracking==0 ) {
            	       constraints.add((m!=null?input.toString(m.start,m.stop):null)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop39;
                }
            } while (true);

            // BON.g:345:3: ( ',' )?
            int alt40=2;
            int LA40_0 = input.LA(1);

            if ( (LA40_0==35) ) {
                alt40=1;
            }
            switch (alt40) {
                case 1 :
                    // BON.g:345:3: ','
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
    // BON.g:348:1: class_name_list returns [List<ClassName> list] : c1= class_name ( ( ',' c= class_name ) | (c= class_name ) )* ;
    public final List<ClassName> class_name_list() throws RecognitionException {
        List<ClassName> list = null;

        BONParser.class_name_return c1 = null;

        BONParser.class_name_return c = null;


        try {
            // BON.g:348:48: (c1= class_name ( ( ',' c= class_name ) | (c= class_name ) )* )
            // BON.g:349:3: c1= class_name ( ( ',' c= class_name ) | (c= class_name ) )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_class_name_in_class_name_list2119);
            c1=class_name();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               list.add((c1!=null?c1.name:null)); 
            }
            // BON.g:352:3: ( ( ',' c= class_name ) | (c= class_name ) )*
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
            	    // BON.g:352:6: ( ',' c= class_name )
            	    {
            	    // BON.g:352:6: ( ',' c= class_name )
            	    // BON.g:352:8: ',' c= class_name
            	    {
            	    match(input,35,FOLLOW_35_in_class_name_list2133); if (state.failed) return list;
            	    pushFollow(FOLLOW_class_name_in_class_name_list2137);
            	    c=class_name();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       list.add((c!=null?c.name:null)); 
            	    }

            	    }


            	    }
            	    break;
            	case 2 :
            	    // BON.g:355:6: (c= class_name )
            	    {
            	    // BON.g:355:6: (c= class_name )
            	    // BON.g:355:8: c= class_name
            	    {
            	    pushFollow(FOLLOW_class_name_in_class_name_list2166);
            	    c=class_name();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       list.add((c!=null?c.name:null)); 
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
    // BON.g:362:1: cluster_name_list returns [List<String> list] : c1= cluster_name ( ( ',' c= cluster_name ) | (c= cluster_name ) )* ;
    public final List<String> cluster_name_list() throws RecognitionException {
        List<String> list = null;

        BONParser.cluster_name_return c1 = null;

        BONParser.cluster_name_return c = null;


        try {
            // BON.g:362:47: (c1= cluster_name ( ( ',' c= cluster_name ) | (c= cluster_name ) )* )
            // BON.g:363:3: c1= cluster_name ( ( ',' c= cluster_name ) | (c= cluster_name ) )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_cluster_name_in_cluster_name_list2235);
            c1=cluster_name();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               list.add((c1!=null?input.toString(c1.start,c1.stop):null)); 
            }
            // BON.g:366:3: ( ( ',' c= cluster_name ) | (c= cluster_name ) )*
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
            	    // BON.g:366:6: ( ',' c= cluster_name )
            	    {
            	    // BON.g:366:6: ( ',' c= cluster_name )
            	    // BON.g:366:8: ',' c= cluster_name
            	    {
            	    match(input,35,FOLLOW_35_in_cluster_name_list2248); if (state.failed) return list;
            	    pushFollow(FOLLOW_cluster_name_in_cluster_name_list2252);
            	    c=cluster_name();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       list.add((c!=null?input.toString(c.start,c.stop):null)); 
            	    }

            	    }


            	    }
            	    break;
            	case 2 :
            	    // BON.g:369:6: (c= cluster_name )
            	    {
            	    // BON.g:369:6: (c= cluster_name )
            	    // BON.g:369:8: c= cluster_name
            	    {
            	    pushFollow(FOLLOW_cluster_name_in_cluster_name_list2280);
            	    c=cluster_name();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       addParseProblem(new MissingElementParseError(getSourceLocation((c!=null?((Token)c.start):null)), "comma", "before additional class name", false)); 
            	    }
            	    if ( state.backtracking==0 ) {
            	       list.add((c!=null?input.toString(c.start,c.stop):null)); 
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
    // BON.g:376:1: class_or_cluster_name_list returns [List<String> list] : c1= class_or_bracketed_cluster_name ( ',' c= class_or_bracketed_cluster_name )* ;
    public final BONParser.class_or_cluster_name_list_return class_or_cluster_name_list() throws RecognitionException {
        BONParser.class_or_cluster_name_list_return retval = new BONParser.class_or_cluster_name_list_return();
        retval.start = input.LT(1);

        String c1 = null;

        String c = null;


        try {
            // BON.g:376:56: (c1= class_or_bracketed_cluster_name ( ',' c= class_or_bracketed_cluster_name )* )
            // BON.g:377:3: c1= class_or_bracketed_cluster_name ( ',' c= class_or_bracketed_cluster_name )*
            {
            if ( state.backtracking==0 ) {
               retval.list = createList(); 
            }
            pushFollow(FOLLOW_class_or_bracketed_cluster_name_in_class_or_cluster_name_list2377);
            c1=class_or_bracketed_cluster_name();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.list.add(c1); 
            }
            // BON.g:380:3: ( ',' c= class_or_bracketed_cluster_name )*
            loop43:
            do {
                int alt43=2;
                int LA43_0 = input.LA(1);

                if ( (LA43_0==35) ) {
                    alt43=1;
                }


                switch (alt43) {
            	case 1 :
            	    // BON.g:380:5: ',' c= class_or_bracketed_cluster_name
            	    {
            	    match(input,35,FOLLOW_35_in_class_or_cluster_name_list2387); if (state.failed) return retval;
            	    pushFollow(FOLLOW_class_or_bracketed_cluster_name_in_class_or_cluster_name_list2391);
            	    c=class_or_bracketed_cluster_name();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       retval.list.add(c); 
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
    // BON.g:385:1: class_or_bracketed_cluster_name returns [String name] : ( class_name | '(' cluster_name ')' );
    public final String class_or_bracketed_cluster_name() throws RecognitionException {
        String name = null;

        BONParser.class_name_return class_name40 = null;

        BONParser.cluster_name_return cluster_name41 = null;


        try {
            // BON.g:385:55: ( class_name | '(' cluster_name ')' )
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
                    // BON.g:386:4: class_name
                    {
                    pushFollow(FOLLOW_class_name_in_class_or_bracketed_cluster_name2419);
                    class_name40=class_name();

                    state._fsp--;
                    if (state.failed) return name;
                    if ( state.backtracking==0 ) {
                       name = (class_name40!=null?class_name40.name:null).getName(); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:389:4: '(' cluster_name ')'
                    {
                    match(input,42,FOLLOW_42_in_class_or_bracketed_cluster_name2433); if (state.failed) return name;
                    pushFollow(FOLLOW_cluster_name_in_class_or_bracketed_cluster_name2435);
                    cluster_name41=cluster_name();

                    state._fsp--;
                    if (state.failed) return name;
                    match(input,43,FOLLOW_43_in_class_or_bracketed_cluster_name2437); if (state.failed) return name;
                    if ( state.backtracking==0 ) {
                       name = (cluster_name41!=null?cluster_name41.name:null); 
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
    // BON.g:393:1: class_name returns [ClassName name] : i= IDENTIFIER ;
    public final BONParser.class_name_return class_name() throws RecognitionException {
        BONParser.class_name_return retval = new BONParser.class_name_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // BON.g:393:37: (i= IDENTIFIER )
            // BON.g:394:3: i= IDENTIFIER
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_class_name2459); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.name = ClassName.mk((i!=null?i.getText():null), getSLoc(i)); 
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
    // BON.g:398:1: event_chart returns [EventChart ec] : e= 'event_chart' system_name ( 'incoming' | 'outgoing' )? ( indexing )? ( explanation )? ( part )? (ee= event_entries | ) end= 'end' ;
    public final EventChart event_chart() throws RecognitionException {
        EventChart ec = null;

        Token e=null;
        Token end=null;
        List<EventEntry> ee = null;

        BONParser.indexing_return indexing42 = null;

        String explanation43 = null;

        String part44 = null;

        String system_name45 = null;


         boolean incoming = false; boolean outgoing = false; Indexing indexing = null;
                String explanation = null; String part = null; List<EventEntry> eventEntries = null; 
        try {
            // BON.g:403:1: (e= 'event_chart' system_name ( 'incoming' | 'outgoing' )? ( indexing )? ( explanation )? ( part )? (ee= event_entries | ) end= 'end' )
            // BON.g:404:3: e= 'event_chart' system_name ( 'incoming' | 'outgoing' )? ( indexing )? ( explanation )? ( part )? (ee= event_entries | ) end= 'end'
            {
            e=(Token)match(input,44,FOLLOW_44_in_event_chart2490); if (state.failed) return ec;
            pushFollow(FOLLOW_system_name_in_event_chart2492);
            system_name45=system_name();

            state._fsp--;
            if (state.failed) return ec;
            // BON.g:405:3: ( 'incoming' | 'outgoing' )?
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
                    // BON.g:405:6: 'incoming'
                    {
                    match(input,45,FOLLOW_45_in_event_chart2500); if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       incoming = true; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:406:6: 'outgoing'
                    {
                    match(input,46,FOLLOW_46_in_event_chart2510); if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       outgoing = true; 
                    }

                    }
                    break;

            }

            // BON.g:408:3: ( indexing )?
            int alt46=2;
            int LA46_0 = input.LA(1);

            if ( (LA46_0==30) ) {
                alt46=1;
            }
            switch (alt46) {
                case 1 :
                    // BON.g:408:4: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_event_chart2522);
                    indexing42=indexing();

                    state._fsp--;
                    if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       indexing = (indexing42!=null?indexing42.indexing:null); 
                    }

                    }
                    break;

            }

            // BON.g:409:3: ( explanation )?
            int alt47=2;
            int LA47_0 = input.LA(1);

            if ( (LA47_0==29) ) {
                alt47=1;
            }
            switch (alt47) {
                case 1 :
                    // BON.g:409:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_event_chart2531);
                    explanation43=explanation();

                    state._fsp--;
                    if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       explanation = explanation43; 
                    }

                    }
                    break;

            }

            // BON.g:410:3: ( part )?
            int alt48=2;
            int LA48_0 = input.LA(1);

            if ( (LA48_0==31) ) {
                alt48=1;
            }
            switch (alt48) {
                case 1 :
                    // BON.g:410:4: part
                    {
                    pushFollow(FOLLOW_part_in_event_chart2541);
                    part44=part();

                    state._fsp--;
                    if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       part = part44; 
                    }

                    }
                    break;

            }

            // BON.g:411:3: (ee= event_entries | )
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
                    // BON.g:411:5: ee= event_entries
                    {
                    pushFollow(FOLLOW_event_entries_in_event_chart2554);
                    ee=event_entries();

                    state._fsp--;
                    if (state.failed) return ec;
                    if ( state.backtracking==0 ) {
                       eventEntries = ee; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:414:5: 
                    {
                    if ( state.backtracking==0 ) {
                       eventEntries = createList(); 
                    }

                    }
                    break;

            }

            end=(Token)match(input,25,FOLLOW_25_in_event_chart2581); if (state.failed) return ec;
            if ( state.backtracking==0 ) {
               ec = EventChart.mk(system_name45, incoming, outgoing, eventEntries, indexing, explanation, part, getSLoc(e,end)); 
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
    // BON.g:420:1: event_entries returns [List<EventEntry> entries] : ( event_entry )+ ;
    public final List<EventEntry> event_entries() throws RecognitionException {
        List<EventEntry> entries = null;

        EventEntry event_entry46 = null;


        try {
            // BON.g:420:50: ( ( event_entry )+ )
            // BON.g:421:3: ( event_entry )+
            {
            if ( state.backtracking==0 ) {
               entries = createList(); 
            }
            // BON.g:422:3: ( event_entry )+
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
            	    // BON.g:422:4: event_entry
            	    {
            	    pushFollow(FOLLOW_event_entry_in_event_entries2618);
            	    event_entry46=event_entry();

            	    state._fsp--;
            	    if (state.failed) return entries;
            	    if ( state.backtracking==0 ) {
            	       entries.add(event_entry46); 
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
    // BON.g:425:1: event_entry returns [EventEntry entry] : e= 'event' ( (m= manifest_textblock ) | ) i= 'involves' ( (ccns= class_or_cluster_name_list ) | ) ;
    public final EventEntry event_entry() throws RecognitionException {
        EventEntry entry = null;

        Token e=null;
        Token i=null;
        BONParser.manifest_textblock_return m = null;

        BONParser.class_or_cluster_name_list_return ccns = null;


         boolean mok=false; boolean cok=false; List<String> ccnl = null; String name = null; Token stop=null; 
        try {
            // BON.g:426:112: (e= 'event' ( (m= manifest_textblock ) | ) i= 'involves' ( (ccns= class_or_cluster_name_list ) | ) )
            // BON.g:427:3: e= 'event' ( (m= manifest_textblock ) | ) i= 'involves' ( (ccns= class_or_cluster_name_list ) | )
            {
            e=(Token)match(input,47,FOLLOW_47_in_event_entry2661); if (state.failed) return entry;
            // BON.g:428:3: ( (m= manifest_textblock ) | )
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
                    // BON.g:428:6: (m= manifest_textblock )
                    {
                    // BON.g:428:6: (m= manifest_textblock )
                    // BON.g:428:8: m= manifest_textblock
                    {
                    pushFollow(FOLLOW_manifest_textblock_in_event_entry2672);
                    m=manifest_textblock();

                    state._fsp--;
                    if (state.failed) return entry;
                    if ( state.backtracking==0 ) {
                      mok=true; name=(m!=null?input.toString(m.start,m.stop):null);
                    }

                    }


                    }
                    break;
                case 2 :
                    // BON.g:432:4: 
                    {
                    if ( state.backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(e), "event name", "in event entry clause", true)); 
                    }

                    }
                    break;

            }

            i=(Token)match(input,48,FOLLOW_48_in_event_entry2712); if (state.failed) return entry;
            // BON.g:435:3: ( (ccns= class_or_cluster_name_list ) | )
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
                    // BON.g:435:6: (ccns= class_or_cluster_name_list )
                    {
                    // BON.g:435:6: (ccns= class_or_cluster_name_list )
                    // BON.g:435:7: ccns= class_or_cluster_name_list
                    {
                    pushFollow(FOLLOW_class_or_cluster_name_list_in_event_entry2722);
                    ccns=class_or_cluster_name_list();

                    state._fsp--;
                    if (state.failed) return entry;
                    if ( state.backtracking==0 ) {
                       cok=true; ccnl = (ccns!=null?ccns.list:null); 
                    }
                    if ( state.backtracking==0 ) {
                       stop = (ccns!=null?((Token)ccns.stop):null); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // BON.g:440:6: 
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
               if (mok && cok) entry = EventEntry.mk(name, ccnl, getSLoc(e,stop)); 
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
    // BON.g:446:1: scenario_chart returns [ScenarioChart sc] : s= 'scenario_chart' system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries | ) e= 'end' ;
    public final ScenarioChart scenario_chart() throws RecognitionException {
        ScenarioChart sc = null;

        Token s=null;
        Token e=null;
        BONParser.indexing_return indexing47 = null;

        String explanation48 = null;

        String part49 = null;

        List<ScenarioEntry> scenario_entries50 = null;

        String system_name51 = null;


         Indexing indexing = null; String explanation = null; String part = null; List<ScenarioEntry> entries = null; 
        try {
            // BON.g:450:1: (s= 'scenario_chart' system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries | ) e= 'end' )
            // BON.g:451:3: s= 'scenario_chart' system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries | ) e= 'end'
            {
            s=(Token)match(input,49,FOLLOW_49_in_scenario_chart2802); if (state.failed) return sc;
            pushFollow(FOLLOW_system_name_in_scenario_chart2804);
            system_name51=system_name();

            state._fsp--;
            if (state.failed) return sc;
            // BON.g:452:3: ( indexing )?
            int alt53=2;
            int LA53_0 = input.LA(1);

            if ( (LA53_0==30) ) {
                alt53=1;
            }
            switch (alt53) {
                case 1 :
                    // BON.g:452:4: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_scenario_chart2809);
                    indexing47=indexing();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       indexing = (indexing47!=null?indexing47.indexing:null); 
                    }

                    }
                    break;

            }

            // BON.g:453:3: ( explanation )?
            int alt54=2;
            int LA54_0 = input.LA(1);

            if ( (LA54_0==29) ) {
                alt54=1;
            }
            switch (alt54) {
                case 1 :
                    // BON.g:453:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_scenario_chart2819);
                    explanation48=explanation();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       explanation = explanation48; 
                    }

                    }
                    break;

            }

            // BON.g:454:3: ( part )?
            int alt55=2;
            int LA55_0 = input.LA(1);

            if ( (LA55_0==31) ) {
                alt55=1;
            }
            switch (alt55) {
                case 1 :
                    // BON.g:454:4: part
                    {
                    pushFollow(FOLLOW_part_in_scenario_chart2829);
                    part49=part();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                      part = part49; 
                    }

                    }
                    break;

            }

            // BON.g:455:3: ( scenario_entries | )
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
                    // BON.g:455:5: scenario_entries
                    {
                    pushFollow(FOLLOW_scenario_entries_in_scenario_chart2840);
                    scenario_entries50=scenario_entries();

                    state._fsp--;
                    if (state.failed) return sc;
                    if ( state.backtracking==0 ) {
                       entries = scenario_entries50; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:456:6: 
                    {
                    if ( state.backtracking==0 ) {
                       entries = emptyList(); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_scenario_chart2861); if (state.failed) return sc;
            if ( state.backtracking==0 ) {
               sc = ScenarioChart.mk(system_name51, entries, indexing, explanation, part, getSLoc(s,e)); 
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
    // BON.g:462:1: scenario_entries returns [List<ScenarioEntry> entries] : ( scenario_entry )+ ;
    public final List<ScenarioEntry> scenario_entries() throws RecognitionException {
        List<ScenarioEntry> entries = null;

        ScenarioEntry scenario_entry52 = null;


        try {
            // BON.g:462:56: ( ( scenario_entry )+ )
            // BON.g:463:3: ( scenario_entry )+
            {
            if ( state.backtracking==0 ) {
               entries = createList(); 
            }
            // BON.g:464:3: ( scenario_entry )+
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
            	    // BON.g:464:4: scenario_entry
            	    {
            	    pushFollow(FOLLOW_scenario_entry_in_scenario_entries2901);
            	    scenario_entry52=scenario_entry();

            	    state._fsp--;
            	    if (state.failed) return entries;
            	    if ( state.backtracking==0 ) {
            	       entries.add(scenario_entry52); 
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
    // BON.g:467:1: scenario_entry returns [ScenarioEntry entry] : s= 'scenario' m= MANIFEST_STRING d= description ;
    public final ScenarioEntry scenario_entry() throws RecognitionException {
        ScenarioEntry entry = null;

        Token s=null;
        Token m=null;
        BONParser.description_return d = null;


        try {
            // BON.g:467:46: (s= 'scenario' m= MANIFEST_STRING d= description )
            // BON.g:468:3: s= 'scenario' m= MANIFEST_STRING d= description
            {
            s=(Token)match(input,50,FOLLOW_50_in_scenario_entry2942); if (state.failed) return entry;
            m=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_scenario_entry2946); if (state.failed) return entry;
            pushFollow(FOLLOW_description_in_scenario_entry2950);
            d=description();

            state._fsp--;
            if (state.failed) return entry;
            if ( state.backtracking==0 ) {
               entry =  ScenarioEntry.mk((m!=null?m.getText():null), (d!=null?d.description:null), getSLoc(s,(d!=null?((Token)d.stop):null))); 
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
    // BON.g:472:1: creation_chart returns [CreationChart cc] : start= 'creation_chart' system_name ( indexing )? ( explanation )? ( part )? ( creation_entries | ) end= 'end' ;
    public final BONParser.creation_chart_return creation_chart() throws RecognitionException {
        BONParser.creation_chart_return retval = new BONParser.creation_chart_return();
        retval.start = input.LT(1);

        Token start=null;
        Token end=null;
        BONParser.indexing_return indexing53 = null;

        String explanation54 = null;

        String part55 = null;

        List<CreationEntry> creation_entries56 = null;

        String system_name57 = null;


         List<CreationEntry> entries = null; Indexing indexing = null; String explanation = null; String part = null; 
        try {
            // BON.g:476:1: (start= 'creation_chart' system_name ( indexing )? ( explanation )? ( part )? ( creation_entries | ) end= 'end' )
            // BON.g:477:3: start= 'creation_chart' system_name ( indexing )? ( explanation )? ( part )? ( creation_entries | ) end= 'end'
            {
            start=(Token)match(input,51,FOLLOW_51_in_creation_chart2979); if (state.failed) return retval;
            pushFollow(FOLLOW_system_name_in_creation_chart2981);
            system_name57=system_name();

            state._fsp--;
            if (state.failed) return retval;
            // BON.g:478:3: ( indexing )?
            int alt58=2;
            int LA58_0 = input.LA(1);

            if ( (LA58_0==30) ) {
                alt58=1;
            }
            switch (alt58) {
                case 1 :
                    // BON.g:478:4: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_creation_chart2986);
                    indexing53=indexing();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       indexing = (indexing53!=null?indexing53.indexing:null); 
                    }

                    }
                    break;

            }

            // BON.g:479:3: ( explanation )?
            int alt59=2;
            int LA59_0 = input.LA(1);

            if ( (LA59_0==29) ) {
                alt59=1;
            }
            switch (alt59) {
                case 1 :
                    // BON.g:479:4: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_creation_chart2996);
                    explanation54=explanation();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       explanation = explanation54; 
                    }

                    }
                    break;

            }

            // BON.g:480:3: ( part )?
            int alt60=2;
            int LA60_0 = input.LA(1);

            if ( (LA60_0==31) ) {
                alt60=1;
            }
            switch (alt60) {
                case 1 :
                    // BON.g:480:4: part
                    {
                    pushFollow(FOLLOW_part_in_creation_chart3006);
                    part55=part();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       part = part55; 
                    }

                    }
                    break;

            }

            // BON.g:481:3: ( creation_entries | )
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
                    // BON.g:481:5: creation_entries
                    {
                    pushFollow(FOLLOW_creation_entries_in_creation_chart3017);
                    creation_entries56=creation_entries();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       entries = creation_entries56; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:482:6: 
                    {
                    if ( state.backtracking==0 ) {
                       entries = emptyList(); 
                    }

                    }
                    break;

            }

            end=(Token)match(input,25,FOLLOW_25_in_creation_chart3034); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.cc = CreationChart.mk(system_name57, entries, indexing, explanation, part,getSLoc(start,end)); 
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
    // BON.g:487:1: creation_entries returns [List<CreationEntry> entries] : ( creation_entry )+ ;
    public final List<CreationEntry> creation_entries() throws RecognitionException {
        List<CreationEntry> entries = null;

        CreationEntry creation_entry58 = null;


        try {
            // BON.g:487:56: ( ( creation_entry )+ )
            // BON.g:488:3: ( creation_entry )+
            {
            if ( state.backtracking==0 ) {
               entries = createList(); 
            }
            // BON.g:489:3: ( creation_entry )+
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
            	    // BON.g:489:4: creation_entry
            	    {
            	    pushFollow(FOLLOW_creation_entry_in_creation_entries3075);
            	    creation_entry58=creation_entry();

            	    state._fsp--;
            	    if (state.failed) return entries;
            	    if ( state.backtracking==0 ) {
            	       entries.add(creation_entry58); 
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
    // BON.g:492:1: creation_entry returns [CreationEntry entry] : c= 'creator' class_name 'creates' ccnl= class_or_cluster_name_list ;
    public final CreationEntry creation_entry() throws RecognitionException {
        CreationEntry entry = null;

        Token c=null;
        BONParser.class_or_cluster_name_list_return ccnl = null;

        BONParser.class_name_return class_name59 = null;


        try {
            // BON.g:492:46: (c= 'creator' class_name 'creates' ccnl= class_or_cluster_name_list )
            // BON.g:493:3: c= 'creator' class_name 'creates' ccnl= class_or_cluster_name_list
            {
            c=(Token)match(input,52,FOLLOW_52_in_creation_entry3115); if (state.failed) return entry;
            pushFollow(FOLLOW_class_name_in_creation_entry3117);
            class_name59=class_name();

            state._fsp--;
            if (state.failed) return entry;
            match(input,53,FOLLOW_53_in_creation_entry3122); if (state.failed) return entry;
            pushFollow(FOLLOW_class_or_cluster_name_list_in_creation_entry3126);
            ccnl=class_or_cluster_name_list();

            state._fsp--;
            if (state.failed) return entry;
            if ( state.backtracking==0 ) {
               entry = CreationEntry.mk((class_name59!=null?class_name59.name:null), (ccnl!=null?ccnl.list:null), getSLoc(c,(ccnl!=null?((Token)ccnl.stop):null))); 
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
    // BON.g:498:1: static_diagram returns [StaticDiagram sd] : s= 'static_diagram' ( extended_id )? (c= COMMENT )? 'component' sb= static_block e= 'end' ;
    public final StaticDiagram static_diagram() throws RecognitionException {
        StaticDiagram sd = null;

        Token s=null;
        Token c=null;
        Token e=null;
        List<StaticComponent> sb = null;

        BONParser.extended_id_return extended_id60 = null;


         String eid = null; String comment = null; 
        try {
            // BON.g:504:1: (s= 'static_diagram' ( extended_id )? (c= COMMENT )? 'component' sb= static_block e= 'end' )
            // BON.g:505:3: s= 'static_diagram' ( extended_id )? (c= COMMENT )? 'component' sb= static_block e= 'end'
            {
            s=(Token)match(input,54,FOLLOW_54_in_static_diagram3159); if (state.failed) return sd;
            // BON.g:506:3: ( extended_id )?
            int alt63=2;
            int LA63_0 = input.LA(1);

            if ( (LA63_0==IDENTIFIER||LA63_0==INTEGER) ) {
                alt63=1;
            }
            switch (alt63) {
                case 1 :
                    // BON.g:506:4: extended_id
                    {
                    pushFollow(FOLLOW_extended_id_in_static_diagram3165);
                    extended_id60=extended_id();

                    state._fsp--;
                    if (state.failed) return sd;
                    if ( state.backtracking==0 ) {
                       eid=(extended_id60!=null?extended_id60.eid:null); 
                    }

                    }
                    break;

            }

            // BON.g:507:3: (c= COMMENT )?
            int alt64=2;
            int LA64_0 = input.LA(1);

            if ( (LA64_0==COMMENT) ) {
                alt64=1;
            }
            switch (alt64) {
                case 1 :
                    // BON.g:507:4: c= COMMENT
                    {
                    c=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_static_diagram3178); if (state.failed) return sd;
                    if ( state.backtracking==0 ) {
                       comment=(c!=null?c.getText():null); 
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
               sd = StaticDiagram.mk(sb, eid, comment, getSLoc(s,e)); 
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
    // BON.g:514:1: extended_id returns [String eid] : (i= IDENTIFIER | i= INTEGER );
    public final BONParser.extended_id_return extended_id() throws RecognitionException {
        BONParser.extended_id_return retval = new BONParser.extended_id_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // BON.g:514:34: (i= IDENTIFIER | i= INTEGER )
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
                    // BON.g:515:4: i= IDENTIFIER
                    {
                    i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_extended_id3258); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.eid = (i!=null?i.getText():null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:517:4: i= INTEGER
                    {
                    i=(Token)match(input,INTEGER,FOLLOW_INTEGER_in_extended_id3271); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.eid = (i!=null?i.getText():null); 
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
    // BON.g:521:1: static_block returns [List<StaticComponent> components] : (sc= static_component )* ;
    public final List<StaticComponent> static_block() throws RecognitionException {
        List<StaticComponent> components = null;

        StaticComponent sc = null;


        try {
            // BON.g:521:57: ( (sc= static_component )* )
            // BON.g:522:3: (sc= static_component )*
            {
            if ( state.backtracking==0 ) {
               components = createList(); 
            }
            // BON.g:523:3: (sc= static_component )*
            loop66:
            do {
                int alt66=2;
                int LA66_0 = input.LA(1);

                if ( (LA66_0==IDENTIFIER||(LA66_0>=26 && LA66_0<=27)||(LA66_0>=57 && LA66_0<=59)) ) {
                    alt66=1;
                }


                switch (alt66) {
            	case 1 :
            	    // BON.g:523:4: sc= static_component
            	    {
            	    pushFollow(FOLLOW_static_component_in_static_block3312);
            	    sc=static_component();

            	    state._fsp--;
            	    if (state.failed) return components;
            	    if ( state.backtracking==0 ) {
            	       components.add(sc); 
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
    // BON.g:526:1: static_component returns [StaticComponent component] : (c1= cluster | c2= clazz | s= static_relation );
    public final StaticComponent static_component() throws RecognitionException {
        StaticComponent component = null;

        Cluster c1 = null;

        Clazz c2 = null;

        StaticRelation s = null;


        try {
            // BON.g:526:54: (c1= cluster | c2= clazz | s= static_relation )
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
                    // BON.g:527:4: c1= cluster
                    {
                    pushFollow(FOLLOW_cluster_in_static_component3347);
                    c1=cluster();

                    state._fsp--;
                    if (state.failed) return component;
                    if ( state.backtracking==0 ) {
                       component = c1; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:529:4: c2= clazz
                    {
                    pushFollow(FOLLOW_clazz_in_static_component3360);
                    c2=clazz();

                    state._fsp--;
                    if (state.failed) return component;
                    if ( state.backtracking==0 ) {
                       component = c2; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:531:4: s= static_relation
                    {
                    pushFollow(FOLLOW_static_relation_in_static_component3373);
                    s=static_relation();

                    state._fsp--;
                    if (state.failed) return component;
                    if ( state.backtracking==0 ) {
                       component = s; 
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
    // BON.g:535:1: cluster returns [Cluster cluster] : c= 'cluster' cluster_name (r= 'reused' )? (co= COMMENT )? (cc= cluster_components | ) ;
    public final Cluster cluster() throws RecognitionException {
        Cluster cluster = null;

        Token c=null;
        Token r=null;
        Token co=null;
        BONParser.cluster_components_return cc = null;

        BONParser.cluster_name_return cluster_name61 = null;


         boolean reused = false; String comment = null; List<StaticComponent> components = null; Token end = null; 
        try {
            // BON.g:539:1: (c= 'cluster' cluster_name (r= 'reused' )? (co= COMMENT )? (cc= cluster_components | ) )
            // BON.g:540:3: c= 'cluster' cluster_name (r= 'reused' )? (co= COMMENT )? (cc= cluster_components | )
            {
            c=(Token)match(input,27,FOLLOW_27_in_cluster3405); if (state.failed) return cluster;
            pushFollow(FOLLOW_cluster_name_in_cluster3407);
            cluster_name61=cluster_name();

            state._fsp--;
            if (state.failed) return cluster;
            if ( state.backtracking==0 ) {
               end = (cluster_name61!=null?((Token)cluster_name61.stop):null); 
            }
            // BON.g:541:3: (r= 'reused' )?
            int alt68=2;
            int LA68_0 = input.LA(1);

            if ( (LA68_0==56) ) {
                alt68=1;
            }
            switch (alt68) {
                case 1 :
                    // BON.g:541:4: r= 'reused'
                    {
                    r=(Token)match(input,56,FOLLOW_56_in_cluster3416); if (state.failed) return cluster;
                    if ( state.backtracking==0 ) {
                       reused = true; end = r; 
                    }

                    }
                    break;

            }

            // BON.g:542:3: (co= COMMENT )?
            int alt69=2;
            int LA69_0 = input.LA(1);

            if ( (LA69_0==COMMENT) ) {
                alt69=1;
            }
            switch (alt69) {
                case 1 :
                    // BON.g:542:4: co= COMMENT
                    {
                    co=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_cluster3429); if (state.failed) return cluster;
                    if ( state.backtracking==0 ) {
                       comment = (co!=null?co.getText():null); end = co;
                    }

                    }
                    break;

            }

            // BON.g:543:3: (cc= cluster_components | )
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
                    // BON.g:543:6: cc= cluster_components
                    {
                    pushFollow(FOLLOW_cluster_components_in_cluster3447);
                    cc=cluster_components();

                    state._fsp--;
                    if (state.failed) return cluster;
                    if ( state.backtracking==0 ) {
                       components = (cc!=null?cc.components:null); end = (cc!=null?((Token)cc.stop):null);
                    }

                    }
                    break;
                case 2 :
                    // BON.g:546:6: 
                    {
                    if ( state.backtracking==0 ) {
                       components = emptyList(); 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               cluster = Cluster.mk((cluster_name61!=null?cluster_name61.name:null), components, reused, comment, getSLoc(c,end)); 
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
    // BON.g:551:1: cluster_components returns [List<StaticComponent> components] : 'component' static_block 'end' ;
    public final BONParser.cluster_components_return cluster_components() throws RecognitionException {
        BONParser.cluster_components_return retval = new BONParser.cluster_components_return();
        retval.start = input.LT(1);

        List<StaticComponent> static_block62 = null;


        try {
            // BON.g:551:63: ( 'component' static_block 'end' )
            // BON.g:552:3: 'component' static_block 'end'
            {
            match(input,55,FOLLOW_55_in_cluster_components3502); if (state.failed) return retval;
            pushFollow(FOLLOW_static_block_in_cluster_components3504);
            static_block62=static_block();

            state._fsp--;
            if (state.failed) return retval;
            match(input,25,FOLLOW_25_in_cluster_components3506); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.components = static_block62; 
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
    // BON.g:556:1: clazz returns [Clazz clazz] : (r= 'root' | d= 'deferred' | e= 'effective' | ) c= 'class' cn= class_name (fg= formal_generics | ) (ru= 'reused' )? (p= 'persistent' )? (i= 'interfaced' )? (co= COMMENT )? (ci= class_interface )? ;
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
            // BON.g:560:1: ( (r= 'root' | d= 'deferred' | e= 'effective' | ) c= 'class' cn= class_name (fg= formal_generics | ) (ru= 'reused' )? (p= 'persistent' )? (i= 'interfaced' )? (co= COMMENT )? (ci= class_interface )? )
            // BON.g:561:3: (r= 'root' | d= 'deferred' | e= 'effective' | ) c= 'class' cn= class_name (fg= formal_generics | ) (ru= 'reused' )? (p= 'persistent' )? (i= 'interfaced' )? (co= COMMENT )? (ci= class_interface )?
            {
            // BON.g:561:3: (r= 'root' | d= 'deferred' | e= 'effective' | )
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
                    // BON.g:561:7: r= 'root'
                    {
                    r=(Token)match(input,57,FOLLOW_57_in_clazz3557); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       mod = Clazz.Mod.ROOT; start = r; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:562:7: d= 'deferred'
                    {
                    d=(Token)match(input,58,FOLLOW_58_in_clazz3574); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       mod = Clazz.Mod.DEFERRED; start = d; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:563:7: e= 'effective'
                    {
                    e=(Token)match(input,59,FOLLOW_59_in_clazz3587); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       mod = Clazz.Mod.EFFECTIVE; start = e; 
                    }

                    }
                    break;
                case 4 :
                    // BON.g:564:21: 
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
            // BON.g:570:3: (fg= formal_generics | )
            int alt72=2;
            int LA72_0 = input.LA(1);

            if ( (LA72_0==66) ) {
                alt72=1;
            }
            else if ( ((LA72_0>=IDENTIFIER && LA72_0<=COMMENT)||(LA72_0>=25 && LA72_0<=27)||LA72_0==30||LA72_0==38||(LA72_0>=56 && LA72_0<=61)||LA72_0==72) ) {
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
                    // BON.g:570:6: fg= formal_generics
                    {
                    pushFollow(FOLLOW_formal_generics_in_clazz3645);
                    fg=formal_generics();

                    state._fsp--;
                    if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       generics = (fg!=null?fg.generics:null); end = (fg!=null?((Token)fg.stop):null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:571:6: 
                    {
                    if ( state.backtracking==0 ) {
                       generics = emptyList(); 
                    }

                    }
                    break;

            }

            // BON.g:573:3: (ru= 'reused' )?
            int alt73=2;
            int LA73_0 = input.LA(1);

            if ( (LA73_0==56) ) {
                alt73=1;
            }
            switch (alt73) {
                case 1 :
                    // BON.g:573:4: ru= 'reused'
                    {
                    ru=(Token)match(input,56,FOLLOW_56_in_clazz3667); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       reused = true; end = ru; 
                    }

                    }
                    break;

            }

            // BON.g:574:3: (p= 'persistent' )?
            int alt74=2;
            int LA74_0 = input.LA(1);

            if ( (LA74_0==60) ) {
                alt74=1;
            }
            switch (alt74) {
                case 1 :
                    // BON.g:574:4: p= 'persistent'
                    {
                    p=(Token)match(input,60,FOLLOW_60_in_clazz3680); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       persistent = true; end = p; 
                    }

                    }
                    break;

            }

            // BON.g:575:3: (i= 'interfaced' )?
            int alt75=2;
            int LA75_0 = input.LA(1);

            if ( (LA75_0==61) ) {
                alt75=1;
            }
            switch (alt75) {
                case 1 :
                    // BON.g:575:4: i= 'interfaced'
                    {
                    i=(Token)match(input,61,FOLLOW_61_in_clazz3694); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       interfaced = true; end = i; 
                    }

                    }
                    break;

            }

            // BON.g:576:3: (co= COMMENT )?
            int alt76=2;
            int LA76_0 = input.LA(1);

            if ( (LA76_0==COMMENT) ) {
                alt76=1;
            }
            switch (alt76) {
                case 1 :
                    // BON.g:576:4: co= COMMENT
                    {
                    co=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_clazz3706); if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       comment = (co!=null?co.getText():null); end = co; 
                    }

                    }
                    break;

            }

            // BON.g:577:3: (ci= class_interface )?
            int alt77=2;
            int LA77_0 = input.LA(1);

            if ( (LA77_0==30||LA77_0==38||LA77_0==72) ) {
                alt77=1;
            }
            switch (alt77) {
                case 1 :
                    // BON.g:577:4: ci= class_interface
                    {
                    pushFollow(FOLLOW_class_interface_in_clazz3718);
                    ci=class_interface();

                    state._fsp--;
                    if (state.failed) return clazz;
                    if ( state.backtracking==0 ) {
                       classInterface = (ci!=null?ci.ci:null); end = (ci!=null?((Token)ci.stop):null); 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               clazz = Clazz.mk((cn!=null?cn.name:null), generics, mod, classInterface, reused, persistent, interfaced, comment, getSLoc(start,end)); 
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
    // BON.g:581:1: static_relation returns [StaticRelation relation] : (ir= inheritance_relation | cr= client_relation );
    public final StaticRelation static_relation() throws RecognitionException {
        StaticRelation relation = null;

        InheritanceRelation ir = null;

        ClientRelation cr = null;


        try {
            // BON.g:581:51: (ir= inheritance_relation | cr= client_relation )
            int alt78=2;
            alt78 = dfa78.predict(input);
            switch (alt78) {
                case 1 :
                    // BON.g:582:4: ir= inheritance_relation
                    {
                    pushFollow(FOLLOW_inheritance_relation_in_static_relation3758);
                    ir=inheritance_relation();

                    state._fsp--;
                    if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       relation = ir; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:584:4: cr= client_relation
                    {
                    pushFollow(FOLLOW_client_relation_in_static_relation3770);
                    cr=client_relation();

                    state._fsp--;
                    if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       relation = cr; 
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
    // BON.g:588:1: inheritance_relation returns [InheritanceRelation relation] : c= child 'inherit' (a= '{' multiplicity b= '}' )? p= parent ( semantic_label )? ;
    public final InheritanceRelation inheritance_relation() throws RecognitionException {
        InheritanceRelation relation = null;

        Token a=null;
        Token b=null;
        BONParser.child_return c = null;

        BONParser.parent_return p = null;

        BONParser.multiplicity_return multiplicity63 = null;

        BONParser.semantic_label_return semantic_label64 = null;


         Multiplicity multiplicity = null; String semanticLabel = null; Token end = null; 
        try {
            // BON.g:592:1: (c= child 'inherit' (a= '{' multiplicity b= '}' )? p= parent ( semantic_label )? )
            // BON.g:593:3: c= child 'inherit' (a= '{' multiplicity b= '}' )? p= parent ( semantic_label )?
            {
            pushFollow(FOLLOW_child_in_inheritance_relation3801);
            c=child();

            state._fsp--;
            if (state.failed) return relation;
            match(input,38,FOLLOW_38_in_inheritance_relation3803); if (state.failed) return relation;
            // BON.g:594:3: (a= '{' multiplicity b= '}' )?
            int alt79=2;
            int LA79_0 = input.LA(1);

            if ( (LA79_0==62) ) {
                alt79=1;
            }
            switch (alt79) {
                case 1 :
                    // BON.g:594:4: a= '{' multiplicity b= '}'
                    {
                    a=(Token)match(input,62,FOLLOW_62_in_inheritance_relation3811); if (state.failed) return relation;
                    pushFollow(FOLLOW_multiplicity_in_inheritance_relation3813);
                    multiplicity63=multiplicity();

                    state._fsp--;
                    if (state.failed) return relation;
                    b=(Token)match(input,63,FOLLOW_63_in_inheritance_relation3817); if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       multiplicity = Multiplicity.mk((multiplicity63!=null?multiplicity63.num:null), getSLoc(a,b)); 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_parent_in_inheritance_relation3834);
            p=parent();

            state._fsp--;
            if (state.failed) return relation;
            if ( state.backtracking==0 ) {
               end = (p!=null?((Token)p.stop):null); 
            }
            // BON.g:599:3: ( semantic_label )?
            int alt80=2;
            int LA80_0 = input.LA(1);

            if ( (LA80_0==MANIFEST_STRING) ) {
                alt80=1;
            }
            switch (alt80) {
                case 1 :
                    // BON.g:599:5: semantic_label
                    {
                    pushFollow(FOLLOW_semantic_label_in_inheritance_relation3845);
                    semantic_label64=semantic_label();

                    state._fsp--;
                    if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       semanticLabel = (semantic_label64!=null?semantic_label64.label:null); end = (semantic_label64!=null?((Token)semantic_label64.stop):null); 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               relation = InheritanceRelation.mk((c!=null?c.ref:null), (p!=null?p.ref:null), multiplicity, semanticLabel, getSLoc((c!=null?((Token)c.start):null), end)); 
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
    // BON.g:605:1: client_relation returns [ClientRelation relation] : c= client 'client' ( client_entities )? ( type_mark | ) s= supplier ( semantic_label )? ;
    public final ClientRelation client_relation() throws RecognitionException {
        ClientRelation relation = null;

        BONParser.client_return c = null;

        BONParser.supplier_return s = null;

        ClientEntityExpression client_entities65 = null;

        BONParser.type_mark_return type_mark66 = null;

        BONParser.semantic_label_return semantic_label67 = null;


         ClientEntityExpression entities = null; TypeMark mark = null; String semanticLabel = null; Token end = null; 
        try {
            // BON.g:607:1: (c= client 'client' ( client_entities )? ( type_mark | ) s= supplier ( semantic_label )? )
            // BON.g:608:3: c= client 'client' ( client_entities )? ( type_mark | ) s= supplier ( semantic_label )?
            {
            pushFollow(FOLLOW_client_in_client_relation3904);
            c=client();

            state._fsp--;
            if (state.failed) return relation;
            match(input,64,FOLLOW_64_in_client_relation3906); if (state.failed) return relation;
            // BON.g:609:3: ( client_entities )?
            int alt81=2;
            int LA81_0 = input.LA(1);

            if ( (LA81_0==62) ) {
                alt81=1;
            }
            switch (alt81) {
                case 1 :
                    // BON.g:609:4: client_entities
                    {
                    pushFollow(FOLLOW_client_entities_in_client_relation3911);
                    client_entities65=client_entities();

                    state._fsp--;
                    if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       entities = client_entities65; 
                    }

                    }
                    break;

            }

            // BON.g:610:3: ( type_mark | )
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
                    // BON.g:610:5: type_mark
                    {
                    pushFollow(FOLLOW_type_mark_in_client_relation3923);
                    type_mark66=type_mark();

                    state._fsp--;
                    if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       mark = (type_mark66!=null?type_mark66.mark:null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:613:4: 
                    {
                    if ( state.backtracking==0 ) {
                       mark = Constants.NO_TYPE_MARK; 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_supplier_in_client_relation3949);
            s=supplier();

            state._fsp--;
            if (state.failed) return relation;
            if ( state.backtracking==0 ) {
               end = (s!=null?((Token)s.stop):null); 
            }
            // BON.g:617:3: ( semantic_label )?
            int alt83=2;
            int LA83_0 = input.LA(1);

            if ( (LA83_0==MANIFEST_STRING) ) {
                alt83=1;
            }
            switch (alt83) {
                case 1 :
                    // BON.g:617:4: semantic_label
                    {
                    pushFollow(FOLLOW_semantic_label_in_client_relation3959);
                    semantic_label67=semantic_label();

                    state._fsp--;
                    if (state.failed) return relation;
                    if ( state.backtracking==0 ) {
                       semanticLabel = (semantic_label67!=null?semantic_label67.label:null); end = (semantic_label67!=null?((Token)semantic_label67.stop):null); 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               relation = ClientRelation.mk((c!=null?c.ref:null),(s!=null?s.ref:null),entities,mark,semanticLabel,getSLoc((c!=null?((Token)c.start):null),end)); 
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
    // BON.g:621:1: client_entities returns [ClientEntityExpression entities] : '{' cee= client_entity_expression '}' ;
    public final ClientEntityExpression client_entities() throws RecognitionException {
        ClientEntityExpression entities = null;

        ClientEntityExpression cee = null;


        try {
            // BON.g:621:59: ( '{' cee= client_entity_expression '}' )
            // BON.g:622:3: '{' cee= client_entity_expression '}'
            {
            match(input,62,FOLLOW_62_in_client_entities4000); if (state.failed) return entities;
            pushFollow(FOLLOW_client_entity_expression_in_client_entities4004);
            cee=client_entity_expression();

            state._fsp--;
            if (state.failed) return entities;
            match(input,63,FOLLOW_63_in_client_entities4006); if (state.failed) return entities;
            if ( state.backtracking==0 ) {
               entities = cee; 
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
    // BON.g:626:1: client_entity_expression returns [ClientEntityExpression entities] : (cel= client_entity_list | m= multiplicity );
    public final ClientEntityExpression client_entity_expression() throws RecognitionException {
        ClientEntityExpression entities = null;

        BONParser.client_entity_list_return cel = null;

        BONParser.multiplicity_return m = null;


        try {
            // BON.g:626:68: (cel= client_entity_list | m= multiplicity )
            int alt84=2;
            int LA84_0 = input.LA(1);

            if ( (LA84_0==IDENTIFIER||LA84_0==42||(LA84_0>=65 && LA84_0<=66)||LA84_0==68||LA84_0==78||LA84_0==80) ) {
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
                    // BON.g:627:4: cel= client_entity_list
                    {
                    pushFollow(FOLLOW_client_entity_list_in_client_entity_expression4045);
                    cel=client_entity_list();

                    state._fsp--;
                    if (state.failed) return entities;
                    if ( state.backtracking==0 ) {
                       entities = ClientEntityList.mk((cel!=null?cel.entities:null),getSLoc((cel!=null?((Token)cel.start):null),(cel!=null?((Token)cel.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:629:4: m= multiplicity
                    {
                    pushFollow(FOLLOW_multiplicity_in_client_entity_expression4058);
                    m=multiplicity();

                    state._fsp--;
                    if (state.failed) return entities;
                    if ( state.backtracking==0 ) {
                       entities = Multiplicity.mk((m!=null?m.num:null), getSLoc((m!=null?((Token)m.start):null),(m!=null?((Token)m.stop):null))); 
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
    // BON.g:633:1: client_entity_list returns [List<ClientEntity> entities] : ce= client_entity ( ',' c= client_entity )* ;
    public final BONParser.client_entity_list_return client_entity_list() throws RecognitionException {
        BONParser.client_entity_list_return retval = new BONParser.client_entity_list_return();
        retval.start = input.LT(1);

        ClientEntity ce = null;

        ClientEntity c = null;


        try {
            // BON.g:633:58: (ce= client_entity ( ',' c= client_entity )* )
            // BON.g:634:3: ce= client_entity ( ',' c= client_entity )*
            {
            if ( state.backtracking==0 ) {
               retval.entities = createList(); 
            }
            pushFollow(FOLLOW_client_entity_in_client_entity_list4111);
            ce=client_entity();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.entities.add(ce); 
            }
            // BON.g:637:3: ( ',' c= client_entity )*
            loop85:
            do {
                int alt85=2;
                int LA85_0 = input.LA(1);

                if ( (LA85_0==35) ) {
                    alt85=1;
                }


                switch (alt85) {
            	case 1 :
            	    // BON.g:637:4: ',' c= client_entity
            	    {
            	    match(input,35,FOLLOW_35_in_client_entity_list4120); if (state.failed) return retval;
            	    pushFollow(FOLLOW_client_entity_in_client_entity_list4124);
            	    c=client_entity();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       retval.entities.add(c); 
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
    // BON.g:646:1: client_entity returns [ClientEntity entity] : ( prefix | infix | supplier_indirection | parent_indirection );
    public final ClientEntity client_entity() throws RecognitionException {
        ClientEntity entity = null;

        SupplierIndirection supplier_indirection68 = null;

        ParentIndirection parent_indirection69 = null;


        try {
            // BON.g:646:45: ( prefix | infix | supplier_indirection | parent_indirection )
            int alt86=4;
            alt86 = dfa86.predict(input);
            switch (alt86) {
                case 1 :
                    // BON.g:647:4: prefix
                    {
                    pushFollow(FOLLOW_prefix_in_client_entity4175);
                    prefix();

                    state._fsp--;
                    if (state.failed) return entity;

                    }
                    break;
                case 2 :
                    // BON.g:648:4: infix
                    {
                    pushFollow(FOLLOW_infix_in_client_entity4180);
                    infix();

                    state._fsp--;
                    if (state.failed) return entity;

                    }
                    break;
                case 3 :
                    // BON.g:649:4: supplier_indirection
                    {
                    pushFollow(FOLLOW_supplier_indirection_in_client_entity4185);
                    supplier_indirection68=supplier_indirection();

                    state._fsp--;
                    if (state.failed) return entity;
                    if ( state.backtracking==0 ) {
                       entity = supplier_indirection68; 
                    }

                    }
                    break;
                case 4 :
                    // BON.g:651:4: parent_indirection
                    {
                    pushFollow(FOLLOW_parent_indirection_in_client_entity4196);
                    parent_indirection69=parent_indirection();

                    state._fsp--;
                    if (state.failed) return entity;
                    if ( state.backtracking==0 ) {
                       entity = parent_indirection69; 
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
    // BON.g:655:1: supplier_indirection returns [SupplierIndirection indirection] : (ifp= indirection_feature_part ':' )? gi= generic_indirection ;
    public final SupplierIndirection supplier_indirection() throws RecognitionException {
        SupplierIndirection indirection = null;

        BONParser.indirection_feature_part_return ifp = null;

        BONParser.generic_indirection_return gi = null;


        IndirectionFeaturePart part = null; Token start = null; 
        try {
            // BON.g:657:1: ( (ifp= indirection_feature_part ':' )? gi= generic_indirection )
            // BON.g:658:3: (ifp= indirection_feature_part ':' )? gi= generic_indirection
            {
            // BON.g:658:3: (ifp= indirection_feature_part ':' )?
            int alt87=2;
            int LA87_0 = input.LA(1);

            if ( (LA87_0==IDENTIFIER) ) {
                int LA87_1 = input.LA(2);

                if ( (LA87_1==34) ) {
                    alt87=1;
                }
            }
            else if ( (LA87_0==42||LA87_0==78||LA87_0==80) ) {
                alt87=1;
            }
            switch (alt87) {
                case 1 :
                    // BON.g:658:4: ifp= indirection_feature_part ':'
                    {
                    pushFollow(FOLLOW_indirection_feature_part_in_supplier_indirection4242);
                    ifp=indirection_feature_part();

                    state._fsp--;
                    if (state.failed) return indirection;
                    if ( state.backtracking==0 ) {
                       start = (ifp!=null?((Token)ifp.start):null); 
                    }
                    match(input,34,FOLLOW_34_in_supplier_indirection4246); if (state.failed) return indirection;

                    }
                    break;

            }

            pushFollow(FOLLOW_generic_indirection_in_supplier_indirection4255);
            gi=generic_indirection();

            state._fsp--;
            if (state.failed) return indirection;
            if ( state.backtracking==0 ) {
               if (start==null) start=(gi!=null?((Token)gi.start):null); 
            }
            if ( state.backtracking==0 ) {
               indirection = SupplierIndirection.mk(part, (gi!=null?gi.indirection:null),getSLoc(start,(gi!=null?((Token)gi.stop):null))); 
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
    // BON.g:664:1: indirection_feature_part returns [IndirectionFeaturePart part] : ( feature_name | indirection_feature_list );
    public final BONParser.indirection_feature_part_return indirection_feature_part() throws RecognitionException {
        BONParser.indirection_feature_part_return retval = new BONParser.indirection_feature_part_return();
        retval.start = input.LT(1);

        BONParser.feature_name_return feature_name70 = null;

        IndirectionFeatureList indirection_feature_list71 = null;


        try {
            // BON.g:664:64: ( feature_name | indirection_feature_list )
            int alt88=2;
            int LA88_0 = input.LA(1);

            if ( (LA88_0==IDENTIFIER||LA88_0==78||LA88_0==80) ) {
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
                    // BON.g:665:4: feature_name
                    {
                    pushFollow(FOLLOW_feature_name_in_indirection_feature_part4304);
                    feature_name70=feature_name();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.part = (feature_name70!=null?feature_name70.name:null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:667:4: indirection_feature_list
                    {
                    pushFollow(FOLLOW_indirection_feature_list_in_indirection_feature_part4315);
                    indirection_feature_list71=indirection_feature_list();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.part = indirection_feature_list71; 
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
    // BON.g:671:1: indirection_feature_list returns [IndirectionFeatureList list] : s= '(' fnl= feature_name_list e= ')' ;
    public final IndirectionFeatureList indirection_feature_list() throws RecognitionException {
        IndirectionFeatureList list = null;

        Token s=null;
        Token e=null;
        BONParser.feature_name_list_return fnl = null;


        try {
            // BON.g:671:64: (s= '(' fnl= feature_name_list e= ')' )
            // BON.g:672:3: s= '(' fnl= feature_name_list e= ')'
            {
            s=(Token)match(input,42,FOLLOW_42_in_indirection_feature_list4365); if (state.failed) return list;
            pushFollow(FOLLOW_feature_name_list_in_indirection_feature_list4369);
            fnl=feature_name_list();

            state._fsp--;
            if (state.failed) return list;
            e=(Token)match(input,43,FOLLOW_43_in_indirection_feature_list4373); if (state.failed) return list;
            if ( state.backtracking==0 ) {
               list = IndirectionFeatureList.mk((fnl!=null?fnl.list:null),getSLoc(s,e)); 
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
    // BON.g:676:1: parent_indirection returns [ParentIndirection indirection] : '->' gi= generic_indirection ;
    public final ParentIndirection parent_indirection() throws RecognitionException {
        ParentIndirection indirection = null;

        BONParser.generic_indirection_return gi = null;


        try {
            // BON.g:676:60: ( '->' gi= generic_indirection )
            // BON.g:677:3: '->' gi= generic_indirection
            {
            match(input,65,FOLLOW_65_in_parent_indirection4421); if (state.failed) return indirection;
            pushFollow(FOLLOW_generic_indirection_in_parent_indirection4425);
            gi=generic_indirection();

            state._fsp--;
            if (state.failed) return indirection;
            if ( state.backtracking==0 ) {
               indirection = ParentIndirection.mk((gi!=null?gi.indirection:null),getSLoc((gi!=null?((Token)gi.start):null),(gi!=null?((Token)gi.stop):null))); 
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
    // BON.g:681:1: generic_indirection returns [GenericIndirection indirection] : ie= indirection_element ;
    public final BONParser.generic_indirection_return generic_indirection() throws RecognitionException {
        BONParser.generic_indirection_return retval = new BONParser.generic_indirection_return();
        retval.start = input.LT(1);

        BONParser.indirection_element_return ie = null;


        try {
            // BON.g:683:62: (ie= indirection_element )
            // BON.g:687:5: ie= indirection_element
            {
            pushFollow(FOLLOW_indirection_element_in_generic_indirection4477);
            ie=indirection_element();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.indirection = GenericIndirection.mk((ie!=null?ie.el:null),getSLoc((ie!=null?((Token)ie.start):null),(ie!=null?((Token)ie.stop):null))); 
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
    // BON.g:691:1: named_indirection returns [NamedIndirection indirection] : (cn= class_name '[' il= indirection_list e= ']' | s= '[' indirection_list ']' );
    public final NamedIndirection named_indirection() throws RecognitionException {
        NamedIndirection indirection = null;

        Token e=null;
        Token s=null;
        BONParser.class_name_return cn = null;

        List<IndirectionElement> il = null;


        try {
            // BON.g:691:58: (cn= class_name '[' il= indirection_list e= ']' | s= '[' indirection_list ']' )
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
                    // BON.g:692:4: cn= class_name '[' il= indirection_list e= ']'
                    {
                    pushFollow(FOLLOW_class_name_in_named_indirection4522);
                    cn=class_name();

                    state._fsp--;
                    if (state.failed) return indirection;
                    match(input,66,FOLLOW_66_in_named_indirection4524); if (state.failed) return indirection;
                    pushFollow(FOLLOW_indirection_list_in_named_indirection4528);
                    il=indirection_list();

                    state._fsp--;
                    if (state.failed) return indirection;
                    e=(Token)match(input,67,FOLLOW_67_in_named_indirection4532); if (state.failed) return indirection;
                    if ( state.backtracking==0 ) {
                       indirection = NamedIndirection.mk((cn!=null?cn.name:null), il, getSLoc((cn!=null?((Token)cn.start):null),e)); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:695:4: s= '[' indirection_list ']'
                    {
                    s=(Token)match(input,66,FOLLOW_66_in_named_indirection4547); if (state.failed) return indirection;
                    pushFollow(FOLLOW_indirection_list_in_named_indirection4549);
                    indirection_list();

                    state._fsp--;
                    if (state.failed) return indirection;
                    match(input,67,FOLLOW_67_in_named_indirection4551); if (state.failed) return indirection;
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
    // BON.g:699:1: indirection_list returns [List<IndirectionElement> list] : i1= indirection_element ( ',' i= indirection_element )* ;
    public final List<IndirectionElement> indirection_list() throws RecognitionException {
        List<IndirectionElement> list = null;

        BONParser.indirection_element_return i1 = null;

        BONParser.indirection_element_return i = null;


        try {
            // BON.g:699:58: (i1= indirection_element ( ',' i= indirection_element )* )
            // BON.g:700:3: i1= indirection_element ( ',' i= indirection_element )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_indirection_element_in_indirection_list4598);
            i1=indirection_element();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               list.add((i1!=null?i1.el:null)); 
            }
            // BON.g:703:3: ( ',' i= indirection_element )*
            loop90:
            do {
                int alt90=2;
                int LA90_0 = input.LA(1);

                if ( (LA90_0==35) ) {
                    alt90=1;
                }


                switch (alt90) {
            	case 1 :
            	    // BON.g:703:4: ',' i= indirection_element
            	    {
            	    match(input,35,FOLLOW_35_in_indirection_list4608); if (state.failed) return list;
            	    pushFollow(FOLLOW_indirection_element_in_indirection_list4612);
            	    i=indirection_element();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       list.add((i!=null?i.el:null)); 
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
    // BON.g:708:1: indirection_element returns [IndirectionElement el] : (t= '...' | named_indirection | class_name );
    public final BONParser.indirection_element_return indirection_element() throws RecognitionException {
        BONParser.indirection_element_return retval = new BONParser.indirection_element_return();
        retval.start = input.LT(1);

        Token t=null;
        NamedIndirection named_indirection72 = null;

        BONParser.class_name_return class_name73 = null;


        try {
            // BON.g:708:53: (t= '...' | named_indirection | class_name )
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

                if ( (LA91_2==66) ) {
                    alt91=2;
                }
                else if ( (LA91_2==35||LA91_2==63||LA91_2==67) ) {
                    alt91=3;
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
                    // BON.g:709:4: t= '...'
                    {
                    t=(Token)match(input,68,FOLLOW_68_in_indirection_element4666); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.el = CompactedIndirectionElementImpl.mk(getSLoc(t)); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:711:4: named_indirection
                    {
                    pushFollow(FOLLOW_named_indirection_in_indirection_element4676);
                    named_indirection72=named_indirection();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.el = named_indirection72; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:713:4: class_name
                    {
                    pushFollow(FOLLOW_class_name_in_indirection_element4687);
                    class_name73=class_name();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.el = (class_name73!=null?class_name73.name:null); 
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
    // BON.g:718:1: type_mark returns [TypeMark mark] : (m= ':' | m= ':{' | sm= shared_mark );
    public final BONParser.type_mark_return type_mark() throws RecognitionException {
        BONParser.type_mark_return retval = new BONParser.type_mark_return();
        retval.start = input.LT(1);

        Token m=null;
        TypeMark sm = null;


        try {
            // BON.g:718:35: (m= ':' | m= ':{' | sm= shared_mark )
            int alt92=3;
            int LA92_0 = input.LA(1);

            if ( (LA92_0==34) ) {
                int LA92_1 = input.LA(2);

                if ( (LA92_1==42) ) {
                    alt92=3;
                }
                else if ( (LA92_1==IDENTIFIER) ) {
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
                    // BON.g:719:4: m= ':'
                    {
                    m=(Token)match(input,34,FOLLOW_34_in_type_mark4732); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.mark = TypeMark.mk(TypeMark.Mark.HASTYPE, null, getSLoc(m)); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:721:4: m= ':{'
                    {
                    m=(Token)match(input,69,FOLLOW_69_in_type_mark4745); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.mark = TypeMark.mk(TypeMark.Mark.AGGREGATE, null, getSLoc(m)); 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:723:4: sm= shared_mark
                    {
                    pushFollow(FOLLOW_shared_mark_in_type_mark4758);
                    sm=shared_mark();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.mark = sm; 
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
    // BON.g:727:1: shared_mark returns [TypeMark mark] : a= ':' '(' m= multiplicity b= ')' ;
    public final TypeMark shared_mark() throws RecognitionException {
        TypeMark mark = null;

        Token a=null;
        Token b=null;
        BONParser.multiplicity_return m = null;


        try {
            // BON.g:727:37: (a= ':' '(' m= multiplicity b= ')' )
            // BON.g:728:3: a= ':' '(' m= multiplicity b= ')'
            {
            a=(Token)match(input,34,FOLLOW_34_in_shared_mark4804); if (state.failed) return mark;
            match(input,42,FOLLOW_42_in_shared_mark4806); if (state.failed) return mark;
            pushFollow(FOLLOW_multiplicity_in_shared_mark4810);
            m=multiplicity();

            state._fsp--;
            if (state.failed) return mark;
            b=(Token)match(input,43,FOLLOW_43_in_shared_mark4814); if (state.failed) return mark;
            if ( state.backtracking==0 ) {
               mark = TypeMark.mk(TypeMark.Mark.SHAREDMARK, m.num, getSLoc(a, b)); 
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
    // BON.g:732:1: child returns [StaticRef ref] : s= static_ref ;
    public final BONParser.child_return child() throws RecognitionException {
        BONParser.child_return retval = new BONParser.child_return();
        retval.start = input.LT(1);

        StaticRef s = null;


        try {
            // BON.g:734:31: (s= static_ref )
            // BON.g:735:3: s= static_ref
            {
            pushFollow(FOLLOW_static_ref_in_child4838);
            s=static_ref();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.ref = s; 
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
    // BON.g:739:1: parent returns [StaticRef ref] : s= static_ref ;
    public final BONParser.parent_return parent() throws RecognitionException {
        BONParser.parent_return retval = new BONParser.parent_return();
        retval.start = input.LT(1);

        StaticRef s = null;


        try {
            // BON.g:739:32: (s= static_ref )
            // BON.g:740:3: s= static_ref
            {
            pushFollow(FOLLOW_static_ref_in_parent4866);
            s=static_ref();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.ref = s; 
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
    // BON.g:744:1: client returns [StaticRef ref] : s= static_ref ;
    public final BONParser.client_return client() throws RecognitionException {
        BONParser.client_return retval = new BONParser.client_return();
        retval.start = input.LT(1);

        StaticRef s = null;


        try {
            // BON.g:744:32: (s= static_ref )
            // BON.g:745:3: s= static_ref
            {
            pushFollow(FOLLOW_static_ref_in_client4904);
            s=static_ref();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.ref = s; 
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
    // BON.g:749:1: supplier returns [StaticRef ref] : s= static_ref ;
    public final BONParser.supplier_return supplier() throws RecognitionException {
        BONParser.supplier_return retval = new BONParser.supplier_return();
        retval.start = input.LT(1);

        StaticRef s = null;


        try {
            // BON.g:749:34: (s= static_ref )
            // BON.g:750:3: s= static_ref
            {
            pushFollow(FOLLOW_static_ref_in_supplier4934);
            s=static_ref();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.ref = s; 
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
    // BON.g:754:1: static_ref returns [StaticRef ref] : (s= static_component_name | cp= cluster_prefix s= static_component_name );
    public final StaticRef static_ref() throws RecognitionException {
        StaticRef ref = null;

        BONParser.static_component_name_return s = null;

        BONParser.cluster_prefix_return cp = null;


        try {
            // BON.g:754:36: (s= static_component_name | cp= cluster_prefix s= static_component_name )
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
                    // BON.g:755:4: s= static_component_name
                    {
                    pushFollow(FOLLOW_static_component_name_in_static_ref4968);
                    s=static_component_name();

                    state._fsp--;
                    if (state.failed) return ref;
                    if ( state.backtracking==0 ) {
                       List<StaticRefPart> empty = emptyList(); ref = StaticRef.mk(empty, (s!=null?s.ref:null), getSLoc((s!=null?((Token)s.start):null),(s!=null?((Token)s.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:758:4: cp= cluster_prefix s= static_component_name
                    {
                    pushFollow(FOLLOW_cluster_prefix_in_static_ref4984);
                    cp=cluster_prefix();

                    state._fsp--;
                    if (state.failed) return ref;
                    pushFollow(FOLLOW_static_component_name_in_static_ref4988);
                    s=static_component_name();

                    state._fsp--;
                    if (state.failed) return ref;
                    if ( state.backtracking==0 ) {
                       ref = StaticRef.mk((cp!=null?cp.prefix:null), (s!=null?s.ref:null), getSLoc((cp!=null?((Token)cp.start):null),(s!=null?((Token)s.stop):null))); 
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
    // BON.g:762:1: cluster_prefix returns [List<StaticRefPart> prefix] : c1= cluster_name '.' (c= cluster_name '.' )* ;
    public final BONParser.cluster_prefix_return cluster_prefix() throws RecognitionException {
        BONParser.cluster_prefix_return retval = new BONParser.cluster_prefix_return();
        retval.start = input.LT(1);

        BONParser.cluster_name_return c1 = null;

        BONParser.cluster_name_return c = null;


        try {
            // BON.g:762:53: (c1= cluster_name '.' (c= cluster_name '.' )* )
            // BON.g:763:3: c1= cluster_name '.' (c= cluster_name '.' )*
            {
            if ( state.backtracking==0 ) {
               retval.prefix = createList(); 
            }
            pushFollow(FOLLOW_cluster_name_in_cluster_prefix5027);
            c1=cluster_name();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.prefix.add(StaticRefPart.mk((c1!=null?c1.name:null), getSLoc((c1!=null?((Token)c1.start):null),(c1!=null?((Token)c1.stop):null)))); 
            }
            match(input,70,FOLLOW_70_in_cluster_prefix5036); if (state.failed) return retval;
            // BON.g:767:3: (c= cluster_name '.' )*
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
            	    // BON.g:767:5: c= cluster_name '.'
            	    {
            	    pushFollow(FOLLOW_cluster_name_in_cluster_prefix5045);
            	    c=cluster_name();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    match(input,70,FOLLOW_70_in_cluster_prefix5047); if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       retval.prefix.add(StaticRefPart.mk((c!=null?c.name:null), getSLoc((c!=null?((Token)c.start):null),(c!=null?((Token)c.stop):null)))); 
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
    // BON.g:774:1: static_component_name returns [StaticRefPart ref] : i= IDENTIFIER ;
    public final BONParser.static_component_name_return static_component_name() throws RecognitionException {
        BONParser.static_component_name_return retval = new BONParser.static_component_name_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // BON.g:774:51: (i= IDENTIFIER )
            // BON.g:775:3: i= IDENTIFIER
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_static_component_name5079); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.ref = StaticRefPart.mk((i!=null?i.getText():null), getSLoc(i)); 
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
    // BON.g:779:1: multiplicity returns [Integer num] : i= INTEGER ;
    public final BONParser.multiplicity_return multiplicity() throws RecognitionException {
        BONParser.multiplicity_return retval = new BONParser.multiplicity_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // BON.g:779:36: (i= INTEGER )
            // BON.g:780:3: i= INTEGER
            {
            i=(Token)match(input,INTEGER,FOLLOW_INTEGER_in_multiplicity5123); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.num = new Integer((i!=null?i.getText():null)); 
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
    // BON.g:784:1: semantic_label returns [String label] : m= MANIFEST_STRING ;
    public final BONParser.semantic_label_return semantic_label() throws RecognitionException {
        BONParser.semantic_label_return retval = new BONParser.semantic_label_return();
        retval.start = input.LT(1);

        Token m=null;

        try {
            // BON.g:784:39: (m= MANIFEST_STRING )
            // BON.g:785:3: m= MANIFEST_STRING
            {
            m=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_semantic_label5159); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.label = (m!=null?m.getText():null); 
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
    // BON.g:789:1: class_interface returns [ClassInterface ci] : ( indexing )? (pcl= parent_class_list | ) features (inv= class_invariant | ) e= 'end' ;
    public final BONParser.class_interface_return class_interface() throws RecognitionException {
        BONParser.class_interface_return retval = new BONParser.class_interface_return();
        retval.start = input.LT(1);

        Token e=null;
        BONParser.parent_class_list_return pcl = null;

        List<Expression> inv = null;

        BONParser.indexing_return indexing74 = null;

        BONParser.features_return features75 = null;


         Indexing indexing = null; List<Type> parents = null; List<Expression> invariant = null; Token start = null; 
        try {
            // BON.g:795:1: ( ( indexing )? (pcl= parent_class_list | ) features (inv= class_invariant | ) e= 'end' )
            // BON.g:796:3: ( indexing )? (pcl= parent_class_list | ) features (inv= class_invariant | ) e= 'end'
            {
            // BON.g:796:3: ( indexing )?
            int alt95=2;
            int LA95_0 = input.LA(1);

            if ( (LA95_0==30) ) {
                alt95=1;
            }
            switch (alt95) {
                case 1 :
                    // BON.g:796:4: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_class_interface5188);
                    indexing74=indexing();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       indexing = (indexing74!=null?indexing74.indexing:null); start = (indexing74!=null?((Token)indexing74.start):null); 
                    }

                    }
                    break;

            }

            // BON.g:797:3: (pcl= parent_class_list | )
            int alt96=2;
            int LA96_0 = input.LA(1);

            if ( (LA96_0==38) ) {
                alt96=1;
            }
            else if ( (LA96_0==72) ) {
                alt96=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 96, 0, input);

                throw nvae;
            }
            switch (alt96) {
                case 1 :
                    // BON.g:797:6: pcl= parent_class_list
                    {
                    pushFollow(FOLLOW_parent_class_list_in_class_interface5202);
                    pcl=parent_class_list();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       parents = (pcl!=null?pcl.parents:null); if (start == null) start = (pcl!=null?((Token)pcl.start):null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:798:6: 
                    {
                    if ( state.backtracking==0 ) {
                       parents = emptyList(); 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_features_in_class_interface5220);
            features75=features();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               if (start == null) start = (features75!=null?((Token)features75.start):null); 
            }
            // BON.g:802:3: (inv= class_invariant | )
            int alt97=2;
            int LA97_0 = input.LA(1);

            if ( (LA97_0==71) ) {
                alt97=1;
            }
            else if ( (LA97_0==25) ) {
                alt97=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 97, 0, input);

                throw nvae;
            }
            switch (alt97) {
                case 1 :
                    // BON.g:802:6: inv= class_invariant
                    {
                    pushFollow(FOLLOW_class_invariant_in_class_interface5233);
                    inv=class_invariant();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       invariant = inv; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:803:6: 
                    {
                    if ( state.backtracking==0 ) {
                       invariant = emptyList(); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_class_interface5253); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.ci = ClassInterface.mk((features75!=null?features75.features:null), parents, invariant, indexing, getSLoc(start, e)); 
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
    // $ANTLR end "class_interface"


    // $ANTLR start "class_invariant"
    // BON.g:809:1: class_invariant returns [List<Expression> invariant] : 'invariant' assertion ;
    public final List<Expression> class_invariant() throws RecognitionException {
        List<Expression> invariant = null;

        List<Expression> assertion76 = null;


        try {
            // BON.g:809:54: ( 'invariant' assertion )
            // BON.g:810:3: 'invariant' assertion
            {
            match(input,71,FOLLOW_71_in_class_invariant5292); if (state.failed) return invariant;
            pushFollow(FOLLOW_assertion_in_class_invariant5294);
            assertion76=assertion();

            state._fsp--;
            if (state.failed) return invariant;
            if ( state.backtracking==0 ) {
               invariant = assertion76; 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return invariant;
    }
    // $ANTLR end "class_invariant"

    public static class parent_class_list_return extends ParserRuleReturnScope {
        public List<Type> parents;
    };

    // $ANTLR start "parent_class_list"
    // BON.g:814:1: parent_class_list returns [List<Type> parents] : ( 'inherit' c1= class_type ( ';' c= class_type )* ( ';' )? | i= 'inherit' );
    public final BONParser.parent_class_list_return parent_class_list() throws RecognitionException {
        BONParser.parent_class_list_return retval = new BONParser.parent_class_list_return();
        retval.start = input.LT(1);

        Token i=null;
        BONParser.class_type_return c1 = null;

        BONParser.class_type_return c = null;


        try {
            // BON.g:814:48: ( 'inherit' c1= class_type ( ';' c= class_type )* ( ';' )? | i= 'inherit' )
            int alt100=2;
            int LA100_0 = input.LA(1);

            if ( (LA100_0==38) ) {
                int LA100_1 = input.LA(2);

                if ( (LA100_1==IDENTIFIER) ) {
                    alt100=1;
                }
                else if ( (LA100_1==72) ) {
                    alt100=2;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 100, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 100, 0, input);

                throw nvae;
            }
            switch (alt100) {
                case 1 :
                    // BON.g:815:3: 'inherit' c1= class_type ( ';' c= class_type )* ( ';' )?
                    {
                    if ( state.backtracking==0 ) {
                       retval.parents = createList(); 
                    }
                    match(input,38,FOLLOW_38_in_parent_class_list5335); if (state.failed) return retval;
                    pushFollow(FOLLOW_class_type_in_parent_class_list5339);
                    c1=class_type();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.parents.add((c1!=null?c1.type:null)); 
                    }
                    // BON.g:818:3: ( ';' c= class_type )*
                    loop98:
                    do {
                        int alt98=2;
                        int LA98_0 = input.LA(1);

                        if ( (LA98_0==33) ) {
                            int LA98_1 = input.LA(2);

                            if ( (LA98_1==IDENTIFIER) ) {
                                alt98=1;
                            }


                        }


                        switch (alt98) {
                    	case 1 :
                    	    // BON.g:818:4: ';' c= class_type
                    	    {
                    	    match(input,33,FOLLOW_33_in_parent_class_list5350); if (state.failed) return retval;
                    	    pushFollow(FOLLOW_class_type_in_parent_class_list5354);
                    	    c=class_type();

                    	    state._fsp--;
                    	    if (state.failed) return retval;
                    	    if ( state.backtracking==0 ) {
                    	       retval.parents.add((c!=null?c.type:null)); 
                    	    }

                    	    }
                    	    break;

                    	default :
                    	    break loop98;
                        }
                    } while (true);

                    // BON.g:821:3: ( ';' )?
                    int alt99=2;
                    int LA99_0 = input.LA(1);

                    if ( (LA99_0==33) ) {
                        alt99=1;
                    }
                    switch (alt99) {
                        case 1 :
                            // BON.g:821:3: ';'
                            {
                            match(input,33,FOLLOW_33_in_parent_class_list5371); if (state.failed) return retval;

                            }
                            break;

                    }


                    }
                    break;
                case 2 :
                    // BON.g:823:3: i= 'inherit'
                    {
                    i=(Token)match(input,38,FOLLOW_38_in_parent_class_list5382); if (state.failed) return retval;
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
    // BON.g:827:1: features returns [List<Feature> features] : ( feature_clause )+ ;
    public final BONParser.features_return features() throws RecognitionException {
        BONParser.features_return retval = new BONParser.features_return();
        retval.start = input.LT(1);

        Feature feature_clause77 = null;


        try {
            // BON.g:827:43: ( ( feature_clause )+ )
            // BON.g:828:3: ( feature_clause )+
            {
            if ( state.backtracking==0 ) {
               retval.features = createList(); 
            }
            // BON.g:829:3: ( feature_clause )+
            int cnt101=0;
            loop101:
            do {
                int alt101=2;
                int LA101_0 = input.LA(1);

                if ( (LA101_0==72) ) {
                    alt101=1;
                }


                switch (alt101) {
            	case 1 :
            	    // BON.g:829:4: feature_clause
            	    {
            	    pushFollow(FOLLOW_feature_clause_in_features5426);
            	    feature_clause77=feature_clause();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       retval.features.add(feature_clause77); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt101 >= 1 ) break loop101;
            	    if (state.backtracking>0) {state.failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(101, input);
                        throw eee;
                }
                cnt101++;
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
    // BON.g:832:1: feature_clause returns [Feature feature] : f= 'feature' (se= selective_export | ) (c= COMMENT )? fs= feature_specifications ;
    public final Feature feature_clause() throws RecognitionException {
        Feature feature = null;

        Token f=null;
        Token c=null;
        List<ClassName> se = null;

        BONParser.feature_specifications_return fs = null;


         String comment = null; List<ClassName> selectiveExport = null; 
        try {
            // BON.g:836:1: (f= 'feature' (se= selective_export | ) (c= COMMENT )? fs= feature_specifications )
            // BON.g:837:3: f= 'feature' (se= selective_export | ) (c= COMMENT )? fs= feature_specifications
            {
            f=(Token)match(input,72,FOLLOW_72_in_feature_clause5467); if (state.failed) return feature;
            // BON.g:838:3: (se= selective_export | )
            int alt102=2;
            int LA102_0 = input.LA(1);

            if ( (LA102_0==62) ) {
                alt102=1;
            }
            else if ( ((LA102_0>=IDENTIFIER && LA102_0<=COMMENT)||(LA102_0>=58 && LA102_0<=59)||LA102_0==73||LA102_0==78||LA102_0==80) ) {
                alt102=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return feature;}
                NoViableAltException nvae =
                    new NoViableAltException("", 102, 0, input);

                throw nvae;
            }
            switch (alt102) {
                case 1 :
                    // BON.g:838:6: se= selective_export
                    {
                    pushFollow(FOLLOW_selective_export_in_feature_clause5477);
                    se=selective_export();

                    state._fsp--;
                    if (state.failed) return feature;
                    if ( state.backtracking==0 ) {
                       selectiveExport = se; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:839:6: 
                    {
                    if ( state.backtracking==0 ) {
                       selectiveExport = emptyList(); 
                    }

                    }
                    break;

            }

            // BON.g:841:3: (c= COMMENT )?
            int alt103=2;
            int LA103_0 = input.LA(1);

            if ( (LA103_0==COMMENT) ) {
                alt103=1;
            }
            switch (alt103) {
                case 1 :
                    // BON.g:841:4: c= COMMENT
                    {
                    c=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_feature_clause5499); if (state.failed) return feature;
                    if ( state.backtracking==0 ) {
                       comment = (c!=null?c.getText():null); 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_feature_specifications_in_feature_clause5511);
            fs=feature_specifications();

            state._fsp--;
            if (state.failed) return feature;
            if ( state.backtracking==0 ) {
               feature = Feature.mk((fs!=null?fs.specs:null), selectiveExport, comment, getSLoc(f,(fs!=null?((Token)fs.stop):null))); 
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
    // BON.g:846:1: feature_specifications returns [List<FeatureSpecification> specs] : (fs= feature_specification )+ ;
    public final BONParser.feature_specifications_return feature_specifications() throws RecognitionException {
        BONParser.feature_specifications_return retval = new BONParser.feature_specifications_return();
        retval.start = input.LT(1);

        FeatureSpecification fs = null;


        try {
            // BON.g:846:67: ( (fs= feature_specification )+ )
            // BON.g:847:3: (fs= feature_specification )+
            {
            if ( state.backtracking==0 ) {
               retval.specs = createList(); 
            }
            // BON.g:848:3: (fs= feature_specification )+
            int cnt104=0;
            loop104:
            do {
                int alt104=2;
                int LA104_0 = input.LA(1);

                if ( (LA104_0==IDENTIFIER||(LA104_0>=58 && LA104_0<=59)||LA104_0==73||LA104_0==78||LA104_0==80) ) {
                    alt104=1;
                }


                switch (alt104) {
            	case 1 :
            	    // BON.g:848:4: fs= feature_specification
            	    {
            	    pushFollow(FOLLOW_feature_specification_in_feature_specifications5554);
            	    fs=feature_specification();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       retval.specs.add(fs); 
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
    // BON.g:851:1: feature_specification returns [FeatureSpecification spec] : (d= 'deferred' | e= 'effective' | r= 'redefined' | ) fnl= feature_name_list ( has_type )? (rc= rename_clause )? (c= COMMENT )? (fa= feature_arguments | ) (cc= contract_clause | ) ;
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

        BONParser.has_type_return has_type78 = null;


         FeatureSpecification.Modifier modifier = FeatureSpecification.Modifier.NONE; 
                List<FeatureArgument> args = null; HasType hasType = null; Token start = null; Token end = null;
                RenameClause renaming = null; String comment = null; ContractClause contracts = null;
        try {
            // BON.g:855:1: ( (d= 'deferred' | e= 'effective' | r= 'redefined' | ) fnl= feature_name_list ( has_type )? (rc= rename_clause )? (c= COMMENT )? (fa= feature_arguments | ) (cc= contract_clause | ) )
            // BON.g:856:3: (d= 'deferred' | e= 'effective' | r= 'redefined' | ) fnl= feature_name_list ( has_type )? (rc= rename_clause )? (c= COMMENT )? (fa= feature_arguments | ) (cc= contract_clause | )
            {
            // BON.g:856:3: (d= 'deferred' | e= 'effective' | r= 'redefined' | )
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
            case 78:
            case 80:
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
                    // BON.g:856:6: d= 'deferred'
                    {
                    d=(Token)match(input,58,FOLLOW_58_in_feature_specification5609); if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       modifier = FeatureSpecification.Modifier.DEFERRED; start = d; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:857:6: e= 'effective'
                    {
                    e=(Token)match(input,59,FOLLOW_59_in_feature_specification5622); if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       modifier = FeatureSpecification.Modifier.EFFECTIVE; start = e; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:858:6: r= 'redefined'
                    {
                    r=(Token)match(input,73,FOLLOW_73_in_feature_specification5633); if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       modifier = FeatureSpecification.Modifier.REDEFINED; start = r; 
                    }

                    }
                    break;
                case 4 :
                    // BON.g:859:18: 
                    {
                    if ( state.backtracking==0 ) {
                       modifier = FeatureSpecification.Modifier.NONE; 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_feature_name_list_in_feature_specification5664);
            fnl=feature_name_list();

            state._fsp--;
            if (state.failed) return spec;
            if ( state.backtracking==0 ) {
               end=(fnl!=null?((Token)fnl.stop):null); if (start==null) start=(fnl!=null?((Token)fnl.start):null); 
            }
            // BON.g:863:3: ( has_type )?
            int alt106=2;
            int LA106_0 = input.LA(1);

            if ( (LA106_0==34||LA106_0==69) ) {
                alt106=1;
            }
            switch (alt106) {
                case 1 :
                    // BON.g:863:4: has_type
                    {
                    pushFollow(FOLLOW_has_type_in_feature_specification5673);
                    has_type78=has_type();

                    state._fsp--;
                    if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       hasType = (has_type78!=null?has_type78.htype:null); end=(has_type78!=null?((Token)has_type78.stop):null); 
                    }

                    }
                    break;

            }

            // BON.g:864:3: (rc= rename_clause )?
            int alt107=2;
            int LA107_0 = input.LA(1);

            if ( (LA107_0==62) ) {
                alt107=1;
            }
            switch (alt107) {
                case 1 :
                    // BON.g:864:4: rc= rename_clause
                    {
                    pushFollow(FOLLOW_rename_clause_in_feature_specification5685);
                    rc=rename_clause();

                    state._fsp--;
                    if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       renaming = (rc!=null?rc.rename:null); end=(rc!=null?((Token)rc.stop):null); 
                    }

                    }
                    break;

            }

            // BON.g:865:3: (c= COMMENT )?
            int alt108=2;
            int LA108_0 = input.LA(1);

            if ( (LA108_0==COMMENT) ) {
                alt108=1;
            }
            switch (alt108) {
                case 1 :
                    // BON.g:865:4: c= COMMENT
                    {
                    c=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_feature_specification5697); if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       comment = (c!=null?c.getText():null); end=c; 
                    }

                    }
                    break;

            }

            // BON.g:866:3: (fa= feature_arguments | )
            int alt109=2;
            int LA109_0 = input.LA(1);

            if ( (LA109_0==65||LA109_0==77) ) {
                alt109=1;
            }
            else if ( (LA109_0==IDENTIFIER||LA109_0==25||(LA109_0>=58 && LA109_0<=59)||(LA109_0>=71 && LA109_0<=75)||LA109_0==78||LA109_0==80) ) {
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
                    // BON.g:866:6: fa= feature_arguments
                    {
                    pushFollow(FOLLOW_feature_arguments_in_feature_specification5711);
                    fa=feature_arguments();

                    state._fsp--;
                    if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       args = (fa!=null?fa.args:null); end=(fa!=null?((Token)fa.stop):null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:868:6: 
                    {
                    if ( state.backtracking==0 ) {
                       args = emptyList(); 
                    }

                    }
                    break;

            }

            // BON.g:870:3: (cc= contract_clause | )
            int alt110=2;
            int LA110_0 = input.LA(1);

            if ( ((LA110_0>=74 && LA110_0<=75)) ) {
                alt110=1;
            }
            else if ( (LA110_0==IDENTIFIER||LA110_0==25||(LA110_0>=58 && LA110_0<=59)||(LA110_0>=71 && LA110_0<=73)||LA110_0==78||LA110_0==80) ) {
                alt110=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return spec;}
                NoViableAltException nvae =
                    new NoViableAltException("", 110, 0, input);

                throw nvae;
            }
            switch (alt110) {
                case 1 :
                    // BON.g:870:6: cc= contract_clause
                    {
                    pushFollow(FOLLOW_contract_clause_in_feature_specification5738);
                    cc=contract_clause();

                    state._fsp--;
                    if (state.failed) return spec;
                    if ( state.backtracking==0 ) {
                       contracts = (cc!=null?cc.contracts:null); end=(cc!=null?((Token)cc.stop):null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:872:6: 
                    {
                    if ( state.backtracking==0 ) {
                       contracts = Constants.EMPTY_CONTRACT; 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               spec = FeatureSpecification.mk(modifier, (fnl!=null?fnl.list:null), args, contracts, hasType, renaming, comment, getSLoc(start,end)); 
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
    // BON.g:877:1: has_type returns [HasType htype] : type_mark type ;
    public final BONParser.has_type_return has_type() throws RecognitionException {
        BONParser.has_type_return retval = new BONParser.has_type_return();
        retval.start = input.LT(1);

        BONParser.type_mark_return type_mark79 = null;

        BONParser.type_return type80 = null;


        try {
            // BON.g:877:34: ( type_mark type )
            // BON.g:878:3: type_mark type
            {
            pushFollow(FOLLOW_type_mark_in_has_type5801);
            type_mark79=type_mark();

            state._fsp--;
            if (state.failed) return retval;
            pushFollow(FOLLOW_type_in_has_type5803);
            type80=type();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.htype = HasType.mk((type_mark79!=null?type_mark79.mark:null), (type80!=null?type80.type:null), getSLoc((type_mark79!=null?((Token)type_mark79.start):null),(type80!=null?((Token)type80.stop):null))); 
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
    // BON.g:882:1: contract_clause returns [ContractClause contracts] : cc= contracting_conditions 'end' ;
    public final BONParser.contract_clause_return contract_clause() throws RecognitionException {
        BONParser.contract_clause_return retval = new BONParser.contract_clause_return();
        retval.start = input.LT(1);

        ContractClause cc = null;


        try {
            // BON.g:884:52: (cc= contracting_conditions 'end' )
            // BON.g:885:3: cc= contracting_conditions 'end'
            {
            pushFollow(FOLLOW_contracting_conditions_in_contract_clause5828);
            cc=contracting_conditions();

            state._fsp--;
            if (state.failed) return retval;
            match(input,25,FOLLOW_25_in_contract_clause5830); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.contracts = cc; 
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
    // BON.g:890:1: contracting_conditions returns [ContractClause contracts] : ( (pre= precondition (post= postcondition )? ) | post= postcondition ) ;
    public final ContractClause contracting_conditions() throws RecognitionException {
        ContractClause contracts = null;

        BONParser.precondition_return pre = null;

        BONParser.postcondition_return post = null;


         List<Expression> postC = null; 
        try {
            // BON.g:892:1: ( ( (pre= precondition (post= postcondition )? ) | post= postcondition ) )
            // BON.g:893:3: ( (pre= precondition (post= postcondition )? ) | post= postcondition )
            {
            // BON.g:893:3: ( (pre= precondition (post= postcondition )? ) | post= postcondition )
            int alt112=2;
            int LA112_0 = input.LA(1);

            if ( (LA112_0==74) ) {
                alt112=1;
            }
            else if ( (LA112_0==75) ) {
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
                    // BON.g:893:6: (pre= precondition (post= postcondition )? )
                    {
                    // BON.g:893:6: (pre= precondition (post= postcondition )? )
                    // BON.g:893:7: pre= precondition (post= postcondition )?
                    {
                    pushFollow(FOLLOW_precondition_in_contracting_conditions5862);
                    pre=precondition();

                    state._fsp--;
                    if (state.failed) return contracts;
                    // BON.g:893:24: (post= postcondition )?
                    int alt111=2;
                    int LA111_0 = input.LA(1);

                    if ( (LA111_0==75) ) {
                        alt111=1;
                    }
                    switch (alt111) {
                        case 1 :
                            // BON.g:893:25: post= postcondition
                            {
                            pushFollow(FOLLOW_postcondition_in_contracting_conditions5867);
                            post=postcondition();

                            state._fsp--;
                            if (state.failed) return contracts;
                            if ( state.backtracking==0 ) {
                               postC = (post!=null?post.assertions:null); 
                            }

                            }
                            break;

                    }


                    }

                    if ( state.backtracking==0 ) {
                       if (postC == null) contracts = ContractClause.mk((pre!=null?pre.assertions:null), Constants.NO_EXPRESSIONS, getSLoc((pre!=null?((Token)pre.start):null),(pre!=null?((Token)pre.stop):null))); 
                             else contracts = ContractClause.mk((pre!=null?pre.assertions:null), postC, getSLoc((pre!=null?((Token)pre.start):null),(post!=null?((Token)post.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:896:6: post= postcondition
                    {
                    pushFollow(FOLLOW_postcondition_in_contracting_conditions5891);
                    post=postcondition();

                    state._fsp--;
                    if (state.failed) return contracts;
                    if ( state.backtracking==0 ) {
                       contracts = ContractClause.mk(Constants.NO_EXPRESSIONS, (post!=null?post.assertions:null), getSLoc((post!=null?((Token)post.start):null),(post!=null?((Token)post.stop):null))); 
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
    // BON.g:901:1: precondition returns [List<Expression> assertions] : 'require' assertion ;
    public final BONParser.precondition_return precondition() throws RecognitionException {
        BONParser.precondition_return retval = new BONParser.precondition_return();
        retval.start = input.LT(1);

        List<Expression> assertion81 = null;


        try {
            // BON.g:901:52: ( 'require' assertion )
            // BON.g:902:3: 'require' assertion
            {
            match(input,74,FOLLOW_74_in_precondition5917); if (state.failed) return retval;
            pushFollow(FOLLOW_assertion_in_precondition5919);
            assertion81=assertion();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.assertions = assertion81; 
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
    // BON.g:906:1: postcondition returns [List<Expression> assertions] : 'ensure' assertion ;
    public final BONParser.postcondition_return postcondition() throws RecognitionException {
        BONParser.postcondition_return retval = new BONParser.postcondition_return();
        retval.start = input.LT(1);

        List<Expression> assertion82 = null;


        try {
            // BON.g:906:53: ( 'ensure' assertion )
            // BON.g:907:3: 'ensure' assertion
            {
            match(input,75,FOLLOW_75_in_postcondition5953); if (state.failed) return retval;
            pushFollow(FOLLOW_assertion_in_postcondition5955);
            assertion82=assertion();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.assertions = assertion82; 
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
    // BON.g:911:1: selective_export returns [List<ClassName> exports] : '{' cnl= class_name_list '}' ;
    public final List<ClassName> selective_export() throws RecognitionException {
        List<ClassName> exports = null;

        List<ClassName> cnl = null;


        try {
            // BON.g:913:52: ( '{' cnl= class_name_list '}' )
            // BON.g:914:3: '{' cnl= class_name_list '}'
            {
            match(input,62,FOLLOW_62_in_selective_export5978); if (state.failed) return exports;
            pushFollow(FOLLOW_class_name_list_in_selective_export5982);
            cnl=class_name_list();

            state._fsp--;
            if (state.failed) return exports;
            match(input,63,FOLLOW_63_in_selective_export5984); if (state.failed) return exports;
            if ( state.backtracking==0 ) {
               exports = cnl; 
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
    // BON.g:918:1: feature_name_list returns [List<FeatureName> list] : f1= feature_name ( ',' f= feature_name )* ;
    public final BONParser.feature_name_list_return feature_name_list() throws RecognitionException {
        BONParser.feature_name_list_return retval = new BONParser.feature_name_list_return();
        retval.start = input.LT(1);

        BONParser.feature_name_return f1 = null;

        BONParser.feature_name_return f = null;


        try {
            // BON.g:918:52: (f1= feature_name ( ',' f= feature_name )* )
            // BON.g:919:3: f1= feature_name ( ',' f= feature_name )*
            {
            if ( state.backtracking==0 ) {
               retval.list = createList(); 
            }
            pushFollow(FOLLOW_feature_name_in_feature_name_list6029);
            f1=feature_name();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.list.add((f1!=null?f1.name:null)); 
            }
            // BON.g:922:3: ( ',' f= feature_name )*
            loop113:
            do {
                int alt113=2;
                int LA113_0 = input.LA(1);

                if ( (LA113_0==35) ) {
                    alt113=1;
                }


                switch (alt113) {
            	case 1 :
            	    // BON.g:922:4: ',' f= feature_name
            	    {
            	    match(input,35,FOLLOW_35_in_feature_name_list6039); if (state.failed) return retval;
            	    pushFollow(FOLLOW_feature_name_in_feature_name_list6043);
            	    f=feature_name();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       retval.list.add((f!=null?f.name:null)); 
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
    // BON.g:927:1: feature_name returns [FeatureName name] : (i= IDENTIFIER | prefix | infix );
    public final BONParser.feature_name_return feature_name() throws RecognitionException {
        BONParser.feature_name_return retval = new BONParser.feature_name_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // BON.g:927:41: (i= IDENTIFIER | prefix | infix )
            int alt114=3;
            switch ( input.LA(1) ) {
            case IDENTIFIER:
                {
                alt114=1;
                }
                break;
            case 78:
                {
                alt114=2;
                }
                break;
            case 80:
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
                    // BON.g:928:4: i= IDENTIFIER
                    {
                    i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_feature_name6092); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.name = FeatureName.mk((i!=null?i.getText():null), getSLoc(i)); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:930:4: prefix
                    {
                    pushFollow(FOLLOW_prefix_in_feature_name6102);
                    prefix();

                    state._fsp--;
                    if (state.failed) return retval;

                    }
                    break;
                case 3 :
                    // BON.g:931:4: infix
                    {
                    pushFollow(FOLLOW_infix_in_feature_name6108);
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
    // BON.g:934:1: rename_clause returns [RenameClause rename] : '{' renaming '}' ;
    public final BONParser.rename_clause_return rename_clause() throws RecognitionException {
        BONParser.rename_clause_return retval = new BONParser.rename_clause_return();
        retval.start = input.LT(1);

        RenameClause renaming83 = null;


        try {
            // BON.g:934:45: ( '{' renaming '}' )
            // BON.g:935:3: '{' renaming '}'
            {
            match(input,62,FOLLOW_62_in_rename_clause6138); if (state.failed) return retval;
            pushFollow(FOLLOW_renaming_in_rename_clause6140);
            renaming83=renaming();

            state._fsp--;
            if (state.failed) return retval;
            match(input,63,FOLLOW_63_in_rename_clause6142); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.rename = renaming83; 
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
    // BON.g:939:1: renaming returns [RenameClause renaming] : s= '^' class_name '.' feature_name ;
    public final RenameClause renaming() throws RecognitionException {
        RenameClause renaming = null;

        Token s=null;
        BONParser.class_name_return class_name84 = null;

        BONParser.feature_name_return feature_name85 = null;


        try {
            // BON.g:939:42: (s= '^' class_name '.' feature_name )
            // BON.g:940:3: s= '^' class_name '.' feature_name
            {
            s=(Token)match(input,76,FOLLOW_76_in_renaming6178); if (state.failed) return renaming;
            pushFollow(FOLLOW_class_name_in_renaming6180);
            class_name84=class_name();

            state._fsp--;
            if (state.failed) return renaming;
            match(input,70,FOLLOW_70_in_renaming6182); if (state.failed) return renaming;
            pushFollow(FOLLOW_feature_name_in_renaming6184);
            feature_name85=feature_name();

            state._fsp--;
            if (state.failed) return renaming;
            if ( state.backtracking==0 ) {
               renaming = RenameClause.mk((class_name84!=null?class_name84.name:null), (feature_name85!=null?feature_name85.name:null), getSLoc(s,(feature_name85!=null?((Token)feature_name85.stop):null))); 
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
    // BON.g:944:1: feature_arguments returns [List<FeatureArgument> args] : ( feature_argument )+ ;
    public final BONParser.feature_arguments_return feature_arguments() throws RecognitionException {
        BONParser.feature_arguments_return retval = new BONParser.feature_arguments_return();
        retval.start = input.LT(1);

        List<FeatureArgument> feature_argument86 = null;


        try {
            // BON.g:944:56: ( ( feature_argument )+ )
            // BON.g:945:3: ( feature_argument )+
            {
            if ( state.backtracking==0 ) {
               retval.args = createList(); 
            }
            // BON.g:946:3: ( feature_argument )+
            int cnt115=0;
            loop115:
            do {
                int alt115=2;
                int LA115_0 = input.LA(1);

                if ( (LA115_0==65||LA115_0==77) ) {
                    alt115=1;
                }


                switch (alt115) {
            	case 1 :
            	    // BON.g:946:4: feature_argument
            	    {
            	    pushFollow(FOLLOW_feature_argument_in_feature_arguments6219);
            	    feature_argument86=feature_argument();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       retval.args.addAll(feature_argument86); 
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
    // BON.g:949:1: feature_argument returns [List<FeatureArgument> args] : ( '->' | '<-' ) ( ( identifier_list ':' t1= type ) | (t2= type ) ) ;
    public final List<FeatureArgument> feature_argument() throws RecognitionException {
        List<FeatureArgument> args = null;

        BONParser.type_return t1 = null;

        BONParser.type_return t2 = null;

        BONParser.identifier_list_return identifier_list87 = null;


        try {
            // BON.g:949:55: ( ( '->' | '<-' ) ( ( identifier_list ':' t1= type ) | (t2= type ) ) )
            // BON.g:950:3: ( '->' | '<-' ) ( ( identifier_list ':' t1= type ) | (t2= type ) )
            {
            if ( input.LA(1)==65||input.LA(1)==77 ) {
                input.consume();
                state.errorRecovery=false;state.failed=false;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return args;}
                MismatchedSetException mse = new MismatchedSetException(null,input);
                throw mse;
            }

            // BON.g:951:3: ( ( identifier_list ':' t1= type ) | (t2= type ) )
            int alt116=2;
            int LA116_0 = input.LA(1);

            if ( (LA116_0==IDENTIFIER) ) {
                int LA116_1 = input.LA(2);

                if ( (LA116_1==IDENTIFIER||LA116_1==25||(LA116_1>=58 && LA116_1<=59)||(LA116_1>=65 && LA116_1<=66)||(LA116_1>=71 && LA116_1<=75)||(LA116_1>=77 && LA116_1<=78)||LA116_1==80) ) {
                    alt116=2;
                }
                else if ( ((LA116_1>=34 && LA116_1<=35)) ) {
                    alt116=1;
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
                    // BON.g:952:6: ( identifier_list ':' t1= type )
                    {
                    // BON.g:952:6: ( identifier_list ':' t1= type )
                    // BON.g:952:8: identifier_list ':' t1= type
                    {
                    pushFollow(FOLLOW_identifier_list_in_feature_argument6283);
                    identifier_list87=identifier_list();

                    state._fsp--;
                    if (state.failed) return args;
                    match(input,34,FOLLOW_34_in_feature_argument6285); if (state.failed) return args;
                    pushFollow(FOLLOW_type_in_feature_argument6289);
                    t1=type();

                    state._fsp--;
                    if (state.failed) return args;
                    if ( state.backtracking==0 ) {
                       List<String> ids = (identifier_list87!=null?identifier_list87.list:null); args = new ArrayList<FeatureArgument>(ids.size()); for (String id : (identifier_list87!=null?identifier_list87.list:null)) args.add(FeatureArgument.mk(id, (t1!=null?t1.type:null), getSLoc((identifier_list87!=null?((Token)identifier_list87.start):null), (t1!=null?((Token)t1.stop):null)))); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // BON.g:955:6: (t2= type )
                    {
                    // BON.g:955:6: (t2= type )
                    // BON.g:955:8: t2= type
                    {
                    pushFollow(FOLLOW_type_in_feature_argument6321);
                    t2=type();

                    state._fsp--;
                    if (state.failed) return args;
                    if ( state.backtracking==0 ) {
                       args = new ArrayList<FeatureArgument>(1); args.add(FeatureArgument.mk(null, (t2!=null?t2.type:null), getSLoc((t2!=null?((Token)t2.start):null),(t2!=null?((Token)t2.stop):null)))); 
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
    // BON.g:961:1: identifier_list returns [List<String> list] : i1= IDENTIFIER ( ',' i= IDENTIFIER )* ;
    public final BONParser.identifier_list_return identifier_list() throws RecognitionException {
        BONParser.identifier_list_return retval = new BONParser.identifier_list_return();
        retval.start = input.LT(1);

        Token i1=null;
        Token i=null;

        try {
            // BON.g:961:45: (i1= IDENTIFIER ( ',' i= IDENTIFIER )* )
            // BON.g:962:3: i1= IDENTIFIER ( ',' i= IDENTIFIER )*
            {
            if ( state.backtracking==0 ) {
               retval.list = createList(); 
            }
            i1=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_identifier_list6381); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.list.add((i1!=null?i1.getText():null)); 
            }
            // BON.g:965:3: ( ',' i= IDENTIFIER )*
            loop117:
            do {
                int alt117=2;
                int LA117_0 = input.LA(1);

                if ( (LA117_0==35) ) {
                    alt117=1;
                }


                switch (alt117) {
            	case 1 :
            	    // BON.g:965:4: ',' i= IDENTIFIER
            	    {
            	    match(input,35,FOLLOW_35_in_identifier_list6391); if (state.failed) return retval;
            	    i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_identifier_list6395); if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       retval.list.add((i!=null?i.getText():null)); 
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
    // BON.g:969:1: prefix : 'prefix' '\"' prefix_operator '\"' ;
    public final void prefix() throws RecognitionException {
        try {
            // BON.g:969:9: ( 'prefix' '\"' prefix_operator '\"' )
            // BON.g:969:12: 'prefix' '\"' prefix_operator '\"'
            {
            match(input,78,FOLLOW_78_in_prefix6412); if (state.failed) return ;
            match(input,79,FOLLOW_79_in_prefix6414); if (state.failed) return ;
            pushFollow(FOLLOW_prefix_operator_in_prefix6416);
            prefix_operator();

            state._fsp--;
            if (state.failed) return ;
            match(input,79,FOLLOW_79_in_prefix6418); if (state.failed) return ;

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
    // BON.g:972:1: infix : 'infix' '\"' infix_operator '\"' ;
    public final void infix() throws RecognitionException {
        try {
            // BON.g:972:8: ( 'infix' '\"' infix_operator '\"' )
            // BON.g:972:11: 'infix' '\"' infix_operator '\"'
            {
            match(input,80,FOLLOW_80_in_infix6437); if (state.failed) return ;
            match(input,79,FOLLOW_79_in_infix6439); if (state.failed) return ;
            pushFollow(FOLLOW_infix_operator_in_infix6441);
            infix_operator();

            state._fsp--;
            if (state.failed) return ;
            match(input,79,FOLLOW_79_in_infix6443); if (state.failed) return ;

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
    // BON.g:976:1: prefix_operator : unary ;
    public final void prefix_operator() throws RecognitionException {
        try {
            // BON.g:976:18: ( unary )
            // BON.g:976:21: unary
            {
            pushFollow(FOLLOW_unary_in_prefix_operator6463);
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
    // BON.g:980:1: infix_operator : binary ;
    public final void infix_operator() throws RecognitionException {
        try {
            // BON.g:980:17: ( binary )
            // BON.g:981:3: binary
            {
            pushFollow(FOLLOW_binary_in_infix_operator6478);
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
    // BON.g:985:1: formal_generics returns [List<FormalGeneric> generics] : '[' fgl= formal_generic_list ']' ;
    public final BONParser.formal_generics_return formal_generics() throws RecognitionException {
        BONParser.formal_generics_return retval = new BONParser.formal_generics_return();
        retval.start = input.LT(1);

        List<FormalGeneric> fgl = null;


        try {
            // BON.g:987:56: ( '[' fgl= formal_generic_list ']' )
            // BON.g:988:3: '[' fgl= formal_generic_list ']'
            {
            match(input,66,FOLLOW_66_in_formal_generics6497); if (state.failed) return retval;
            pushFollow(FOLLOW_formal_generic_list_in_formal_generics6501);
            fgl=formal_generic_list();

            state._fsp--;
            if (state.failed) return retval;
            match(input,67,FOLLOW_67_in_formal_generics6503); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.generics = fgl; 
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
    // BON.g:992:1: formal_generic_list returns [List<FormalGeneric> list] : fg1= formal_generic ( ',' fg= formal_generic )* ;
    public final List<FormalGeneric> formal_generic_list() throws RecognitionException {
        List<FormalGeneric> list = null;

        FormalGeneric fg1 = null;

        FormalGeneric fg = null;


        try {
            // BON.g:992:56: (fg1= formal_generic ( ',' fg= formal_generic )* )
            // BON.g:993:3: fg1= formal_generic ( ',' fg= formal_generic )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_formal_generic_in_formal_generic_list6546);
            fg1=formal_generic();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               list.add(fg1); 
            }
            // BON.g:996:3: ( ',' fg= formal_generic )*
            loop118:
            do {
                int alt118=2;
                int LA118_0 = input.LA(1);

                if ( (LA118_0==35) ) {
                    alt118=1;
                }


                switch (alt118) {
            	case 1 :
            	    // BON.g:996:4: ',' fg= formal_generic
            	    {
            	    match(input,35,FOLLOW_35_in_formal_generic_list6555); if (state.failed) return list;
            	    pushFollow(FOLLOW_formal_generic_in_formal_generic_list6559);
            	    fg=formal_generic();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       list.add(fg); 
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
    // BON.g:1001:1: formal_generic returns [FormalGeneric generic] : (f= formal_generic_name | f= formal_generic_name '->' ct= class_type );
    public final FormalGeneric formal_generic() throws RecognitionException {
        FormalGeneric generic = null;

        BONParser.formal_generic_name_return f = null;

        BONParser.class_type_return ct = null;


        try {
            // BON.g:1001:48: (f= formal_generic_name | f= formal_generic_name '->' ct= class_type )
            int alt119=2;
            int LA119_0 = input.LA(1);

            if ( (LA119_0==IDENTIFIER) ) {
                int LA119_1 = input.LA(2);

                if ( (LA119_1==65) ) {
                    alt119=2;
                }
                else if ( (LA119_1==35||LA119_1==67) ) {
                    alt119=1;
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
                    // BON.g:1002:4: f= formal_generic_name
                    {
                    pushFollow(FOLLOW_formal_generic_name_in_formal_generic6609);
                    f=formal_generic_name();

                    state._fsp--;
                    if (state.failed) return generic;
                    if ( state.backtracking==0 ) {
                       generic = FormalGeneric.mk((f!=null?f.name:null), null, getSLoc((f!=null?((Token)f.start):null),(f!=null?((Token)f.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1004:4: f= formal_generic_name '->' ct= class_type
                    {
                    pushFollow(FOLLOW_formal_generic_name_in_formal_generic6621);
                    f=formal_generic_name();

                    state._fsp--;
                    if (state.failed) return generic;
                    match(input,65,FOLLOW_65_in_formal_generic6623); if (state.failed) return generic;
                    pushFollow(FOLLOW_class_type_in_formal_generic6627);
                    ct=class_type();

                    state._fsp--;
                    if (state.failed) return generic;
                    if ( state.backtracking==0 ) {
                       generic = FormalGeneric.mk((f!=null?f.name:null), (ct!=null?ct.type:null), getSLoc((f!=null?((Token)f.start):null), (ct!=null?((Token)ct.stop):null))); 
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
    // BON.g:1008:1: formal_generic_name returns [String name] : i= IDENTIFIER ;
    public final BONParser.formal_generic_name_return formal_generic_name() throws RecognitionException {
        BONParser.formal_generic_name_return retval = new BONParser.formal_generic_name_return();
        retval.start = input.LT(1);

        Token i=null;

        try {
            // BON.g:1008:43: (i= IDENTIFIER )
            // BON.g:1009:3: i= IDENTIFIER
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_formal_generic_name6666); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.name = (i!=null?i.getText():null); 
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
    // BON.g:1013:1: class_type returns [Type type] : c= class_name ( actual_generics | ) ;
    public final BONParser.class_type_return class_type() throws RecognitionException {
        BONParser.class_type_return retval = new BONParser.class_type_return();
        retval.start = input.LT(1);

        BONParser.class_name_return c = null;

        BONParser.actual_generics_return actual_generics88 = null;


        try {
            // BON.g:1013:32: (c= class_name ( actual_generics | ) )
            // BON.g:1014:3: c= class_name ( actual_generics | )
            {
            pushFollow(FOLLOW_class_name_in_class_type6711);
            c=class_name();

            state._fsp--;
            if (state.failed) return retval;
            // BON.g:1015:3: ( actual_generics | )
            int alt120=2;
            int LA120_0 = input.LA(1);

            if ( (LA120_0==66) ) {
                alt120=1;
            }
            else if ( (LA120_0==33||LA120_0==35||LA120_0==67||LA120_0==72) ) {
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
                    // BON.g:1015:6: actual_generics
                    {
                    pushFollow(FOLLOW_actual_generics_in_class_type6719);
                    actual_generics88=actual_generics();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.type = BONType.mk((c!=null?input.toString(c.start,c.stop):null), (actual_generics88!=null?actual_generics88.types:null), (c!=null?input.toString(c.start,c.stop):null).concat((actual_generics88!=null?input.toString(actual_generics88.start,actual_generics88.stop):null)), getSLoc((c!=null?((Token)c.start):null), (actual_generics88!=null?((Token)actual_generics88.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1018:6: 
                    {
                    if ( state.backtracking==0 ) {
                       retval.type = BONType.mk((c!=null?input.toString(c.start,c.stop):null), Constants.EMPTY_TYPE_LIST, (c!=null?input.toString(c.start,c.stop):null), getSLoc((c!=null?((Token)c.start):null),(c!=null?((Token)c.stop):null))); 
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
    // BON.g:1022:1: actual_generics returns [List<Type> types] : '[' type_list ']' ;
    public final BONParser.actual_generics_return actual_generics() throws RecognitionException {
        BONParser.actual_generics_return retval = new BONParser.actual_generics_return();
        retval.start = input.LT(1);

        List<Type> type_list89 = null;


        try {
            // BON.g:1022:44: ( '[' type_list ']' )
            // BON.g:1023:19: '[' type_list ']'
            {
            match(input,66,FOLLOW_66_in_actual_generics6790); if (state.failed) return retval;
            pushFollow(FOLLOW_type_list_in_actual_generics6792);
            type_list89=type_list();

            state._fsp--;
            if (state.failed) return retval;
            match(input,67,FOLLOW_67_in_actual_generics6794); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.types = type_list89; 
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
    // BON.g:1027:1: type_list returns [List<Type> types] : t1= type ( ',' t= type )* ;
    public final List<Type> type_list() throws RecognitionException {
        List<Type> types = null;

        BONParser.type_return t1 = null;

        BONParser.type_return t = null;


        try {
            // BON.g:1027:39: (t1= type ( ',' t= type )* )
            // BON.g:1028:12: t1= type ( ',' t= type )*
            {
            pushFollow(FOLLOW_type_in_type_list6858);
            t1=type();

            state._fsp--;
            if (state.failed) return types;
            if ( state.backtracking==0 ) {
               types = createList(); types.add((t1!=null?t1.type:null)); 
            }
            // BON.g:1030:12: ( ',' t= type )*
            loop121:
            do {
                int alt121=2;
                int LA121_0 = input.LA(1);

                if ( (LA121_0==35) ) {
                    alt121=1;
                }


                switch (alt121) {
            	case 1 :
            	    // BON.g:1030:13: ',' t= type
            	    {
            	    match(input,35,FOLLOW_35_in_type_list6886); if (state.failed) return types;
            	    pushFollow(FOLLOW_type_in_type_list6890);
            	    t=type();

            	    state._fsp--;
            	    if (state.failed) return types;
            	    if ( state.backtracking==0 ) {
            	       types.add((t!=null?t.type:null)); 
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
    // BON.g:1038:1: type returns [Type type] : i= IDENTIFIER ( ( actual_generics ) | ) ;
    public final BONParser.type_return type() throws RecognitionException {
        BONParser.type_return retval = new BONParser.type_return();
        retval.start = input.LT(1);

        Token i=null;
        BONParser.actual_generics_return actual_generics90 = null;


        try {
            // BON.g:1038:26: (i= IDENTIFIER ( ( actual_generics ) | ) )
            // BON.g:1039:8: i= IDENTIFIER ( ( actual_generics ) | )
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_type6945); if (state.failed) return retval;
            // BON.g:1040:8: ( ( actual_generics ) | )
            int alt122=2;
            int LA122_0 = input.LA(1);

            if ( (LA122_0==66) ) {
                alt122=1;
            }
            else if ( ((LA122_0>=IDENTIFIER && LA122_0<=COMMENT)||LA122_0==25||LA122_0==33||LA122_0==35||(LA122_0>=58 && LA122_0<=59)||LA122_0==62||LA122_0==65||LA122_0==67||(LA122_0>=71 && LA122_0<=75)||(LA122_0>=77 && LA122_0<=78)||LA122_0==80||(LA122_0>=83 && LA122_0<=84)) ) {
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
                    // BON.g:1041:9: ( actual_generics )
                    {
                    // BON.g:1041:9: ( actual_generics )
                    // BON.g:1041:11: actual_generics
                    {
                    pushFollow(FOLLOW_actual_generics_in_type6967);
                    actual_generics90=actual_generics();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.type = BONType.mk((i!=null?i.getText():null), (actual_generics90!=null?actual_generics90.types:null), (i!=null?i.getText():null).concat((actual_generics90!=null?input.toString(actual_generics90.start,actual_generics90.stop):null)), getSLoc(i,(actual_generics90!=null?((Token)actual_generics90.stop):null))); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // BON.g:1045:9: 
                    {
                    if ( state.backtracking==0 ) {
                       retval.type = BONType.mk((i!=null?i.getText():null), Constants.EMPTY_TYPE_LIST, (i!=null?i.getText():null),getSLoc(i)); 
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
    // BON.g:1049:1: assertion returns [List<Expression> clauses] : a1= assertion_clause ( ';' a= assertion_clause )* ( ';' )? ;
    public final List<Expression> assertion() throws RecognitionException {
        List<Expression> clauses = null;

        Expression a1 = null;

        Expression a = null;


        try {
            // BON.g:1054:46: (a1= assertion_clause ( ';' a= assertion_clause )* ( ';' )? )
            // BON.g:1055:3: a1= assertion_clause ( ';' a= assertion_clause )* ( ';' )?
            {
            if ( state.backtracking==0 ) {
               clauses = createList(); 
            }
            pushFollow(FOLLOW_assertion_clause_in_assertion7046);
            a1=assertion_clause();

            state._fsp--;
            if (state.failed) return clauses;
            if ( state.backtracking==0 ) {
               clauses.add(a1); 
            }
            // BON.g:1058:3: ( ';' a= assertion_clause )*
            loop123:
            do {
                int alt123=2;
                int LA123_0 = input.LA(1);

                if ( (LA123_0==33) ) {
                    int LA123_1 = input.LA(2);

                    if ( ((LA123_1>=MANIFEST_STRING && LA123_1<=IDENTIFIER)||(LA123_1>=INTEGER && LA123_1<=REAL)||LA123_1==42||LA123_1==62||(LA123_1>=81 && LA123_1<=82)||(LA123_1>=87 && LA123_1<=91)||(LA123_1>=103 && LA123_1<=104)||(LA123_1>=108 && LA123_1<=110)) ) {
                        alt123=1;
                    }


                }


                switch (alt123) {
            	case 1 :
            	    // BON.g:1058:4: ';' a= assertion_clause
            	    {
            	    match(input,33,FOLLOW_33_in_assertion7055); if (state.failed) return clauses;
            	    pushFollow(FOLLOW_assertion_clause_in_assertion7059);
            	    a=assertion_clause();

            	    state._fsp--;
            	    if (state.failed) return clauses;
            	    if ( state.backtracking==0 ) {
            	       clauses.add(a); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop123;
                }
            } while (true);

            // BON.g:1061:3: ( ';' )?
            int alt124=2;
            int LA124_0 = input.LA(1);

            if ( (LA124_0==33) ) {
                alt124=1;
            }
            switch (alt124) {
                case 1 :
                    // BON.g:1061:3: ';'
                    {
                    match(input,33,FOLLOW_33_in_assertion7076); if (state.failed) return clauses;

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
    // BON.g:1064:1: assertion_clause returns [Expression clause] : be= boolean_expression ;
    public final Expression assertion_clause() throws RecognitionException {
        Expression clause = null;

        Expression be = null;


        try {
            // BON.g:1064:46: (be= boolean_expression )
            // BON.g:1065:3: be= boolean_expression
            {
            pushFollow(FOLLOW_boolean_expression_in_assertion_clause7105);
            be=boolean_expression();

            state._fsp--;
            if (state.failed) return clause;
            if ( state.backtracking==0 ) {
               clause = be; 
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
    // BON.g:1072:1: boolean_expression returns [Expression exp] : expression ;
    public final Expression boolean_expression() throws RecognitionException {
        Expression exp = null;

        BONParser.expression_return expression91 = null;


        try {
            // BON.g:1072:45: ( expression )
            // BON.g:1073:3: expression
            {
            pushFollow(FOLLOW_expression_in_boolean_expression7127);
            expression91=expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               exp = (expression91!=null?expression91.exp:null); 
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
    // BON.g:1077:1: quantification returns [Quantification quantification] : q= quantifier rexp= range_expression (r= restriction )? p= proposition ;
    public final Quantification quantification() throws RecognitionException {
        Quantification quantification = null;

        BONParser.quantifier_return q = null;

        List<VariableRange> rexp = null;

        Expression r = null;

        BONParser.proposition_return p = null;


         Expression restrict = null; 
        try {
            // BON.g:1079:1: (q= quantifier rexp= range_expression (r= restriction )? p= proposition )
            // BON.g:1080:3: q= quantifier rexp= range_expression (r= restriction )? p= proposition
            {
            pushFollow(FOLLOW_quantifier_in_quantification7167);
            q=quantifier();

            state._fsp--;
            if (state.failed) return quantification;
            pushFollow(FOLLOW_range_expression_in_quantification7174);
            rexp=range_expression();

            state._fsp--;
            if (state.failed) return quantification;
            // BON.g:1082:3: (r= restriction )?
            int alt125=2;
            int LA125_0 = input.LA(1);

            if ( (LA125_0==83) ) {
                alt125=1;
            }
            switch (alt125) {
                case 1 :
                    // BON.g:1082:4: r= restriction
                    {
                    pushFollow(FOLLOW_restriction_in_quantification7182);
                    r=restriction();

                    state._fsp--;
                    if (state.failed) return quantification;
                    if ( state.backtracking==0 ) {
                       restrict = r; 
                    }

                    }
                    break;

            }

            pushFollow(FOLLOW_proposition_in_quantification7194);
            p=proposition();

            state._fsp--;
            if (state.failed) return quantification;
            if ( state.backtracking==0 ) {
               quantification = Quantification.mk((q!=null?q.q:null), rexp, restrict, (p!=null?p.exp:null), getSLoc((q!=null?((Token)q.start):null),(p!=null?((Token)p.stop):null))); 
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
    // BON.g:1087:1: quantifier returns [Quantification.Quantifier q] : (f= 'for_all' | e= 'exists' );
    public final BONParser.quantifier_return quantifier() throws RecognitionException {
        BONParser.quantifier_return retval = new BONParser.quantifier_return();
        retval.start = input.LT(1);

        Token f=null;
        Token e=null;

        try {
            // BON.g:1087:50: (f= 'for_all' | e= 'exists' )
            int alt126=2;
            int LA126_0 = input.LA(1);

            if ( (LA126_0==81) ) {
                alt126=1;
            }
            else if ( (LA126_0==82) ) {
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
                    // BON.g:1088:4: f= 'for_all'
                    {
                    f=(Token)match(input,81,FOLLOW_81_in_quantifier7233); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.q = Quantification.Quantifier.FORALL; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1090:4: e= 'exists'
                    {
                    e=(Token)match(input,82,FOLLOW_82_in_quantifier7246); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.q = Quantification.Quantifier.EXISTS; 
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
    // BON.g:1094:1: range_expression returns [List<VariableRange> ranges] : vr1= variable_range ( ';' vr= variable_range )* ( ';' )? ;
    public final List<VariableRange> range_expression() throws RecognitionException {
        List<VariableRange> ranges = null;

        VariableRange vr1 = null;

        VariableRange vr = null;


        try {
            // BON.g:1094:55: (vr1= variable_range ( ';' vr= variable_range )* ( ';' )? )
            // BON.g:1095:3: vr1= variable_range ( ';' vr= variable_range )* ( ';' )?
            {
            if ( state.backtracking==0 ) {
               ranges = createList(); 
            }
            pushFollow(FOLLOW_variable_range_in_range_expression7284);
            vr1=variable_range();

            state._fsp--;
            if (state.failed) return ranges;
            if ( state.backtracking==0 ) {
               ranges.add(vr); 
            }
            // BON.g:1098:3: ( ';' vr= variable_range )*
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
            	    // BON.g:1098:4: ';' vr= variable_range
            	    {
            	    match(input,33,FOLLOW_33_in_range_expression7294); if (state.failed) return ranges;
            	    pushFollow(FOLLOW_variable_range_in_range_expression7298);
            	    vr=variable_range();

            	    state._fsp--;
            	    if (state.failed) return ranges;
            	    if ( state.backtracking==0 ) {
            	       ranges.add(vr); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop127;
                }
            } while (true);

            // BON.g:1101:3: ( ';' )?
            int alt128=2;
            int LA128_0 = input.LA(1);

            if ( (LA128_0==33) ) {
                alt128=1;
            }
            switch (alt128) {
                case 1 :
                    // BON.g:1101:3: ';'
                    {
                    match(input,33,FOLLOW_33_in_range_expression7313); if (state.failed) return ranges;

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
    // BON.g:1104:1: restriction returns [Expression exp] : st= 'such_that' be= boolean_expression ;
    public final Expression restriction() throws RecognitionException {
        Expression exp = null;

        Token st=null;
        Expression be = null;


        try {
            // BON.g:1104:38: (st= 'such_that' be= boolean_expression )
            // BON.g:1105:3: st= 'such_that' be= boolean_expression
            {
            st=(Token)match(input,83,FOLLOW_83_in_restriction7350); if (state.failed) return exp;
            pushFollow(FOLLOW_boolean_expression_in_restriction7354);
            be=boolean_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               exp =  be; 
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
    // BON.g:1109:1: proposition returns [Expression exp] : ih= 'it_holds' be= boolean_expression ;
    public final BONParser.proposition_return proposition() throws RecognitionException {
        BONParser.proposition_return retval = new BONParser.proposition_return();
        retval.start = input.LT(1);

        Token ih=null;
        Expression be = null;


        try {
            // BON.g:1109:38: (ih= 'it_holds' be= boolean_expression )
            // BON.g:1110:3: ih= 'it_holds' be= boolean_expression
            {
            ih=(Token)match(input,84,FOLLOW_84_in_proposition7388); if (state.failed) return retval;
            pushFollow(FOLLOW_boolean_expression_in_proposition7392);
            be=boolean_expression();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.exp = be; 
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
    // BON.g:1114:1: variable_range returns [VariableRange range] : (mr= member_range | tr= type_range );
    public final VariableRange variable_range() throws RecognitionException {
        VariableRange range = null;

        MemberRange mr = null;

        TypeRange tr = null;


        try {
            // BON.g:1114:46: (mr= member_range | tr= type_range )
            int alt129=2;
            alt129 = dfa129.predict(input);
            switch (alt129) {
                case 1 :
                    // BON.g:1115:4: mr= member_range
                    {
                    pushFollow(FOLLOW_member_range_in_variable_range7428);
                    mr=member_range();

                    state._fsp--;
                    if (state.failed) return range;
                    if ( state.backtracking==0 ) {
                       range = mr; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1117:4: tr= type_range
                    {
                    pushFollow(FOLLOW_type_range_in_variable_range7440);
                    tr=type_range();

                    state._fsp--;
                    if (state.failed) return range;
                    if ( state.backtracking==0 ) {
                       range = tr; 
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
    // BON.g:1121:1: member_range returns [MemberRange range] : il= identifier_list 'member_of' e= expression ;
    public final MemberRange member_range() throws RecognitionException {
        MemberRange range = null;

        BONParser.identifier_list_return il = null;

        BONParser.expression_return e = null;


        try {
            // BON.g:1121:42: (il= identifier_list 'member_of' e= expression )
            // BON.g:1122:3: il= identifier_list 'member_of' e= expression
            {
            pushFollow(FOLLOW_identifier_list_in_member_range7480);
            il=identifier_list();

            state._fsp--;
            if (state.failed) return range;
            match(input,85,FOLLOW_85_in_member_range7482); if (state.failed) return range;
            pushFollow(FOLLOW_expression_in_member_range7486);
            e=expression();

            state._fsp--;
            if (state.failed) return range;
            if ( state.backtracking==0 ) {
               range = MemberRange.mk((il!=null?il.list:null), (e!=null?e.exp:null), getSLoc((il!=null?((Token)il.start):null),(e!=null?((Token)e.stop):null))); 
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
    // BON.g:1126:1: type_range returns [TypeRange range] : il= identifier_list ':' t= type ;
    public final TypeRange type_range() throws RecognitionException {
        TypeRange range = null;

        BONParser.identifier_list_return il = null;

        BONParser.type_return t = null;


        try {
            // BON.g:1126:38: (il= identifier_list ':' t= type )
            // BON.g:1127:3: il= identifier_list ':' t= type
            {
            pushFollow(FOLLOW_identifier_list_in_type_range7522);
            il=identifier_list();

            state._fsp--;
            if (state.failed) return range;
            match(input,34,FOLLOW_34_in_type_range7524); if (state.failed) return range;
            pushFollow(FOLLOW_type_in_type_range7528);
            t=type();

            state._fsp--;
            if (state.failed) return range;
            if ( state.backtracking==0 ) {
               range = TypeRange.mk((il!=null?il.list:null), (t!=null?t.type:null), getSLoc((il!=null?((Token)il.start):null),(t!=null?((Token)t.stop):null))); 
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
    // BON.g:1131:1: call_chain returns [List<UnqualifiedCall> calls] : uc1= unqualified_call ( '.' uc= unqualified_call )* ;
    public final BONParser.call_chain_return call_chain() throws RecognitionException {
        BONParser.call_chain_return retval = new BONParser.call_chain_return();
        retval.start = input.LT(1);

        UnqualifiedCall uc1 = null;

        UnqualifiedCall uc = null;


        try {
            // BON.g:1133:50: (uc1= unqualified_call ( '.' uc= unqualified_call )* )
            // BON.g:1134:3: uc1= unqualified_call ( '.' uc= unqualified_call )*
            {
            if ( state.backtracking==0 ) {
               retval.calls = createList(); 
            }
            pushFollow(FOLLOW_unqualified_call_in_call_chain7588);
            uc1=unqualified_call();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.calls.add(uc1); 
            }
            // BON.g:1137:3: ( '.' uc= unqualified_call )*
            loop130:
            do {
                int alt130=2;
                int LA130_0 = input.LA(1);

                if ( (LA130_0==70) ) {
                    alt130=1;
                }


                switch (alt130) {
            	case 1 :
            	    // BON.g:1137:4: '.' uc= unqualified_call
            	    {
            	    match(input,70,FOLLOW_70_in_call_chain7597); if (state.failed) return retval;
            	    pushFollow(FOLLOW_unqualified_call_in_call_chain7601);
            	    uc=unqualified_call();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) {
            	       retval.calls.add(uc); 
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
    // BON.g:1140:1: unqualified_call returns [UnqualifiedCall call] : i= IDENTIFIER (aa= actual_arguments | ) ;
    public final UnqualifiedCall unqualified_call() throws RecognitionException {
        UnqualifiedCall call = null;

        Token i=null;
        BONParser.actual_arguments_return aa = null;


         List<Expression> args = null; Token end = null;
        try {
            // BON.g:1142:1: (i= IDENTIFIER (aa= actual_arguments | ) )
            // BON.g:1143:3: i= IDENTIFIER (aa= actual_arguments | )
            {
            i=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_unqualified_call7642); if (state.failed) return call;
            if ( state.backtracking==0 ) {
               end = i; 
            }
            // BON.g:1145:3: (aa= actual_arguments | )
            int alt131=2;
            int LA131_0 = input.LA(1);

            if ( (LA131_0==42) ) {
                alt131=1;
            }
            else if ( (LA131_0==25||(LA131_0>=33 && LA131_0<=35)||LA131_0==43||LA131_0==63||LA131_0==65||LA131_0==70||(LA131_0>=75 && LA131_0<=76)||(LA131_0>=83 && LA131_0<=85)||(LA131_0>=102 && LA131_0<=107)||(LA131_0>=110 && LA131_0<=120)) ) {
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
                    // BON.g:1145:6: aa= actual_arguments
                    {
                    pushFollow(FOLLOW_actual_arguments_in_unqualified_call7656);
                    aa=actual_arguments();

                    state._fsp--;
                    if (state.failed) return call;
                    if ( state.backtracking==0 ) {
                       args = (aa!=null?aa.args:null); end = (aa!=null?((Token)aa.stop):null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1147:6: 
                    {
                    if ( state.backtracking==0 ) {
                       args = emptyList(); 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               call = UnqualifiedCall.mk((i!=null?i.getText():null), args, getSLoc(i,end)); 
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
    // BON.g:1152:1: actual_arguments returns [List<Expression> args] : '(' (el= expression_list | ) ')' ;
    public final BONParser.actual_arguments_return actual_arguments() throws RecognitionException {
        BONParser.actual_arguments_return retval = new BONParser.actual_arguments_return();
        retval.start = input.LT(1);

        List<Expression> el = null;


        try {
            // BON.g:1153:1: ( '(' (el= expression_list | ) ')' )
            // BON.g:1154:3: '(' (el= expression_list | ) ')'
            {
            match(input,42,FOLLOW_42_in_actual_arguments7695); if (state.failed) return retval;
            // BON.g:1155:3: (el= expression_list | )
            int alt132=2;
            int LA132_0 = input.LA(1);

            if ( ((LA132_0>=MANIFEST_STRING && LA132_0<=IDENTIFIER)||(LA132_0>=INTEGER && LA132_0<=REAL)||LA132_0==42||LA132_0==62||(LA132_0>=81 && LA132_0<=82)||(LA132_0>=87 && LA132_0<=91)||(LA132_0>=103 && LA132_0<=104)||(LA132_0>=108 && LA132_0<=110)) ) {
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
                    // BON.g:1155:6: el= expression_list
                    {
                    pushFollow(FOLLOW_expression_list_in_actual_arguments7705);
                    el=expression_list();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.args = el; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1157:6: 
                    {
                    if ( state.backtracking==0 ) {
                       retval.args = emptyList(); 
                    }

                    }
                    break;

            }

            match(input,43,FOLLOW_43_in_actual_arguments7728); if (state.failed) return retval;

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
    // BON.g:1162:1: expression_list returns [List<Expression> list] : e1= expression ( ',' e= expression )* ;
    public final List<Expression> expression_list() throws RecognitionException {
        List<Expression> list = null;

        BONParser.expression_return e1 = null;

        BONParser.expression_return e = null;


        try {
            // BON.g:1162:49: (e1= expression ( ',' e= expression )* )
            // BON.g:1163:3: e1= expression ( ',' e= expression )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_expression_in_expression_list7764);
            e1=expression();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               list.add((e1!=null?e1.exp:null)); 
            }
            // BON.g:1166:3: ( ',' e= expression )*
            loop133:
            do {
                int alt133=2;
                int LA133_0 = input.LA(1);

                if ( (LA133_0==35) ) {
                    alt133=1;
                }


                switch (alt133) {
            	case 1 :
            	    // BON.g:1166:4: ',' e= expression
            	    {
            	    match(input,35,FOLLOW_35_in_expression_list7774); if (state.failed) return list;
            	    pushFollow(FOLLOW_expression_in_expression_list7778);
            	    e=expression();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       list.add((e!=null?e.exp:null)); 
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
    // BON.g:1169:1: enumerated_set returns [List<EnumerationElement> list] : '{' el= enumeration_list '}' ;
    public final BONParser.enumerated_set_return enumerated_set() throws RecognitionException {
        BONParser.enumerated_set_return retval = new BONParser.enumerated_set_return();
        retval.start = input.LT(1);

        List<EnumerationElement> el = null;


        try {
            // BON.g:1177:56: ( '{' el= enumeration_list '}' )
            // BON.g:1178:3: '{' el= enumeration_list '}'
            {
            match(input,62,FOLLOW_62_in_enumerated_set7824); if (state.failed) return retval;
            pushFollow(FOLLOW_enumeration_list_in_enumerated_set7828);
            el=enumeration_list();

            state._fsp--;
            if (state.failed) return retval;
            match(input,63,FOLLOW_63_in_enumerated_set7830); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.list = el; 
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
    // BON.g:1182:1: enumeration_list returns [List<EnumerationElement> list] : el1= enumeration_element ( ',' el= enumeration_element )* ;
    public final List<EnumerationElement> enumeration_list() throws RecognitionException {
        List<EnumerationElement> list = null;

        EnumerationElement el1 = null;

        EnumerationElement el = null;


        try {
            // BON.g:1182:58: (el1= enumeration_element ( ',' el= enumeration_element )* )
            // BON.g:1183:3: el1= enumeration_element ( ',' el= enumeration_element )*
            {
            if ( state.backtracking==0 ) {
               list = createList(); 
            }
            pushFollow(FOLLOW_enumeration_element_in_enumeration_list7872);
            el1=enumeration_element();

            state._fsp--;
            if (state.failed) return list;
            if ( state.backtracking==0 ) {
               list.add(el1); 
            }
            // BON.g:1186:3: ( ',' el= enumeration_element )*
            loop134:
            do {
                int alt134=2;
                int LA134_0 = input.LA(1);

                if ( (LA134_0==35) ) {
                    alt134=1;
                }


                switch (alt134) {
            	case 1 :
            	    // BON.g:1186:4: ',' el= enumeration_element
            	    {
            	    match(input,35,FOLLOW_35_in_enumeration_list7882); if (state.failed) return list;
            	    pushFollow(FOLLOW_enumeration_element_in_enumeration_list7886);
            	    el=enumeration_element();

            	    state._fsp--;
            	    if (state.failed) return list;
            	    if ( state.backtracking==0 ) {
            	       list.add(el); 
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
    // BON.g:1189:1: enumeration_element returns [EnumerationElement el] : (e= expression | i= interval );
    public final EnumerationElement enumeration_element() throws RecognitionException {
        EnumerationElement el = null;

        BONParser.expression_return e = null;

        Interval i = null;


        try {
            // BON.g:1189:53: (e= expression | i= interval )
            int alt135=2;
            switch ( input.LA(1) ) {
            case MANIFEST_STRING:
            case IDENTIFIER:
            case REAL:
            case 42:
            case 62:
            case 81:
            case 82:
            case 87:
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

                if ( ((LA135_2>=34 && LA135_2<=35)||LA135_2==63||LA135_2==65||LA135_2==70||LA135_2==76||LA135_2==85||(LA135_2>=102 && LA135_2<=107)||(LA135_2>=110 && LA135_2<=120)) ) {
                    alt135=1;
                }
                else if ( (LA135_2==86) ) {
                    alt135=2;
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

                if ( (LA135_3==INTEGER) ) {
                    int LA135_7 = input.LA(3);

                    if ( ((LA135_7>=34 && LA135_7<=35)||LA135_7==63||LA135_7==65||LA135_7==70||LA135_7==76||LA135_7==85||(LA135_7>=102 && LA135_7<=107)||(LA135_7>=110 && LA135_7<=120)) ) {
                        alt135=1;
                    }
                    else if ( (LA135_7==86) ) {
                        alt135=2;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return el;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 135, 7, input);

                        throw nvae;
                    }
                }
                else if ( ((LA135_3>=MANIFEST_STRING && LA135_3<=IDENTIFIER)||(LA135_3>=CHARACTER_CONSTANT && LA135_3<=REAL)||LA135_3==42||LA135_3==62||(LA135_3>=87 && LA135_3<=91)||(LA135_3>=103 && LA135_3<=104)||(LA135_3>=108 && LA135_3<=110)) ) {
                    alt135=1;
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

                if ( (LA135_4==INTEGER) ) {
                    int LA135_7 = input.LA(3);

                    if ( ((LA135_7>=34 && LA135_7<=35)||LA135_7==63||LA135_7==65||LA135_7==70||LA135_7==76||LA135_7==85||(LA135_7>=102 && LA135_7<=107)||(LA135_7>=110 && LA135_7<=120)) ) {
                        alt135=1;
                    }
                    else if ( (LA135_7==86) ) {
                        alt135=2;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return el;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 135, 7, input);

                        throw nvae;
                    }
                }
                else if ( ((LA135_4>=MANIFEST_STRING && LA135_4<=IDENTIFIER)||(LA135_4>=CHARACTER_CONSTANT && LA135_4<=REAL)||LA135_4==42||LA135_4==62||(LA135_4>=87 && LA135_4<=91)||(LA135_4>=103 && LA135_4<=104)||(LA135_4>=108 && LA135_4<=110)) ) {
                    alt135=1;
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

                if ( ((LA135_5>=34 && LA135_5<=35)||LA135_5==63||LA135_5==65||LA135_5==70||LA135_5==76||LA135_5==85||(LA135_5>=102 && LA135_5<=107)||(LA135_5>=110 && LA135_5<=120)) ) {
                    alt135=1;
                }
                else if ( (LA135_5==86) ) {
                    alt135=2;
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
                    // BON.g:1190:4: e= expression
                    {
                    pushFollow(FOLLOW_expression_in_enumeration_element7918);
                    e=expression();

                    state._fsp--;
                    if (state.failed) return el;
                    if ( state.backtracking==0 ) {
                       el = (e!=null?e.exp:null); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1192:4: i= interval
                    {
                    pushFollow(FOLLOW_interval_in_enumeration_element7932);
                    i=interval();

                    state._fsp--;
                    if (state.failed) return el;
                    if ( state.backtracking==0 ) {
                       el = i; 
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
    // BON.g:1196:1: interval returns [Interval interval] : (ii= integer_interval | ci= character_interval );
    public final Interval interval() throws RecognitionException {
        Interval interval = null;

        IntegerInterval ii = null;

        CharacterInterval ci = null;


        try {
            // BON.g:1196:39: (ii= integer_interval | ci= character_interval )
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
                    // BON.g:1197:4: ii= integer_interval
                    {
                    pushFollow(FOLLOW_integer_interval_in_interval7979);
                    ii=integer_interval();

                    state._fsp--;
                    if (state.failed) return interval;
                    if ( state.backtracking==0 ) {
                       interval = ii; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1199:4: ci= character_interval
                    {
                    pushFollow(FOLLOW_character_interval_in_interval7991);
                    ci=character_interval();

                    state._fsp--;
                    if (state.failed) return interval;
                    if ( state.backtracking==0 ) {
                       interval = ci; 
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
    // BON.g:1203:1: integer_interval returns [IntegerInterval interval] : i1= integer_constant '..' i2= integer_constant ;
    public final IntegerInterval integer_interval() throws RecognitionException {
        IntegerInterval interval = null;

        BONParser.integer_constant_return i1 = null;

        BONParser.integer_constant_return i2 = null;


        try {
            // BON.g:1203:53: (i1= integer_constant '..' i2= integer_constant )
            // BON.g:1204:3: i1= integer_constant '..' i2= integer_constant
            {
            pushFollow(FOLLOW_integer_constant_in_integer_interval8024);
            i1=integer_constant();

            state._fsp--;
            if (state.failed) return interval;
            match(input,86,FOLLOW_86_in_integer_interval8026); if (state.failed) return interval;
            pushFollow(FOLLOW_integer_constant_in_integer_interval8030);
            i2=integer_constant();

            state._fsp--;
            if (state.failed) return interval;
            if ( state.backtracking==0 ) {
               interval = IntegerInterval.mk((i1!=null?i1.value:null),(i2!=null?i2.value:null),getSLoc((i1!=null?((Token)i1.start):null),(i2!=null?((Token)i2.stop):null))); 
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
    // BON.g:1208:1: character_interval returns [CharacterInterval interval] : c1= character_constant '..' c2= character_constant ;
    public final CharacterInterval character_interval() throws RecognitionException {
        CharacterInterval interval = null;

        BONParser.character_constant_return c1 = null;

        BONParser.character_constant_return c2 = null;


        try {
            // BON.g:1208:57: (c1= character_constant '..' c2= character_constant )
            // BON.g:1209:3: c1= character_constant '..' c2= character_constant
            {
            pushFollow(FOLLOW_character_constant_in_character_interval8072);
            c1=character_constant();

            state._fsp--;
            if (state.failed) return interval;
            match(input,86,FOLLOW_86_in_character_interval8074); if (state.failed) return interval;
            pushFollow(FOLLOW_character_constant_in_character_interval8078);
            c2=character_constant();

            state._fsp--;
            if (state.failed) return interval;
            if ( state.backtracking==0 ) {
               interval = CharacterInterval.mk((c1!=null?c1.value:null),(c2!=null?c2.value:null),getSLoc((c1!=null?((Token)c1.start):null),(c2!=null?((Token)c2.stop):null))); 
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
    // BON.g:1213:1: constant returns [Constant constant] : (mc= manifest_constant | c= 'Current' | v= 'Void' | v= 'Result' );
    public final BONParser.constant_return constant() throws RecognitionException {
        BONParser.constant_return retval = new BONParser.constant_return();
        retval.start = input.LT(1);

        Token c=null;
        Token v=null;
        ManifestConstant mc = null;


        try {
            // BON.g:1215:38: (mc= manifest_constant | c= 'Current' | v= 'Void' | v= 'Result' )
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
            case 87:
                {
                alt137=2;
                }
                break;
            case 88:
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
                    // BON.g:1216:4: mc= manifest_constant
                    {
                    pushFollow(FOLLOW_manifest_constant_in_constant8104);
                    mc=manifest_constant();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.constant = mc; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1218:4: c= 'Current'
                    {
                    c=(Token)match(input,87,FOLLOW_87_in_constant8117); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.constant = KeywordConstant.mk(KeywordConstant.Constant.CURRENT, getSLoc(c)); 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:1220:4: v= 'Void'
                    {
                    v=(Token)match(input,88,FOLLOW_88_in_constant8130); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.constant = KeywordConstant.mk(KeywordConstant.Constant.VOID, getSLoc(v)); 
                    }

                    }
                    break;
                case 4 :
                    // BON.g:1222:4: v= 'Result'
                    {
                    v=(Token)match(input,89,FOLLOW_89_in_constant8154); if (state.failed) return retval;
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
    // BON.g:1226:1: manifest_constant returns [ManifestConstant constant] : (bc= boolean_constant | cc= character_constant | ic= integer_constant | rc= real_constant | ms= MANIFEST_STRING | es= enumerated_set );
    public final ManifestConstant manifest_constant() throws RecognitionException {
        ManifestConstant constant = null;

        Token ms=null;
        BONParser.boolean_constant_return bc = null;

        BONParser.character_constant_return cc = null;

        BONParser.integer_constant_return ic = null;

        BONParser.real_constant_return rc = null;

        BONParser.enumerated_set_return es = null;


        try {
            // BON.g:1226:55: (bc= boolean_constant | cc= character_constant | ic= integer_constant | rc= real_constant | ms= MANIFEST_STRING | es= enumerated_set )
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

                if ( (LA138_3==INTEGER) ) {
                    alt138=3;
                }
                else if ( (LA138_3==REAL) ) {
                    alt138=4;
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
                    // BON.g:1227:4: bc= boolean_constant
                    {
                    pushFollow(FOLLOW_boolean_constant_in_manifest_constant8177);
                    bc=boolean_constant();

                    state._fsp--;
                    if (state.failed) return constant;
                    if ( state.backtracking==0 ) {
                       constant = BooleanConstant.mk((bc!=null?bc.value:null),getSLoc((bc!=null?((Token)bc.start):null),(bc!=null?((Token)bc.stop):null))); 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1229:4: cc= character_constant
                    {
                    pushFollow(FOLLOW_character_constant_in_manifest_constant8190);
                    cc=character_constant();

                    state._fsp--;
                    if (state.failed) return constant;
                    if ( state.backtracking==0 ) {
                       constant = CharacterConstant.mk((cc!=null?cc.value:null),getSLoc((cc!=null?((Token)cc.start):null),(cc!=null?((Token)cc.stop):null))); 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:1231:4: ic= integer_constant
                    {
                    pushFollow(FOLLOW_integer_constant_in_manifest_constant8203);
                    ic=integer_constant();

                    state._fsp--;
                    if (state.failed) return constant;
                    if ( state.backtracking==0 ) {
                       constant = IntegerConstant.mk((ic!=null?ic.value:null),getSLoc((ic!=null?((Token)ic.start):null),(ic!=null?((Token)ic.stop):null))); 
                    }

                    }
                    break;
                case 4 :
                    // BON.g:1233:4: rc= real_constant
                    {
                    pushFollow(FOLLOW_real_constant_in_manifest_constant8216);
                    rc=real_constant();

                    state._fsp--;
                    if (state.failed) return constant;
                    if ( state.backtracking==0 ) {
                       constant = RealConstant.mk((rc!=null?rc.value:null),getSLoc((rc!=null?((Token)rc.start):null),(rc!=null?((Token)rc.stop):null))); 
                    }

                    }
                    break;
                case 5 :
                    // BON.g:1235:4: ms= MANIFEST_STRING
                    {
                    ms=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_manifest_constant8229); if (state.failed) return constant;
                    if ( state.backtracking==0 ) {
                       constant = StringConstant.mk((ms!=null?ms.getText():null),getSLoc(ms)); 
                    }

                    }
                    break;
                case 6 :
                    // BON.g:1237:4: es= enumerated_set
                    {
                    pushFollow(FOLLOW_enumerated_set_in_manifest_constant8242);
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
    // BON.g:1241:1: sign returns [BinaryExp.Op op] : add_sub_op ;
    public final BinaryExp.Op sign() throws RecognitionException {
        BinaryExp.Op op = null;

        BinaryExp.Op add_sub_op92 = null;


        try {
            // BON.g:1241:32: ( add_sub_op )
            // BON.g:1242:3: add_sub_op
            {
            pushFollow(FOLLOW_add_sub_op_in_sign8281);
            add_sub_op92=add_sub_op();

            state._fsp--;
            if (state.failed) return op;
            if ( state.backtracking==0 ) {
               op = add_sub_op92; 
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
    // BON.g:1246:1: boolean_constant returns [Boolean value] : ( 'true' | 'false' );
    public final BONParser.boolean_constant_return boolean_constant() throws RecognitionException {
        BONParser.boolean_constant_return retval = new BONParser.boolean_constant_return();
        retval.start = input.LT(1);

        try {
            // BON.g:1246:42: ( 'true' | 'false' )
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
                    // BON.g:1247:4: 'true'
                    {
                    match(input,90,FOLLOW_90_in_boolean_constant8307); if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.value = true; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1249:4: 'false'
                    {
                    match(input,91,FOLLOW_91_in_boolean_constant8318); if (state.failed) return retval;
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
    // BON.g:1255:1: character_constant returns [Character value] : cc= CHARACTER_CONSTANT ;
    public final BONParser.character_constant_return character_constant() throws RecognitionException {
        BONParser.character_constant_return retval = new BONParser.character_constant_return();
        retval.start = input.LT(1);

        Token cc=null;

        try {
            // BON.g:1255:46: (cc= CHARACTER_CONSTANT )
            // BON.g:1256:2: cc= CHARACTER_CONSTANT
            {
            cc=(Token)match(input,CHARACTER_CONSTANT,FOLLOW_CHARACTER_CONSTANT_in_character_constant8342); if (state.failed) return retval;
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
    // BON.g:1264:1: integer_constant returns [Integer value] : ( sign )? i= INTEGER ;
    public final BONParser.integer_constant_return integer_constant() throws RecognitionException {
        BONParser.integer_constant_return retval = new BONParser.integer_constant_return();
        retval.start = input.LT(1);

        Token i=null;
        BinaryExp.Op sign93 = null;


         boolean negative = false; 
        try {
            // BON.g:1266:1: ( ( sign )? i= INTEGER )
            // BON.g:1267:3: ( sign )? i= INTEGER
            {
            // BON.g:1267:3: ( sign )?
            int alt140=2;
            int LA140_0 = input.LA(1);

            if ( ((LA140_0>=103 && LA140_0<=104)) ) {
                alt140=1;
            }
            switch (alt140) {
                case 1 :
                    // BON.g:1267:4: sign
                    {
                    pushFollow(FOLLOW_sign_in_integer_constant8408);
                    sign93=sign();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if (sign93 == BinaryExp.Op.SUB) negative = true; 
                    }

                    }
                    break;

            }

            i=(Token)match(input,INTEGER,FOLLOW_INTEGER_in_integer_constant8419); if (state.failed) return retval;
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
    // BON.g:1272:1: real_constant returns [Double value] : ( sign )? r= REAL ;
    public final BONParser.real_constant_return real_constant() throws RecognitionException {
        BONParser.real_constant_return retval = new BONParser.real_constant_return();
        retval.start = input.LT(1);

        Token r=null;
        BinaryExp.Op sign94 = null;


         boolean negative = false; 
        try {
            // BON.g:1274:1: ( ( sign )? r= REAL )
            // BON.g:1275:3: ( sign )? r= REAL
            {
            // BON.g:1275:3: ( sign )?
            int alt141=2;
            int LA141_0 = input.LA(1);

            if ( ((LA141_0>=103 && LA141_0<=104)) ) {
                alt141=1;
            }
            switch (alt141) {
                case 1 :
                    // BON.g:1275:4: sign
                    {
                    pushFollow(FOLLOW_sign_in_real_constant8464);
                    sign94=sign();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       if (sign94 == BinaryExp.Op.SUB) negative = true; 
                    }

                    }
                    break;

            }

            r=(Token)match(input,REAL,FOLLOW_REAL_in_real_constant8476); if (state.failed) return retval;
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
    // BON.g:1280:1: dynamic_diagram returns [DynamicDiagram dd] : s= 'dynamic_diagram' (eid= extended_id )? (c= COMMENT )? 'component' (db= dynamic_block | ) e= 'end' ;
    public final DynamicDiagram dynamic_diagram() throws RecognitionException {
        DynamicDiagram dd = null;

        Token s=null;
        Token c=null;
        Token e=null;
        BONParser.extended_id_return eid = null;

        List<DynamicComponent> db = null;


         String id = null; String comment = null; List<DynamicComponent> components = null; 
        try {
            // BON.g:1286:1: (s= 'dynamic_diagram' (eid= extended_id )? (c= COMMENT )? 'component' (db= dynamic_block | ) e= 'end' )
            // BON.g:1287:3: s= 'dynamic_diagram' (eid= extended_id )? (c= COMMENT )? 'component' (db= dynamic_block | ) e= 'end'
            {
            s=(Token)match(input,92,FOLLOW_92_in_dynamic_diagram8507); if (state.failed) return dd;
            // BON.g:1288:3: (eid= extended_id )?
            int alt142=2;
            int LA142_0 = input.LA(1);

            if ( (LA142_0==IDENTIFIER||LA142_0==INTEGER) ) {
                alt142=1;
            }
            switch (alt142) {
                case 1 :
                    // BON.g:1288:4: eid= extended_id
                    {
                    pushFollow(FOLLOW_extended_id_in_dynamic_diagram8515);
                    eid=extended_id();

                    state._fsp--;
                    if (state.failed) return dd;
                    if ( state.backtracking==0 ) {
                       id = (eid!=null?eid.eid:null); 
                    }

                    }
                    break;

            }

            // BON.g:1289:3: (c= COMMENT )?
            int alt143=2;
            int LA143_0 = input.LA(1);

            if ( (LA143_0==COMMENT) ) {
                alt143=1;
            }
            switch (alt143) {
                case 1 :
                    // BON.g:1289:4: c= COMMENT
                    {
                    c=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_dynamic_diagram8528); if (state.failed) return dd;
                    if ( state.backtracking==0 ) {
                       comment = (c!=null?c.getText():null); 
                    }

                    }
                    break;

            }

            match(input,55,FOLLOW_55_in_dynamic_diagram8537); if (state.failed) return dd;
            // BON.g:1291:3: (db= dynamic_block | )
            int alt144=2;
            int LA144_0 = input.LA(1);

            if ( (LA144_0==IDENTIFIER||LA144_0==INTEGER||LA144_0==50||(LA144_0>=94 && LA144_0<=97)) ) {
                alt144=1;
            }
            else if ( (LA144_0==25) ) {
                alt144=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return dd;}
                NoViableAltException nvae =
                    new NoViableAltException("", 144, 0, input);

                throw nvae;
            }
            switch (alt144) {
                case 1 :
                    // BON.g:1291:5: db= dynamic_block
                    {
                    pushFollow(FOLLOW_dynamic_block_in_dynamic_diagram8546);
                    db=dynamic_block();

                    state._fsp--;
                    if (state.failed) return dd;
                    if ( state.backtracking==0 ) {
                       components = db; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1293:6: 
                    {
                    if ( state.backtracking==0 ) {
                       components = emptyList(); 
                    }

                    }
                    break;

            }

            e=(Token)match(input,25,FOLLOW_25_in_dynamic_diagram8570); if (state.failed) return dd;
            if ( state.backtracking==0 ) {
               dd = DynamicDiagram.mk(components, id, comment, getSLoc(s,e)); 
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
    // BON.g:1299:1: dynamic_block returns [List<DynamicComponent> components] : (dc= dynamic_component )+ ;
    public final List<DynamicComponent> dynamic_block() throws RecognitionException {
        List<DynamicComponent> components = null;

        DynamicComponent dc = null;


        try {
            // BON.g:1299:59: ( (dc= dynamic_component )+ )
            // BON.g:1300:3: (dc= dynamic_component )+
            {
            if ( state.backtracking==0 ) {
               components = createList(); 
            }
            // BON.g:1301:3: (dc= dynamic_component )+
            int cnt145=0;
            loop145:
            do {
                int alt145=2;
                int LA145_0 = input.LA(1);

                if ( (LA145_0==IDENTIFIER||LA145_0==INTEGER||LA145_0==50||(LA145_0>=94 && LA145_0<=97)) ) {
                    alt145=1;
                }


                switch (alt145) {
            	case 1 :
            	    // BON.g:1301:4: dc= dynamic_component
            	    {
            	    pushFollow(FOLLOW_dynamic_component_in_dynamic_block8613);
            	    dc=dynamic_component();

            	    state._fsp--;
            	    if (state.failed) return components;
            	    if ( state.backtracking==0 ) {
            	       components.add(dc); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt145 >= 1 ) break loop145;
            	    if (state.backtracking>0) {state.failed=true; return components;}
                        EarlyExitException eee =
                            new EarlyExitException(145, input);
                        throw eee;
                }
                cnt145++;
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
    // BON.g:1304:1: dynamic_component returns [DynamicComponent component] : ( scenario_description | object_group | object_stack | object | message_relation );
    public final DynamicComponent dynamic_component() throws RecognitionException {
        DynamicComponent component = null;

        try {
            // BON.g:1304:56: ( scenario_description | object_group | object_stack | object | message_relation )
            int alt146=5;
            switch ( input.LA(1) ) {
            case 50:
                {
                alt146=1;
                }
                break;
            case 94:
            case 95:
                {
                alt146=2;
                }
                break;
            case 96:
                {
                alt146=3;
                }
                break;
            case 97:
                {
                alt146=4;
                }
                break;
            case IDENTIFIER:
            case INTEGER:
                {
                alt146=5;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return component;}
                NoViableAltException nvae =
                    new NoViableAltException("", 146, 0, input);

                throw nvae;
            }

            switch (alt146) {
                case 1 :
                    // BON.g:1305:4: scenario_description
                    {
                    pushFollow(FOLLOW_scenario_description_in_dynamic_component8650);
                    scenario_description();

                    state._fsp--;
                    if (state.failed) return component;

                    }
                    break;
                case 2 :
                    // BON.g:1306:4: object_group
                    {
                    pushFollow(FOLLOW_object_group_in_dynamic_component8655);
                    object_group();

                    state._fsp--;
                    if (state.failed) return component;

                    }
                    break;
                case 3 :
                    // BON.g:1307:4: object_stack
                    {
                    pushFollow(FOLLOW_object_stack_in_dynamic_component8661);
                    object_stack();

                    state._fsp--;
                    if (state.failed) return component;

                    }
                    break;
                case 4 :
                    // BON.g:1308:4: object
                    {
                    pushFollow(FOLLOW_object_in_dynamic_component8666);
                    object();

                    state._fsp--;
                    if (state.failed) return component;

                    }
                    break;
                case 5 :
                    // BON.g:1309:4: message_relation
                    {
                    pushFollow(FOLLOW_message_relation_in_dynamic_component8671);
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
    // BON.g:1312:1: scenario_description returns [ScenarioDescription description] : s= 'scenario' scenario_name (c= COMMENT )? 'action' la= labelled_actions e= 'end' ;
    public final ScenarioDescription scenario_description() throws RecognitionException {
        ScenarioDescription description = null;

        Token s=null;
        Token c=null;
        Token e=null;
        List<LabelledAction> la = null;

        String scenario_name95 = null;


         String comment = null; 
        try {
            // BON.g:1316:1: (s= 'scenario' scenario_name (c= COMMENT )? 'action' la= labelled_actions e= 'end' )
            // BON.g:1317:3: s= 'scenario' scenario_name (c= COMMENT )? 'action' la= labelled_actions e= 'end'
            {
            s=(Token)match(input,50,FOLLOW_50_in_scenario_description8699); if (state.failed) return description;
            pushFollow(FOLLOW_scenario_name_in_scenario_description8701);
            scenario_name95=scenario_name();

            state._fsp--;
            if (state.failed) return description;
            // BON.g:1318:3: (c= COMMENT )?
            int alt147=2;
            int LA147_0 = input.LA(1);

            if ( (LA147_0==COMMENT) ) {
                alt147=1;
            }
            switch (alt147) {
                case 1 :
                    // BON.g:1318:4: c= COMMENT
                    {
                    c=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_scenario_description8709); if (state.failed) return description;
                    if ( state.backtracking==0 ) {
                       comment = (c!=null?c.getText():null); 
                    }

                    }
                    break;

            }

            match(input,93,FOLLOW_93_in_scenario_description8718); if (state.failed) return description;
            pushFollow(FOLLOW_labelled_actions_in_scenario_description8725);
            la=labelled_actions();

            state._fsp--;
            if (state.failed) return description;
            e=(Token)match(input,25,FOLLOW_25_in_scenario_description8732); if (state.failed) return description;
            if ( state.backtracking==0 ) {
               description = ScenarioDescription.mk(scenario_name95, la, comment, getSLoc(s,c)); 
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
    // BON.g:1325:1: labelled_actions returns [List<LabelledAction> actions] : (la= labelled_action )+ ;
    public final List<LabelledAction> labelled_actions() throws RecognitionException {
        List<LabelledAction> actions = null;

        LabelledAction la = null;


        try {
            // BON.g:1325:57: ( (la= labelled_action )+ )
            // BON.g:1326:3: (la= labelled_action )+
            {
            if ( state.backtracking==0 ) {
               actions = createList(); 
            }
            // BON.g:1327:3: (la= labelled_action )+
            int cnt148=0;
            loop148:
            do {
                int alt148=2;
                int LA148_0 = input.LA(1);

                if ( (LA148_0==MANIFEST_STRING) ) {
                    alt148=1;
                }


                switch (alt148) {
            	case 1 :
            	    // BON.g:1327:4: la= labelled_action
            	    {
            	    pushFollow(FOLLOW_labelled_action_in_labelled_actions8780);
            	    la=labelled_action();

            	    state._fsp--;
            	    if (state.failed) return actions;
            	    if ( state.backtracking==0 ) {
            	       actions.add(la); 
            	    }

            	    }
            	    break;

            	default :
            	    if ( cnt148 >= 1 ) break loop148;
            	    if (state.backtracking>0) {state.failed=true; return actions;}
                        EarlyExitException eee =
                            new EarlyExitException(148, input);
                        throw eee;
                }
                cnt148++;
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
    // BON.g:1330:1: labelled_action returns [LabelledAction action] : al= action_label ad= action_description ;
    public final LabelledAction labelled_action() throws RecognitionException {
        LabelledAction action = null;

        BONParser.action_label_return al = null;

        BONParser.action_description_return ad = null;


        try {
            // BON.g:1330:49: (al= action_label ad= action_description )
            // BON.g:1331:3: al= action_label ad= action_description
            {
            pushFollow(FOLLOW_action_label_in_labelled_action8821);
            al=action_label();

            state._fsp--;
            if (state.failed) return action;
            pushFollow(FOLLOW_action_description_in_labelled_action8825);
            ad=action_description();

            state._fsp--;
            if (state.failed) return action;
            if ( state.backtracking==0 ) {
               action = LabelledAction.mk((al!=null?al.label:null), (ad!=null?ad.description:null), getSLoc((al!=null?((Token)al.start):null),(ad!=null?((Token)ad.stop):null))); 
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
    // BON.g:1335:1: action_label returns [String label] : m= MANIFEST_STRING ;
    public final BONParser.action_label_return action_label() throws RecognitionException {
        BONParser.action_label_return retval = new BONParser.action_label_return();
        retval.start = input.LT(1);

        Token m=null;

        try {
            // BON.g:1335:37: (m= MANIFEST_STRING )
            // BON.g:1336:3: m= MANIFEST_STRING
            {
            m=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_action_label8864); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.label = (m!=null?m.getText():null); 
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
    // BON.g:1340:1: action_description returns [String description] : m= manifest_textblock ;
    public final BONParser.action_description_return action_description() throws RecognitionException {
        BONParser.action_description_return retval = new BONParser.action_description_return();
        retval.start = input.LT(1);

        BONParser.manifest_textblock_return m = null;


        try {
            // BON.g:1340:49: (m= manifest_textblock )
            // BON.g:1341:3: m= manifest_textblock
            {
            pushFollow(FOLLOW_manifest_textblock_in_action_description8899);
            m=manifest_textblock();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.description = (m!=null?input.toString(m.start,m.stop):null); 
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
    // BON.g:1345:1: scenario_name returns [String name] : m= manifest_textblock ;
    public final String scenario_name() throws RecognitionException {
        String name = null;

        BONParser.manifest_textblock_return m = null;


        try {
            // BON.g:1345:37: (m= manifest_textblock )
            // BON.g:1346:3: m= manifest_textblock
            {
            pushFollow(FOLLOW_manifest_textblock_in_scenario_name8940);
            m=manifest_textblock();

            state._fsp--;
            if (state.failed) return name;
            if ( state.backtracking==0 ) {
               name = (m!=null?input.toString(m.start,m.stop):null); 
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
    // BON.g:1350:1: object_group returns [ObjectGroup group] : (n= 'nameless' | ) s= 'object_group' group_name (c= COMMENT )? (gc= group_components | ) ;
    public final ObjectGroup object_group() throws RecognitionException {
        ObjectGroup group = null;

        Token n=null;
        Token s=null;
        Token c=null;
        List<DynamicComponent> gc = null;

        BONParser.group_name_return group_name96 = null;


         String comment = null; List<DynamicComponent> components = null; 
                ObjectGroup.Nameless nameless = ObjectGroup.Nameless.NOTNAMELESS; 
                Token start = null; Token end = null; 
        try {
            // BON.g:1356:1: ( (n= 'nameless' | ) s= 'object_group' group_name (c= COMMENT )? (gc= group_components | ) )
            // BON.g:1357:3: (n= 'nameless' | ) s= 'object_group' group_name (c= COMMENT )? (gc= group_components | )
            {
            // BON.g:1357:3: (n= 'nameless' | )
            int alt149=2;
            int LA149_0 = input.LA(1);

            if ( (LA149_0==94) ) {
                alt149=1;
            }
            else if ( (LA149_0==95) ) {
                alt149=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return group;}
                NoViableAltException nvae =
                    new NoViableAltException("", 149, 0, input);

                throw nvae;
            }
            switch (alt149) {
                case 1 :
                    // BON.g:1357:6: n= 'nameless'
                    {
                    n=(Token)match(input,94,FOLLOW_94_in_object_group8973); if (state.failed) return group;
                    if ( state.backtracking==0 ) {
                       nameless = ObjectGroup.Nameless.NAMELESS; start = n; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1359:6: 
                    {
                    if ( state.backtracking==0 ) {
                       nameless = ObjectGroup.Nameless.NOTNAMELESS; 
                    }

                    }
                    break;

            }

            s=(Token)match(input,95,FOLLOW_95_in_object_group8998); if (state.failed) return group;
            if ( state.backtracking==0 ) {
               if (start==null) start=s; 
            }
            pushFollow(FOLLOW_group_name_in_object_group9004);
            group_name96=group_name();

            state._fsp--;
            if (state.failed) return group;
            if ( state.backtracking==0 ) {
               end = (group_name96!=null?((Token)group_name96.stop):null); 
            }
            // BON.g:1364:3: (c= COMMENT )?
            int alt150=2;
            int LA150_0 = input.LA(1);

            if ( (LA150_0==COMMENT) ) {
                alt150=1;
            }
            switch (alt150) {
                case 1 :
                    // BON.g:1364:4: c= COMMENT
                    {
                    c=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_object_group9016); if (state.failed) return group;
                    if ( state.backtracking==0 ) {
                       comment = (c!=null?c.getText():null); end = c; 
                    }

                    }
                    break;

            }

            // BON.g:1365:3: (gc= group_components | )
            int alt151=2;
            int LA151_0 = input.LA(1);

            if ( (LA151_0==55) ) {
                alt151=1;
            }
            else if ( (LA151_0==IDENTIFIER||LA151_0==INTEGER||LA151_0==25||LA151_0==50||(LA151_0>=94 && LA151_0<=97)) ) {
                alt151=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return group;}
                NoViableAltException nvae =
                    new NoViableAltException("", 151, 0, input);

                throw nvae;
            }
            switch (alt151) {
                case 1 :
                    // BON.g:1365:6: gc= group_components
                    {
                    pushFollow(FOLLOW_group_components_in_object_group9031);
                    gc=group_components();

                    state._fsp--;
                    if (state.failed) return group;
                    if ( state.backtracking==0 ) {
                       components = gc; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1367:6: 
                    {
                    if ( state.backtracking==0 ) {
                       components = emptyList(); 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               group = ObjectGroup.mk(nameless, (group_name96!=null?input.toString(group_name96.start,group_name96.stop):null), components, comment, getSLoc(start,end)); 
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
    // BON.g:1372:1: group_components returns [List<DynamicComponent> components] : 'component' dynamic_block 'end' ;
    public final List<DynamicComponent> group_components() throws RecognitionException {
        List<DynamicComponent> components = null;

        List<DynamicComponent> dynamic_block97 = null;


        try {
            // BON.g:1372:62: ( 'component' dynamic_block 'end' )
            // BON.g:1373:3: 'component' dynamic_block 'end'
            {
            match(input,55,FOLLOW_55_in_group_components9082); if (state.failed) return components;
            pushFollow(FOLLOW_dynamic_block_in_group_components9084);
            dynamic_block97=dynamic_block();

            state._fsp--;
            if (state.failed) return components;
            match(input,25,FOLLOW_25_in_group_components9086); if (state.failed) return components;
            if ( state.backtracking==0 ) {
               components = dynamic_block97; 
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
    // BON.g:1377:1: object_stack returns [ObjectStack stack] : s= 'object_stack' n= object_name (c= COMMENT )? ;
    public final ObjectStack object_stack() throws RecognitionException {
        ObjectStack stack = null;

        Token s=null;
        Token c=null;
        BONParser.object_name_return n = null;


         String comment = null; Token end = null; 
        try {
            // BON.g:1379:1: (s= 'object_stack' n= object_name (c= COMMENT )? )
            // BON.g:1380:3: s= 'object_stack' n= object_name (c= COMMENT )?
            {
            s=(Token)match(input,96,FOLLOW_96_in_object_stack9131); if (state.failed) return stack;
            pushFollow(FOLLOW_object_name_in_object_stack9138);
            n=object_name();

            state._fsp--;
            if (state.failed) return stack;
            if ( state.backtracking==0 ) {
               end = (n!=null?((Token)n.stop):null); 
            }
            // BON.g:1383:3: (c= COMMENT )?
            int alt152=2;
            int LA152_0 = input.LA(1);

            if ( (LA152_0==COMMENT) ) {
                alt152=1;
            }
            switch (alt152) {
                case 1 :
                    // BON.g:1383:4: c= COMMENT
                    {
                    c=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_object_stack9150); if (state.failed) return stack;
                    if ( state.backtracking==0 ) {
                       comment = (c!=null?c.getText():null); end = c; 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               stack = ObjectStack.mk((n!=null?n.name:null), comment, getSLoc(s,end)); 
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
    // BON.g:1387:1: object returns [ObjectInstance object] : s= 'object' n= object_name (c= COMMENT )? ;
    public final ObjectInstance object() throws RecognitionException {
        ObjectInstance object = null;

        Token s=null;
        Token c=null;
        BONParser.object_name_return n = null;


         String comment = null; Token end = null; 
        try {
            // BON.g:1389:1: (s= 'object' n= object_name (c= COMMENT )? )
            // BON.g:1390:3: s= 'object' n= object_name (c= COMMENT )?
            {
            s=(Token)match(input,97,FOLLOW_97_in_object9198); if (state.failed) return object;
            pushFollow(FOLLOW_object_name_in_object9205);
            n=object_name();

            state._fsp--;
            if (state.failed) return object;
            if ( state.backtracking==0 ) {
               end = (n!=null?((Token)n.stop):null); 
            }
            // BON.g:1393:3: (c= COMMENT )?
            int alt153=2;
            int LA153_0 = input.LA(1);

            if ( (LA153_0==COMMENT) ) {
                alt153=1;
            }
            switch (alt153) {
                case 1 :
                    // BON.g:1393:4: c= COMMENT
                    {
                    c=(Token)match(input,COMMENT,FOLLOW_COMMENT_in_object9217); if (state.failed) return object;
                    if ( state.backtracking==0 ) {
                       comment = (c!=null?c.getText():null); end = c; 
                    }

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               object = ObjectInstance.mk((n!=null?n.name:null), comment, getSLoc(s,end)); 
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
    // BON.g:1397:1: message_relation : caller 'calls' receiver ( message_label )? ;
    public final void message_relation() throws RecognitionException {
        try {
            // BON.g:1399:19: ( caller 'calls' receiver ( message_label )? )
            // BON.g:1399:22: caller 'calls' receiver ( message_label )?
            {
            pushFollow(FOLLOW_caller_in_message_relation9241);
            caller();

            state._fsp--;
            if (state.failed) return ;
            match(input,98,FOLLOW_98_in_message_relation9243); if (state.failed) return ;
            pushFollow(FOLLOW_receiver_in_message_relation9245);
            receiver();

            state._fsp--;
            if (state.failed) return ;
            // BON.g:1399:46: ( message_label )?
            int alt154=2;
            int LA154_0 = input.LA(1);

            if ( (LA154_0==MANIFEST_STRING) ) {
                alt154=1;
            }
            switch (alt154) {
                case 1 :
                    // BON.g:1399:47: message_label
                    {
                    pushFollow(FOLLOW_message_label_in_message_relation9248);
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
    // BON.g:1402:1: caller : dynamic_ref ;
    public final void caller() throws RecognitionException {
        try {
            // BON.g:1402:9: ( dynamic_ref )
            // BON.g:1402:12: dynamic_ref
            {
            pushFollow(FOLLOW_dynamic_ref_in_caller9280);
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
    // BON.g:1405:1: receiver : dynamic_ref ;
    public final void receiver() throws RecognitionException {
        try {
            // BON.g:1405:11: ( dynamic_ref )
            // BON.g:1405:14: dynamic_ref
            {
            pushFollow(FOLLOW_dynamic_ref_in_receiver9300);
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
    // BON.g:1412:1: dynamic_ref : extended_id ( '.' extended_id )* ;
    public final void dynamic_ref() throws RecognitionException {
        try {
            // BON.g:1412:14: ( extended_id ( '.' extended_id )* )
            // BON.g:1412:17: extended_id ( '.' extended_id )*
            {
            pushFollow(FOLLOW_extended_id_in_dynamic_ref9326);
            extended_id();

            state._fsp--;
            if (state.failed) return ;
            // BON.g:1412:29: ( '.' extended_id )*
            loop155:
            do {
                int alt155=2;
                int LA155_0 = input.LA(1);

                if ( (LA155_0==70) ) {
                    alt155=1;
                }


                switch (alt155) {
            	case 1 :
            	    // BON.g:1412:30: '.' extended_id
            	    {
            	    match(input,70,FOLLOW_70_in_dynamic_ref9329); if (state.failed) return ;
            	    pushFollow(FOLLOW_extended_id_in_dynamic_ref9331);
            	    extended_id();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop155;
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
    // BON.g:1421:1: dynamic_component_name : ( ( IDENTIFIER ( '.' extended_id )? ) | INTEGER );
    public final void dynamic_component_name() throws RecognitionException {
        try {
            // BON.g:1421:25: ( ( IDENTIFIER ( '.' extended_id )? ) | INTEGER )
            int alt157=2;
            int LA157_0 = input.LA(1);

            if ( (LA157_0==IDENTIFIER) ) {
                alt157=1;
            }
            else if ( (LA157_0==INTEGER) ) {
                alt157=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 157, 0, input);

                throw nvae;
            }
            switch (alt157) {
                case 1 :
                    // BON.g:1422:4: ( IDENTIFIER ( '.' extended_id )? )
                    {
                    // BON.g:1422:4: ( IDENTIFIER ( '.' extended_id )? )
                    // BON.g:1422:5: IDENTIFIER ( '.' extended_id )?
                    {
                    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_dynamic_component_name9362); if (state.failed) return ;
                    // BON.g:1422:16: ( '.' extended_id )?
                    int alt156=2;
                    int LA156_0 = input.LA(1);

                    if ( (LA156_0==70) ) {
                        alt156=1;
                    }
                    switch (alt156) {
                        case 1 :
                            // BON.g:1422:17: '.' extended_id
                            {
                            match(input,70,FOLLOW_70_in_dynamic_component_name9365); if (state.failed) return ;
                            pushFollow(FOLLOW_extended_id_in_dynamic_component_name9367);
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
                    // BON.g:1423:4: INTEGER
                    {
                    match(input,INTEGER,FOLLOW_INTEGER_in_dynamic_component_name9376); if (state.failed) return ;

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
    // BON.g:1426:1: object_name returns [ObjectName name] : n= class_name ( '.' e= extended_id )? ;
    public final BONParser.object_name_return object_name() throws RecognitionException {
        BONParser.object_name_return retval = new BONParser.object_name_return();
        retval.start = input.LT(1);

        BONParser.class_name_return n = null;

        BONParser.extended_id_return e = null;


         String id = null; Token end = null; 
        try {
            // BON.g:1428:1: (n= class_name ( '.' e= extended_id )? )
            // BON.g:1429:3: n= class_name ( '.' e= extended_id )?
            {
            pushFollow(FOLLOW_class_name_in_object_name9399);
            n=class_name();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               end = (n!=null?((Token)n.stop):null); 
            }
            // BON.g:1431:3: ( '.' e= extended_id )?
            int alt158=2;
            int LA158_0 = input.LA(1);

            if ( (LA158_0==70) ) {
                alt158=1;
            }
            switch (alt158) {
                case 1 :
                    // BON.g:1431:4: '.' e= extended_id
                    {
                    match(input,70,FOLLOW_70_in_object_name9409); if (state.failed) return retval;
                    pushFollow(FOLLOW_extended_id_in_object_name9413);
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
               retval.name = ObjectName.mk((n!=null?n.name:null), id, getSLoc((n!=null?((Token)n.start):null),end)); 
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
    // BON.g:1435:1: group_name returns [String name] : e= extended_id ;
    public final BONParser.group_name_return group_name() throws RecognitionException {
        BONParser.group_name_return retval = new BONParser.group_name_return();
        retval.start = input.LT(1);

        BONParser.extended_id_return e = null;


        try {
            // BON.g:1435:34: (e= extended_id )
            // BON.g:1436:3: e= extended_id
            {
            pushFollow(FOLLOW_extended_id_in_group_name9453);
            e=extended_id();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) {
               retval.name = (e!=null?e.eid:null); 
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
    // BON.g:1440:1: message_label returns [String label] : m= MANIFEST_STRING ;
    public final String message_label() throws RecognitionException {
        String label = null;

        Token m=null;

        try {
            // BON.g:1440:38: (m= MANIFEST_STRING )
            // BON.g:1441:3: m= MANIFEST_STRING
            {
            m=(Token)match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_message_label9486); if (state.failed) return label;
            if ( state.backtracking==0 ) {
               label = (m!=null?m.getText():null); 
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
    // BON.g:1445:1: notational_tuning : ( change_string_marks | change_concatenator | change_prefix );
    public final void notational_tuning() throws RecognitionException {
        try {
            // BON.g:1449:19: ( change_string_marks | change_concatenator | change_prefix )
            int alt159=3;
            switch ( input.LA(1) ) {
            case 99:
                {
                alt159=1;
                }
                break;
            case 100:
                {
                alt159=2;
                }
                break;
            case 101:
                {
                alt159=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 159, 0, input);

                throw nvae;
            }

            switch (alt159) {
                case 1 :
                    // BON.g:1450:4: change_string_marks
                    {
                    pushFollow(FOLLOW_change_string_marks_in_notational_tuning9510);
                    change_string_marks();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 2 :
                    // BON.g:1451:4: change_concatenator
                    {
                    pushFollow(FOLLOW_change_concatenator_in_notational_tuning9516);
                    change_concatenator();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 3 :
                    // BON.g:1452:4: change_prefix
                    {
                    pushFollow(FOLLOW_change_prefix_in_notational_tuning9521);
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
    // BON.g:1455:1: change_string_marks : 'string_marks' MANIFEST_STRING MANIFEST_STRING ;
    public final void change_string_marks() throws RecognitionException {
        try {
            // BON.g:1455:22: ( 'string_marks' MANIFEST_STRING MANIFEST_STRING )
            // BON.g:1456:3: 'string_marks' MANIFEST_STRING MANIFEST_STRING
            {
            match(input,99,FOLLOW_99_in_change_string_marks9536); if (state.failed) return ;
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_string_marks9538); if (state.failed) return ;
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_string_marks9540); if (state.failed) return ;

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
    // BON.g:1459:1: change_concatenator : 'concatenator' MANIFEST_STRING ;
    public final void change_concatenator() throws RecognitionException {
        try {
            // BON.g:1459:22: ( 'concatenator' MANIFEST_STRING )
            // BON.g:1460:3: 'concatenator' MANIFEST_STRING
            {
            match(input,100,FOLLOW_100_in_change_concatenator9574); if (state.failed) return ;
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_concatenator9576); if (state.failed) return ;

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
    // BON.g:1463:1: change_prefix : 'keyword_prefix' MANIFEST_STRING ;
    public final void change_prefix() throws RecognitionException {
        try {
            // BON.g:1463:16: ( 'keyword_prefix' MANIFEST_STRING )
            // BON.g:1464:3: 'keyword_prefix' MANIFEST_STRING
            {
            match(input,101,FOLLOW_101_in_change_prefix9610); if (state.failed) return ;
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_prefix9612); if (state.failed) return ;

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
    // BON.g:1467:1: expression returns [Expression exp] : (e= equivalence_expression | q= quantification );
    public final BONParser.expression_return expression() throws RecognitionException {
        BONParser.expression_return retval = new BONParser.expression_return();
        retval.start = input.LT(1);

        Expression e = null;

        Quantification q = null;


        try {
            // BON.g:1471:37: (e= equivalence_expression | q= quantification )
            int alt160=2;
            int LA160_0 = input.LA(1);

            if ( ((LA160_0>=MANIFEST_STRING && LA160_0<=IDENTIFIER)||(LA160_0>=INTEGER && LA160_0<=REAL)||LA160_0==42||LA160_0==62||(LA160_0>=87 && LA160_0<=91)||(LA160_0>=103 && LA160_0<=104)||(LA160_0>=108 && LA160_0<=110)) ) {
                alt160=1;
            }
            else if ( ((LA160_0>=81 && LA160_0<=82)) ) {
                alt160=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 160, 0, input);

                throw nvae;
            }
            switch (alt160) {
                case 1 :
                    // BON.g:1472:4: e= equivalence_expression
                    {
                    pushFollow(FOLLOW_equivalence_expression_in_expression9638);
                    e=equivalence_expression();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.exp = e; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1474:4: q= quantification
                    {
                    pushFollow(FOLLOW_quantification_in_expression9652);
                    q=quantification();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.exp = q; 
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
    // BON.g:1478:1: equivalence_expression returns [Expression exp] : l= implies_expression ( '<->' r= implies_expression )* ;
    public final Expression equivalence_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        Expression r = null;


        try {
            // BON.g:1478:49: (l= implies_expression ( '<->' r= implies_expression )* )
            // BON.g:1479:3: l= implies_expression ( '<->' r= implies_expression )*
            {
            pushFollow(FOLLOW_implies_expression_in_equivalence_expression9674);
            l=implies_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               exp = l; 
            }
            // BON.g:1481:3: ( '<->' r= implies_expression )*
            loop161:
            do {
                int alt161=2;
                int LA161_0 = input.LA(1);

                if ( (LA161_0==102) ) {
                    alt161=1;
                }


                switch (alt161) {
            	case 1 :
            	    // BON.g:1481:4: '<->' r= implies_expression
            	    {
            	    match(input,102,FOLLOW_102_in_equivalence_expression9684); if (state.failed) return exp;
            	    pushFollow(FOLLOW_implies_expression_in_equivalence_expression9688);
            	    r=implies_expression();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    if ( state.backtracking==0 ) {
            	       exp = BinaryExp.mk(BinaryExp.Op.EQUIV, exp, r, getSLoc(exp.getLocation(),r.getLocation())); 
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
    // $ANTLR end "equivalence_expression"


    // $ANTLR start "implies_expression"
    // BON.g:1487:1: implies_expression returns [Expression exp] : l= and_or_xor_expression ( '->' r= implies_expression )? ;
    public final Expression implies_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        Expression r = null;


        try {
            // BON.g:1487:45: (l= and_or_xor_expression ( '->' r= implies_expression )? )
            // BON.g:1488:3: l= and_or_xor_expression ( '->' r= implies_expression )?
            {
            pushFollow(FOLLOW_and_or_xor_expression_in_implies_expression9716);
            l=and_or_xor_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               exp = l; 
            }
            // BON.g:1490:3: ( '->' r= implies_expression )?
            int alt162=2;
            int LA162_0 = input.LA(1);

            if ( (LA162_0==65) ) {
                alt162=1;
            }
            switch (alt162) {
                case 1 :
                    // BON.g:1490:4: '->' r= implies_expression
                    {
                    match(input,65,FOLLOW_65_in_implies_expression9726); if (state.failed) return exp;
                    pushFollow(FOLLOW_implies_expression_in_implies_expression9730);
                    r=implies_expression();

                    state._fsp--;
                    if (state.failed) return exp;
                    if ( state.backtracking==0 ) {
                       exp = BinaryExp.mk(BinaryExp.Op.IMPLIES, exp, r, getSLoc(exp.getLocation(),r.getLocation())); 
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
    // BON.g:1495:1: and_or_xor_expression returns [Expression exp] : l= comparison_expression (op= and_or_xor_op r= comparison_expression )* ;
    public final Expression and_or_xor_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        BinaryExp.Op op = null;

        Expression r = null;


        try {
            // BON.g:1495:48: (l= comparison_expression (op= and_or_xor_op r= comparison_expression )* )
            // BON.g:1496:3: l= comparison_expression (op= and_or_xor_op r= comparison_expression )*
            {
            pushFollow(FOLLOW_comparison_expression_in_and_or_xor_expression9757);
            l=comparison_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               exp = l; 
            }
            // BON.g:1498:3: (op= and_or_xor_op r= comparison_expression )*
            loop163:
            do {
                int alt163=2;
                int LA163_0 = input.LA(1);

                if ( ((LA163_0>=105 && LA163_0<=107)) ) {
                    alt163=1;
                }


                switch (alt163) {
            	case 1 :
            	    // BON.g:1498:4: op= and_or_xor_op r= comparison_expression
            	    {
            	    pushFollow(FOLLOW_and_or_xor_op_in_and_or_xor_expression9769);
            	    op=and_or_xor_op();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    pushFollow(FOLLOW_comparison_expression_in_and_or_xor_expression9773);
            	    r=comparison_expression();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    if ( state.backtracking==0 ) {
            	       exp = BinaryExp.mk(op, exp, r, getSLoc(exp.getLocation(),r.getLocation())); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop163;
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
    // BON.g:1503:1: comparison_expression returns [Expression exp] : l= add_sub_expression (op= comparison_op r= add_sub_expression )* ;
    public final Expression comparison_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        BinaryExp.Op op = null;

        Expression r = null;


        try {
            // BON.g:1503:48: (l= add_sub_expression (op= comparison_op r= add_sub_expression )* )
            // BON.g:1504:3: l= add_sub_expression (op= comparison_op r= add_sub_expression )*
            {
            pushFollow(FOLLOW_add_sub_expression_in_comparison_expression9801);
            l=add_sub_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               exp = l; 
            }
            // BON.g:1506:3: (op= comparison_op r= add_sub_expression )*
            loop164:
            do {
                int alt164=2;
                int LA164_0 = input.LA(1);

                if ( (LA164_0==34||LA164_0==85||(LA164_0>=110 && LA164_0<=116)) ) {
                    alt164=1;
                }


                switch (alt164) {
            	case 1 :
            	    // BON.g:1506:4: op= comparison_op r= add_sub_expression
            	    {
            	    pushFollow(FOLLOW_comparison_op_in_comparison_expression9813);
            	    op=comparison_op();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    pushFollow(FOLLOW_add_sub_expression_in_comparison_expression9818);
            	    r=add_sub_expression();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    if ( state.backtracking==0 ) {
            	       exp = BinaryExp.mk(op, exp, r, getSLoc(exp.getLocation(),r.getLocation())); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop164;
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
    // BON.g:1511:1: add_sub_expression returns [Expression exp] : l= mul_div_expression (op= add_sub_op r= mul_div_expression )* ;
    public final Expression add_sub_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        BinaryExp.Op op = null;

        Expression r = null;


        try {
            // BON.g:1511:45: (l= mul_div_expression (op= add_sub_op r= mul_div_expression )* )
            // BON.g:1512:3: l= mul_div_expression (op= add_sub_op r= mul_div_expression )*
            {
            pushFollow(FOLLOW_mul_div_expression_in_add_sub_expression9846);
            l=mul_div_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               exp = l; 
            }
            // BON.g:1514:3: (op= add_sub_op r= mul_div_expression )*
            loop165:
            do {
                int alt165=2;
                int LA165_0 = input.LA(1);

                if ( ((LA165_0>=103 && LA165_0<=104)) ) {
                    alt165=1;
                }


                switch (alt165) {
            	case 1 :
            	    // BON.g:1514:4: op= add_sub_op r= mul_div_expression
            	    {
            	    pushFollow(FOLLOW_add_sub_op_in_add_sub_expression9858);
            	    op=add_sub_op();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    pushFollow(FOLLOW_mul_div_expression_in_add_sub_expression9862);
            	    r=mul_div_expression();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    if ( state.backtracking==0 ) {
            	       exp = BinaryExp.mk(op, exp, r, getSLoc(exp.getLocation(),r.getLocation())); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop165;
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
    // BON.g:1519:1: mul_div_expression returns [Expression exp] : l= mod_pow_expression (op= mul_div_op r= mod_pow_expression )* ;
    public final Expression mul_div_expression() throws RecognitionException {
        Expression exp = null;

        Expression l = null;

        BinaryExp.Op op = null;

        Expression r = null;


        try {
            // BON.g:1519:45: (l= mod_pow_expression (op= mul_div_op r= mod_pow_expression )* )
            // BON.g:1520:3: l= mod_pow_expression (op= mul_div_op r= mod_pow_expression )*
            {
            pushFollow(FOLLOW_mod_pow_expression_in_mul_div_expression9890);
            l=mod_pow_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               exp = l; 
            }
            // BON.g:1522:3: (op= mul_div_op r= mod_pow_expression )*
            loop166:
            do {
                int alt166=2;
                int LA166_0 = input.LA(1);

                if ( ((LA166_0>=117 && LA166_0<=119)) ) {
                    alt166=1;
                }


                switch (alt166) {
            	case 1 :
            	    // BON.g:1522:4: op= mul_div_op r= mod_pow_expression
            	    {
            	    pushFollow(FOLLOW_mul_div_op_in_mul_div_expression9902);
            	    op=mul_div_op();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    pushFollow(FOLLOW_mod_pow_expression_in_mul_div_expression9906);
            	    r=mod_pow_expression();

            	    state._fsp--;
            	    if (state.failed) return exp;
            	    if ( state.backtracking==0 ) {
            	       exp = BinaryExp.mk(op, exp, r, getSLoc(exp.getLocation(),r.getLocation())); 
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
    // $ANTLR end "mul_div_expression"


    // $ANTLR start "mod_pow_expression"
    // BON.g:1528:1: mod_pow_expression returns [Expression exp] : l= lowest_expression (op= mod_pow_op r= mod_pow_expression )? ;
    public final Expression mod_pow_expression() throws RecognitionException {
        Expression exp = null;

        BONParser.lowest_expression_return l = null;

        BinaryExp.Op op = null;

        Expression r = null;


        try {
            // BON.g:1528:45: (l= lowest_expression (op= mod_pow_op r= mod_pow_expression )? )
            // BON.g:1529:3: l= lowest_expression (op= mod_pow_op r= mod_pow_expression )?
            {
            pushFollow(FOLLOW_lowest_expression_in_mod_pow_expression9935);
            l=lowest_expression();

            state._fsp--;
            if (state.failed) return exp;
            if ( state.backtracking==0 ) {
               exp = (l!=null?l.exp:null); 
            }
            // BON.g:1531:3: (op= mod_pow_op r= mod_pow_expression )?
            int alt167=2;
            int LA167_0 = input.LA(1);

            if ( (LA167_0==76||LA167_0==120) ) {
                alt167=1;
            }
            switch (alt167) {
                case 1 :
                    // BON.g:1531:4: op= mod_pow_op r= mod_pow_expression
                    {
                    pushFollow(FOLLOW_mod_pow_op_in_mod_pow_expression9947);
                    op=mod_pow_op();

                    state._fsp--;
                    if (state.failed) return exp;
                    pushFollow(FOLLOW_mod_pow_expression_in_mod_pow_expression9951);
                    r=mod_pow_expression();

                    state._fsp--;
                    if (state.failed) return exp;
                    if ( state.backtracking==0 ) {
                       exp = BinaryExp.mk(op, exp, r, getSLoc(exp.getLocation(),r.getLocation())); 
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
    // BON.g:1536:1: lowest_expression returns [Expression exp] : ( ( constant )=> constant ( ( '.' cc= call_chain ) | ) | unary le= lowest_expression | s= '(' e= expression ')' ( ( '.' cc= call_chain ) | ) | cc= call_chain );
    public final BONParser.lowest_expression_return lowest_expression() throws RecognitionException {
        BONParser.lowest_expression_return retval = new BONParser.lowest_expression_return();
        retval.start = input.LT(1);

        Token s=null;
        BONParser.call_chain_return cc = null;

        BONParser.lowest_expression_return le = null;

        BONParser.expression_return e = null;

        BONParser.constant_return constant98 = null;

        BONParser.unary_return unary99 = null;


        try {
            // BON.g:1536:44: ( ( constant )=> constant ( ( '.' cc= call_chain ) | ) | unary le= lowest_expression | s= '(' e= expression ')' ( ( '.' cc= call_chain ) | ) | cc= call_chain )
            int alt170=4;
            alt170 = dfa170.predict(input);
            switch (alt170) {
                case 1 :
                    // BON.g:1537:5: ( constant )=> constant ( ( '.' cc= call_chain ) | )
                    {
                    pushFollow(FOLLOW_constant_in_lowest_expression9984);
                    constant98=constant();

                    state._fsp--;
                    if (state.failed) return retval;
                    // BON.g:1538:5: ( ( '.' cc= call_chain ) | )
                    int alt168=2;
                    int LA168_0 = input.LA(1);

                    if ( (LA168_0==70) ) {
                        alt168=1;
                    }
                    else if ( (LA168_0==25||(LA168_0>=33 && LA168_0<=35)||LA168_0==43||LA168_0==63||LA168_0==65||(LA168_0>=75 && LA168_0<=76)||(LA168_0>=83 && LA168_0<=85)||(LA168_0>=102 && LA168_0<=107)||(LA168_0>=110 && LA168_0<=120)) ) {
                        alt168=2;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return retval;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 168, 0, input);

                        throw nvae;
                    }
                    switch (alt168) {
                        case 1 :
                            // BON.g:1538:7: ( '.' cc= call_chain )
                            {
                            // BON.g:1538:7: ( '.' cc= call_chain )
                            // BON.g:1538:8: '.' cc= call_chain
                            {
                            match(input,70,FOLLOW_70_in_lowest_expression9993); if (state.failed) return retval;
                            pushFollow(FOLLOW_call_chain_in_lowest_expression9997);
                            cc=call_chain();

                            state._fsp--;
                            if (state.failed) return retval;
                            if ( state.backtracking==0 ) {
                               retval.exp = CallExp.mk((constant98!=null?constant98.constant:null), (cc!=null?cc.calls:null), getSLoc((constant98!=null?((Token)constant98.start):null),(cc!=null?((Token)cc.stop):null))); 
                            }

                            }


                            }
                            break;
                        case 2 :
                            // BON.g:1542:7: 
                            {
                            if ( state.backtracking==0 ) {
                               retval.exp = (constant98!=null?constant98.constant:null); 
                            }

                            }
                            break;

                    }


                    }
                    break;
                case 2 :
                    // BON.g:1544:4: unary le= lowest_expression
                    {
                    pushFollow(FOLLOW_unary_in_lowest_expression10047);
                    unary99=unary();

                    state._fsp--;
                    if (state.failed) return retval;
                    pushFollow(FOLLOW_lowest_expression_in_lowest_expression10051);
                    le=lowest_expression();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.exp = UnaryExp.mk((unary99!=null?unary99.op:null), (le!=null?le.exp:null), getSLoc((unary99!=null?((Token)unary99.start):null),(le!=null?((Token)le.stop):null))); 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:1546:4: s= '(' e= expression ')' ( ( '.' cc= call_chain ) | )
                    {
                    s=(Token)match(input,42,FOLLOW_42_in_lowest_expression10064); if (state.failed) return retval;
                    pushFollow(FOLLOW_expression_in_lowest_expression10068);
                    e=expression();

                    state._fsp--;
                    if (state.failed) return retval;
                    match(input,43,FOLLOW_43_in_lowest_expression10070); if (state.failed) return retval;
                    // BON.g:1547:4: ( ( '.' cc= call_chain ) | )
                    int alt169=2;
                    int LA169_0 = input.LA(1);

                    if ( (LA169_0==70) ) {
                        alt169=1;
                    }
                    else if ( (LA169_0==25||(LA169_0>=33 && LA169_0<=35)||LA169_0==43||LA169_0==63||LA169_0==65||(LA169_0>=75 && LA169_0<=76)||(LA169_0>=83 && LA169_0<=85)||(LA169_0>=102 && LA169_0<=107)||(LA169_0>=110 && LA169_0<=120)) ) {
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
                            // BON.g:1547:6: ( '.' cc= call_chain )
                            {
                            // BON.g:1547:6: ( '.' cc= call_chain )
                            // BON.g:1547:7: '.' cc= call_chain
                            {
                            match(input,70,FOLLOW_70_in_lowest_expression10080); if (state.failed) return retval;
                            pushFollow(FOLLOW_call_chain_in_lowest_expression10084);
                            cc=call_chain();

                            state._fsp--;
                            if (state.failed) return retval;
                            if ( state.backtracking==0 ) {
                               retval.exp = CallExp.mk((e!=null?e.exp:null), (cc!=null?cc.calls:null), getSLoc(s,(cc!=null?((Token)cc.stop):null))); 
                            }

                            }


                            }
                            break;
                        case 2 :
                            // BON.g:1550:7: 
                            {
                            if ( state.backtracking==0 ) {
                               retval.exp = (e!=null?e.exp:null); 
                            }

                            }
                            break;

                    }


                    }
                    break;
                case 4 :
                    // BON.g:1552:4: cc= call_chain
                    {
                    pushFollow(FOLLOW_call_chain_in_lowest_expression10120);
                    cc=call_chain();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.exp =  CallExp.mk(null, (cc!=null?cc.calls:null), getSLoc((cc!=null?((Token)cc.start):null),(cc!=null?((Token)cc.stop):null))); 
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
    // BON.g:1556:1: add_sub_op returns [BinaryExp.Op op] : ( '+' | '-' );
    public final BinaryExp.Op add_sub_op() throws RecognitionException {
        BinaryExp.Op op = null;

        try {
            // BON.g:1560:38: ( '+' | '-' )
            int alt171=2;
            int LA171_0 = input.LA(1);

            if ( (LA171_0==103) ) {
                alt171=1;
            }
            else if ( (LA171_0==104) ) {
                alt171=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 171, 0, input);

                throw nvae;
            }
            switch (alt171) {
                case 1 :
                    // BON.g:1561:4: '+'
                    {
                    match(input,103,FOLLOW_103_in_add_sub_op10144); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.ADD; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1562:4: '-'
                    {
                    match(input,104,FOLLOW_104_in_add_sub_op10152); if (state.failed) return op;
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
    // BON.g:1565:1: add_sub_op_unary returns [UnaryExp.Op op] : ( '+' | '-' );
    public final UnaryExp.Op add_sub_op_unary() throws RecognitionException {
        UnaryExp.Op op = null;

        try {
            // BON.g:1565:43: ( '+' | '-' )
            int alt172=2;
            int LA172_0 = input.LA(1);

            if ( (LA172_0==103) ) {
                alt172=1;
            }
            else if ( (LA172_0==104) ) {
                alt172=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 172, 0, input);

                throw nvae;
            }
            switch (alt172) {
                case 1 :
                    // BON.g:1566:4: '+'
                    {
                    match(input,103,FOLLOW_103_in_add_sub_op_unary10170); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = UnaryExp.Op.ADD; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1567:4: '-'
                    {
                    match(input,104,FOLLOW_104_in_add_sub_op_unary10178); if (state.failed) return op;
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
    // BON.g:1570:1: and_or_xor_op returns [BinaryExp.Op op] : ( 'and' | 'or' | 'xor' );
    public final BinaryExp.Op and_or_xor_op() throws RecognitionException {
        BinaryExp.Op op = null;

        try {
            // BON.g:1570:41: ( 'and' | 'or' | 'xor' )
            int alt173=3;
            switch ( input.LA(1) ) {
            case 105:
                {
                alt173=1;
                }
                break;
            case 106:
                {
                alt173=2;
                }
                break;
            case 107:
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
                    // BON.g:1571:4: 'and'
                    {
                    match(input,105,FOLLOW_105_in_and_or_xor_op10196); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.AND; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1572:4: 'or'
                    {
                    match(input,106,FOLLOW_106_in_and_or_xor_op10203); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.OR; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:1573:4: 'xor'
                    {
                    match(input,107,FOLLOW_107_in_and_or_xor_op10211); if (state.failed) return op;
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
    // BON.g:1576:1: unary returns [UnaryExp.Op op] : ( other_unary | add_sub_op_unary );
    public final BONParser.unary_return unary() throws RecognitionException {
        BONParser.unary_return retval = new BONParser.unary_return();
        retval.start = input.LT(1);

        UnaryExp.Op other_unary100 = null;

        UnaryExp.Op add_sub_op_unary101 = null;


        try {
            // BON.g:1576:33: ( other_unary | add_sub_op_unary )
            int alt174=2;
            int LA174_0 = input.LA(1);

            if ( ((LA174_0>=108 && LA174_0<=110)) ) {
                alt174=1;
            }
            else if ( ((LA174_0>=103 && LA174_0<=104)) ) {
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
                    // BON.g:1577:4: other_unary
                    {
                    pushFollow(FOLLOW_other_unary_in_unary10231);
                    other_unary100=other_unary();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.op = other_unary100; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1578:4: add_sub_op_unary
                    {
                    pushFollow(FOLLOW_add_sub_op_unary_in_unary10245);
                    add_sub_op_unary101=add_sub_op_unary();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) {
                       retval.op = add_sub_op_unary101; 
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
    // BON.g:1581:1: other_unary returns [UnaryExp.Op op] : ( 'delta' | 'old' | 'not' );
    public final UnaryExp.Op other_unary() throws RecognitionException {
        UnaryExp.Op op = null;

        try {
            // BON.g:1581:39: ( 'delta' | 'old' | 'not' )
            int alt175=3;
            switch ( input.LA(1) ) {
            case 108:
                {
                alt175=1;
                }
                break;
            case 109:
                {
                alt175=2;
                }
                break;
            case 110:
                {
                alt175=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 175, 0, input);

                throw nvae;
            }

            switch (alt175) {
                case 1 :
                    // BON.g:1582:4: 'delta'
                    {
                    match(input,108,FOLLOW_108_in_other_unary10265); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = UnaryExp.Op.DELTA; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1583:4: 'old'
                    {
                    match(input,109,FOLLOW_109_in_other_unary10273); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = UnaryExp.Op.OLD; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:1584:4: 'not'
                    {
                    match(input,110,FOLLOW_110_in_other_unary10282); if (state.failed) return op;
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
    // BON.g:1587:1: binary : ( add_sub_op | mul_div_op | comparison_op | mod_pow_op | and_or_xor_op | '->' | '<->' );
    public final void binary() throws RecognitionException {
        try {
            // BON.g:1587:9: ( add_sub_op | mul_div_op | comparison_op | mod_pow_op | and_or_xor_op | '->' | '<->' )
            int alt176=7;
            switch ( input.LA(1) ) {
            case 103:
            case 104:
                {
                alt176=1;
                }
                break;
            case 117:
            case 118:
            case 119:
                {
                alt176=2;
                }
                break;
            case 34:
            case 85:
            case 110:
            case 111:
            case 112:
            case 113:
            case 114:
            case 115:
            case 116:
                {
                alt176=3;
                }
                break;
            case 76:
            case 120:
                {
                alt176=4;
                }
                break;
            case 105:
            case 106:
            case 107:
                {
                alt176=5;
                }
                break;
            case 65:
                {
                alt176=6;
                }
                break;
            case 102:
                {
                alt176=7;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 176, 0, input);

                throw nvae;
            }

            switch (alt176) {
                case 1 :
                    // BON.g:1587:13: add_sub_op
                    {
                    pushFollow(FOLLOW_add_sub_op_in_binary10313);
                    add_sub_op();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 2 :
                    // BON.g:1587:26: mul_div_op
                    {
                    pushFollow(FOLLOW_mul_div_op_in_binary10317);
                    mul_div_op();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 3 :
                    // BON.g:1587:39: comparison_op
                    {
                    pushFollow(FOLLOW_comparison_op_in_binary10321);
                    comparison_op();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 4 :
                    // BON.g:1588:13: mod_pow_op
                    {
                    pushFollow(FOLLOW_mod_pow_op_in_binary10336);
                    mod_pow_op();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 5 :
                    // BON.g:1588:26: and_or_xor_op
                    {
                    pushFollow(FOLLOW_and_or_xor_op_in_binary10340);
                    and_or_xor_op();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;
                case 6 :
                    // BON.g:1589:13: '->'
                    {
                    match(input,65,FOLLOW_65_in_binary10355); if (state.failed) return ;

                    }
                    break;
                case 7 :
                    // BON.g:1589:20: '<->'
                    {
                    match(input,102,FOLLOW_102_in_binary10359); if (state.failed) return ;

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
    // BON.g:1591:1: comparison_op returns [BinaryExp.Op op] : ( '<' | '>' | '<=' | '>=' | '=' | '/=' | 'member_of' | 'not' 'member_of' | ':' );
    public final BinaryExp.Op comparison_op() throws RecognitionException {
        BinaryExp.Op op = null;

        try {
            // BON.g:1591:41: ( '<' | '>' | '<=' | '>=' | '=' | '/=' | 'member_of' | 'not' 'member_of' | ':' )
            int alt177=9;
            switch ( input.LA(1) ) {
            case 111:
                {
                alt177=1;
                }
                break;
            case 112:
                {
                alt177=2;
                }
                break;
            case 113:
                {
                alt177=3;
                }
                break;
            case 114:
                {
                alt177=4;
                }
                break;
            case 115:
                {
                alt177=5;
                }
                break;
            case 116:
                {
                alt177=6;
                }
                break;
            case 85:
                {
                alt177=7;
                }
                break;
            case 110:
                {
                alt177=8;
                }
                break;
            case 34:
                {
                alt177=9;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 177, 0, input);

                throw nvae;
            }

            switch (alt177) {
                case 1 :
                    // BON.g:1592:4: '<'
                    {
                    match(input,111,FOLLOW_111_in_comparison_op10375); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.LT; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1593:4: '>'
                    {
                    match(input,112,FOLLOW_112_in_comparison_op10383); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.GT; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:1594:4: '<='
                    {
                    match(input,113,FOLLOW_113_in_comparison_op10391); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.LE; 
                    }

                    }
                    break;
                case 4 :
                    // BON.g:1595:4: '>='
                    {
                    match(input,114,FOLLOW_114_in_comparison_op10398); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.GE; 
                    }

                    }
                    break;
                case 5 :
                    // BON.g:1596:4: '='
                    {
                    match(input,115,FOLLOW_115_in_comparison_op10405); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.EQ; 
                    }

                    }
                    break;
                case 6 :
                    // BON.g:1597:4: '/='
                    {
                    match(input,116,FOLLOW_116_in_comparison_op10413); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.NEQ; 
                    }

                    }
                    break;
                case 7 :
                    // BON.g:1598:4: 'member_of'
                    {
                    match(input,85,FOLLOW_85_in_comparison_op10420); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.MEMBEROF; 
                    }

                    }
                    break;
                case 8 :
                    // BON.g:1599:4: 'not' 'member_of'
                    {
                    match(input,110,FOLLOW_110_in_comparison_op10427); if (state.failed) return op;
                    match(input,85,FOLLOW_85_in_comparison_op10429); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.NOTMEMBEROF; 
                    }

                    }
                    break;
                case 9 :
                    // BON.g:1600:4: ':'
                    {
                    match(input,34,FOLLOW_34_in_comparison_op10436); if (state.failed) return op;
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
    // BON.g:1604:1: mul_div_op returns [BinaryExp.Op op] : ( '*' | '/' | '//' );
    public final BinaryExp.Op mul_div_op() throws RecognitionException {
        BinaryExp.Op op = null;

        try {
            // BON.g:1604:38: ( '*' | '/' | '//' )
            int alt178=3;
            switch ( input.LA(1) ) {
            case 117:
                {
                alt178=1;
                }
                break;
            case 118:
                {
                alt178=2;
                }
                break;
            case 119:
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
                    // BON.g:1605:4: '*'
                    {
                    match(input,117,FOLLOW_117_in_mul_div_op10463); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.MUL; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1606:4: '/'
                    {
                    match(input,118,FOLLOW_118_in_mul_div_op10471); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.DIV; 
                    }

                    }
                    break;
                case 3 :
                    // BON.g:1607:4: '//'
                    {
                    match(input,119,FOLLOW_119_in_mul_div_op10479); if (state.failed) return op;
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
    // BON.g:1610:1: mod_pow_op returns [BinaryExp.Op op] : ( '\\\\\\\\' | '^' );
    public final BinaryExp.Op mod_pow_op() throws RecognitionException {
        BinaryExp.Op op = null;

        try {
            // BON.g:1610:38: ( '\\\\\\\\' | '^' )
            int alt179=2;
            int LA179_0 = input.LA(1);

            if ( (LA179_0==120) ) {
                alt179=1;
            }
            else if ( (LA179_0==76) ) {
                alt179=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return op;}
                NoViableAltException nvae =
                    new NoViableAltException("", 179, 0, input);

                throw nvae;
            }
            switch (alt179) {
                case 1 :
                    // BON.g:1611:4: '\\\\\\\\'
                    {
                    match(input,120,FOLLOW_120_in_mod_pow_op10512); if (state.failed) return op;
                    if ( state.backtracking==0 ) {
                       op = BinaryExp.Op.MOD; 
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1612:4: '^'
                    {
                    match(input,76,FOLLOW_76_in_mod_pow_op10520); if (state.failed) return op;
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
    // BON.g:1654:1: manifest_textblock : ( MANIFEST_STRING | MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END );
    public final BONParser.manifest_textblock_return manifest_textblock() throws RecognitionException {
        BONParser.manifest_textblock_return retval = new BONParser.manifest_textblock_return();
        retval.start = input.LT(1);

        try {
            // BON.g:1654:21: ( MANIFEST_STRING | MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END )
            int alt181=2;
            int LA181_0 = input.LA(1);

            if ( (LA181_0==MANIFEST_STRING) ) {
                alt181=1;
            }
            else if ( (LA181_0==MANIFEST_TEXTBLOCK_START) ) {
                alt181=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 181, 0, input);

                throw nvae;
            }
            switch (alt181) {
                case 1 :
                    // BON.g:1654:25: MANIFEST_STRING
                    {
                    match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_manifest_textblock10823); if (state.failed) return retval;

                    }
                    break;
                case 2 :
                    // BON.g:1655:10: MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END
                    {
                    match(input,MANIFEST_TEXTBLOCK_START,FOLLOW_MANIFEST_TEXTBLOCK_START_in_manifest_textblock10835); if (state.failed) return retval;
                    // BON.g:1655:35: ( MANIFEST_TEXTBLOCK_MIDDLE )*
                    loop180:
                    do {
                        int alt180=2;
                        int LA180_0 = input.LA(1);

                        if ( (LA180_0==MANIFEST_TEXTBLOCK_MIDDLE) ) {
                            alt180=1;
                        }


                        switch (alt180) {
                    	case 1 :
                    	    // BON.g:1655:35: MANIFEST_TEXTBLOCK_MIDDLE
                    	    {
                    	    match(input,MANIFEST_TEXTBLOCK_MIDDLE,FOLLOW_MANIFEST_TEXTBLOCK_MIDDLE_in_manifest_textblock10837); if (state.failed) return retval;

                    	    }
                    	    break;

                    	default :
                    	    break loop180;
                        }
                    } while (true);

                    match(input,MANIFEST_TEXTBLOCK_END,FOLLOW_MANIFEST_TEXTBLOCK_END_in_manifest_textblock10840); if (state.failed) return retval;

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
        // BON.g:1537:5: ( constant )
        // BON.g:1537:6: constant
        {
        pushFollow(FOLLOW_constant_in_synpred1_BON9980);
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
    protected DFA129 dfa129 = new DFA129(this);
    protected DFA170 dfa170 = new DFA170(this);
    static final String DFA1_eotS =
        "\26\uffff";
    static final String DFA1_eofS =
        "\1\3\1\uffff\1\5\4\uffff\2\5\1\uffff\1\5\1\uffff\1\5\1\uffff\4\5"+
        "\2\uffff\2\5";
    static final String DFA1_minS =
        "\1\30\1\uffff\1\5\1\uffff\1\42\2\uffff\1\4\1\5\1\42\1\5\1\42\3\4"+
        "\3\5\2\4\2\5";
    static final String DFA1_maxS =
        "\1\134\1\uffff\1\134\1\uffff\1\42\2\uffff\2\134\1\42\1\134\1\42"+
        "\1\134\1\4\4\134\2\4\2\134";
    static final String DFA1_acceptS =
        "\1\uffff\1\1\1\uffff\1\3\1\uffff\1\4\1\2\17\uffff";
    static final String DFA1_specialS =
        "\26\uffff}>";
    static final String[] DFA1_transitionS = {
            "\1\1\3\uffff\1\1\1\uffff\1\2\5\uffff\2\1\6\uffff\1\1\4\uffff"+
            "\1\1\1\uffff\1\1\2\uffff\1\1\45\uffff\1\1",
            "",
            "\1\4\22\uffff\1\6\3\uffff\1\6\7\uffff\2\6\6\uffff\1\6\4\uffff"+
            "\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff\1\6",
            "",
            "\1\7",
            "",
            "",
            "\1\12\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\2\uffff\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\13\22\uffff\1\6\3\uffff\1\6\7\uffff\2\6\6\uffff\1\6\4\uffff"+
            "\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff\1\6",
            "\1\14",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\15\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\16",
            "\1\17\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\2\uffff\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\20",
            "\1\21\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\2\uffff\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\22\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\15\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\23\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\24",
            "\1\25",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\22\2"+
            "\6\6\uffff\1\6\4\uffff\1\6\1\uffff\1\6\2\uffff\1\6\45\uffff"+
            "\1\6",
            "\1\11\22\uffff\1\6\3\uffff\1\6\4\uffff\1\10\1\uffff\1\23\2"+
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
            return "31:1: prog returns [BonSourceFile bonSource] : (bs= bon_specification EOF | i= indexing bs= bon_specification EOF | e= EOF | indexing e= EOF );";
        }
    }
    static final String DFA78_eotS =
        "\7\uffff";
    static final String DFA78_eofS =
        "\7\uffff";
    static final String DFA78_minS =
        "\1\5\1\46\1\uffff\1\5\1\uffff\1\46\1\5";
    static final String DFA78_maxS =
        "\1\5\1\106\1\uffff\1\5\1\uffff\1\106\1\5";
    static final String DFA78_acceptS =
        "\2\uffff\1\2\1\uffff\1\1\2\uffff";
    static final String DFA78_specialS =
        "\7\uffff}>";
    static final String[] DFA78_transitionS = {
            "\1\1",
            "\1\4\31\uffff\1\2\5\uffff\1\3",
            "",
            "\1\5",
            "",
            "\1\4\31\uffff\1\2\5\uffff\1\6",
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
            return "581:1: static_relation returns [StaticRelation relation] : (ir= inheritance_relation | cr= client_relation );";
        }
    }
    static final String DFA86_eotS =
        "\46\uffff";
    static final String DFA86_eofS =
        "\46\uffff";
    static final String DFA86_minS =
        "\1\5\2\117\2\uffff\1\147\1\42\21\117\1\125\10\117\2\42\1\117\2\uffff";
    static final String DFA86_maxS =
        "\1\120\2\117\2\uffff\1\156\1\170\21\117\1\125\10\117\2\77\1\117"+
        "\2\uffff";
    static final String DFA86_acceptS =
        "\3\uffff\1\3\1\4\37\uffff\1\1\1\2";
    static final String DFA86_specialS =
        "\46\uffff}>";
    static final String[] DFA86_transitionS = {
            "\1\3\44\uffff\1\3\26\uffff\1\4\1\3\1\uffff\1\3\11\uffff\1\1"+
            "\1\uffff\1\2",
            "\1\5",
            "\1\6",
            "",
            "",
            "\1\12\1\13\3\uffff\1\7\1\10\1\11",
            "\1\31\36\uffff\1\37\12\uffff\1\33\10\uffff\1\27\20\uffff\1"+
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
            return "646:1: client_entity returns [ClientEntity entity] : ( prefix | infix | supplier_indirection | parent_indirection );";
        }
    }
    static final String DFA129_eotS =
        "\6\uffff";
    static final String DFA129_eofS =
        "\6\uffff";
    static final String DFA129_minS =
        "\1\5\1\42\1\5\2\uffff\1\42";
    static final String DFA129_maxS =
        "\1\5\1\125\1\5\2\uffff\1\125";
    static final String DFA129_acceptS =
        "\3\uffff\1\1\1\2\1\uffff";
    static final String DFA129_specialS =
        "\6\uffff}>";
    static final String[] DFA129_transitionS = {
            "\1\1",
            "\1\4\1\2\61\uffff\1\3",
            "\1\5",
            "",
            "",
            "\1\4\1\2\61\uffff\1\3"
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
            return "1114:1: variable_range returns [VariableRange range] : (mr= member_range | tr= type_range );";
        }
    }
    static final String DFA170_eotS =
        "\20\uffff";
    static final String DFA170_eofS =
        "\20\uffff";
    static final String DFA170_minS =
        "\1\4\3\uffff\2\0\12\uffff";
    static final String DFA170_maxS =
        "\1\156\3\uffff\2\0\12\uffff";
    static final String DFA170_acceptS =
        "\1\uffff\3\1\2\uffff\7\1\1\2\1\3\1\4";
    static final String DFA170_specialS =
        "\1\1\3\uffff\1\0\1\2\12\uffff}>";
    static final String[] DFA170_transitionS = {
            "\1\10\1\17\1\uffff\1\6\1\3\1\7\40\uffff\1\16\23\uffff\1\11\30"+
            "\uffff\1\12\1\13\1\14\1\1\1\2\13\uffff\1\4\1\5\3\uffff\3\15",
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

    static final short[] DFA170_eot = DFA.unpackEncodedString(DFA170_eotS);
    static final short[] DFA170_eof = DFA.unpackEncodedString(DFA170_eofS);
    static final char[] DFA170_min = DFA.unpackEncodedStringToUnsignedChars(DFA170_minS);
    static final char[] DFA170_max = DFA.unpackEncodedStringToUnsignedChars(DFA170_maxS);
    static final short[] DFA170_accept = DFA.unpackEncodedString(DFA170_acceptS);
    static final short[] DFA170_special = DFA.unpackEncodedString(DFA170_specialS);
    static final short[][] DFA170_transition;

    static {
        int numStates = DFA170_transitionS.length;
        DFA170_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA170_transition[i] = DFA.unpackEncodedString(DFA170_transitionS[i]);
        }
    }

    class DFA170 extends DFA {

        public DFA170(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 170;
            this.eot = DFA170_eot;
            this.eof = DFA170_eof;
            this.min = DFA170_min;
            this.max = DFA170_max;
            this.accept = DFA170_accept;
            this.special = DFA170_special;
            this.transition = DFA170_transition;
        }
        public String getDescription() {
            return "1536:1: lowest_expression returns [Expression exp] : ( ( constant )=> constant ( ( '.' cc= call_chain ) | ) | unary le= lowest_expression | s= '(' e= expression ')' ( ( '.' cc= call_chain ) | ) | cc= call_chain );";
        }
        public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
            TokenStream input = (TokenStream)_input;
        	int _s = s;
            switch ( s ) {
                    case 0 : 
                        int LA170_4 = input.LA(1);

                         
                        int index170_4 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred1_BON()) ) {s = 12;}

                        else if ( (true) ) {s = 13;}

                         
                        input.seek(index170_4);
                        if ( s>=0 ) return s;
                        break;
                    case 1 : 
                        int LA170_0 = input.LA(1);

                         
                        int index170_0 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (LA170_0==90) && (synpred1_BON())) {s = 1;}

                        else if ( (LA170_0==91) && (synpred1_BON())) {s = 2;}

                        else if ( (LA170_0==CHARACTER_CONSTANT) && (synpred1_BON())) {s = 3;}

                        else if ( (LA170_0==103) ) {s = 4;}

                        else if ( (LA170_0==104) ) {s = 5;}

                        else if ( (LA170_0==INTEGER) && (synpred1_BON())) {s = 6;}

                        else if ( (LA170_0==REAL) && (synpred1_BON())) {s = 7;}

                        else if ( (LA170_0==MANIFEST_STRING) && (synpred1_BON())) {s = 8;}

                        else if ( (LA170_0==62) && (synpred1_BON())) {s = 9;}

                        else if ( (LA170_0==87) && (synpred1_BON())) {s = 10;}

                        else if ( (LA170_0==88) && (synpred1_BON())) {s = 11;}

                        else if ( (LA170_0==89) && (synpred1_BON())) {s = 12;}

                        else if ( ((LA170_0>=108 && LA170_0<=110)) ) {s = 13;}

                        else if ( (LA170_0==42) ) {s = 14;}

                        else if ( (LA170_0==IDENTIFIER) ) {s = 15;}

                         
                        input.seek(index170_0);
                        if ( s>=0 ) return s;
                        break;
                    case 2 : 
                        int LA170_5 = input.LA(1);

                         
                        int index170_5 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred1_BON()) ) {s = 12;}

                        else if ( (true) ) {s = 13;}

                         
                        input.seek(index170_5);
                        if ( s>=0 ) return s;
                        break;
            }
            if (state.backtracking>0) {state.failed=true; return -1;}
            NoViableAltException nvae =
                new NoViableAltException(getDescription(), 170, _s, input);
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
    public static final BitSet FOLLOW_34_in_index_clause1152 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_index_term_list_in_index_clause1154 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_index_clause1168 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_34_in_index_clause1170 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_index_string_in_index_term_list1212 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_index_term_list1222 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_index_string_in_index_term_list1226 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_index_string1271 = new BitSet(new long[]{0x0000000000000002L});
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
    public static final BitSet FOLLOW_class_name_in_clazz3632 = new BitSet(new long[]{0x3100004040000042L,0x0000000000000104L});
    public static final BitSet FOLLOW_formal_generics_in_clazz3645 = new BitSet(new long[]{0x3100004040000042L,0x0000000000000100L});
    public static final BitSet FOLLOW_56_in_clazz3667 = new BitSet(new long[]{0x3000004040000042L,0x0000000000000100L});
    public static final BitSet FOLLOW_60_in_clazz3680 = new BitSet(new long[]{0x2000004040000042L,0x0000000000000100L});
    public static final BitSet FOLLOW_61_in_clazz3694 = new BitSet(new long[]{0x0000004040000042L,0x0000000000000100L});
    public static final BitSet FOLLOW_COMMENT_in_clazz3706 = new BitSet(new long[]{0x0000004040000002L,0x0000000000000100L});
    public static final BitSet FOLLOW_class_interface_in_clazz3718 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_inheritance_relation_in_static_relation3758 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_client_relation_in_static_relation3770 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_child_in_inheritance_relation3801 = new BitSet(new long[]{0x0000004000000000L});
    public static final BitSet FOLLOW_38_in_inheritance_relation3803 = new BitSet(new long[]{0x4000000000000020L});
    public static final BitSet FOLLOW_62_in_inheritance_relation3811 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_multiplicity_in_inheritance_relation3813 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_63_in_inheritance_relation3817 = new BitSet(new long[]{0x4000000000000020L});
    public static final BitSet FOLLOW_parent_in_inheritance_relation3834 = new BitSet(new long[]{0x0000000000000012L});
    public static final BitSet FOLLOW_semantic_label_in_inheritance_relation3845 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_client_in_client_relation3904 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000001L});
    public static final BitSet FOLLOW_64_in_client_relation3906 = new BitSet(new long[]{0x4000000400000020L,0x0000000000000020L});
    public static final BitSet FOLLOW_client_entities_in_client_relation3911 = new BitSet(new long[]{0x4000000400000020L,0x0000000000000020L});
    public static final BitSet FOLLOW_type_mark_in_client_relation3923 = new BitSet(new long[]{0x4000000400000020L,0x0000000000000020L});
    public static final BitSet FOLLOW_supplier_in_client_relation3949 = new BitSet(new long[]{0x0000000000000012L});
    public static final BitSet FOLLOW_semantic_label_in_client_relation3959 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_62_in_client_entities4000 = new BitSet(new long[]{0x00000400000000A0L,0x0000000000014016L});
    public static final BitSet FOLLOW_client_entity_expression_in_client_entities4004 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_63_in_client_entities4006 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_client_entity_list_in_client_entity_expression4045 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_multiplicity_in_client_entity_expression4058 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_client_entity_in_client_entity_list4111 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_client_entity_list4120 = new BitSet(new long[]{0x0000040000000020L,0x0000000000014016L});
    public static final BitSet FOLLOW_client_entity_in_client_entity_list4124 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_prefix_in_client_entity4175 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_infix_in_client_entity4180 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_supplier_indirection_in_client_entity4185 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_parent_indirection_in_client_entity4196 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indirection_feature_part_in_supplier_indirection4242 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_34_in_supplier_indirection4246 = new BitSet(new long[]{0x0000040000000020L,0x0000000000014014L});
    public static final BitSet FOLLOW_generic_indirection_in_supplier_indirection4255 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_name_in_indirection_feature_part4304 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indirection_feature_list_in_indirection_feature_part4315 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_42_in_indirection_feature_list4365 = new BitSet(new long[]{0x0000000000000020L,0x0000000000014000L});
    public static final BitSet FOLLOW_feature_name_list_in_indirection_feature_list4369 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_43_in_indirection_feature_list4373 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_65_in_parent_indirection4421 = new BitSet(new long[]{0x0000040000000020L,0x0000000000014014L});
    public static final BitSet FOLLOW_generic_indirection_in_parent_indirection4425 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indirection_element_in_generic_indirection4477 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_named_indirection4522 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000004L});
    public static final BitSet FOLLOW_66_in_named_indirection4524 = new BitSet(new long[]{0x0000040000000020L,0x0000000000014014L});
    public static final BitSet FOLLOW_indirection_list_in_named_indirection4528 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_67_in_named_indirection4532 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_66_in_named_indirection4547 = new BitSet(new long[]{0x0000040000000020L,0x0000000000014014L});
    public static final BitSet FOLLOW_indirection_list_in_named_indirection4549 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_67_in_named_indirection4551 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indirection_element_in_indirection_list4598 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_indirection_list4608 = new BitSet(new long[]{0x0000040000000020L,0x0000000000014014L});
    public static final BitSet FOLLOW_indirection_element_in_indirection_list4612 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_68_in_indirection_element4666 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_named_indirection_in_indirection_element4676 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_indirection_element4687 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_34_in_type_mark4732 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_69_in_type_mark4745 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_shared_mark_in_type_mark4758 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_34_in_shared_mark4804 = new BitSet(new long[]{0x0000040000000000L});
    public static final BitSet FOLLOW_42_in_shared_mark4806 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_multiplicity_in_shared_mark4810 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_43_in_shared_mark4814 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_ref_in_child4838 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_ref_in_parent4866 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_ref_in_client4904 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_ref_in_supplier4934 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_component_name_in_static_ref4968 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cluster_prefix_in_static_ref4984 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_static_component_name_in_static_ref4988 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_prefix5027 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_cluster_prefix5036 = new BitSet(new long[]{0x0000000000000022L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_prefix5045 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_cluster_prefix5047 = new BitSet(new long[]{0x0000000000000022L});
    public static final BitSet FOLLOW_IDENTIFIER_in_static_component_name5079 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_INTEGER_in_multiplicity5123 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_semantic_label5159 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indexing_in_class_interface5188 = new BitSet(new long[]{0x0000004040000000L,0x0000000000000100L});
    public static final BitSet FOLLOW_parent_class_list_in_class_interface5202 = new BitSet(new long[]{0x0000004040000000L,0x0000000000000100L});
    public static final BitSet FOLLOW_features_in_class_interface5220 = new BitSet(new long[]{0x0000000002000000L,0x0000000000000080L});
    public static final BitSet FOLLOW_class_invariant_in_class_interface5233 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_class_interface5253 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_71_in_class_invariant5292 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F860000L});
    public static final BitSet FOLLOW_assertion_in_class_invariant5294 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_38_in_parent_class_list5335 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_type_in_parent_class_list5339 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_parent_class_list5350 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_type_in_parent_class_list5354 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_parent_class_list5371 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_38_in_parent_class_list5382 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_clause_in_features5426 = new BitSet(new long[]{0x0000004040000002L,0x0000000000000100L});
    public static final BitSet FOLLOW_72_in_feature_clause5467 = new BitSet(new long[]{0x4C00000000000060L,0x0000000000014200L});
    public static final BitSet FOLLOW_selective_export_in_feature_clause5477 = new BitSet(new long[]{0x4C00000000000060L,0x0000000000014200L});
    public static final BitSet FOLLOW_COMMENT_in_feature_clause5499 = new BitSet(new long[]{0x4C00000000000060L,0x0000000000014200L});
    public static final BitSet FOLLOW_feature_specifications_in_feature_clause5511 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_specification_in_feature_specifications5554 = new BitSet(new long[]{0x4C00000000000062L,0x0000000000014200L});
    public static final BitSet FOLLOW_58_in_feature_specification5609 = new BitSet(new long[]{0x0000000000000020L,0x0000000000014000L});
    public static final BitSet FOLLOW_59_in_feature_specification5622 = new BitSet(new long[]{0x0000000000000020L,0x0000000000014000L});
    public static final BitSet FOLLOW_73_in_feature_specification5633 = new BitSet(new long[]{0x0000000000000020L,0x0000000000014000L});
    public static final BitSet FOLLOW_feature_name_list_in_feature_specification5664 = new BitSet(new long[]{0x4000000400000042L,0x0000000000002C22L});
    public static final BitSet FOLLOW_has_type_in_feature_specification5673 = new BitSet(new long[]{0x4000000000000042L,0x0000000000002C02L});
    public static final BitSet FOLLOW_rename_clause_in_feature_specification5685 = new BitSet(new long[]{0x0000000000000042L,0x0000000000002C02L});
    public static final BitSet FOLLOW_COMMENT_in_feature_specification5697 = new BitSet(new long[]{0x0000000000000002L,0x0000000000002C02L});
    public static final BitSet FOLLOW_feature_arguments_in_feature_specification5711 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000C00L});
    public static final BitSet FOLLOW_contract_clause_in_feature_specification5738 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_type_mark_in_has_type5801 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_type_in_has_type5803 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_contracting_conditions_in_contract_clause5828 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_contract_clause5830 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_precondition_in_contracting_conditions5862 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000C00L});
    public static final BitSet FOLLOW_postcondition_in_contracting_conditions5867 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_postcondition_in_contracting_conditions5891 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_74_in_precondition5917 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F860000L});
    public static final BitSet FOLLOW_assertion_in_precondition5919 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_75_in_postcondition5953 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F860000L});
    public static final BitSet FOLLOW_assertion_in_postcondition5955 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_62_in_selective_export5978 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_list_in_selective_export5982 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_63_in_selective_export5984 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_name_in_feature_name_list6029 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_feature_name_list6039 = new BitSet(new long[]{0x0000000000000020L,0x0000000000014000L});
    public static final BitSet FOLLOW_feature_name_in_feature_name_list6043 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_feature_name6092 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_prefix_in_feature_name6102 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_infix_in_feature_name6108 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_62_in_rename_clause6138 = new BitSet(new long[]{0x0000000000000000L,0x0000000000001000L});
    public static final BitSet FOLLOW_renaming_in_rename_clause6140 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_63_in_rename_clause6142 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_76_in_renaming6178 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_in_renaming6180 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_renaming6182 = new BitSet(new long[]{0x0000000000000020L,0x0000000000014000L});
    public static final BitSet FOLLOW_feature_name_in_renaming6184 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_argument_in_feature_arguments6219 = new BitSet(new long[]{0x0000000000000002L,0x0000000000002002L});
    public static final BitSet FOLLOW_set_in_feature_argument6259 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_identifier_list_in_feature_argument6283 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_34_in_feature_argument6285 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_type_in_feature_argument6289 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_type_in_feature_argument6321 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_identifier_list6381 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_identifier_list6391 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_IDENTIFIER_in_identifier_list6395 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_78_in_prefix6412 = new BitSet(new long[]{0x0000000000000000L,0x0000000000008000L});
    public static final BitSet FOLLOW_79_in_prefix6414 = new BitSet(new long[]{0x0000000000000000L,0x0000718000000000L});
    public static final BitSet FOLLOW_prefix_operator_in_prefix6416 = new BitSet(new long[]{0x0000000000000000L,0x0000000000008000L});
    public static final BitSet FOLLOW_79_in_prefix6418 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_80_in_infix6437 = new BitSet(new long[]{0x0000000000000000L,0x0000000000008000L});
    public static final BitSet FOLLOW_79_in_infix6439 = new BitSet(new long[]{0x0000000400000000L,0x01FFCFC000201002L});
    public static final BitSet FOLLOW_infix_operator_in_infix6441 = new BitSet(new long[]{0x0000000000000000L,0x0000000000008000L});
    public static final BitSet FOLLOW_79_in_infix6443 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unary_in_prefix_operator6463 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_binary_in_infix_operator6478 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_66_in_formal_generics6497 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_formal_generic_list_in_formal_generics6501 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_67_in_formal_generics6503 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_formal_generic_in_formal_generic_list6546 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_formal_generic_list6555 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_formal_generic_in_formal_generic_list6559 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_formal_generic_name_in_formal_generic6609 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_formal_generic_name_in_formal_generic6621 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000002L});
    public static final BitSet FOLLOW_65_in_formal_generic6623 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_class_type_in_formal_generic6627 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_formal_generic_name6666 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_class_type6711 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000004L});
    public static final BitSet FOLLOW_actual_generics_in_class_type6719 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_66_in_actual_generics6790 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_type_list_in_actual_generics6792 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_67_in_actual_generics6794 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_type_in_type_list6858 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_type_list6886 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_type_in_type_list6890 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_type6945 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000004L});
    public static final BitSet FOLLOW_actual_generics_in_type6967 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_assertion_clause_in_assertion7046 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_assertion7055 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F860000L});
    public static final BitSet FOLLOW_assertion_clause_in_assertion7059 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_assertion7076 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_boolean_expression_in_assertion_clause7105 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_expression_in_boolean_expression7127 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_quantifier_in_quantification7167 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_range_expression_in_quantification7174 = new BitSet(new long[]{0x0000000000000000L,0x0000000000180000L});
    public static final BitSet FOLLOW_restriction_in_quantification7182 = new BitSet(new long[]{0x0000000000000000L,0x0000000000180000L});
    public static final BitSet FOLLOW_proposition_in_quantification7194 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_81_in_quantifier7233 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_82_in_quantifier7246 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_variable_range_in_range_expression7284 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_range_expression7294 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_variable_range_in_range_expression7298 = new BitSet(new long[]{0x0000000200000002L});
    public static final BitSet FOLLOW_33_in_range_expression7313 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_83_in_restriction7350 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F860000L});
    public static final BitSet FOLLOW_boolean_expression_in_restriction7354 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_84_in_proposition7388 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F860000L});
    public static final BitSet FOLLOW_boolean_expression_in_proposition7392 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_member_range_in_variable_range7428 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_type_range_in_variable_range7440 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_identifier_list_in_member_range7480 = new BitSet(new long[]{0x0000000000000000L,0x0000000000200000L});
    public static final BitSet FOLLOW_85_in_member_range7482 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F860000L});
    public static final BitSet FOLLOW_expression_in_member_range7486 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_identifier_list_in_type_range7522 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_34_in_type_range7524 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_type_in_type_range7528 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unqualified_call_in_call_chain7588 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_call_chain7597 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F800000L});
    public static final BitSet FOLLOW_unqualified_call_in_call_chain7601 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_IDENTIFIER_in_unqualified_call7642 = new BitSet(new long[]{0x0000040000000002L});
    public static final BitSet FOLLOW_actual_arguments_in_unqualified_call7656 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_42_in_actual_arguments7695 = new BitSet(new long[]{0x40000C00000003B0L,0x000071800F860000L});
    public static final BitSet FOLLOW_expression_list_in_actual_arguments7705 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_43_in_actual_arguments7728 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_expression_in_expression_list7764 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_expression_list7774 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F860000L});
    public static final BitSet FOLLOW_expression_in_expression_list7778 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_62_in_enumerated_set7824 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F860000L});
    public static final BitSet FOLLOW_enumeration_list_in_enumerated_set7828 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_63_in_enumerated_set7830 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_enumeration_element_in_enumeration_list7872 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_35_in_enumeration_list7882 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F860000L});
    public static final BitSet FOLLOW_enumeration_element_in_enumeration_list7886 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_expression_in_enumeration_element7918 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_interval_in_enumeration_element7932 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_integer_interval_in_interval7979 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_character_interval_in_interval7991 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_integer_constant_in_integer_interval8024 = new BitSet(new long[]{0x0000000000000000L,0x0000000000400000L});
    public static final BitSet FOLLOW_86_in_integer_interval8026 = new BitSet(new long[]{0x0000000000000080L,0x0000018000000000L});
    public static final BitSet FOLLOW_integer_constant_in_integer_interval8030 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_character_constant_in_character_interval8072 = new BitSet(new long[]{0x0000000000000000L,0x0000000000400000L});
    public static final BitSet FOLLOW_86_in_character_interval8074 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_character_constant_in_character_interval8078 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_constant_in_constant8104 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_87_in_constant8117 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_88_in_constant8130 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_89_in_constant8154 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_boolean_constant_in_manifest_constant8177 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_character_constant_in_manifest_constant8190 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_integer_constant_in_manifest_constant8203 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_real_constant_in_manifest_constant8216 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_manifest_constant8229 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_enumerated_set_in_manifest_constant8242 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_in_sign8281 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_90_in_boolean_constant8307 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_91_in_boolean_constant8318 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CHARACTER_CONSTANT_in_character_constant8342 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_integer_constant8408 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_INTEGER_in_integer_constant8419 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_real_constant8464 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_REAL_in_real_constant8476 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_92_in_dynamic_diagram8507 = new BitSet(new long[]{0x00800000000000E0L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_diagram8515 = new BitSet(new long[]{0x0080000000000040L});
    public static final BitSet FOLLOW_COMMENT_in_dynamic_diagram8528 = new BitSet(new long[]{0x0080000000000000L});
    public static final BitSet FOLLOW_55_in_dynamic_diagram8537 = new BitSet(new long[]{0x00040000020000A0L,0x00000003C0000000L});
    public static final BitSet FOLLOW_dynamic_block_in_dynamic_diagram8546 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_dynamic_diagram8570 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_dynamic_component_in_dynamic_block8613 = new BitSet(new long[]{0x00040000000000A2L,0x00000003C0000000L});
    public static final BitSet FOLLOW_scenario_description_in_dynamic_component8650 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_object_group_in_dynamic_component8655 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_object_stack_in_dynamic_component8661 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_object_in_dynamic_component8666 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_message_relation_in_dynamic_component8671 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_50_in_scenario_description8699 = new BitSet(new long[]{0x0000000000000810L});
    public static final BitSet FOLLOW_scenario_name_in_scenario_description8701 = new BitSet(new long[]{0x0000000000000040L,0x0000000020000000L});
    public static final BitSet FOLLOW_COMMENT_in_scenario_description8709 = new BitSet(new long[]{0x0000000000000000L,0x0000000020000000L});
    public static final BitSet FOLLOW_93_in_scenario_description8718 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_labelled_actions_in_scenario_description8725 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_scenario_description8732 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_labelled_action_in_labelled_actions8780 = new BitSet(new long[]{0x0000000000000012L});
    public static final BitSet FOLLOW_action_label_in_labelled_action8821 = new BitSet(new long[]{0x0000000000000810L});
    public static final BitSet FOLLOW_action_description_in_labelled_action8825 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_action_label8864 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_action_description8899 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_scenario_name8940 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_94_in_object_group8973 = new BitSet(new long[]{0x0000000000000000L,0x0000000080000000L});
    public static final BitSet FOLLOW_95_in_object_group8998 = new BitSet(new long[]{0x00000000000000A0L});
    public static final BitSet FOLLOW_group_name_in_object_group9004 = new BitSet(new long[]{0x0080000000000042L});
    public static final BitSet FOLLOW_COMMENT_in_object_group9016 = new BitSet(new long[]{0x0080000000000002L});
    public static final BitSet FOLLOW_group_components_in_object_group9031 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_55_in_group_components9082 = new BitSet(new long[]{0x00040000000000A0L,0x00000003C0000000L});
    public static final BitSet FOLLOW_dynamic_block_in_group_components9084 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_25_in_group_components9086 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_96_in_object_stack9131 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_object_name_in_object_stack9138 = new BitSet(new long[]{0x0000000000000042L});
    public static final BitSet FOLLOW_COMMENT_in_object_stack9150 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_97_in_object9198 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_object_name_in_object9205 = new BitSet(new long[]{0x0000000000000042L});
    public static final BitSet FOLLOW_COMMENT_in_object9217 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_caller_in_message_relation9241 = new BitSet(new long[]{0x0000000000000000L,0x0000000400000000L});
    public static final BitSet FOLLOW_98_in_message_relation9243 = new BitSet(new long[]{0x00040000000000A0L,0x00000003C0000000L});
    public static final BitSet FOLLOW_receiver_in_message_relation9245 = new BitSet(new long[]{0x0000000000000012L});
    public static final BitSet FOLLOW_message_label_in_message_relation9248 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_dynamic_ref_in_caller9280 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_dynamic_ref_in_receiver9300 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_ref9326 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_dynamic_ref9329 = new BitSet(new long[]{0x00000000000000A0L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_ref9331 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_IDENTIFIER_in_dynamic_component_name9362 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_dynamic_component_name9365 = new BitSet(new long[]{0x00000000000000A0L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_component_name9367 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_INTEGER_in_dynamic_component_name9376 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_object_name9399 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_object_name9409 = new BitSet(new long[]{0x00000000000000A0L});
    public static final BitSet FOLLOW_extended_id_in_object_name9413 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_extended_id_in_group_name9453 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_message_label9486 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_change_string_marks_in_notational_tuning9510 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_change_concatenator_in_notational_tuning9516 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_change_prefix_in_notational_tuning9521 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_99_in_change_string_marks9536 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_string_marks9538 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_string_marks9540 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_100_in_change_concatenator9574 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_concatenator9576 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_101_in_change_prefix9610 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_prefix9612 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_equivalence_expression_in_expression9638 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_quantification_in_expression9652 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_implies_expression_in_equivalence_expression9674 = new BitSet(new long[]{0x0000000000000002L,0x0000004000000000L});
    public static final BitSet FOLLOW_102_in_equivalence_expression9684 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F800000L});
    public static final BitSet FOLLOW_implies_expression_in_equivalence_expression9688 = new BitSet(new long[]{0x0000000000000002L,0x0000004000000000L});
    public static final BitSet FOLLOW_and_or_xor_expression_in_implies_expression9716 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000002L});
    public static final BitSet FOLLOW_65_in_implies_expression9726 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F800000L});
    public static final BitSet FOLLOW_implies_expression_in_implies_expression9730 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_comparison_expression_in_and_or_xor_expression9757 = new BitSet(new long[]{0x0000000000000002L,0x00000E0000000000L});
    public static final BitSet FOLLOW_and_or_xor_op_in_and_or_xor_expression9769 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F800000L});
    public static final BitSet FOLLOW_comparison_expression_in_and_or_xor_expression9773 = new BitSet(new long[]{0x0000000000000002L,0x00000E0000000000L});
    public static final BitSet FOLLOW_add_sub_expression_in_comparison_expression9801 = new BitSet(new long[]{0x0000000400000002L,0x001FC00000200000L});
    public static final BitSet FOLLOW_comparison_op_in_comparison_expression9813 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F800000L});
    public static final BitSet FOLLOW_add_sub_expression_in_comparison_expression9818 = new BitSet(new long[]{0x0000000400000002L,0x001FC00000200000L});
    public static final BitSet FOLLOW_mul_div_expression_in_add_sub_expression9846 = new BitSet(new long[]{0x0000000000000002L,0x0000018000000000L});
    public static final BitSet FOLLOW_add_sub_op_in_add_sub_expression9858 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F800000L});
    public static final BitSet FOLLOW_mul_div_expression_in_add_sub_expression9862 = new BitSet(new long[]{0x0000000000000002L,0x0000018000000000L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mul_div_expression9890 = new BitSet(new long[]{0x0000000000000002L,0x00E0000000000000L});
    public static final BitSet FOLLOW_mul_div_op_in_mul_div_expression9902 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F800000L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mul_div_expression9906 = new BitSet(new long[]{0x0000000000000002L,0x00E0000000000000L});
    public static final BitSet FOLLOW_lowest_expression_in_mod_pow_expression9935 = new BitSet(new long[]{0x0000000000000002L,0x0100000000001000L});
    public static final BitSet FOLLOW_mod_pow_op_in_mod_pow_expression9947 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F800000L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mod_pow_expression9951 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constant_in_lowest_expression9984 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_lowest_expression9993 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F800000L});
    public static final BitSet FOLLOW_call_chain_in_lowest_expression9997 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unary_in_lowest_expression10047 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F800000L});
    public static final BitSet FOLLOW_lowest_expression_in_lowest_expression10051 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_42_in_lowest_expression10064 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F860000L});
    public static final BitSet FOLLOW_expression_in_lowest_expression10068 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_43_in_lowest_expression10070 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_lowest_expression10080 = new BitSet(new long[]{0x40000400000003B0L,0x000071800F800000L});
    public static final BitSet FOLLOW_call_chain_in_lowest_expression10084 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_call_chain_in_lowest_expression10120 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_103_in_add_sub_op10144 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_104_in_add_sub_op10152 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_103_in_add_sub_op_unary10170 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_104_in_add_sub_op_unary10178 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_105_in_and_or_xor_op10196 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_106_in_and_or_xor_op10203 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_107_in_and_or_xor_op10211 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_other_unary_in_unary10231 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_unary_in_unary10245 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_108_in_other_unary10265 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_109_in_other_unary10273 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_110_in_other_unary10282 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_in_binary10313 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_mul_div_op_in_binary10317 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_comparison_op_in_binary10321 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_mod_pow_op_in_binary10336 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_and_or_xor_op_in_binary10340 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_65_in_binary10355 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_102_in_binary10359 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_111_in_comparison_op10375 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_112_in_comparison_op10383 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_113_in_comparison_op10391 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_114_in_comparison_op10398 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_115_in_comparison_op10405 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_116_in_comparison_op10413 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_85_in_comparison_op10420 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_110_in_comparison_op10427 = new BitSet(new long[]{0x0000000000000000L,0x0000000000200000L});
    public static final BitSet FOLLOW_85_in_comparison_op10429 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_34_in_comparison_op10436 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_117_in_mul_div_op10463 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_118_in_mul_div_op10471 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_119_in_mul_div_op10479 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_120_in_mod_pow_op10512 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_76_in_mod_pow_op10520 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_manifest_textblock10823 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_START_in_manifest_textblock10835 = new BitSet(new long[]{0x0000000000003000L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_MIDDLE_in_manifest_textblock10837 = new BitSet(new long[]{0x0000000000003000L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_END_in_manifest_textblock10840 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constant_in_synpred1_BON9980 = new BitSet(new long[]{0x0000000000000002L});

}