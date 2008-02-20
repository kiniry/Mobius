// $ANTLR 3.0.1 BONTCTreeWalker.g 2008-02-20 14:22:06

  package ie.ucd.bon.parser; 
  
  import java.util.LinkedList;
  
  import ie.ucd.bon.typechecker.Type;


import org.antlr.runtime.*;
import org.antlr.runtime.tree.*;import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
public class BONTCTreeWalker extends AbstractBONTCWalker {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "PROG", "CLASS_CHART", "CLASS_DICTIONARY", "DICTIONARY_ENTRY", "SYSTEM_CHART", "EXPLANATION", "INDEXING", "PART", "DESCRIPTION", "CLUSTER_ENTRIES", "CLUSTER_ENTRY", "SYSTEM_NAME", "INDEX_LIST", "INDEX_CLAUSE", "INDEX_TERM_LIST", "INDEX_STRING", "CLUSTER_CHART", "CLASS_ENTRIES", "CLASS_ENTRY", "CLUSTER_NAME", "QUERY_LIST", "COMMAND_LIST", "CONSTRAINT_LIST", "CLASS_NAME_LIST", "CLASS_NAME", "EVENT_CHART", "EVENT_ENTRIES", "EVENT_ENTRY", "SCENARIO_CHART", "SCENARIO_ENTRIES", "SCENARIO_ENTRY", "CREATION_CHART", "CREATION_ENTRIES", "CREATION_ENTRY", "STATIC_DIAGRAM", "EXTENDED_ID", "STATIC_BLOCK", "STATIC_COMPONENT", "CLUSTER", "CLUSTER_COMPONENTS", "CLASS", "STATIC_RELATION", "INHERITENCE_RELATION", "CLIENT_RELATION", "CLIENT_ENTITIES", "INDIRECTION_ELEMENT", "CLIENT_ENTITY_EXPRESSION", "CLIENT_ENTITY_LIST", "CLIENT_ENTITY", "SUPPLIER_INDIRECTION", "INDIRECTION_FEATURE_PART", "INDIRECTION_FEATURE_LIST", "PARENT_INDIRECTION", "GENERIC_INDIRECTION", "NAMED_INDIRECTION", "INDIRECTION_LIST", "TYPE_MARK", "SHARED_MARK", "CHILD", "PARENT", "CLIENT", "SUPPLIER", "STATIC_REF", "CLUSTER_PREFIX", "STATIC_COMPONENT_NAME", "MULTIPLICITY", "SEMANTIC_LABEL", "CLASS_INTERFACE", "CLASS_INVARIANT", "PARENT_CLASS_LIST", "FEATURES", "FEATURE_CLAUSE", "FEATURE_SPECIFICATIONS", "FEATURE_SPECIFICATION", "CONTRACT_CLAUSE", "CONTRACTING_CONDITIONS", "PRECONDITION", "POSTCONDITION", "SELECTIVE_EXPORT", "FEATURE_NAME_LIST", "FEATURE_NAME", "RENAME_CLAUSE", "RENAMING", "FEATURE_ARGUMENTS", "FEATURE_ARGUMENT", "IDENTIFIER_LIST", "PREFIX", "INFIX", "PREFIX_OPERATOR", "INFIX_OPERATOR", "FORMAL_GENERICS", "FORMAL_GENERIC_LIST", "FORMAL_GENERIC", "FORMAL_GENERIC_NAME", "CLASS_TYPE", "ACTUAL_GENERICS", "TYPE_LIST", "TYPE", "ASSERTION", "ASSERTION_CLAUSE", "BOOLEAN_EXPRESSION", "QUANTIFICATION", "QUANTIFIER", "RANGE_EXPRESSION", "RESTRICTION", "PROPOSITION", "VARIABLE_RANGE", "MEMBER_RANGE", "TYPE_RANGE", "CALL", "CALL_CHAIN", "UNQUALIFIED_CALL", "ACTUAL_ARGUMENTS", "EXPRESSION_LIST", "ENUMERATED_SET", "ENUMERATION_LIST", "ENUMERATION_ELEMENT", "INTERVAL", "INTEGER_INTERVAL", "CHARACTER_INTERVAL", "CONSTANT", "MANIFEST_CONSTANT", "SIGN", "BOOLEAN_CONSTANT", "INTEGER_CONSTANT", "REAL_CONSTANT", "DYNAMIC_DIAGRAM", "DYNAMIC_BLOCK", "DYNAMIC_COMPONENT", "SCENARIO_DESCRIPTION", "LABELLED_ACTIONS", "LABELLED_ACTION", "ACTION_LABEL", "ACTION_DESCRIPTION", "SCENARIO_NAME", "OBJECT_GROUP", "GROUP_COMPONENTS", "OBJECT_STACK", "OBJECT", "MESSAGE_RELATION", "RECEIVER", "DYNAMIC_REF", "DYNAMIC_COMPONENT_NAME", "OBJECT_NAME", "GROUP_NAME", "MESSAGE_LABEL", "NOTATIONAL_TUNING", "CHANGE_STRING_MARKS", "CHANGE_CONCATENATOR", "MANFIEST_STRING", "CHANGE_PREFIX", "LOWEST", "SET_EXPRESSION", "EXPRESSION", "NOT_MEMBER_OF", "INHERITS", "QUERIES", "COMMANDS", "CONSTRAINTS", "HAS_TYPE", "PARSE_ERROR", "MANIFEST_STRING", "IDENTIFIER", "COMMENT", "INTEGER", "CHARACTER_CONSTANT", "REAL", "MOD_POW_OP", "NEWLINE", "MANIFEST_TEXTBLOCK_START", "MANIFEST_TEXTBLOCK_MIDDLE", "MANIFEST_TEXTBLOCK_END", "LINE_COMMENT", "COMMENT_START", "DIGIT", "ALPHA", "ALPHANUMERIC_OR_UNDERSCORE", "ALPHANUMERIC", "UNDERSCORE", "LOWER", "UPPER", "WHITESPACE", "'dictionary'", "'end'", "'class'", "'cluster'", "'system_chart'", "'explanation'", "'indexing'", "'part'", "'description'", "';'", "':'", "','", "'cluster_chart'", "'class_chart'", "'inherit'", "'query'", "'command'", "'constraint'", "'event_chart'", "'incoming'", "'outgoing'", "'event'", "'involves'", "'scenario_chart'", "'scenario'", "'creation_chart'", "'creator'", "'creates'", "'static_diagram'", "'component'", "'reused'", "'root'", "'deferred'", "'effective'", "'persistent'", "'interfaced'", "'{'", "'}'", "'client'", "'('", "')'", "'->'", "'['", "']'", "'...'", "':{'", "'.'", "'invariant'", "'feature'", "'redefined'", "'require'", "'ensure'", "'^'", "'prefix'", "'\"'", "'infix'", "'for_all'", "'exists'", "'such_that'", "'it_holds'", "'member_of'", "'..'", "'Current'", "'Void'", "'true'", "'false'", "'dynamic_diagram'", "'action'", "'nameless'", "'object_group'", "'object_stack'", "'object'", "'calls'", "'string_marks'", "'concatenator'", "'keyword_prefix'", "'<->'", "'+'", "'-'", "'and'", "'or'", "'xor'", "'delta'", "'old'", "'not'", "'<'", "'>'", "'<='", "'>='", "'='", "'/='", "'*'", "'/'", "'\\'", "'//'"
    };
    public static final int ENUMERATED_SET=118;
    public static final int SIGN=126;
    public static final int CREATION_ENTRIES=36;
    public static final int CLASS_TYPE=98;
    public static final int PREFIX=90;
    public static final int UNQUALIFIED_CALL=115;
    public static final int SUPPLIER=65;
    public static final int ENUMERATION_LIST=119;
    public static final int STATIC_RELATION=45;
    public static final int INDEX_LIST=16;
    public static final int FEATURE_ARGUMENTS=87;
    public static final int SCENARIO_DESCRIPTION=133;
    public static final int EOF=-1;
    public static final int SET_EXPRESSION=156;
    public static final int INDEXING=10;
    public static final int CONTRACTING_CONDITIONS=79;
    public static final int TYPE=101;
    public static final int COMMAND_LIST=25;
    public static final int MULTIPLICITY=69;
    public static final int OBJECT_NAME=147;
    public static final int CALL_CHAIN=114;
    public static final int DESCRIPTION=12;
    public static final int MEMBER_RANGE=111;
    public static final int COMMANDS=161;
    public static final int INHERITS=159;
    public static final int MANIFEST_TEXTBLOCK_END=175;
    public static final int SCENARIO_NAME=138;
    public static final int PARSE_ERROR=164;
    public static final int ALPHANUMERIC_OR_UNDERSCORE=180;
    public static final int FEATURE_SPECIFICATIONS=76;
    public static final int BOOLEAN_CONSTANT=127;
    public static final int DYNAMIC_DIAGRAM=130;
    public static final int INFIX=91;
    public static final int INDIRECTION_FEATURE_LIST=55;
    public static final int SCENARIO_ENTRIES=33;
    public static final int RENAME_CLAUSE=85;
    public static final int FEATURE_CLAUSE=75;
    public static final int PARENT_CLASS_LIST=73;
    public static final int COMMENT=167;
    public static final int VARIABLE_RANGE=110;
    public static final int CHANGE_STRING_MARKS=151;
    public static final int ENUMERATION_ELEMENT=120;
    public static final int CHILD=62;
    public static final int RENAMING=86;
    public static final int OBJECT_STACK=141;
    public static final int CHARACTER_INTERVAL=123;
    public static final int LABELLED_ACTIONS=134;
    public static final int CLIENT=64;
    public static final int LINE_COMMENT=176;
    public static final int FORMAL_GENERIC_NAME=97;
    public static final int LABELLED_ACTION=135;
    public static final int HAS_TYPE=163;
    public static final int PARENT_INDIRECTION=56;
    public static final int CLASS_ENTRIES=21;
    public static final int WHITESPACE=185;
    public static final int MESSAGE_RELATION=143;
    public static final int UNDERSCORE=182;
    public static final int INHERITENCE_RELATION=46;
    public static final int CLASS_NAME_LIST=27;
    public static final int CLUSTER_ENTRIES=13;
    public static final int MOD_POW_OP=171;
    public static final int IDENTIFIER_LIST=89;
    public static final int LOWEST=155;
    public static final int CONSTRAINT_LIST=26;
    public static final int CLIENT_ENTITY_LIST=51;
    public static final int EVENT_ENTRIES=30;
    public static final int INTEGER_INTERVAL=122;
    public static final int CLUSTER_CHART=20;
    public static final int CONTRACT_CLAUSE=78;
    public static final int ALPHA=179;
    public static final int CLUSTER_PREFIX=67;
    public static final int REAL=170;
    public static final int RANGE_EXPRESSION=107;
    public static final int FEATURE_NAME=84;
    public static final int RECEIVER=144;
    public static final int CLIENT_ENTITIES=48;
    public static final int DYNAMIC_REF=145;
    public static final int QUERIES=160;
    public static final int CLASS_INTERFACE=71;
    public static final int FORMAL_GENERIC=96;
    public static final int EXTENDED_ID=39;
    public static final int CLUSTER_ENTRY=14;
    public static final int SUPPLIER_INDIRECTION=53;
    public static final int CONSTANT=124;
    public static final int DICTIONARY_ENTRY=7;
    public static final int CALL=113;
    public static final int LOWER=183;
    public static final int DYNAMIC_COMPONENT_NAME=146;
    public static final int PREFIX_OPERATOR=92;
    public static final int STATIC_BLOCK=40;
    public static final int UPPER=184;
    public static final int SHARED_MARK=61;
    public static final int CONSTRAINTS=162;
    public static final int CLASS=44;
    public static final int QUANTIFICATION=105;
    public static final int ACTUAL_ARGUMENTS=116;
    public static final int CHARACTER_CONSTANT=169;
    public static final int PART=11;
    public static final int INDEX_CLAUSE=17;
    public static final int FORMAL_GENERIC_LIST=95;
    public static final int ASSERTION=102;
    public static final int CLUSTER_COMPONENTS=43;
    public static final int NOT_MEMBER_OF=158;
    public static final int SYSTEM_CHART=8;
    public static final int INFIX_OPERATOR=93;
    public static final int CLUSTER_NAME=23;
    public static final int TYPE_LIST=100;
    public static final int DYNAMIC_COMPONENT=132;
    public static final int CLASS_ENTRY=22;
    public static final int SYSTEM_NAME=15;
    public static final int BOOLEAN_EXPRESSION=104;
    public static final int REAL_CONSTANT=129;
    public static final int COMMENT_START=177;
    public static final int INTERVAL=121;
    public static final int INDIRECTION_ELEMENT=49;
    public static final int CLIENT_RELATION=47;
    public static final int TYPE_RANGE=112;
    public static final int PARENT=63;
    public static final int PROG=4;
    public static final int CREATION_ENTRY=37;
    public static final int STATIC_DIAGRAM=38;
    public static final int NOTATIONAL_TUNING=150;
    public static final int INDEX_TERM_LIST=18;
    public static final int EXPRESSION_LIST=117;
    public static final int OBJECT=142;
    public static final int IDENTIFIER=166;
    public static final int FEATURE_NAME_LIST=83;
    public static final int EVENT_CHART=29;
    public static final int CHANGE_CONCATENATOR=152;
    public static final int ALPHANUMERIC=181;
    public static final int MANIFEST_TEXTBLOCK_START=173;
    public static final int STATIC_REF=66;
    public static final int GROUP_COMPONENTS=140;
    public static final int MANFIEST_STRING=153;
    public static final int SEMANTIC_LABEL=70;
    public static final int CLASS_CHART=5;
    public static final int INDIRECTION_FEATURE_PART=54;
    public static final int FEATURE_ARGUMENT=88;
    public static final int CLASS_DICTIONARY=6;
    public static final int OBJECT_GROUP=139;
    public static final int DIGIT=178;
    public static final int INTEGER_CONSTANT=128;
    public static final int SCENARIO_CHART=32;
    public static final int EXPRESSION=157;
    public static final int CREATION_CHART=35;
    public static final int DYNAMIC_BLOCK=131;
    public static final int INTEGER=168;
    public static final int CLIENT_ENTITY=52;
    public static final int ACTUAL_GENERICS=99;
    public static final int QUERY_LIST=24;
    public static final int CLASS_NAME=28;
    public static final int FEATURES=74;
    public static final int EXPLANATION=9;
    public static final int MANIFEST_CONSTANT=125;
    public static final int CHANGE_PREFIX=154;
    public static final int CLASS_INVARIANT=72;
    public static final int CLIENT_ENTITY_EXPRESSION=50;
    public static final int GROUP_NAME=148;
    public static final int GENERIC_INDIRECTION=57;
    public static final int FEATURE_SPECIFICATION=77;
    public static final int SELECTIVE_EXPORT=82;
    public static final int INDEX_STRING=19;
    public static final int ACTION_DESCRIPTION=137;
    public static final int TYPE_MARK=60;
    public static final int RESTRICTION=108;
    public static final int MANIFEST_STRING=165;
    public static final int PROPOSITION=109;
    public static final int POSTCONDITION=81;
    public static final int STATIC_COMPONENT_NAME=68;
    public static final int NEWLINE=172;
    public static final int MESSAGE_LABEL=149;
    public static final int PRECONDITION=80;
    public static final int SCENARIO_ENTRY=34;
    public static final int ASSERTION_CLAUSE=103;
    public static final int NAMED_INDIRECTION=58;
    public static final int CLUSTER=42;
    public static final int MANIFEST_TEXTBLOCK_MIDDLE=174;
    public static final int FORMAL_GENERICS=94;
    public static final int QUANTIFIER=106;
    public static final int EVENT_ENTRY=31;
    public static final int INDIRECTION_LIST=59;
    public static final int STATIC_COMPONENT=41;
    public static final int ACTION_LABEL=136;

        public BONTCTreeWalker(TreeNodeStream input) {
            super(input);
        }
        

    public String[] getTokenNames() { return tokenNames; }
    public String getGrammarFileName() { return "BONTCTreeWalker.g"; }



    // $ANTLR start prog
    // BONTCTreeWalker.g:22:1: prog : ( ^( PROG ( indexing )? bon_specification ) | ^( PROG PARSE_ERROR ) );
    public final void prog() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:28:7: ( ^( PROG ( indexing )? bon_specification ) | ^( PROG PARSE_ERROR ) )
            int alt2=2;
            int LA2_0 = input.LA(1);

            if ( (LA2_0==PROG) ) {
                int LA2_1 = input.LA(2);

                if ( (LA2_1==DOWN) ) {
                    int LA2_2 = input.LA(3);

                    if ( (LA2_2==PARSE_ERROR) ) {
                        alt2=2;
                    }
                    else if ( ((LA2_2>=CLASS_CHART && LA2_2<=CLASS_DICTIONARY)||LA2_2==SYSTEM_CHART||LA2_2==INDEXING||LA2_2==CLUSTER_CHART||LA2_2==EVENT_CHART||LA2_2==SCENARIO_CHART||LA2_2==CREATION_CHART||LA2_2==STATIC_DIAGRAM||LA2_2==DYNAMIC_DIAGRAM||LA2_2==NOTATIONAL_TUNING) ) {
                        alt2=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("22:1: prog : ( ^( PROG ( indexing )? bon_specification ) | ^( PROG PARSE_ERROR ) );", 2, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("22:1: prog : ( ^( PROG ( indexing )? bon_specification ) | ^( PROG PARSE_ERROR ) );", 2, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("22:1: prog : ( ^( PROG ( indexing )? bon_specification ) | ^( PROG PARSE_ERROR ) );", 2, 0, input);

                throw nvae;
            }
            switch (alt2) {
                case 1 :
                    // BONTCTreeWalker.g:28:10: ^( PROG ( indexing )? bon_specification )
                    {
                    match(input,PROG,FOLLOW_PROG_in_prog56); 

                    match(input, Token.DOWN, null); 
                    // BONTCTreeWalker.g:28:18: ( indexing )?
                    int alt1=2;
                    int LA1_0 = input.LA(1);

                    if ( (LA1_0==INDEXING) ) {
                        alt1=1;
                    }
                    switch (alt1) {
                        case 1 :
                            // BONTCTreeWalker.g:28:18: indexing
                            {
                            pushFollow(FOLLOW_indexing_in_prog58);
                            indexing();
                            _fsp--;


                            }
                            break;

                    }

                    pushFollow(FOLLOW_bon_specification_in_prog61);
                    bon_specification();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:30:10: ^( PROG PARSE_ERROR )
                    {
                    match(input,PROG,FOLLOW_PROG_in_prog86); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_prog88); 

                    match(input, Token.UP, null); 

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
    // $ANTLR end prog


    // $ANTLR start bon_specification
    // BONTCTreeWalker.g:33:1: bon_specification : ( specification_element )+ ;
    public final void bon_specification() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:37:20: ( ( specification_element )+ )
            // BONTCTreeWalker.g:37:23: ( specification_element )+
            {
            // BONTCTreeWalker.g:37:23: ( specification_element )+
            int cnt3=0;
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( ((LA3_0>=CLASS_CHART && LA3_0<=CLASS_DICTIONARY)||LA3_0==SYSTEM_CHART||LA3_0==CLUSTER_CHART||LA3_0==EVENT_CHART||LA3_0==SCENARIO_CHART||LA3_0==CREATION_CHART||LA3_0==STATIC_DIAGRAM||LA3_0==DYNAMIC_DIAGRAM||LA3_0==NOTATIONAL_TUNING) ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // BONTCTreeWalker.g:37:24: specification_element
            	    {
            	    pushFollow(FOLLOW_specification_element_in_bon_specification111);
            	    specification_element();
            	    _fsp--;


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
    // $ANTLR end bon_specification


    // $ANTLR start specification_element
    // BONTCTreeWalker.g:40:1: specification_element : ( informal_chart | class_dictionary | static_diagram | dynamic_diagram | notational_tuning );
    public final void specification_element() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:40:24: ( informal_chart | class_dictionary | static_diagram | dynamic_diagram | notational_tuning )
            int alt4=5;
            switch ( input.LA(1) ) {
            case CLASS_CHART:
            case SYSTEM_CHART:
            case CLUSTER_CHART:
            case EVENT_CHART:
            case SCENARIO_CHART:
            case CREATION_CHART:
                {
                alt4=1;
                }
                break;
            case CLASS_DICTIONARY:
                {
                alt4=2;
                }
                break;
            case STATIC_DIAGRAM:
                {
                alt4=3;
                }
                break;
            case DYNAMIC_DIAGRAM:
                {
                alt4=4;
                }
                break;
            case NOTATIONAL_TUNING:
                {
                alt4=5;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("40:1: specification_element : ( informal_chart | class_dictionary | static_diagram | dynamic_diagram | notational_tuning );", 4, 0, input);

                throw nvae;
            }

            switch (alt4) {
                case 1 :
                    // BONTCTreeWalker.g:40:29: informal_chart
                    {
                    pushFollow(FOLLOW_informal_chart_in_specification_element148);
                    informal_chart();
                    _fsp--;


                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:41:29: class_dictionary
                    {
                    pushFollow(FOLLOW_class_dictionary_in_specification_element178);
                    class_dictionary();
                    _fsp--;


                    }
                    break;
                case 3 :
                    // BONTCTreeWalker.g:42:29: static_diagram
                    {
                    pushFollow(FOLLOW_static_diagram_in_specification_element208);
                    static_diagram();
                    _fsp--;


                    }
                    break;
                case 4 :
                    // BONTCTreeWalker.g:43:29: dynamic_diagram
                    {
                    pushFollow(FOLLOW_dynamic_diagram_in_specification_element238);
                    dynamic_diagram();
                    _fsp--;


                    }
                    break;
                case 5 :
                    // BONTCTreeWalker.g:44:29: notational_tuning
                    {
                    pushFollow(FOLLOW_notational_tuning_in_specification_element268);
                    notational_tuning();
                    _fsp--;


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
    // $ANTLR end specification_element


    // $ANTLR start informal_chart
    // BONTCTreeWalker.g:47:1: informal_chart : ( system_chart | cluster_chart | class_chart | event_chart | scenario_chart | creation_chart );
    public final void informal_chart() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:51:17: ( system_chart | cluster_chart | class_chart | event_chart | scenario_chart | creation_chart )
            int alt5=6;
            switch ( input.LA(1) ) {
            case SYSTEM_CHART:
                {
                alt5=1;
                }
                break;
            case CLUSTER_CHART:
                {
                alt5=2;
                }
                break;
            case CLASS_CHART:
                {
                alt5=3;
                }
                break;
            case EVENT_CHART:
                {
                alt5=4;
                }
                break;
            case SCENARIO_CHART:
                {
                alt5=5;
                }
                break;
            case CREATION_CHART:
                {
                alt5=6;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("47:1: informal_chart : ( system_chart | cluster_chart | class_chart | event_chart | scenario_chart | creation_chart );", 5, 0, input);

                throw nvae;
            }

            switch (alt5) {
                case 1 :
                    // BONTCTreeWalker.g:51:22: system_chart
                    {
                    pushFollow(FOLLOW_system_chart_in_informal_chart307);
                    system_chart();
                    _fsp--;


                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:52:22: cluster_chart
                    {
                    pushFollow(FOLLOW_cluster_chart_in_informal_chart330);
                    cluster_chart();
                    _fsp--;


                    }
                    break;
                case 3 :
                    // BONTCTreeWalker.g:53:22: class_chart
                    {
                    pushFollow(FOLLOW_class_chart_in_informal_chart353);
                    class_chart();
                    _fsp--;


                    }
                    break;
                case 4 :
                    // BONTCTreeWalker.g:54:22: event_chart
                    {
                    pushFollow(FOLLOW_event_chart_in_informal_chart376);
                    event_chart();
                    _fsp--;


                    }
                    break;
                case 5 :
                    // BONTCTreeWalker.g:55:22: scenario_chart
                    {
                    pushFollow(FOLLOW_scenario_chart_in_informal_chart399);
                    scenario_chart();
                    _fsp--;


                    }
                    break;
                case 6 :
                    // BONTCTreeWalker.g:56:22: creation_chart
                    {
                    pushFollow(FOLLOW_creation_chart_in_informal_chart422);
                    creation_chart();
                    _fsp--;


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
    // $ANTLR end informal_chart


    // $ANTLR start class_dictionary
    // BONTCTreeWalker.g:59:1: class_dictionary : ( ^( CLASS_DICTIONARY system_name ( dictionary_entry )+ ) | ^( CLASS_DICTIONARY PARSE_ERROR ) );
    public final void class_dictionary() throws RecognitionException {
        system_name_return system_name1 = null;


        try {
            // BONTCTreeWalker.g:59:19: ( ^( CLASS_DICTIONARY system_name ( dictionary_entry )+ ) | ^( CLASS_DICTIONARY PARSE_ERROR ) )
            int alt7=2;
            int LA7_0 = input.LA(1);

            if ( (LA7_0==CLASS_DICTIONARY) ) {
                int LA7_1 = input.LA(2);

                if ( (LA7_1==DOWN) ) {
                    int LA7_2 = input.LA(3);

                    if ( (LA7_2==PARSE_ERROR) ) {
                        alt7=2;
                    }
                    else if ( (LA7_2==SYSTEM_NAME) ) {
                        alt7=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("59:1: class_dictionary : ( ^( CLASS_DICTIONARY system_name ( dictionary_entry )+ ) | ^( CLASS_DICTIONARY PARSE_ERROR ) );", 7, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("59:1: class_dictionary : ( ^( CLASS_DICTIONARY system_name ( dictionary_entry )+ ) | ^( CLASS_DICTIONARY PARSE_ERROR ) );", 7, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("59:1: class_dictionary : ( ^( CLASS_DICTIONARY system_name ( dictionary_entry )+ ) | ^( CLASS_DICTIONARY PARSE_ERROR ) );", 7, 0, input);

                throw nvae;
            }
            switch (alt7) {
                case 1 :
                    // BONTCTreeWalker.g:59:20: ^( CLASS_DICTIONARY system_name ( dictionary_entry )+ )
                    {
                    match(input,CLASS_DICTIONARY,FOLLOW_CLASS_DICTIONARY_in_class_dictionary473); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_system_name_in_class_dictionary475);
                    system_name1=system_name();
                    _fsp--;

                     getITC().checkSystemName(input.getTokenStream().toString(
                      input.getTreeAdaptor().getTokenStartIndex(system_name1.start),
                      input.getTreeAdaptor().getTokenStopIndex(system_name1.start)),getSLoc(((CommonTree)system_name1.start).token)); 
                    // BONTCTreeWalker.g:62:22: ( dictionary_entry )+
                    int cnt6=0;
                    loop6:
                    do {
                        int alt6=2;
                        int LA6_0 = input.LA(1);

                        if ( (LA6_0==DICTIONARY_ENTRY) ) {
                            alt6=1;
                        }


                        switch (alt6) {
                    	case 1 :
                    	    // BONTCTreeWalker.g:62:23: dictionary_entry
                    	    {
                    	    pushFollow(FOLLOW_dictionary_entry_in_class_dictionary523);
                    	    dictionary_entry();
                    	    _fsp--;


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


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:65:20: ^( CLASS_DICTIONARY PARSE_ERROR )
                    {
                    match(input,CLASS_DICTIONARY,FOLLOW_CLASS_DICTIONARY_in_class_dictionary592); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_class_dictionary595); 

                    match(input, Token.UP, null); 

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
    // $ANTLR end class_dictionary


    // $ANTLR start dictionary_entry
    // BONTCTreeWalker.g:68:1: dictionary_entry : ^( DICTIONARY_ENTRY class_name cluster_name description ) ;
    public final void dictionary_entry() throws RecognitionException {
        class_name_return class_name2 = null;

        cluster_name_return cluster_name3 = null;


        try {
            // BONTCTreeWalker.g:68:19: ( ^( DICTIONARY_ENTRY class_name cluster_name description ) )
            // BONTCTreeWalker.g:68:20: ^( DICTIONARY_ENTRY class_name cluster_name description )
            {
            match(input,DICTIONARY_ENTRY,FOLLOW_DICTIONARY_ENTRY_in_dictionary_entry650); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_class_name_in_dictionary_entry652);
            class_name2=class_name();
            _fsp--;

             getITC().checkValidClassType(input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(class_name2.start),
              input.getTreeAdaptor().getTokenStopIndex(class_name2.start)), getSLoc(((CommonTree)class_name2.start).token)); 
            pushFollow(FOLLOW_cluster_name_in_dictionary_entry698);
            cluster_name3=cluster_name();
            _fsp--;

             getITC().checkValidClusterType(input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(cluster_name3.start),
              input.getTreeAdaptor().getTokenStopIndex(cluster_name3.start)), getSLoc(((CommonTree)cluster_name3.start).token)); 
             getITC().checkClassIsInCluster(input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(class_name2.start),
              input.getTreeAdaptor().getTokenStopIndex(class_name2.start)), input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(cluster_name3.start),
              input.getTreeAdaptor().getTokenStopIndex(cluster_name3.start)), getSLoc(((CommonTree)class_name2.start).token)); 
            pushFollow(FOLLOW_description_in_dictionary_entry789);
            description();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end dictionary_entry


    // $ANTLR start system_chart
    // BONTCTreeWalker.g:78:1: system_chart : ^( SYSTEM_CHART system_name ( indexing )? ( explanation )? ( part )? ( cluster_entries )? ) ;
    public final void system_chart() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:80:15: ( ^( SYSTEM_CHART system_name ( indexing )? ( explanation )? ( part )? ( cluster_entries )? ) )
            // BONTCTreeWalker.g:80:16: ^( SYSTEM_CHART system_name ( indexing )? ( explanation )? ( part )? ( cluster_entries )? )
            {
            match(input,SYSTEM_CHART,FOLLOW_SYSTEM_CHART_in_system_chart861); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_system_name_in_system_chart863);
            system_name();
            _fsp--;

            // BONTCTreeWalker.g:82:18: ( indexing )?
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( (LA8_0==INDEXING) ) {
                alt8=1;
            }
            switch (alt8) {
                case 1 :
                    // BONTCTreeWalker.g:82:19: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_system_chart883);
                    indexing();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:83:18: ( explanation )?
            int alt9=2;
            int LA9_0 = input.LA(1);

            if ( (LA9_0==EXPLANATION) ) {
                alt9=1;
            }
            switch (alt9) {
                case 1 :
                    // BONTCTreeWalker.g:83:19: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_system_chart905);
                    explanation();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:84:18: ( part )?
            int alt10=2;
            int LA10_0 = input.LA(1);

            if ( (LA10_0==PART) ) {
                alt10=1;
            }
            switch (alt10) {
                case 1 :
                    // BONTCTreeWalker.g:84:19: part
                    {
                    pushFollow(FOLLOW_part_in_system_chart928);
                    part();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:85:18: ( cluster_entries )?
            int alt11=2;
            int LA11_0 = input.LA(1);

            if ( (LA11_0==CLUSTER_ENTRIES) ) {
                alt11=1;
            }
            switch (alt11) {
                case 1 :
                    // BONTCTreeWalker.g:85:19: cluster_entries
                    {
                    pushFollow(FOLLOW_cluster_entries_in_system_chart951);
                    cluster_entries();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end system_chart


    // $ANTLR start explanation
    // BONTCTreeWalker.g:89:1: explanation : ( ^( EXPLANATION manifest_textblock ) | ^( EXPLANATION PARSE_ERROR ) );
    public final void explanation() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:89:14: ( ^( EXPLANATION manifest_textblock ) | ^( EXPLANATION PARSE_ERROR ) )
            int alt12=2;
            int LA12_0 = input.LA(1);

            if ( (LA12_0==EXPLANATION) ) {
                int LA12_1 = input.LA(2);

                if ( (LA12_1==DOWN) ) {
                    int LA12_2 = input.LA(3);

                    if ( (LA12_2==PARSE_ERROR) ) {
                        alt12=2;
                    }
                    else if ( (LA12_2==MANIFEST_STRING||LA12_2==MANIFEST_TEXTBLOCK_START) ) {
                        alt12=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("89:1: explanation : ( ^( EXPLANATION manifest_textblock ) | ^( EXPLANATION PARSE_ERROR ) );", 12, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("89:1: explanation : ( ^( EXPLANATION manifest_textblock ) | ^( EXPLANATION PARSE_ERROR ) );", 12, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("89:1: explanation : ( ^( EXPLANATION manifest_textblock ) | ^( EXPLANATION PARSE_ERROR ) );", 12, 0, input);

                throw nvae;
            }
            switch (alt12) {
                case 1 :
                    // BONTCTreeWalker.g:89:15: ^( EXPLANATION manifest_textblock )
                    {
                    match(input,EXPLANATION,FOLLOW_EXPLANATION_in_explanation1013); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_manifest_textblock_in_explanation1015);
                    manifest_textblock();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:93:15: ^( EXPLANATION PARSE_ERROR )
                    {
                    match(input,EXPLANATION,FOLLOW_EXPLANATION_in_explanation1066); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_explanation1068); 

                    match(input, Token.UP, null); 

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
    // $ANTLR end explanation


    // $ANTLR start indexing
    // BONTCTreeWalker.g:96:1: indexing : ( ^( INDEXING index_list ) | ^( INDEXING PARSE_ERROR ) );
    public final void indexing() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:96:11: ( ^( INDEXING index_list ) | ^( INDEXING PARSE_ERROR ) )
            int alt13=2;
            int LA13_0 = input.LA(1);

            if ( (LA13_0==INDEXING) ) {
                int LA13_1 = input.LA(2);

                if ( (LA13_1==DOWN) ) {
                    int LA13_2 = input.LA(3);

                    if ( (LA13_2==PARSE_ERROR) ) {
                        alt13=2;
                    }
                    else if ( (LA13_2==INDEX_LIST) ) {
                        alt13=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("96:1: indexing : ( ^( INDEXING index_list ) | ^( INDEXING PARSE_ERROR ) );", 13, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("96:1: indexing : ( ^( INDEXING index_list ) | ^( INDEXING PARSE_ERROR ) );", 13, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("96:1: indexing : ( ^( INDEXING index_list ) | ^( INDEXING PARSE_ERROR ) );", 13, 0, input);

                throw nvae;
            }
            switch (alt13) {
                case 1 :
                    // BONTCTreeWalker.g:96:12: ^( INDEXING index_list )
                    {
                    match(input,INDEXING,FOLLOW_INDEXING_in_indexing1107); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_index_list_in_indexing1109);
                    index_list();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:100:12: ^( INDEXING PARSE_ERROR )
                    {
                    match(input,INDEXING,FOLLOW_INDEXING_in_indexing1151); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_indexing1153); 

                    match(input, Token.UP, null); 

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
    // $ANTLR end indexing


    // $ANTLR start part
    // BONTCTreeWalker.g:103:1: part : ( ^( PART MANIFEST_STRING ) | ^( PART PARSE_ERROR ) );
    public final void part() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:103:7: ( ^( PART MANIFEST_STRING ) | ^( PART PARSE_ERROR ) )
            int alt14=2;
            int LA14_0 = input.LA(1);

            if ( (LA14_0==PART) ) {
                int LA14_1 = input.LA(2);

                if ( (LA14_1==DOWN) ) {
                    int LA14_2 = input.LA(3);

                    if ( (LA14_2==MANIFEST_STRING) ) {
                        alt14=1;
                    }
                    else if ( (LA14_2==PARSE_ERROR) ) {
                        alt14=2;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("103:1: part : ( ^( PART MANIFEST_STRING ) | ^( PART PARSE_ERROR ) );", 14, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("103:1: part : ( ^( PART MANIFEST_STRING ) | ^( PART PARSE_ERROR ) );", 14, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("103:1: part : ( ^( PART MANIFEST_STRING ) | ^( PART PARSE_ERROR ) );", 14, 0, input);

                throw nvae;
            }
            switch (alt14) {
                case 1 :
                    // BONTCTreeWalker.g:103:8: ^( PART MANIFEST_STRING )
                    {
                    match(input,PART,FOLLOW_PART_in_part1185); 

                    match(input, Token.DOWN, null); 
                    match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_part1187); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:107:8: ^( PART PARSE_ERROR )
                    {
                    match(input,PART,FOLLOW_PART_in_part1217); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_part1219); 

                    match(input, Token.UP, null); 

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
    // $ANTLR end part


    // $ANTLR start description
    // BONTCTreeWalker.g:110:1: description : ^( DESCRIPTION manifest_textblock ) ;
    public final void description() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:110:14: ( ^( DESCRIPTION manifest_textblock ) )
            // BONTCTreeWalker.g:110:15: ^( DESCRIPTION manifest_textblock )
            {
            match(input,DESCRIPTION,FOLLOW_DESCRIPTION_in_description1254); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_manifest_textblock_in_description1256);
            manifest_textblock();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end description


    // $ANTLR start cluster_entries
    // BONTCTreeWalker.g:115:1: cluster_entries : ^( CLUSTER_ENTRIES ( cluster_entry )+ ) ;
    public final void cluster_entries() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:115:18: ( ^( CLUSTER_ENTRIES ( cluster_entry )+ ) )
            // BONTCTreeWalker.g:115:19: ^( CLUSTER_ENTRIES ( cluster_entry )+ )
            {
            match(input,CLUSTER_ENTRIES,FOLLOW_CLUSTER_ENTRIES_in_cluster_entries1317); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:116:37: ( cluster_entry )+
            int cnt15=0;
            loop15:
            do {
                int alt15=2;
                int LA15_0 = input.LA(1);

                if ( (LA15_0==CLUSTER_ENTRY) ) {
                    alt15=1;
                }


                switch (alt15) {
            	case 1 :
            	    // BONTCTreeWalker.g:116:38: cluster_entry
            	    {
            	    pushFollow(FOLLOW_cluster_entry_in_cluster_entries1320);
            	    cluster_entry();
            	    _fsp--;


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


            match(input, Token.UP, null); 

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
    // $ANTLR end cluster_entries


    // $ANTLR start cluster_entry
    // BONTCTreeWalker.g:120:1: cluster_entry : ^( CLUSTER_ENTRY cluster_name description ) ;
    public final void cluster_entry() throws RecognitionException {
        cluster_name_return cluster_name4 = null;


        try {
            // BONTCTreeWalker.g:120:16: ( ^( CLUSTER_ENTRY cluster_name description ) )
            // BONTCTreeWalker.g:120:17: ^( CLUSTER_ENTRY cluster_name description )
            {
            match(input,CLUSTER_ENTRY,FOLLOW_CLUSTER_ENTRY_in_cluster_entry1407); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_cluster_name_in_cluster_entry1409);
            cluster_name4=cluster_name();
            _fsp--;

            pushFollow(FOLLOW_description_in_cluster_entry1411);
            description();
            _fsp--;

             getITC().checkValidClusterType(input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(cluster_name4.start),
              input.getTreeAdaptor().getTokenStopIndex(cluster_name4.start)),getSLoc(((CommonTree)cluster_name4.start).token)); 

            match(input, Token.UP, null); 

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
    // $ANTLR end cluster_entry

    public static class system_name_return extends TreeRuleReturnScope {
    };

    // $ANTLR start system_name
    // BONTCTreeWalker.g:126:1: system_name : ^( SYSTEM_NAME IDENTIFIER ) ;
    public final system_name_return system_name() throws RecognitionException {
        system_name_return retval = new system_name_return();
        retval.start = input.LT(1);

        try {
            // BONTCTreeWalker.g:126:14: ( ^( SYSTEM_NAME IDENTIFIER ) )
            // BONTCTreeWalker.g:126:15: ^( SYSTEM_NAME IDENTIFIER )
            {
            match(input,SYSTEM_NAME,FOLLOW_SYSTEM_NAME_in_system_name1508); 

            match(input, Token.DOWN, null); 
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_system_name1510); 

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end system_name


    // $ANTLR start index_list
    // BONTCTreeWalker.g:131:1: index_list : ^( INDEX_LIST ( index_clause )+ ) ;
    public final void index_list() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:133:13: ( ^( INDEX_LIST ( index_clause )+ ) )
            // BONTCTreeWalker.g:133:14: ^( INDEX_LIST ( index_clause )+ )
            {
            match(input,INDEX_LIST,FOLLOW_INDEX_LIST_in_index_list1569); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:134:27: ( index_clause )+
            int cnt16=0;
            loop16:
            do {
                int alt16=2;
                int LA16_0 = input.LA(1);

                if ( (LA16_0==INDEX_CLAUSE) ) {
                    alt16=1;
                }


                switch (alt16) {
            	case 1 :
            	    // BONTCTreeWalker.g:134:28: index_clause
            	    {
            	    pushFollow(FOLLOW_index_clause_in_index_list1572);
            	    index_clause();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt16 >= 1 ) break loop16;
                        EarlyExitException eee =
                            new EarlyExitException(16, input);
                        throw eee;
                }
                cnt16++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end index_list


    // $ANTLR start index_clause
    // BONTCTreeWalker.g:138:1: index_clause : ( ^( INDEX_CLAUSE IDENTIFIER index_term_list ) | ^( INDEX_CLAUSE PARSE_ERROR ) );
    public final void index_clause() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:138:15: ( ^( INDEX_CLAUSE IDENTIFIER index_term_list ) | ^( INDEX_CLAUSE PARSE_ERROR ) )
            int alt17=2;
            int LA17_0 = input.LA(1);

            if ( (LA17_0==INDEX_CLAUSE) ) {
                int LA17_1 = input.LA(2);

                if ( (LA17_1==DOWN) ) {
                    int LA17_2 = input.LA(3);

                    if ( (LA17_2==IDENTIFIER) ) {
                        alt17=1;
                    }
                    else if ( (LA17_2==PARSE_ERROR) ) {
                        alt17=2;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("138:1: index_clause : ( ^( INDEX_CLAUSE IDENTIFIER index_term_list ) | ^( INDEX_CLAUSE PARSE_ERROR ) );", 17, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("138:1: index_clause : ( ^( INDEX_CLAUSE IDENTIFIER index_term_list ) | ^( INDEX_CLAUSE PARSE_ERROR ) );", 17, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("138:1: index_clause : ( ^( INDEX_CLAUSE IDENTIFIER index_term_list ) | ^( INDEX_CLAUSE PARSE_ERROR ) );", 17, 0, input);

                throw nvae;
            }
            switch (alt17) {
                case 1 :
                    // BONTCTreeWalker.g:138:16: ^( INDEX_CLAUSE IDENTIFIER index_term_list )
                    {
                    match(input,INDEX_CLAUSE,FOLLOW_INDEX_CLAUSE_in_index_clause1642); 

                    match(input, Token.DOWN, null); 
                    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_index_clause1644); 
                    pushFollow(FOLLOW_index_term_list_in_index_clause1646);
                    index_term_list();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:142:16: ^( INDEX_CLAUSE PARSE_ERROR )
                    {
                    match(input,INDEX_CLAUSE,FOLLOW_INDEX_CLAUSE_in_index_clause1701); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_index_clause1703); 

                    match(input, Token.UP, null); 

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
    // $ANTLR end index_clause


    // $ANTLR start index_term_list
    // BONTCTreeWalker.g:145:1: index_term_list : ^( INDEX_TERM_LIST ( index_string )+ ) ;
    public final void index_term_list() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:145:18: ( ^( INDEX_TERM_LIST ( index_string )+ ) )
            // BONTCTreeWalker.g:145:19: ^( INDEX_TERM_LIST ( index_string )+ )
            {
            match(input,INDEX_TERM_LIST,FOLLOW_INDEX_TERM_LIST_in_index_term_list1766); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:146:37: ( index_string )+
            int cnt18=0;
            loop18:
            do {
                int alt18=2;
                int LA18_0 = input.LA(1);

                if ( (LA18_0==INDEX_STRING) ) {
                    alt18=1;
                }


                switch (alt18) {
            	case 1 :
            	    // BONTCTreeWalker.g:146:38: index_string
            	    {
            	    pushFollow(FOLLOW_index_string_in_index_term_list1769);
            	    index_string();
            	    _fsp--;


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


            match(input, Token.UP, null); 

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
    // $ANTLR end index_term_list


    // $ANTLR start index_string
    // BONTCTreeWalker.g:150:1: index_string : ^( INDEX_STRING MANIFEST_STRING ) ;
    public final void index_string() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:150:15: ( ^( INDEX_STRING MANIFEST_STRING ) )
            // BONTCTreeWalker.g:150:16: ^( INDEX_STRING MANIFEST_STRING )
            {
            match(input,INDEX_STRING,FOLLOW_INDEX_STRING_in_index_string1854); 

            match(input, Token.DOWN, null); 
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_index_string1856); 

            match(input, Token.UP, null); 

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
    // $ANTLR end index_string


    // $ANTLR start cluster_chart
    // BONTCTreeWalker.g:155:1: cluster_chart : ^( CLUSTER_CHART cluster_name ( indexing )? ( explanation )? ( part )? ( class_entries )? ( cluster_entries )? ) ;
    public final void cluster_chart() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:157:16: ( ^( CLUSTER_CHART cluster_name ( indexing )? ( explanation )? ( part )? ( class_entries )? ( cluster_entries )? ) )
            // BONTCTreeWalker.g:157:17: ^( CLUSTER_CHART cluster_name ( indexing )? ( explanation )? ( part )? ( class_entries )? ( cluster_entries )? )
            {
            match(input,CLUSTER_CHART,FOLLOW_CLUSTER_CHART_in_cluster_chart1920); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_cluster_name_in_cluster_chart1922);
            cluster_name();
            _fsp--;

            // BONTCTreeWalker.g:159:19: ( indexing )?
            int alt19=2;
            int LA19_0 = input.LA(1);

            if ( (LA19_0==INDEXING) ) {
                alt19=1;
            }
            switch (alt19) {
                case 1 :
                    // BONTCTreeWalker.g:159:20: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_cluster_chart1944);
                    indexing();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:160:19: ( explanation )?
            int alt20=2;
            int LA20_0 = input.LA(1);

            if ( (LA20_0==EXPLANATION) ) {
                alt20=1;
            }
            switch (alt20) {
                case 1 :
                    // BONTCTreeWalker.g:160:20: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_cluster_chart1968);
                    explanation();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:161:19: ( part )?
            int alt21=2;
            int LA21_0 = input.LA(1);

            if ( (LA21_0==PART) ) {
                alt21=1;
            }
            switch (alt21) {
                case 1 :
                    // BONTCTreeWalker.g:161:20: part
                    {
                    pushFollow(FOLLOW_part_in_cluster_chart1992);
                    part();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:162:19: ( class_entries )?
            int alt22=2;
            int LA22_0 = input.LA(1);

            if ( (LA22_0==CLASS_ENTRIES) ) {
                alt22=1;
            }
            switch (alt22) {
                case 1 :
                    // BONTCTreeWalker.g:162:20: class_entries
                    {
                    pushFollow(FOLLOW_class_entries_in_cluster_chart2016);
                    class_entries();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:163:19: ( cluster_entries )?
            int alt23=2;
            int LA23_0 = input.LA(1);

            if ( (LA23_0==CLUSTER_ENTRIES) ) {
                alt23=1;
            }
            switch (alt23) {
                case 1 :
                    // BONTCTreeWalker.g:163:20: cluster_entries
                    {
                    pushFollow(FOLLOW_cluster_entries_in_cluster_chart2040);
                    cluster_entries();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end cluster_chart


    // $ANTLR start class_entries
    // BONTCTreeWalker.g:167:1: class_entries : ^( CLASS_ENTRIES ( class_entry )+ ) ;
    public final void class_entries() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:167:16: ( ^( CLASS_ENTRIES ( class_entry )+ ) )
            // BONTCTreeWalker.g:167:17: ^( CLASS_ENTRIES ( class_entry )+ )
            {
            match(input,CLASS_ENTRIES,FOLLOW_CLASS_ENTRIES_in_class_entries2121); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:168:33: ( class_entry )+
            int cnt24=0;
            loop24:
            do {
                int alt24=2;
                int LA24_0 = input.LA(1);

                if ( (LA24_0==CLASS_ENTRY) ) {
                    alt24=1;
                }


                switch (alt24) {
            	case 1 :
            	    // BONTCTreeWalker.g:168:34: class_entry
            	    {
            	    pushFollow(FOLLOW_class_entry_in_class_entries2124);
            	    class_entry();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt24 >= 1 ) break loop24;
                        EarlyExitException eee =
                            new EarlyExitException(24, input);
                        throw eee;
                }
                cnt24++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end class_entries


    // $ANTLR start class_entry
    // BONTCTreeWalker.g:172:1: class_entry : ^( CLASS_ENTRY class_name description ) ;
    public final void class_entry() throws RecognitionException {
        class_name_return class_name5 = null;


        try {
            // BONTCTreeWalker.g:172:14: ( ^( CLASS_ENTRY class_name description ) )
            // BONTCTreeWalker.g:172:15: ^( CLASS_ENTRY class_name description )
            {
            match(input,CLASS_ENTRY,FOLLOW_CLASS_ENTRY_in_class_entry2203); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_class_name_in_class_entry2205);
            class_name5=class_name();
            _fsp--;

            pushFollow(FOLLOW_description_in_class_entry2207);
            description();
            _fsp--;

             getITC().checkValidClassType(input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(class_name5.start),
              input.getTreeAdaptor().getTokenStopIndex(class_name5.start)),getSLoc(((CommonTree)class_name5.start).token)); 

            match(input, Token.UP, null); 

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
    // $ANTLR end class_entry

    public static class cluster_name_return extends TreeRuleReturnScope {
    };

    // $ANTLR start cluster_name
    // BONTCTreeWalker.g:178:1: cluster_name : ^( CLUSTER_NAME IDENTIFIER ) ;
    public final cluster_name_return cluster_name() throws RecognitionException {
        cluster_name_return retval = new cluster_name_return();
        retval.start = input.LT(1);

        try {
            // BONTCTreeWalker.g:178:15: ( ^( CLUSTER_NAME IDENTIFIER ) )
            // BONTCTreeWalker.g:178:16: ^( CLUSTER_NAME IDENTIFIER )
            {
            match(input,CLUSTER_NAME,FOLLOW_CLUSTER_NAME_in_cluster_name2297); 

            match(input, Token.DOWN, null); 
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_cluster_name2299); 

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end cluster_name


    // $ANTLR start class_chart
    // BONTCTreeWalker.g:183:1: class_chart : ^( CLASS_CHART class_name ( indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? ) ;
    public final void class_chart() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:185:14: ( ^( CLASS_CHART class_name ( indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? ) )
            // BONTCTreeWalker.g:185:15: ^( CLASS_CHART class_name ( indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? )
            {
            match(input,CLASS_CHART,FOLLOW_CLASS_CHART_in_class_chart2362); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_class_name_in_class_chart2364);
            class_name();
            _fsp--;

            // BONTCTreeWalker.g:187:17: ( indexing )?
            int alt25=2;
            int LA25_0 = input.LA(1);

            if ( (LA25_0==INDEXING) ) {
                alt25=1;
            }
            switch (alt25) {
                case 1 :
                    // BONTCTreeWalker.g:187:18: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_class_chart2383);
                    indexing();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:188:17: ( explanation )?
            int alt26=2;
            int LA26_0 = input.LA(1);

            if ( (LA26_0==EXPLANATION) ) {
                alt26=1;
            }
            switch (alt26) {
                case 1 :
                    // BONTCTreeWalker.g:188:18: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_class_chart2405);
                    explanation();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:189:17: ( part )?
            int alt27=2;
            int LA27_0 = input.LA(1);

            if ( (LA27_0==PART) ) {
                alt27=1;
            }
            switch (alt27) {
                case 1 :
                    // BONTCTreeWalker.g:189:18: part
                    {
                    pushFollow(FOLLOW_part_in_class_chart2427);
                    part();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:190:17: ( inherits )?
            int alt28=2;
            int LA28_0 = input.LA(1);

            if ( (LA28_0==INHERITS) ) {
                alt28=1;
            }
            switch (alt28) {
                case 1 :
                    // BONTCTreeWalker.g:190:18: inherits
                    {
                    pushFollow(FOLLOW_inherits_in_class_chart2449);
                    inherits();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:191:17: ( queries )?
            int alt29=2;
            int LA29_0 = input.LA(1);

            if ( (LA29_0==QUERIES) ) {
                alt29=1;
            }
            switch (alt29) {
                case 1 :
                    // BONTCTreeWalker.g:191:18: queries
                    {
                    pushFollow(FOLLOW_queries_in_class_chart2470);
                    queries();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:192:17: ( commands )?
            int alt30=2;
            int LA30_0 = input.LA(1);

            if ( (LA30_0==COMMANDS) ) {
                alt30=1;
            }
            switch (alt30) {
                case 1 :
                    // BONTCTreeWalker.g:192:18: commands
                    {
                    pushFollow(FOLLOW_commands_in_class_chart2492);
                    commands();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:193:17: ( constraints )?
            int alt31=2;
            int LA31_0 = input.LA(1);

            if ( (LA31_0==CONSTRAINTS) ) {
                alt31=1;
            }
            switch (alt31) {
                case 1 :
                    // BONTCTreeWalker.g:193:18: constraints
                    {
                    pushFollow(FOLLOW_constraints_in_class_chart2514);
                    constraints();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end class_chart


    // $ANTLR start inherits
    // BONTCTreeWalker.g:197:1: inherits : ( ^( INHERITS class_name_list ) | ^( INHERITS PARSE_ERROR ) );
    public final void inherits() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:197:11: ( ^( INHERITS class_name_list ) | ^( INHERITS PARSE_ERROR ) )
            int alt32=2;
            int LA32_0 = input.LA(1);

            if ( (LA32_0==INHERITS) ) {
                int LA32_1 = input.LA(2);

                if ( (LA32_1==DOWN) ) {
                    int LA32_2 = input.LA(3);

                    if ( (LA32_2==PARSE_ERROR) ) {
                        alt32=2;
                    }
                    else if ( (LA32_2==CLASS_NAME_LIST) ) {
                        alt32=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("197:1: inherits : ( ^( INHERITS class_name_list ) | ^( INHERITS PARSE_ERROR ) );", 32, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("197:1: inherits : ( ^( INHERITS class_name_list ) | ^( INHERITS PARSE_ERROR ) );", 32, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("197:1: inherits : ( ^( INHERITS class_name_list ) | ^( INHERITS PARSE_ERROR ) );", 32, 0, input);

                throw nvae;
            }
            switch (alt32) {
                case 1 :
                    // BONTCTreeWalker.g:197:14: ^( INHERITS class_name_list )
                    {
                    match(input,INHERITS,FOLLOW_INHERITS_in_inherits2574); 

                     getContext().enterInheritsClause(); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_class_name_list_in_inherits2609);
                    class_name_list();
                    _fsp--;

                     getContext().leaveInheritsClause(); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:204:14: ^( INHERITS PARSE_ERROR )
                    {
                    match(input,INHERITS,FOLLOW_INHERITS_in_inherits2673); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_inherits2675); 

                    match(input, Token.UP, null); 

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
    // $ANTLR end inherits


    // $ANTLR start queries
    // BONTCTreeWalker.g:207:1: queries : ^( QUERIES query_list ) ;
    public final void queries() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:207:10: ( ^( QUERIES query_list ) )
            // BONTCTreeWalker.g:207:12: ^( QUERIES query_list )
            {
            match(input,QUERIES,FOLLOW_QUERIES_in_queries2698); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_query_list_in_queries2700);
            query_list();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end queries


    // $ANTLR start commands
    // BONTCTreeWalker.g:210:1: commands : ^( COMMANDS command_list ) ;
    public final void commands() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:210:11: ( ^( COMMANDS command_list ) )
            // BONTCTreeWalker.g:210:13: ^( COMMANDS command_list )
            {
            match(input,COMMANDS,FOLLOW_COMMANDS_in_commands2730); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_command_list_in_commands2732);
            command_list();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end commands


    // $ANTLR start constraints
    // BONTCTreeWalker.g:213:1: constraints : ^( CONSTRAINTS constraint_list ) ;
    public final void constraints() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:213:14: ( ^( CONSTRAINTS constraint_list ) )
            // BONTCTreeWalker.g:213:16: ^( CONSTRAINTS constraint_list )
            {
            match(input,CONSTRAINTS,FOLLOW_CONSTRAINTS_in_constraints2754); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_constraint_list_in_constraints2756);
            constraint_list();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end constraints


    // $ANTLR start query_list
    // BONTCTreeWalker.g:216:1: query_list : ^( QUERY_LIST ( manifest_textblock )+ ) ;
    public final void query_list() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:216:13: ( ^( QUERY_LIST ( manifest_textblock )+ ) )
            // BONTCTreeWalker.g:216:14: ^( QUERY_LIST ( manifest_textblock )+ )
            {
            match(input,QUERY_LIST,FOLLOW_QUERY_LIST_in_query_list2796); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:217:27: ( manifest_textblock )+
            int cnt33=0;
            loop33:
            do {
                int alt33=2;
                int LA33_0 = input.LA(1);

                if ( (LA33_0==MANIFEST_STRING||LA33_0==MANIFEST_TEXTBLOCK_START) ) {
                    alt33=1;
                }


                switch (alt33) {
            	case 1 :
            	    // BONTCTreeWalker.g:217:28: manifest_textblock
            	    {
            	    pushFollow(FOLLOW_manifest_textblock_in_query_list2799);
            	    manifest_textblock();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt33 >= 1 ) break loop33;
                        EarlyExitException eee =
                            new EarlyExitException(33, input);
                        throw eee;
                }
                cnt33++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end query_list


    // $ANTLR start command_list
    // BONTCTreeWalker.g:221:1: command_list : ^( COMMAND_LIST ( manifest_textblock )+ ) ;
    public final void command_list() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:221:15: ( ^( COMMAND_LIST ( manifest_textblock )+ ) )
            // BONTCTreeWalker.g:221:16: ^( COMMAND_LIST ( manifest_textblock )+ )
            {
            match(input,COMMAND_LIST,FOLLOW_COMMAND_LIST_in_command_list2869); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:222:31: ( manifest_textblock )+
            int cnt34=0;
            loop34:
            do {
                int alt34=2;
                int LA34_0 = input.LA(1);

                if ( (LA34_0==MANIFEST_STRING||LA34_0==MANIFEST_TEXTBLOCK_START) ) {
                    alt34=1;
                }


                switch (alt34) {
            	case 1 :
            	    // BONTCTreeWalker.g:222:32: manifest_textblock
            	    {
            	    pushFollow(FOLLOW_manifest_textblock_in_command_list2872);
            	    manifest_textblock();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt34 >= 1 ) break loop34;
                        EarlyExitException eee =
                            new EarlyExitException(34, input);
                        throw eee;
                }
                cnt34++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end command_list


    // $ANTLR start constraint_list
    // BONTCTreeWalker.g:226:1: constraint_list : ^( CONSTRAINT_LIST ( manifest_textblock )+ ) ;
    public final void constraint_list() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:226:18: ( ^( CONSTRAINT_LIST ( manifest_textblock )+ ) )
            // BONTCTreeWalker.g:226:19: ^( CONSTRAINT_LIST ( manifest_textblock )+ )
            {
            match(input,CONSTRAINT_LIST,FOLLOW_CONSTRAINT_LIST_in_constraint_list2951); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:227:37: ( manifest_textblock )+
            int cnt35=0;
            loop35:
            do {
                int alt35=2;
                int LA35_0 = input.LA(1);

                if ( (LA35_0==MANIFEST_STRING||LA35_0==MANIFEST_TEXTBLOCK_START) ) {
                    alt35=1;
                }


                switch (alt35) {
            	case 1 :
            	    // BONTCTreeWalker.g:227:38: manifest_textblock
            	    {
            	    pushFollow(FOLLOW_manifest_textblock_in_constraint_list2954);
            	    manifest_textblock();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt35 >= 1 ) break loop35;
                        EarlyExitException eee =
                            new EarlyExitException(35, input);
                        throw eee;
                }
                cnt35++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end constraint_list


    // $ANTLR start class_name_list
    // BONTCTreeWalker.g:231:1: class_name_list : ^( CLASS_NAME_LIST ( class_name )+ ) ;
    public final void class_name_list() throws RecognitionException {
        class_name_return class_name6 = null;


        try {
            // BONTCTreeWalker.g:231:18: ( ^( CLASS_NAME_LIST ( class_name )+ ) )
            // BONTCTreeWalker.g:231:19: ^( CLASS_NAME_LIST ( class_name )+ )
            {
            match(input,CLASS_NAME_LIST,FOLLOW_CLASS_NAME_LIST_in_class_name_list3025); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:233:21: ( class_name )+
            int cnt36=0;
            loop36:
            do {
                int alt36=2;
                int LA36_0 = input.LA(1);

                if ( (LA36_0==CLASS_NAME) ) {
                    alt36=1;
                }


                switch (alt36) {
            	case 1 :
            	    // BONTCTreeWalker.g:233:23: class_name
            	    {
            	    pushFollow(FOLLOW_class_name_in_class_name_list3050);
            	    class_name6=class_name();
            	    _fsp--;

            	     getFTC().checkValidClassTypeByContext(input.getTokenStream().toString(
            	      input.getTreeAdaptor().getTokenStartIndex(class_name6.start),
            	      input.getTreeAdaptor().getTokenStopIndex(class_name6.start)), getSLoc(((CommonTree)class_name6.start).token));
            	                            getITC().checkValidClassTypeByContext(input.getTokenStream().toString(
            	      input.getTreeAdaptor().getTokenStartIndex(class_name6.start),
            	      input.getTreeAdaptor().getTokenStopIndex(class_name6.start)), getSLoc(((CommonTree)class_name6.start).token)); 
            	                          

            	    }
            	    break;

            	default :
            	    if ( cnt36 >= 1 ) break loop36;
                        EarlyExitException eee =
                            new EarlyExitException(36, input);
                        throw eee;
                }
                cnt36++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end class_name_list

    public static class class_name_return extends TreeRuleReturnScope {
    };

    // $ANTLR start class_name
    // BONTCTreeWalker.g:240:1: class_name : ^( CLASS_NAME IDENTIFIER ) ;
    public final class_name_return class_name() throws RecognitionException {
        class_name_return retval = new class_name_return();
        retval.start = input.LT(1);

        try {
            // BONTCTreeWalker.g:240:13: ( ^( CLASS_NAME IDENTIFIER ) )
            // BONTCTreeWalker.g:240:14: ^( CLASS_NAME IDENTIFIER )
            {
            match(input,CLASS_NAME,FOLLOW_CLASS_NAME_in_class_name3159); 

            match(input, Token.DOWN, null); 
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_class_name3161); 

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end class_name


    // $ANTLR start event_chart
    // BONTCTreeWalker.g:245:1: event_chart : ^( EVENT_CHART system_name ( 'incoming' )? ( 'outgoing' )? ( indexing )? ( explanation )? ( part )? ( event_entries )? ) ;
    public final void event_chart() throws RecognitionException {
        system_name_return system_name7 = null;


        try {
            // BONTCTreeWalker.g:247:14: ( ^( EVENT_CHART system_name ( 'incoming' )? ( 'outgoing' )? ( indexing )? ( explanation )? ( part )? ( event_entries )? ) )
            // BONTCTreeWalker.g:247:15: ^( EVENT_CHART system_name ( 'incoming' )? ( 'outgoing' )? ( indexing )? ( explanation )? ( part )? ( event_entries )? )
            {
            match(input,EVENT_CHART,FOLLOW_EVENT_CHART_in_event_chart3219); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_system_name_in_event_chart3237);
            system_name7=system_name();
            _fsp--;

             getITC().checkSystemName(input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(system_name7.start),
              input.getTreeAdaptor().getTokenStopIndex(system_name7.start)),getSLoc(((CommonTree)system_name7.start).token)); 
            // BONTCTreeWalker.g:251:17: ( 'incoming' )?
            int alt37=2;
            int LA37_0 = input.LA(1);

            if ( (LA37_0==205) ) {
                alt37=1;
            }
            switch (alt37) {
                case 1 :
                    // BONTCTreeWalker.g:251:18: 'incoming'
                    {
                    match(input,205,FOLLOW_205_in_event_chart3276); 

                    }
                    break;

            }

            // BONTCTreeWalker.g:251:31: ( 'outgoing' )?
            int alt38=2;
            int LA38_0 = input.LA(1);

            if ( (LA38_0==206) ) {
                alt38=1;
            }
            switch (alt38) {
                case 1 :
                    // BONTCTreeWalker.g:251:32: 'outgoing'
                    {
                    match(input,206,FOLLOW_206_in_event_chart3281); 

                    }
                    break;

            }

            // BONTCTreeWalker.g:252:17: ( indexing )?
            int alt39=2;
            int LA39_0 = input.LA(1);

            if ( (LA39_0==INDEXING) ) {
                alt39=1;
            }
            switch (alt39) {
                case 1 :
                    // BONTCTreeWalker.g:252:18: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_event_chart3302);
                    indexing();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:253:17: ( explanation )?
            int alt40=2;
            int LA40_0 = input.LA(1);

            if ( (LA40_0==EXPLANATION) ) {
                alt40=1;
            }
            switch (alt40) {
                case 1 :
                    // BONTCTreeWalker.g:253:18: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_event_chart3323);
                    explanation();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:254:17: ( part )?
            int alt41=2;
            int LA41_0 = input.LA(1);

            if ( (LA41_0==PART) ) {
                alt41=1;
            }
            switch (alt41) {
                case 1 :
                    // BONTCTreeWalker.g:254:18: part
                    {
                    pushFollow(FOLLOW_part_in_event_chart3344);
                    part();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:255:17: ( event_entries )?
            int alt42=2;
            int LA42_0 = input.LA(1);

            if ( (LA42_0==EVENT_ENTRIES) ) {
                alt42=1;
            }
            switch (alt42) {
                case 1 :
                    // BONTCTreeWalker.g:255:18: event_entries
                    {
                    pushFollow(FOLLOW_event_entries_in_event_chart3365);
                    event_entries();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end event_chart


    // $ANTLR start event_entries
    // BONTCTreeWalker.g:259:1: event_entries : ^( EVENT_ENTRIES ( event_entry )+ ) ;
    public final void event_entries() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:259:16: ( ^( EVENT_ENTRIES ( event_entry )+ ) )
            // BONTCTreeWalker.g:259:17: ^( EVENT_ENTRIES ( event_entry )+ )
            {
            match(input,EVENT_ENTRIES,FOLLOW_EVENT_ENTRIES_in_event_entries3439); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:261:19: ( event_entry )+
            int cnt43=0;
            loop43:
            do {
                int alt43=2;
                int LA43_0 = input.LA(1);

                if ( (LA43_0==EVENT_ENTRY) ) {
                    alt43=1;
                }


                switch (alt43) {
            	case 1 :
            	    // BONTCTreeWalker.g:261:20: event_entry
            	    {
            	    pushFollow(FOLLOW_event_entry_in_event_entries3460);
            	    event_entry();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt43 >= 1 ) break loop43;
                        EarlyExitException eee =
                            new EarlyExitException(43, input);
                        throw eee;
                }
                cnt43++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end event_entries


    // $ANTLR start event_entry
    // BONTCTreeWalker.g:265:1: event_entry : ( ^( EVENT_ENTRY manifest_textblock class_name_list ) | ^( EVENT_ENTRY PARSE_ERROR ) );
    public final void event_entry() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:265:14: ( ^( EVENT_ENTRY manifest_textblock class_name_list ) | ^( EVENT_ENTRY PARSE_ERROR ) )
            int alt44=2;
            int LA44_0 = input.LA(1);

            if ( (LA44_0==EVENT_ENTRY) ) {
                int LA44_1 = input.LA(2);

                if ( (LA44_1==DOWN) ) {
                    int LA44_2 = input.LA(3);

                    if ( (LA44_2==PARSE_ERROR) ) {
                        alt44=2;
                    }
                    else if ( (LA44_2==MANIFEST_STRING||LA44_2==MANIFEST_TEXTBLOCK_START) ) {
                        alt44=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("265:1: event_entry : ( ^( EVENT_ENTRY manifest_textblock class_name_list ) | ^( EVENT_ENTRY PARSE_ERROR ) );", 44, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("265:1: event_entry : ( ^( EVENT_ENTRY manifest_textblock class_name_list ) | ^( EVENT_ENTRY PARSE_ERROR ) );", 44, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("265:1: event_entry : ( ^( EVENT_ENTRY manifest_textblock class_name_list ) | ^( EVENT_ENTRY PARSE_ERROR ) );", 44, 0, input);

                throw nvae;
            }
            switch (alt44) {
                case 1 :
                    // BONTCTreeWalker.g:265:15: ^( EVENT_ENTRY manifest_textblock class_name_list )
                    {
                    match(input,EVENT_ENTRY,FOLLOW_EVENT_ENTRY_in_event_entry3538); 

                     getContext().enterEventEntry(); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_manifest_textblock_in_event_entry3574);
                    manifest_textblock();
                    _fsp--;

                    pushFollow(FOLLOW_class_name_list_in_event_entry3592);
                    class_name_list();
                    _fsp--;

                     getContext().leaveEventEntry(); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:273:15: ^( EVENT_ENTRY PARSE_ERROR )
                    {
                    match(input,EVENT_ENTRY,FOLLOW_EVENT_ENTRY_in_event_entry3660); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_event_entry3662); 

                    match(input, Token.UP, null); 

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
    // $ANTLR end event_entry


    // $ANTLR start scenario_chart
    // BONTCTreeWalker.g:276:1: scenario_chart : ^( SCENARIO_CHART system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries )? ) ;
    public final void scenario_chart() throws RecognitionException {
        system_name_return system_name8 = null;


        try {
            // BONTCTreeWalker.g:278:17: ( ^( SCENARIO_CHART system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries )? ) )
            // BONTCTreeWalker.g:278:18: ^( SCENARIO_CHART system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries )? )
            {
            match(input,SCENARIO_CHART,FOLLOW_SCENARIO_CHART_in_scenario_chart3709); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_system_name_in_scenario_chart3730);
            system_name8=system_name();
            _fsp--;

             getITC().checkSystemName(input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(system_name8.start),
              input.getTreeAdaptor().getTokenStopIndex(system_name8.start)),getSLoc(((CommonTree)system_name8.start).token)); 
            // BONTCTreeWalker.g:282:20: ( indexing )?
            int alt45=2;
            int LA45_0 = input.LA(1);

            if ( (LA45_0==INDEXING) ) {
                alt45=1;
            }
            switch (alt45) {
                case 1 :
                    // BONTCTreeWalker.g:282:21: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_scenario_chart3773);
                    indexing();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:283:20: ( explanation )?
            int alt46=2;
            int LA46_0 = input.LA(1);

            if ( (LA46_0==EXPLANATION) ) {
                alt46=1;
            }
            switch (alt46) {
                case 1 :
                    // BONTCTreeWalker.g:283:21: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_scenario_chart3797);
                    explanation();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:284:20: ( part )?
            int alt47=2;
            int LA47_0 = input.LA(1);

            if ( (LA47_0==PART) ) {
                alt47=1;
            }
            switch (alt47) {
                case 1 :
                    // BONTCTreeWalker.g:284:21: part
                    {
                    pushFollow(FOLLOW_part_in_scenario_chart3821);
                    part();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:285:20: ( scenario_entries )?
            int alt48=2;
            int LA48_0 = input.LA(1);

            if ( (LA48_0==SCENARIO_ENTRIES) ) {
                alt48=1;
            }
            switch (alt48) {
                case 1 :
                    // BONTCTreeWalker.g:285:21: scenario_entries
                    {
                    pushFollow(FOLLOW_scenario_entries_in_scenario_chart3845);
                    scenario_entries();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end scenario_chart


    // $ANTLR start scenario_entries
    // BONTCTreeWalker.g:289:1: scenario_entries : ^( SCENARIO_ENTRIES ( scenario_entry )+ ) ;
    public final void scenario_entries() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:289:19: ( ^( SCENARIO_ENTRIES ( scenario_entry )+ ) )
            // BONTCTreeWalker.g:289:20: ^( SCENARIO_ENTRIES ( scenario_entry )+ )
            {
            match(input,SCENARIO_ENTRIES,FOLLOW_SCENARIO_ENTRIES_in_scenario_entries3931); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:291:22: ( scenario_entry )+
            int cnt49=0;
            loop49:
            do {
                int alt49=2;
                int LA49_0 = input.LA(1);

                if ( (LA49_0==SCENARIO_ENTRY) ) {
                    alt49=1;
                }


                switch (alt49) {
            	case 1 :
            	    // BONTCTreeWalker.g:291:23: scenario_entry
            	    {
            	    pushFollow(FOLLOW_scenario_entry_in_scenario_entries3955);
            	    scenario_entry();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt49 >= 1 ) break loop49;
                        EarlyExitException eee =
                            new EarlyExitException(49, input);
                        throw eee;
                }
                cnt49++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end scenario_entries


    // $ANTLR start scenario_entry
    // BONTCTreeWalker.g:295:1: scenario_entry : ^( SCENARIO_ENTRY MANIFEST_STRING description ) ;
    public final void scenario_entry() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:295:17: ( ^( SCENARIO_ENTRY MANIFEST_STRING description ) )
            // BONTCTreeWalker.g:295:18: ^( SCENARIO_ENTRY MANIFEST_STRING description )
            {
            match(input,SCENARIO_ENTRY,FOLLOW_SCENARIO_ENTRY_in_scenario_entry4063); 

            match(input, Token.DOWN, null); 
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_scenario_entry4084); 
            pushFollow(FOLLOW_description_in_scenario_entry4086);
            description();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end scenario_entry


    // $ANTLR start creation_chart
    // BONTCTreeWalker.g:301:1: creation_chart : ^( CREATION_CHART system_name ( indexing )? ( explanation )? ( part )? ( creation_entries )? ) ;
    public final void creation_chart() throws RecognitionException {
        system_name_return system_name9 = null;


        try {
            // BONTCTreeWalker.g:303:17: ( ^( CREATION_CHART system_name ( indexing )? ( explanation )? ( part )? ( creation_entries )? ) )
            // BONTCTreeWalker.g:303:18: ^( CREATION_CHART system_name ( indexing )? ( explanation )? ( part )? ( creation_entries )? )
            {
            match(input,CREATION_CHART,FOLLOW_CREATION_CHART_in_creation_chart4156); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_system_name_in_creation_chart4177);
            system_name9=system_name();
            _fsp--;

             getITC().checkSystemName(input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(system_name9.start),
              input.getTreeAdaptor().getTokenStopIndex(system_name9.start)),getSLoc(((CommonTree)system_name9.start).token)); 
            // BONTCTreeWalker.g:307:20: ( indexing )?
            int alt50=2;
            int LA50_0 = input.LA(1);

            if ( (LA50_0==INDEXING) ) {
                alt50=1;
            }
            switch (alt50) {
                case 1 :
                    // BONTCTreeWalker.g:307:21: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_creation_chart4220);
                    indexing();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:308:20: ( explanation )?
            int alt51=2;
            int LA51_0 = input.LA(1);

            if ( (LA51_0==EXPLANATION) ) {
                alt51=1;
            }
            switch (alt51) {
                case 1 :
                    // BONTCTreeWalker.g:308:21: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_creation_chart4244);
                    explanation();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:309:20: ( part )?
            int alt52=2;
            int LA52_0 = input.LA(1);

            if ( (LA52_0==PART) ) {
                alt52=1;
            }
            switch (alt52) {
                case 1 :
                    // BONTCTreeWalker.g:309:21: part
                    {
                    pushFollow(FOLLOW_part_in_creation_chart4268);
                    part();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:310:20: ( creation_entries )?
            int alt53=2;
            int LA53_0 = input.LA(1);

            if ( (LA53_0==CREATION_ENTRIES) ) {
                alt53=1;
            }
            switch (alt53) {
                case 1 :
                    // BONTCTreeWalker.g:310:21: creation_entries
                    {
                    pushFollow(FOLLOW_creation_entries_in_creation_chart4292);
                    creation_entries();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end creation_chart


    // $ANTLR start creation_entries
    // BONTCTreeWalker.g:314:1: creation_entries : ^( CREATION_ENTRIES ( creation_entry )+ ) ;
    public final void creation_entries() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:314:19: ( ^( CREATION_ENTRIES ( creation_entry )+ ) )
            // BONTCTreeWalker.g:314:20: ^( CREATION_ENTRIES ( creation_entry )+ )
            {
            match(input,CREATION_ENTRIES,FOLLOW_CREATION_ENTRIES_in_creation_entries4378); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:316:22: ( creation_entry )+
            int cnt54=0;
            loop54:
            do {
                int alt54=2;
                int LA54_0 = input.LA(1);

                if ( (LA54_0==CREATION_ENTRY) ) {
                    alt54=1;
                }


                switch (alt54) {
            	case 1 :
            	    // BONTCTreeWalker.g:316:23: creation_entry
            	    {
            	    pushFollow(FOLLOW_creation_entry_in_creation_entries4402);
            	    creation_entry();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt54 >= 1 ) break loop54;
                        EarlyExitException eee =
                            new EarlyExitException(54, input);
                        throw eee;
                }
                cnt54++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end creation_entries


    // $ANTLR start creation_entry
    // BONTCTreeWalker.g:320:1: creation_entry : ^( CREATION_ENTRY class_name class_name_list ) ;
    public final void creation_entry() throws RecognitionException {
        class_name_return class_name10 = null;


        try {
            // BONTCTreeWalker.g:320:17: ( ^( CREATION_ENTRY class_name class_name_list ) )
            // BONTCTreeWalker.g:320:18: ^( CREATION_ENTRY class_name class_name_list )
            {
            match(input,CREATION_ENTRY,FOLLOW_CREATION_ENTRY_in_creation_entry4492); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_class_name_in_creation_entry4513);
            class_name10=class_name();
            _fsp--;

             getITC().checkValidClassType(input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(class_name10.start),
              input.getTreeAdaptor().getTokenStopIndex(class_name10.start)),getSLoc(((CommonTree)class_name10.start).token)); 
                                 getContext().enterCreationEntry(); 
            pushFollow(FOLLOW_class_name_list_in_creation_entry4556);
            class_name_list();
            _fsp--;

             getContext().leaveCreationEntry(); 

            match(input, Token.UP, null); 

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
    // $ANTLR end creation_entry


    // $ANTLR start static_diagram
    // BONTCTreeWalker.g:330:1: static_diagram : ^( STATIC_DIAGRAM ( extended_id )? ( COMMENT )? ( static_block )? ) ;
    public final void static_diagram() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:334:17: ( ^( STATIC_DIAGRAM ( extended_id )? ( COMMENT )? ( static_block )? ) )
            // BONTCTreeWalker.g:334:18: ^( STATIC_DIAGRAM ( extended_id )? ( COMMENT )? ( static_block )? )
            {
            match(input,STATIC_DIAGRAM,FOLLOW_STATIC_DIAGRAM_in_static_diagram4648); 

            if ( input.LA(1)==Token.DOWN ) {
                match(input, Token.DOWN, null); 
                // BONTCTreeWalker.g:336:20: ( extended_id )?
                int alt55=2;
                int LA55_0 = input.LA(1);

                if ( (LA55_0==EXTENDED_ID) ) {
                    alt55=1;
                }
                switch (alt55) {
                    case 1 :
                        // BONTCTreeWalker.g:336:21: extended_id
                        {
                        pushFollow(FOLLOW_extended_id_in_static_diagram4670);
                        extended_id();
                        _fsp--;


                        }
                        break;

                }

                // BONTCTreeWalker.g:336:35: ( COMMENT )?
                int alt56=2;
                int LA56_0 = input.LA(1);

                if ( (LA56_0==COMMENT) ) {
                    alt56=1;
                }
                switch (alt56) {
                    case 1 :
                        // BONTCTreeWalker.g:336:36: COMMENT
                        {
                        match(input,COMMENT,FOLLOW_COMMENT_in_static_diagram4675); 

                        }
                        break;

                }

                // BONTCTreeWalker.g:337:20: ( static_block )?
                int alt57=2;
                int LA57_0 = input.LA(1);

                if ( (LA57_0==STATIC_BLOCK) ) {
                    alt57=1;
                }
                switch (alt57) {
                    case 1 :
                        // BONTCTreeWalker.g:337:21: static_block
                        {
                        pushFollow(FOLLOW_static_block_in_static_diagram4701);
                        static_block();
                        _fsp--;


                        }
                        break;

                }


                match(input, Token.UP, null); 
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
    // $ANTLR end static_diagram


    // $ANTLR start extended_id
    // BONTCTreeWalker.g:341:1: extended_id : ( ^( EXTENDED_ID IDENTIFIER ) | ^( EXTENDED_ID INTEGER ) );
    public final void extended_id() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:341:14: ( ^( EXTENDED_ID IDENTIFIER ) | ^( EXTENDED_ID INTEGER ) )
            int alt58=2;
            int LA58_0 = input.LA(1);

            if ( (LA58_0==EXTENDED_ID) ) {
                int LA58_1 = input.LA(2);

                if ( (LA58_1==DOWN) ) {
                    int LA58_2 = input.LA(3);

                    if ( (LA58_2==INTEGER) ) {
                        alt58=2;
                    }
                    else if ( (LA58_2==IDENTIFIER) ) {
                        alt58=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("341:1: extended_id : ( ^( EXTENDED_ID IDENTIFIER ) | ^( EXTENDED_ID INTEGER ) );", 58, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("341:1: extended_id : ( ^( EXTENDED_ID IDENTIFIER ) | ^( EXTENDED_ID INTEGER ) );", 58, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("341:1: extended_id : ( ^( EXTENDED_ID IDENTIFIER ) | ^( EXTENDED_ID INTEGER ) );", 58, 0, input);

                throw nvae;
            }
            switch (alt58) {
                case 1 :
                    // BONTCTreeWalker.g:341:15: ^( EXTENDED_ID IDENTIFIER )
                    {
                    match(input,EXTENDED_ID,FOLLOW_EXTENDED_ID_in_extended_id4783); 

                    match(input, Token.DOWN, null); 
                    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_extended_id4785); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:345:15: ^( EXTENDED_ID INTEGER )
                    {
                    match(input,EXTENDED_ID,FOLLOW_EXTENDED_ID_in_extended_id4852); 

                    match(input, Token.DOWN, null); 
                    match(input,INTEGER,FOLLOW_INTEGER_in_extended_id4854); 

                    match(input, Token.UP, null); 

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
    // $ANTLR end extended_id


    // $ANTLR start static_block
    // BONTCTreeWalker.g:350:1: static_block : ^( STATIC_BLOCK ( static_component )+ ) ;
    public final void static_block() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:350:15: ( ^( STATIC_BLOCK ( static_component )+ ) )
            // BONTCTreeWalker.g:350:16: ^( STATIC_BLOCK ( static_component )+ )
            {
            match(input,STATIC_BLOCK,FOLLOW_STATIC_BLOCK_in_static_block4925); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:351:31: ( static_component )+
            int cnt59=0;
            loop59:
            do {
                int alt59=2;
                int LA59_0 = input.LA(1);

                if ( (LA59_0==STATIC_COMPONENT) ) {
                    alt59=1;
                }


                switch (alt59) {
            	case 1 :
            	    // BONTCTreeWalker.g:351:32: static_component
            	    {
            	    pushFollow(FOLLOW_static_component_in_static_block4928);
            	    static_component();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt59 >= 1 ) break loop59;
                        EarlyExitException eee =
                            new EarlyExitException(59, input);
                        throw eee;
                }
                cnt59++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end static_block


    // $ANTLR start static_component
    // BONTCTreeWalker.g:356:1: static_component : ( ^( STATIC_COMPONENT cluster ) | ^( STATIC_COMPONENT classX ) | ^( STATIC_COMPONENT static_relation ) );
    public final void static_component() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:356:19: ( ^( STATIC_COMPONENT cluster ) | ^( STATIC_COMPONENT classX ) | ^( STATIC_COMPONENT static_relation ) )
            int alt60=3;
            int LA60_0 = input.LA(1);

            if ( (LA60_0==STATIC_COMPONENT) ) {
                int LA60_1 = input.LA(2);

                if ( (LA60_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case CLASS:
                        {
                        alt60=2;
                        }
                        break;
                    case STATIC_RELATION:
                        {
                        alt60=3;
                        }
                        break;
                    case CLUSTER:
                        {
                        alt60=1;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("356:1: static_component : ( ^( STATIC_COMPONENT cluster ) | ^( STATIC_COMPONENT classX ) | ^( STATIC_COMPONENT static_relation ) );", 60, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("356:1: static_component : ( ^( STATIC_COMPONENT cluster ) | ^( STATIC_COMPONENT classX ) | ^( STATIC_COMPONENT static_relation ) );", 60, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("356:1: static_component : ( ^( STATIC_COMPONENT cluster ) | ^( STATIC_COMPONENT classX ) | ^( STATIC_COMPONENT static_relation ) );", 60, 0, input);

                throw nvae;
            }
            switch (alt60) {
                case 1 :
                    // BONTCTreeWalker.g:356:21: ^( STATIC_COMPONENT cluster )
                    {
                    match(input,STATIC_COMPONENT,FOLLOW_STATIC_COMPONENT_in_static_component4997); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_cluster_in_static_component4999);
                    cluster();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:360:21: ^( STATIC_COMPONENT classX )
                    {
                    match(input,STATIC_COMPONENT,FOLLOW_STATIC_COMPONENT_in_static_component5090); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_classX_in_static_component5092);
                    classX();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 3 :
                    // BONTCTreeWalker.g:364:21: ^( STATIC_COMPONENT static_relation )
                    {
                    match(input,STATIC_COMPONENT,FOLLOW_STATIC_COMPONENT_in_static_component5183); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_static_relation_in_static_component5185);
                    static_relation();
                    _fsp--;


                    match(input, Token.UP, null); 

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
    // $ANTLR end static_component


    // $ANTLR start cluster
    // BONTCTreeWalker.g:369:1: cluster : ^( CLUSTER cluster_name ( 'reused' )? ( COMMENT )? ( cluster_components )? ) ;
    public final void cluster() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:371:10: ( ^( CLUSTER cluster_name ( 'reused' )? ( COMMENT )? ( cluster_components )? ) )
            // BONTCTreeWalker.g:371:11: ^( CLUSTER cluster_name ( 'reused' )? ( COMMENT )? ( cluster_components )? )
            {
            match(input,CLUSTER,FOLLOW_CLUSTER_in_cluster5252); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_cluster_name_in_cluster5254);
            cluster_name();
            _fsp--;

            // BONTCTreeWalker.g:373:13: ( 'reused' )?
            int alt61=2;
            int LA61_0 = input.LA(1);

            if ( (LA61_0==216) ) {
                alt61=1;
            }
            switch (alt61) {
                case 1 :
                    // BONTCTreeWalker.g:373:14: 'reused'
                    {
                    match(input,216,FOLLOW_216_in_cluster5269); 

                    }
                    break;

            }

            // BONTCTreeWalker.g:373:25: ( COMMENT )?
            int alt62=2;
            int LA62_0 = input.LA(1);

            if ( (LA62_0==COMMENT) ) {
                alt62=1;
            }
            switch (alt62) {
                case 1 :
                    // BONTCTreeWalker.g:373:26: COMMENT
                    {
                    match(input,COMMENT,FOLLOW_COMMENT_in_cluster5274); 

                    }
                    break;

            }

            // BONTCTreeWalker.g:374:13: ( cluster_components )?
            int alt63=2;
            int LA63_0 = input.LA(1);

            if ( (LA63_0==CLUSTER_COMPONENTS) ) {
                alt63=1;
            }
            switch (alt63) {
                case 1 :
                    // BONTCTreeWalker.g:374:14: cluster_components
                    {
                    pushFollow(FOLLOW_cluster_components_in_cluster5292);
                    cluster_components();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end cluster


    // $ANTLR start cluster_components
    // BONTCTreeWalker.g:378:1: cluster_components : ^( CLUSTER_COMPONENTS ( static_block )? ) ;
    public final void cluster_components() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:378:21: ( ^( CLUSTER_COMPONENTS ( static_block )? ) )
            // BONTCTreeWalker.g:378:22: ^( CLUSTER_COMPONENTS ( static_block )? )
            {
            match(input,CLUSTER_COMPONENTS,FOLLOW_CLUSTER_COMPONENTS_in_cluster_components5359); 

            if ( input.LA(1)==Token.DOWN ) {
                match(input, Token.DOWN, null); 
                // BONTCTreeWalker.g:379:43: ( static_block )?
                int alt64=2;
                int LA64_0 = input.LA(1);

                if ( (LA64_0==STATIC_BLOCK) ) {
                    alt64=1;
                }
                switch (alt64) {
                    case 1 :
                        // BONTCTreeWalker.g:379:44: static_block
                        {
                        pushFollow(FOLLOW_static_block_in_cluster_components5362);
                        static_block();
                        _fsp--;


                        }
                        break;

                }


                match(input, Token.UP, null); 
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
    // $ANTLR end cluster_components


    // $ANTLR start classX
    // BONTCTreeWalker.g:383:1: classX : ^( CLASS ( 'root' )? ( 'deferred' )? ( 'effective' )? class_name ( formal_generics )? ( 'reused' )? ( 'persistent' )? ( 'interfaced' )? ( COMMENT )? ( class_interface )? ) ;
    public final void classX() throws RecognitionException {
        class_name_return class_name11 = null;


        try {
            // BONTCTreeWalker.g:383:9: ( ^( CLASS ( 'root' )? ( 'deferred' )? ( 'effective' )? class_name ( formal_generics )? ( 'reused' )? ( 'persistent' )? ( 'interfaced' )? ( COMMENT )? ( class_interface )? ) )
            // BONTCTreeWalker.g:383:10: ^( CLASS ( 'root' )? ( 'deferred' )? ( 'effective' )? class_name ( formal_generics )? ( 'reused' )? ( 'persistent' )? ( 'interfaced' )? ( COMMENT )? ( class_interface )? )
            {
            match(input,CLASS,FOLLOW_CLASS_in_classX5450); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:385:12: ( 'root' )?
            int alt65=2;
            int LA65_0 = input.LA(1);

            if ( (LA65_0==217) ) {
                alt65=1;
            }
            switch (alt65) {
                case 1 :
                    // BONTCTreeWalker.g:385:13: 'root'
                    {
                    match(input,217,FOLLOW_217_in_classX5464); 

                    }
                    break;

            }

            // BONTCTreeWalker.g:385:22: ( 'deferred' )?
            int alt66=2;
            int LA66_0 = input.LA(1);

            if ( (LA66_0==218) ) {
                alt66=1;
            }
            switch (alt66) {
                case 1 :
                    // BONTCTreeWalker.g:385:23: 'deferred'
                    {
                    match(input,218,FOLLOW_218_in_classX5469); 

                    }
                    break;

            }

            // BONTCTreeWalker.g:385:36: ( 'effective' )?
            int alt67=2;
            int LA67_0 = input.LA(1);

            if ( (LA67_0==219) ) {
                alt67=1;
            }
            switch (alt67) {
                case 1 :
                    // BONTCTreeWalker.g:385:37: 'effective'
                    {
                    match(input,219,FOLLOW_219_in_classX5474); 

                    }
                    break;

            }

            pushFollow(FOLLOW_class_name_in_classX5490);
            class_name11=class_name();
            _fsp--;

             getContext().enterClass(input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(class_name11.start),
              input.getTreeAdaptor().getTokenStopIndex(class_name11.start))); 
            // BONTCTreeWalker.g:388:12: ( formal_generics )?
            int alt68=2;
            int LA68_0 = input.LA(1);

            if ( (LA68_0==FORMAL_GENERICS) ) {
                alt68=1;
            }
            switch (alt68) {
                case 1 :
                    // BONTCTreeWalker.g:388:13: formal_generics
                    {
                    pushFollow(FOLLOW_formal_generics_in_classX5518);
                    formal_generics();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:389:12: ( 'reused' )?
            int alt69=2;
            int LA69_0 = input.LA(1);

            if ( (LA69_0==216) ) {
                alt69=1;
            }
            switch (alt69) {
                case 1 :
                    // BONTCTreeWalker.g:389:13: 'reused'
                    {
                    match(input,216,FOLLOW_216_in_classX5534); 

                    }
                    break;

            }

            // BONTCTreeWalker.g:389:24: ( 'persistent' )?
            int alt70=2;
            int LA70_0 = input.LA(1);

            if ( (LA70_0==220) ) {
                alt70=1;
            }
            switch (alt70) {
                case 1 :
                    // BONTCTreeWalker.g:389:25: 'persistent'
                    {
                    match(input,220,FOLLOW_220_in_classX5539); 

                    }
                    break;

            }

            // BONTCTreeWalker.g:389:41: ( 'interfaced' )?
            int alt71=2;
            int LA71_0 = input.LA(1);

            if ( (LA71_0==221) ) {
                alt71=1;
            }
            switch (alt71) {
                case 1 :
                    // BONTCTreeWalker.g:389:42: 'interfaced'
                    {
                    match(input,221,FOLLOW_221_in_classX5545); 

                    }
                    break;

            }

            // BONTCTreeWalker.g:389:57: ( COMMENT )?
            int alt72=2;
            int LA72_0 = input.LA(1);

            if ( (LA72_0==COMMENT) ) {
                alt72=1;
            }
            switch (alt72) {
                case 1 :
                    // BONTCTreeWalker.g:389:58: COMMENT
                    {
                    match(input,COMMENT,FOLLOW_COMMENT_in_classX5550); 

                    }
                    break;

            }

            // BONTCTreeWalker.g:390:12: ( class_interface )?
            int alt73=2;
            int LA73_0 = input.LA(1);

            if ( (LA73_0==CLASS_INTERFACE) ) {
                alt73=1;
            }
            switch (alt73) {
                case 1 :
                    // BONTCTreeWalker.g:390:13: class_interface
                    {
                    pushFollow(FOLLOW_class_interface_in_classX5566);
                    class_interface();
                    _fsp--;


                    }
                    break;

            }

             getContext().leaveClass(); 

            match(input, Token.UP, null); 

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
    // $ANTLR end classX


    // $ANTLR start static_relation
    // BONTCTreeWalker.g:395:1: static_relation : ( ^( STATIC_RELATION inheritance_relation ) | ^( STATIC_RELATION client_relation ) );
    public final void static_relation() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:395:18: ( ^( STATIC_RELATION inheritance_relation ) | ^( STATIC_RELATION client_relation ) )
            int alt74=2;
            int LA74_0 = input.LA(1);

            if ( (LA74_0==STATIC_RELATION) ) {
                int LA74_1 = input.LA(2);

                if ( (LA74_1==DOWN) ) {
                    int LA74_2 = input.LA(3);

                    if ( (LA74_2==INHERITENCE_RELATION) ) {
                        alt74=1;
                    }
                    else if ( (LA74_2==CLIENT_RELATION) ) {
                        alt74=2;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("395:1: static_relation : ( ^( STATIC_RELATION inheritance_relation ) | ^( STATIC_RELATION client_relation ) );", 74, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("395:1: static_relation : ( ^( STATIC_RELATION inheritance_relation ) | ^( STATIC_RELATION client_relation ) );", 74, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("395:1: static_relation : ( ^( STATIC_RELATION inheritance_relation ) | ^( STATIC_RELATION client_relation ) );", 74, 0, input);

                throw nvae;
            }
            switch (alt74) {
                case 1 :
                    // BONTCTreeWalker.g:395:19: ^( STATIC_RELATION inheritance_relation )
                    {
                    match(input,STATIC_RELATION,FOLLOW_STATIC_RELATION_in_static_relation5645); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_inheritance_relation_in_static_relation5647);
                    inheritance_relation();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:399:19: ^( STATIC_RELATION client_relation )
                    {
                    match(input,STATIC_RELATION,FOLLOW_STATIC_RELATION_in_static_relation5730); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_client_relation_in_static_relation5732);
                    client_relation();
                    _fsp--;


                    match(input, Token.UP, null); 

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
    // $ANTLR end static_relation


    // $ANTLR start inheritance_relation
    // BONTCTreeWalker.g:404:1: inheritance_relation : ^( INHERITENCE_RELATION child ( multiplicity )? parent ( semantic_label )? ) ;
    public final void inheritance_relation() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:406:23: ( ^( INHERITENCE_RELATION child ( multiplicity )? parent ( semantic_label )? ) )
            // BONTCTreeWalker.g:406:24: ^( INHERITENCE_RELATION child ( multiplicity )? parent ( semantic_label )? )
            {
            match(input,INHERITENCE_RELATION,FOLLOW_INHERITENCE_RELATION_in_inheritance_relation5809); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_child_in_inheritance_relation5836);
            child();
            _fsp--;

            // BONTCTreeWalker.g:408:32: ( multiplicity )?
            int alt75=2;
            int LA75_0 = input.LA(1);

            if ( (LA75_0==MULTIPLICITY) ) {
                alt75=1;
            }
            switch (alt75) {
                case 1 :
                    // BONTCTreeWalker.g:408:33: multiplicity
                    {
                    pushFollow(FOLLOW_multiplicity_in_inheritance_relation5839);
                    multiplicity();
                    _fsp--;


                    }
                    break;

            }

            pushFollow(FOLLOW_parent_in_inheritance_relation5869);
            parent();
            _fsp--;

            // BONTCTreeWalker.g:409:33: ( semantic_label )?
            int alt76=2;
            int LA76_0 = input.LA(1);

            if ( (LA76_0==SEMANTIC_LABEL) ) {
                alt76=1;
            }
            switch (alt76) {
                case 1 :
                    // BONTCTreeWalker.g:409:34: semantic_label
                    {
                    pushFollow(FOLLOW_semantic_label_in_inheritance_relation5872);
                    semantic_label();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end inheritance_relation


    // $ANTLR start client_relation
    // BONTCTreeWalker.g:413:1: client_relation : ^( CLIENT_RELATION client ( client_entities )? ( type_mark )? supplier ( semantic_label )? ) ;
    public final void client_relation() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:413:18: ( ^( CLIENT_RELATION client ( client_entities )? ( type_mark )? supplier ( semantic_label )? ) )
            // BONTCTreeWalker.g:413:19: ^( CLIENT_RELATION client ( client_entities )? ( type_mark )? supplier ( semantic_label )? )
            {
            match(input,CLIENT_RELATION,FOLLOW_CLIENT_RELATION_in_client_relation5973); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_client_in_client_relation5995);
            client();
            _fsp--;

            // BONTCTreeWalker.g:415:28: ( client_entities )?
            int alt77=2;
            int LA77_0 = input.LA(1);

            if ( (LA77_0==CLIENT_ENTITIES) ) {
                alt77=1;
            }
            switch (alt77) {
                case 1 :
                    // BONTCTreeWalker.g:415:29: client_entities
                    {
                    pushFollow(FOLLOW_client_entities_in_client_relation5998);
                    client_entities();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:415:47: ( type_mark )?
            int alt78=2;
            int LA78_0 = input.LA(1);

            if ( (LA78_0==TYPE_MARK) ) {
                alt78=1;
            }
            switch (alt78) {
                case 1 :
                    // BONTCTreeWalker.g:415:48: type_mark
                    {
                    pushFollow(FOLLOW_type_mark_in_client_relation6003);
                    type_mark();
                    _fsp--;


                    }
                    break;

            }

            pushFollow(FOLLOW_supplier_in_client_relation6028);
            supplier();
            _fsp--;

            // BONTCTreeWalker.g:416:30: ( semantic_label )?
            int alt79=2;
            int LA79_0 = input.LA(1);

            if ( (LA79_0==SEMANTIC_LABEL) ) {
                alt79=1;
            }
            switch (alt79) {
                case 1 :
                    // BONTCTreeWalker.g:416:31: semantic_label
                    {
                    pushFollow(FOLLOW_semantic_label_in_client_relation6031);
                    semantic_label();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end client_relation


    // $ANTLR start client_entities
    // BONTCTreeWalker.g:420:1: client_entities : ^( CLIENT_ENTITIES client_entity_expression ) ;
    public final void client_entities() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:420:18: ( ^( CLIENT_ENTITIES client_entity_expression ) )
            // BONTCTreeWalker.g:420:19: ^( CLIENT_ENTITIES client_entity_expression )
            {
            match(input,CLIENT_ENTITIES,FOLLOW_CLIENT_ENTITIES_in_client_entities6120); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_client_entity_expression_in_client_entities6142);
            client_entity_expression();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end client_entities


    // $ANTLR start client_entity_expression
    // BONTCTreeWalker.g:426:1: client_entity_expression : ( ^( CLIENT_ENTITY_EXPRESSION client_entity_list ) | ^( CLIENT_ENTITY_EXPRESSION multiplicity ) );
    public final void client_entity_expression() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:426:27: ( ^( CLIENT_ENTITY_EXPRESSION client_entity_list ) | ^( CLIENT_ENTITY_EXPRESSION multiplicity ) )
            int alt80=2;
            int LA80_0 = input.LA(1);

            if ( (LA80_0==CLIENT_ENTITY_EXPRESSION) ) {
                int LA80_1 = input.LA(2);

                if ( (LA80_1==DOWN) ) {
                    int LA80_2 = input.LA(3);

                    if ( (LA80_2==CLIENT_ENTITY_LIST) ) {
                        alt80=1;
                    }
                    else if ( (LA80_2==MULTIPLICITY) ) {
                        alt80=2;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("426:1: client_entity_expression : ( ^( CLIENT_ENTITY_EXPRESSION client_entity_list ) | ^( CLIENT_ENTITY_EXPRESSION multiplicity ) );", 80, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("426:1: client_entity_expression : ( ^( CLIENT_ENTITY_EXPRESSION client_entity_list ) | ^( CLIENT_ENTITY_EXPRESSION multiplicity ) );", 80, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("426:1: client_entity_expression : ( ^( CLIENT_ENTITY_EXPRESSION client_entity_list ) | ^( CLIENT_ENTITY_EXPRESSION multiplicity ) );", 80, 0, input);

                throw nvae;
            }
            switch (alt80) {
                case 1 :
                    // BONTCTreeWalker.g:426:28: ^( CLIENT_ENTITY_EXPRESSION client_entity_list )
                    {
                    match(input,CLIENT_ENTITY_EXPRESSION,FOLLOW_CLIENT_ENTITY_EXPRESSION_in_client_entity_expression6237); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_client_entity_list_in_client_entity_expression6239);
                    client_entity_list();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:430:28: ^( CLIENT_ENTITY_EXPRESSION multiplicity )
                    {
                    match(input,CLIENT_ENTITY_EXPRESSION,FOLLOW_CLIENT_ENTITY_EXPRESSION_in_client_entity_expression6358); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_multiplicity_in_client_entity_expression6360);
                    multiplicity();
                    _fsp--;


                    match(input, Token.UP, null); 

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
    // $ANTLR end client_entity_expression


    // $ANTLR start client_entity_list
    // BONTCTreeWalker.g:435:1: client_entity_list : ^( CLIENT_ENTITY_LIST ( client_entity )+ ) ;
    public final void client_entity_list() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:435:21: ( ^( CLIENT_ENTITY_LIST ( client_entity )+ ) )
            // BONTCTreeWalker.g:435:22: ^( CLIENT_ENTITY_LIST ( client_entity )+ )
            {
            match(input,CLIENT_ENTITY_LIST,FOLLOW_CLIENT_ENTITY_LIST_in_client_entity_list6476); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:436:43: ( client_entity )+
            int cnt81=0;
            loop81:
            do {
                int alt81=2;
                int LA81_0 = input.LA(1);

                if ( (LA81_0==CLIENT_ENTITY) ) {
                    alt81=1;
                }


                switch (alt81) {
            	case 1 :
            	    // BONTCTreeWalker.g:436:44: client_entity
            	    {
            	    pushFollow(FOLLOW_client_entity_in_client_entity_list6479);
            	    client_entity();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt81 >= 1 ) break loop81;
                        EarlyExitException eee =
                            new EarlyExitException(81, input);
                        throw eee;
                }
                cnt81++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end client_entity_list


    // $ANTLR start client_entity
    // BONTCTreeWalker.g:440:1: client_entity : ( ^( CLIENT_ENTITY prefix ) | ^( CLIENT_ENTITY infix ) | ^( CLIENT_ENTITY supplier_indirection ) | ^( CLIENT_ENTITY parent_indirection ) );
    public final void client_entity() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:440:16: ( ^( CLIENT_ENTITY prefix ) | ^( CLIENT_ENTITY infix ) | ^( CLIENT_ENTITY supplier_indirection ) | ^( CLIENT_ENTITY parent_indirection ) )
            int alt82=4;
            int LA82_0 = input.LA(1);

            if ( (LA82_0==CLIENT_ENTITY) ) {
                int LA82_1 = input.LA(2);

                if ( (LA82_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case SUPPLIER_INDIRECTION:
                        {
                        alt82=3;
                        }
                        break;
                    case PREFIX:
                        {
                        alt82=1;
                        }
                        break;
                    case PARENT_INDIRECTION:
                        {
                        alt82=4;
                        }
                        break;
                    case INFIX:
                        {
                        alt82=2;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("440:1: client_entity : ( ^( CLIENT_ENTITY prefix ) | ^( CLIENT_ENTITY infix ) | ^( CLIENT_ENTITY supplier_indirection ) | ^( CLIENT_ENTITY parent_indirection ) );", 82, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("440:1: client_entity : ( ^( CLIENT_ENTITY prefix ) | ^( CLIENT_ENTITY infix ) | ^( CLIENT_ENTITY supplier_indirection ) | ^( CLIENT_ENTITY parent_indirection ) );", 82, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("440:1: client_entity : ( ^( CLIENT_ENTITY prefix ) | ^( CLIENT_ENTITY infix ) | ^( CLIENT_ENTITY supplier_indirection ) | ^( CLIENT_ENTITY parent_indirection ) );", 82, 0, input);

                throw nvae;
            }
            switch (alt82) {
                case 1 :
                    // BONTCTreeWalker.g:440:19: ^( CLIENT_ENTITY prefix )
                    {
                    match(input,CLIENT_ENTITY,FOLLOW_CLIENT_ENTITY_in_client_entity6578); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_prefix_in_client_entity6580);
                    prefix();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:444:19: ^( CLIENT_ENTITY infix )
                    {
                    match(input,CLIENT_ENTITY,FOLLOW_CLIENT_ENTITY_in_client_entity6664); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_infix_in_client_entity6666);
                    infix();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 3 :
                    // BONTCTreeWalker.g:448:19: ^( CLIENT_ENTITY supplier_indirection )
                    {
                    match(input,CLIENT_ENTITY,FOLLOW_CLIENT_ENTITY_in_client_entity6750); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_supplier_indirection_in_client_entity6752);
                    supplier_indirection();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 4 :
                    // BONTCTreeWalker.g:452:19: ^( CLIENT_ENTITY parent_indirection )
                    {
                    match(input,CLIENT_ENTITY,FOLLOW_CLIENT_ENTITY_in_client_entity6836); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_parent_indirection_in_client_entity6838);
                    parent_indirection();
                    _fsp--;


                    match(input, Token.UP, null); 

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
    // $ANTLR end client_entity


    // $ANTLR start supplier_indirection
    // BONTCTreeWalker.g:457:1: supplier_indirection : ^( SUPPLIER_INDIRECTION ( indirection_feature_part )? generic_indirection ) ;
    public final void supplier_indirection() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:457:23: ( ^( SUPPLIER_INDIRECTION ( indirection_feature_part )? generic_indirection ) )
            // BONTCTreeWalker.g:457:24: ^( SUPPLIER_INDIRECTION ( indirection_feature_part )? generic_indirection )
            {
            match(input,SUPPLIER_INDIRECTION,FOLLOW_SUPPLIER_INDIRECTION_in_supplier_indirection6925); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:458:47: ( indirection_feature_part )?
            int alt83=2;
            int LA83_0 = input.LA(1);

            if ( (LA83_0==INDIRECTION_FEATURE_PART) ) {
                alt83=1;
            }
            switch (alt83) {
                case 1 :
                    // BONTCTreeWalker.g:458:48: indirection_feature_part
                    {
                    pushFollow(FOLLOW_indirection_feature_part_in_supplier_indirection6928);
                    indirection_feature_part();
                    _fsp--;


                    }
                    break;

            }

            pushFollow(FOLLOW_generic_indirection_in_supplier_indirection6932);
            generic_indirection();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end supplier_indirection


    // $ANTLR start indirection_feature_part
    // BONTCTreeWalker.g:462:1: indirection_feature_part : ( ^( INDIRECTION_FEATURE_PART feature_name ) | ^( INDIRECTION_FEATURE_PART indirection_feature_list ) );
    public final void indirection_feature_part() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:462:27: ( ^( INDIRECTION_FEATURE_PART feature_name ) | ^( INDIRECTION_FEATURE_PART indirection_feature_list ) )
            int alt84=2;
            int LA84_0 = input.LA(1);

            if ( (LA84_0==INDIRECTION_FEATURE_PART) ) {
                int LA84_1 = input.LA(2);

                if ( (LA84_1==DOWN) ) {
                    int LA84_2 = input.LA(3);

                    if ( (LA84_2==FEATURE_NAME) ) {
                        alt84=1;
                    }
                    else if ( (LA84_2==INDIRECTION_FEATURE_LIST) ) {
                        alt84=2;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("462:1: indirection_feature_part : ( ^( INDIRECTION_FEATURE_PART feature_name ) | ^( INDIRECTION_FEATURE_PART indirection_feature_list ) );", 84, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("462:1: indirection_feature_part : ( ^( INDIRECTION_FEATURE_PART feature_name ) | ^( INDIRECTION_FEATURE_PART indirection_feature_list ) );", 84, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("462:1: indirection_feature_part : ( ^( INDIRECTION_FEATURE_PART feature_name ) | ^( INDIRECTION_FEATURE_PART indirection_feature_list ) );", 84, 0, input);

                throw nvae;
            }
            switch (alt84) {
                case 1 :
                    // BONTCTreeWalker.g:462:28: ^( INDIRECTION_FEATURE_PART feature_name )
                    {
                    match(input,INDIRECTION_FEATURE_PART,FOLLOW_INDIRECTION_FEATURE_PART_in_indirection_feature_part7043); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_feature_name_in_indirection_feature_part7045);
                    feature_name();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:466:28: ^( INDIRECTION_FEATURE_PART indirection_feature_list )
                    {
                    match(input,INDIRECTION_FEATURE_PART,FOLLOW_INDIRECTION_FEATURE_PART_in_indirection_feature_part7164); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_indirection_feature_list_in_indirection_feature_part7166);
                    indirection_feature_list();
                    _fsp--;


                    match(input, Token.UP, null); 

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
    // $ANTLR end indirection_feature_part


    // $ANTLR start indirection_feature_list
    // BONTCTreeWalker.g:471:1: indirection_feature_list : ^( INDIRECTION_FEATURE_LIST feature_name_list ) ;
    public final void indirection_feature_list() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:471:27: ( ^( INDIRECTION_FEATURE_LIST feature_name_list ) )
            // BONTCTreeWalker.g:471:28: ^( INDIRECTION_FEATURE_LIST feature_name_list )
            {
            match(input,INDIRECTION_FEATURE_LIST,FOLLOW_INDIRECTION_FEATURE_LIST_in_indirection_feature_list7289); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_feature_name_list_in_indirection_feature_list7291);
            feature_name_list();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end indirection_feature_list


    // $ANTLR start parent_indirection
    // BONTCTreeWalker.g:476:1: parent_indirection : ^( PARENT_INDIRECTION generic_indirection ) ;
    public final void parent_indirection() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:476:21: ( ^( PARENT_INDIRECTION generic_indirection ) )
            // BONTCTreeWalker.g:476:22: ^( PARENT_INDIRECTION generic_indirection )
            {
            match(input,PARENT_INDIRECTION,FOLLOW_PARENT_INDIRECTION_in_parent_indirection7407); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_generic_indirection_in_parent_indirection7409);
            generic_indirection();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end parent_indirection


    // $ANTLR start generic_indirection
    // BONTCTreeWalker.g:481:1: generic_indirection : ^( GENERIC_INDIRECTION indirection_element ) ;
    public final void generic_indirection() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:483:22: ( ^( GENERIC_INDIRECTION indirection_element ) )
            // BONTCTreeWalker.g:488:23: ^( GENERIC_INDIRECTION indirection_element )
            {
            match(input,GENERIC_INDIRECTION,FOLLOW_GENERIC_INDIRECTION_in_generic_indirection7518); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_indirection_element_in_generic_indirection7520);
            indirection_element();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end generic_indirection


    // $ANTLR start named_indirection
    // BONTCTreeWalker.g:493:1: named_indirection : ( ^( NAMED_INDIRECTION class_name indirection_list ) | ^( NAMED_INDIRECTION PARSE_ERROR ) );
    public final void named_indirection() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:493:20: ( ^( NAMED_INDIRECTION class_name indirection_list ) | ^( NAMED_INDIRECTION PARSE_ERROR ) )
            int alt85=2;
            int LA85_0 = input.LA(1);

            if ( (LA85_0==NAMED_INDIRECTION) ) {
                int LA85_1 = input.LA(2);

                if ( (LA85_1==DOWN) ) {
                    int LA85_2 = input.LA(3);

                    if ( (LA85_2==PARSE_ERROR) ) {
                        alt85=2;
                    }
                    else if ( (LA85_2==CLASS_NAME) ) {
                        alt85=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("493:1: named_indirection : ( ^( NAMED_INDIRECTION class_name indirection_list ) | ^( NAMED_INDIRECTION PARSE_ERROR ) );", 85, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("493:1: named_indirection : ( ^( NAMED_INDIRECTION class_name indirection_list ) | ^( NAMED_INDIRECTION PARSE_ERROR ) );", 85, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("493:1: named_indirection : ( ^( NAMED_INDIRECTION class_name indirection_list ) | ^( NAMED_INDIRECTION PARSE_ERROR ) );", 85, 0, input);

                throw nvae;
            }
            switch (alt85) {
                case 1 :
                    // BONTCTreeWalker.g:493:21: ^( NAMED_INDIRECTION class_name indirection_list )
                    {
                    match(input,NAMED_INDIRECTION,FOLLOW_NAMED_INDIRECTION_in_named_indirection7620); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_class_name_in_named_indirection7622);
                    class_name();
                    _fsp--;

                    pushFollow(FOLLOW_indirection_list_in_named_indirection7624);
                    indirection_list();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:497:21: ^( NAMED_INDIRECTION PARSE_ERROR )
                    {
                    match(input,NAMED_INDIRECTION,FOLLOW_NAMED_INDIRECTION_in_named_indirection7692); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_named_indirection7694); 

                    match(input, Token.UP, null); 

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
    // $ANTLR end named_indirection


    // $ANTLR start indirection_list
    // BONTCTreeWalker.g:500:1: indirection_list : ^( INDIRECTION_LIST ( indirection_element )+ ) ;
    public final void indirection_list() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:500:19: ( ^( INDIRECTION_LIST ( indirection_element )+ ) )
            // BONTCTreeWalker.g:500:20: ^( INDIRECTION_LIST ( indirection_element )+ )
            {
            match(input,INDIRECTION_LIST,FOLLOW_INDIRECTION_LIST_in_indirection_list7765); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:501:39: ( indirection_element )+
            int cnt86=0;
            loop86:
            do {
                int alt86=2;
                int LA86_0 = input.LA(1);

                if ( (LA86_0==INDIRECTION_ELEMENT) ) {
                    alt86=1;
                }


                switch (alt86) {
            	case 1 :
            	    // BONTCTreeWalker.g:501:40: indirection_element
            	    {
            	    pushFollow(FOLLOW_indirection_element_in_indirection_list7768);
            	    indirection_element();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt86 >= 1 ) break loop86;
                        EarlyExitException eee =
                            new EarlyExitException(86, input);
                        throw eee;
                }
                cnt86++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end indirection_list


    // $ANTLR start indirection_element
    // BONTCTreeWalker.g:505:1: indirection_element : ( ^( INDIRECTION_ELEMENT '...' ) | ^( INDIRECTION_ELEMENT named_indirection ) | ^( INDIRECTION_ELEMENT class_name ) );
    public final void indirection_element() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:505:22: ( ^( INDIRECTION_ELEMENT '...' ) | ^( INDIRECTION_ELEMENT named_indirection ) | ^( INDIRECTION_ELEMENT class_name ) )
            int alt87=3;
            int LA87_0 = input.LA(1);

            if ( (LA87_0==INDIRECTION_ELEMENT) ) {
                int LA87_1 = input.LA(2);

                if ( (LA87_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case 230:
                        {
                        alt87=1;
                        }
                        break;
                    case CLASS_NAME:
                        {
                        alt87=3;
                        }
                        break;
                    case NAMED_INDIRECTION:
                        {
                        alt87=2;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("505:1: indirection_element : ( ^( INDIRECTION_ELEMENT '...' ) | ^( INDIRECTION_ELEMENT named_indirection ) | ^( INDIRECTION_ELEMENT class_name ) );", 87, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("505:1: indirection_element : ( ^( INDIRECTION_ELEMENT '...' ) | ^( INDIRECTION_ELEMENT named_indirection ) | ^( INDIRECTION_ELEMENT class_name ) );", 87, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("505:1: indirection_element : ( ^( INDIRECTION_ELEMENT '...' ) | ^( INDIRECTION_ELEMENT named_indirection ) | ^( INDIRECTION_ELEMENT class_name ) );", 87, 0, input);

                throw nvae;
            }
            switch (alt87) {
                case 1 :
                    // BONTCTreeWalker.g:505:24: ^( INDIRECTION_ELEMENT '...' )
                    {
                    match(input,INDIRECTION_ELEMENT,FOLLOW_INDIRECTION_ELEMENT_in_indirection_element7865); 

                    match(input, Token.DOWN, null); 
                    match(input,230,FOLLOW_230_in_indirection_element7867); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:509:24: ^( INDIRECTION_ELEMENT named_indirection )
                    {
                    match(input,INDIRECTION_ELEMENT,FOLLOW_INDIRECTION_ELEMENT_in_indirection_element7970); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_named_indirection_in_indirection_element7972);
                    named_indirection();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 3 :
                    // BONTCTreeWalker.g:513:24: ^( INDIRECTION_ELEMENT class_name )
                    {
                    match(input,INDIRECTION_ELEMENT,FOLLOW_INDIRECTION_ELEMENT_in_indirection_element8075); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_class_name_in_indirection_element8077);
                    class_name();
                    _fsp--;


                    match(input, Token.UP, null); 

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
    // $ANTLR end indirection_element


    // $ANTLR start type_mark
    // BONTCTreeWalker.g:519:1: type_mark : ( ^( TYPE_MARK ':' ) | ^( TYPE_MARK ':{' ) | ^( TYPE_MARK shared_mark ) );
    public final void type_mark() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:519:12: ( ^( TYPE_MARK ':' ) | ^( TYPE_MARK ':{' ) | ^( TYPE_MARK shared_mark ) )
            int alt88=3;
            int LA88_0 = input.LA(1);

            if ( (LA88_0==TYPE_MARK) ) {
                int LA88_1 = input.LA(2);

                if ( (LA88_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case 231:
                        {
                        alt88=2;
                        }
                        break;
                    case 196:
                        {
                        alt88=1;
                        }
                        break;
                    case SHARED_MARK:
                        {
                        alt88=3;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("519:1: type_mark : ( ^( TYPE_MARK ':' ) | ^( TYPE_MARK ':{' ) | ^( TYPE_MARK shared_mark ) );", 88, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("519:1: type_mark : ( ^( TYPE_MARK ':' ) | ^( TYPE_MARK ':{' ) | ^( TYPE_MARK shared_mark ) );", 88, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("519:1: type_mark : ( ^( TYPE_MARK ':' ) | ^( TYPE_MARK ':{' ) | ^( TYPE_MARK shared_mark ) );", 88, 0, input);

                throw nvae;
            }
            switch (alt88) {
                case 1 :
                    // BONTCTreeWalker.g:519:13: ^( TYPE_MARK ':' )
                    {
                    match(input,TYPE_MARK,FOLLOW_TYPE_MARK_in_type_mark8171); 

                    match(input, Token.DOWN, null); 
                    match(input,196,FOLLOW_196_in_type_mark8173); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:523:13: ^( TYPE_MARK ':{' )
                    {
                    match(input,TYPE_MARK,FOLLOW_TYPE_MARK_in_type_mark8232); 

                    match(input, Token.DOWN, null); 
                    match(input,231,FOLLOW_231_in_type_mark8234); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 3 :
                    // BONTCTreeWalker.g:527:13: ^( TYPE_MARK shared_mark )
                    {
                    match(input,TYPE_MARK,FOLLOW_TYPE_MARK_in_type_mark8294); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_shared_mark_in_type_mark8296);
                    shared_mark();
                    _fsp--;


                    match(input, Token.UP, null); 

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
    // $ANTLR end type_mark


    // $ANTLR start shared_mark
    // BONTCTreeWalker.g:532:1: shared_mark : ^( SHARED_MARK multiplicity ) ;
    public final void shared_mark() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:532:14: ( ^( SHARED_MARK multiplicity ) )
            // BONTCTreeWalker.g:532:15: ^( SHARED_MARK multiplicity )
            {
            match(input,SHARED_MARK,FOLLOW_SHARED_MARK_in_shared_mark8360); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_multiplicity_in_shared_mark8362);
            multiplicity();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end shared_mark


    // $ANTLR start child
    // BONTCTreeWalker.g:537:1: child : ^( CHILD static_ref ) ;
    public final void child() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:539:8: ( ^( CHILD static_ref ) )
            // BONTCTreeWalker.g:539:9: ^( CHILD static_ref )
            {
            match(input,CHILD,FOLLOW_CHILD_in_child8416); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_static_ref_in_child8418);
            static_ref();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end child


    // $ANTLR start parent
    // BONTCTreeWalker.g:544:1: parent : ^( PARENT static_ref ) ;
    public final void parent() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:544:9: ( ^( PARENT static_ref ) )
            // BONTCTreeWalker.g:544:10: ^( PARENT static_ref )
            {
            match(input,PARENT,FOLLOW_PARENT_in_parent8465); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_static_ref_in_parent8467);
            static_ref();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end parent


    // $ANTLR start client
    // BONTCTreeWalker.g:549:1: client : ^( CLIENT static_ref ) ;
    public final void client() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:549:9: ( ^( CLIENT static_ref ) )
            // BONTCTreeWalker.g:549:10: ^( CLIENT static_ref )
            {
            match(input,CLIENT,FOLLOW_CLIENT_in_client8517); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_static_ref_in_client8519);
            static_ref();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end client


    // $ANTLR start supplier
    // BONTCTreeWalker.g:554:1: supplier : ^( SUPPLIER static_ref ) ;
    public final void supplier() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:554:11: ( ^( SUPPLIER static_ref ) )
            // BONTCTreeWalker.g:554:12: ^( SUPPLIER static_ref )
            {
            match(input,SUPPLIER,FOLLOW_SUPPLIER_in_supplier8571); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_static_ref_in_supplier8573);
            static_ref();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end supplier


    // $ANTLR start static_ref
    // BONTCTreeWalker.g:559:1: static_ref : ( ^( STATIC_REF p= cluster_prefix n= static_component_name ) | ^( STATIC_REF n= static_component_name ) );
    public final void static_ref() throws RecognitionException {
        cluster_prefix_return p = null;

        static_component_name_return n = null;


        try {
            // BONTCTreeWalker.g:559:13: ( ^( STATIC_REF p= cluster_prefix n= static_component_name ) | ^( STATIC_REF n= static_component_name ) )
            int alt89=2;
            int LA89_0 = input.LA(1);

            if ( (LA89_0==STATIC_REF) ) {
                int LA89_1 = input.LA(2);

                if ( (LA89_1==DOWN) ) {
                    int LA89_2 = input.LA(3);

                    if ( (LA89_2==CLUSTER_PREFIX) ) {
                        alt89=1;
                    }
                    else if ( (LA89_2==STATIC_COMPONENT_NAME) ) {
                        alt89=2;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("559:1: static_ref : ( ^( STATIC_REF p= cluster_prefix n= static_component_name ) | ^( STATIC_REF n= static_component_name ) );", 89, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("559:1: static_ref : ( ^( STATIC_REF p= cluster_prefix n= static_component_name ) | ^( STATIC_REF n= static_component_name ) );", 89, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("559:1: static_ref : ( ^( STATIC_REF p= cluster_prefix n= static_component_name ) | ^( STATIC_REF n= static_component_name ) );", 89, 0, input);

                throw nvae;
            }
            switch (alt89) {
                case 1 :
                    // BONTCTreeWalker.g:559:15: ^( STATIC_REF p= cluster_prefix n= static_component_name )
                    {
                    match(input,STATIC_REF,FOLLOW_STATIC_REF_in_static_ref8635); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_cluster_prefix_in_static_ref8639);
                    p=cluster_prefix();
                    _fsp--;

                    pushFollow(FOLLOW_static_component_name_in_static_ref8643);
                    n=static_component_name();
                    _fsp--;

                     getFTC().checkValidStaticRef(input.getTokenStream().toString(
                      input.getTreeAdaptor().getTokenStartIndex(p.start),
                      input.getTreeAdaptor().getTokenStopIndex(p.start)),getSLoc(((CommonTree)p.start).token),input.getTokenStream().toString(
                      input.getTreeAdaptor().getTokenStartIndex(n.start),
                      input.getTreeAdaptor().getTokenStopIndex(n.start)),getSLoc(((CommonTree)n.start).token)); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:564:15: ^( STATIC_REF n= static_component_name )
                    {
                    match(input,STATIC_REF,FOLLOW_STATIC_REF_in_static_ref8728); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_static_component_name_in_static_ref8732);
                    n=static_component_name();
                    _fsp--;

                     getFTC().checkValidStaticRef(null,null,input.getTokenStream().toString(
                      input.getTreeAdaptor().getTokenStartIndex(n.start),
                      input.getTreeAdaptor().getTokenStopIndex(n.start)),getSLoc(((CommonTree)n.start).token)); 

                    match(input, Token.UP, null); 

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
    // $ANTLR end static_ref

    public static class cluster_prefix_return extends TreeRuleReturnScope {
    };

    // $ANTLR start cluster_prefix
    // BONTCTreeWalker.g:570:1: cluster_prefix : ^( CLUSTER_PREFIX ( cluster_name )+ ) ;
    public final cluster_prefix_return cluster_prefix() throws RecognitionException {
        cluster_prefix_return retval = new cluster_prefix_return();
        retval.start = input.LT(1);

        try {
            // BONTCTreeWalker.g:570:17: ( ^( CLUSTER_PREFIX ( cluster_name )+ ) )
            // BONTCTreeWalker.g:570:18: ^( CLUSTER_PREFIX ( cluster_name )+ )
            {
            match(input,CLUSTER_PREFIX,FOLLOW_CLUSTER_PREFIX_in_cluster_prefix8821); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:571:35: ( cluster_name )+
            int cnt90=0;
            loop90:
            do {
                int alt90=2;
                int LA90_0 = input.LA(1);

                if ( (LA90_0==CLUSTER_NAME) ) {
                    alt90=1;
                }


                switch (alt90) {
            	case 1 :
            	    // BONTCTreeWalker.g:571:36: cluster_name
            	    {
            	    pushFollow(FOLLOW_cluster_name_in_cluster_prefix8824);
            	    cluster_name();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt90 >= 1 ) break loop90;
                        EarlyExitException eee =
                            new EarlyExitException(90, input);
                        throw eee;
                }
                cnt90++;
            } while (true);


            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end cluster_prefix

    public static class static_component_name_return extends TreeRuleReturnScope {
    };

    // $ANTLR start static_component_name
    // BONTCTreeWalker.g:575:1: static_component_name : ^( STATIC_COMPONENT_NAME IDENTIFIER ) ;
    public final static_component_name_return static_component_name() throws RecognitionException {
        static_component_name_return retval = new static_component_name_return();
        retval.start = input.LT(1);

        try {
            // BONTCTreeWalker.g:575:24: ( ^( STATIC_COMPONENT_NAME IDENTIFIER ) )
            // BONTCTreeWalker.g:575:25: ^( STATIC_COMPONENT_NAME IDENTIFIER )
            {
            match(input,STATIC_COMPONENT_NAME,FOLLOW_STATIC_COMPONENT_NAME_in_static_component_name8901); 

            match(input, Token.DOWN, null); 
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_static_component_name8903); 

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end static_component_name


    // $ANTLR start multiplicity
    // BONTCTreeWalker.g:580:1: multiplicity : ^( MULTIPLICITY INTEGER ) ;
    public final void multiplicity() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:580:15: ( ^( MULTIPLICITY INTEGER ) )
            // BONTCTreeWalker.g:580:16: ^( MULTIPLICITY INTEGER )
            {
            match(input,MULTIPLICITY,FOLLOW_MULTIPLICITY_in_multiplicity9004); 

            match(input, Token.DOWN, null); 
            match(input,INTEGER,FOLLOW_INTEGER_in_multiplicity9006); 

            match(input, Token.UP, null); 

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
    // $ANTLR end multiplicity


    // $ANTLR start semantic_label
    // BONTCTreeWalker.g:585:1: semantic_label : ^( SEMANTIC_LABEL MANIFEST_STRING ) ;
    public final void semantic_label() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:585:17: ( ^( SEMANTIC_LABEL MANIFEST_STRING ) )
            // BONTCTreeWalker.g:585:18: ^( SEMANTIC_LABEL MANIFEST_STRING )
            {
            match(input,SEMANTIC_LABEL,FOLLOW_SEMANTIC_LABEL_in_semantic_label9082); 

            match(input, Token.DOWN, null); 
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_semantic_label9084); 

            match(input, Token.UP, null); 

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
    // $ANTLR end semantic_label


    // $ANTLR start class_interface
    // BONTCTreeWalker.g:590:1: class_interface : ^( CLASS_INTERFACE ( indexing )? ( parent_class_list )? features ( class_invariant )? ) ;
    public final void class_interface() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:594:18: ( ^( CLASS_INTERFACE ( indexing )? ( parent_class_list )? features ( class_invariant )? ) )
            // BONTCTreeWalker.g:594:19: ^( CLASS_INTERFACE ( indexing )? ( parent_class_list )? features ( class_invariant )? )
            {
            match(input,CLASS_INTERFACE,FOLLOW_CLASS_INTERFACE_in_class_interface9154); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:596:21: ( indexing )?
            int alt91=2;
            int LA91_0 = input.LA(1);

            if ( (LA91_0==INDEXING) ) {
                alt91=1;
            }
            switch (alt91) {
                case 1 :
                    // BONTCTreeWalker.g:596:22: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_class_interface9177);
                    indexing();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:597:21: ( parent_class_list )?
            int alt92=2;
            int LA92_0 = input.LA(1);

            if ( (LA92_0==PARENT_CLASS_LIST) ) {
                alt92=1;
            }
            switch (alt92) {
                case 1 :
                    // BONTCTreeWalker.g:597:22: parent_class_list
                    {
                    pushFollow(FOLLOW_parent_class_list_in_class_interface9202);
                    parent_class_list();
                    _fsp--;


                    }
                    break;

            }

            pushFollow(FOLLOW_features_in_class_interface9226);
            features();
            _fsp--;

            // BONTCTreeWalker.g:599:21: ( class_invariant )?
            int alt93=2;
            int LA93_0 = input.LA(1);

            if ( (LA93_0==CLASS_INVARIANT) ) {
                alt93=1;
            }
            switch (alt93) {
                case 1 :
                    // BONTCTreeWalker.g:599:22: class_invariant
                    {
                    pushFollow(FOLLOW_class_invariant_in_class_interface9249);
                    class_invariant();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end class_interface


    // $ANTLR start class_invariant
    // BONTCTreeWalker.g:603:1: class_invariant : ^( CLASS_INVARIANT assertion ) ;
    public final void class_invariant() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:603:18: ( ^( CLASS_INVARIANT assertion ) )
            // BONTCTreeWalker.g:603:19: ^( CLASS_INVARIANT assertion )
            {
            match(input,CLASS_INVARIANT,FOLLOW_CLASS_INVARIANT_in_class_invariant9340); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_assertion_in_class_invariant9342);
            assertion();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end class_invariant


    // $ANTLR start parent_class_list
    // BONTCTreeWalker.g:608:1: parent_class_list : ( ^( PARENT_CLASS_LIST ( class_type )+ ) | ^( PARENT_CLASS_LIST PARSE_ERROR ) );
    public final void parent_class_list() throws RecognitionException {
        class_type_return class_type12 = null;


        try {
            // BONTCTreeWalker.g:608:20: ( ^( PARENT_CLASS_LIST ( class_type )+ ) | ^( PARENT_CLASS_LIST PARSE_ERROR ) )
            int alt95=2;
            int LA95_0 = input.LA(1);

            if ( (LA95_0==PARENT_CLASS_LIST) ) {
                int LA95_1 = input.LA(2);

                if ( (LA95_1==DOWN) ) {
                    int LA95_2 = input.LA(3);

                    if ( (LA95_2==PARSE_ERROR) ) {
                        alt95=2;
                    }
                    else if ( (LA95_2==CLASS_TYPE) ) {
                        alt95=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("608:1: parent_class_list : ( ^( PARENT_CLASS_LIST ( class_type )+ ) | ^( PARENT_CLASS_LIST PARSE_ERROR ) );", 95, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("608:1: parent_class_list : ( ^( PARENT_CLASS_LIST ( class_type )+ ) | ^( PARENT_CLASS_LIST PARSE_ERROR ) );", 95, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("608:1: parent_class_list : ( ^( PARENT_CLASS_LIST ( class_type )+ ) | ^( PARENT_CLASS_LIST PARSE_ERROR ) );", 95, 0, input);

                throw nvae;
            }
            switch (alt95) {
                case 1 :
                    // BONTCTreeWalker.g:608:21: ^( PARENT_CLASS_LIST ( class_type )+ )
                    {
                    match(input,PARENT_CLASS_LIST,FOLLOW_PARENT_CLASS_LIST_in_parent_class_list9430); 

                    match(input, Token.DOWN, null); 
                    // BONTCTreeWalker.g:609:41: ( class_type )+
                    int cnt94=0;
                    loop94:
                    do {
                        int alt94=2;
                        int LA94_0 = input.LA(1);

                        if ( (LA94_0==CLASS_TYPE) ) {
                            alt94=1;
                        }


                        switch (alt94) {
                    	case 1 :
                    	    // BONTCTreeWalker.g:609:42: class_type
                    	    {
                    	    pushFollow(FOLLOW_class_type_in_parent_class_list9433);
                    	    class_type12=class_type();
                    	    _fsp--;

                    	     getFTC().checkValidClassType(input.getTokenStream().toString(
                    	      input.getTreeAdaptor().getTokenStartIndex(class_type12.start),
                    	      input.getTreeAdaptor().getTokenStopIndex(class_type12.start)),getSLoc(((CommonTree)class_type12.start).token),true); 

                    	    }
                    	    break;

                    	default :
                    	    if ( cnt94 >= 1 ) break loop94;
                                EarlyExitException eee =
                                    new EarlyExitException(94, input);
                                throw eee;
                        }
                        cnt94++;
                    } while (true);


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:612:21: ^( PARENT_CLASS_LIST PARSE_ERROR )
                    {
                    match(input,PARENT_CLASS_LIST,FOLLOW_PARENT_CLASS_LIST_in_parent_class_list9506); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_parent_class_list9508); 

                    match(input, Token.UP, null); 

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
    // $ANTLR end parent_class_list


    // $ANTLR start features
    // BONTCTreeWalker.g:615:1: features : ^( FEATURES ( feature_clause )+ ) ;
    public final void features() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:615:11: ( ^( FEATURES ( feature_clause )+ ) )
            // BONTCTreeWalker.g:615:12: ^( FEATURES ( feature_clause )+ )
            {
            match(input,FEATURES,FOLLOW_FEATURES_in_features9572); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:616:23: ( feature_clause )+
            int cnt96=0;
            loop96:
            do {
                int alt96=2;
                int LA96_0 = input.LA(1);

                if ( (LA96_0==FEATURE_CLAUSE) ) {
                    alt96=1;
                }


                switch (alt96) {
            	case 1 :
            	    // BONTCTreeWalker.g:616:24: feature_clause
            	    {
            	    pushFollow(FOLLOW_feature_clause_in_features9575);
            	    feature_clause();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt96 >= 1 ) break loop96;
                        EarlyExitException eee =
                            new EarlyExitException(96, input);
                        throw eee;
                }
                cnt96++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end features


    // $ANTLR start feature_clause
    // BONTCTreeWalker.g:620:1: feature_clause : ^( FEATURE_CLAUSE ( selective_export )? ( COMMENT )? feature_specifications ) ;
    public final void feature_clause() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:622:17: ( ^( FEATURE_CLAUSE ( selective_export )? ( COMMENT )? feature_specifications ) )
            // BONTCTreeWalker.g:622:18: ^( FEATURE_CLAUSE ( selective_export )? ( COMMENT )? feature_specifications )
            {
            match(input,FEATURE_CLAUSE,FOLLOW_FEATURE_CLAUSE_in_feature_clause9644); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:624:20: ( selective_export )?
            int alt97=2;
            int LA97_0 = input.LA(1);

            if ( (LA97_0==SELECTIVE_EXPORT) ) {
                alt97=1;
            }
            switch (alt97) {
                case 1 :
                    // BONTCTreeWalker.g:624:21: selective_export
                    {
                    pushFollow(FOLLOW_selective_export_in_feature_clause9666);
                    selective_export();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:625:20: ( COMMENT )?
            int alt98=2;
            int LA98_0 = input.LA(1);

            if ( (LA98_0==COMMENT) ) {
                alt98=1;
            }
            switch (alt98) {
                case 1 :
                    // BONTCTreeWalker.g:625:21: COMMENT
                    {
                    match(input,COMMENT,FOLLOW_COMMENT_in_feature_clause9691); 

                    }
                    break;

            }

            pushFollow(FOLLOW_feature_specifications_in_feature_clause9715);
            feature_specifications();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end feature_clause


    // $ANTLR start feature_specifications
    // BONTCTreeWalker.g:630:1: feature_specifications : ^( FEATURE_SPECIFICATIONS ( feature_specification )+ ) ;
    public final void feature_specifications() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:630:25: ( ^( FEATURE_SPECIFICATIONS ( feature_specification )+ ) )
            // BONTCTreeWalker.g:630:26: ^( FEATURE_SPECIFICATIONS ( feature_specification )+ )
            {
            match(input,FEATURE_SPECIFICATIONS,FOLLOW_FEATURE_SPECIFICATIONS_in_feature_specifications9806); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:632:28: ( feature_specification )+
            int cnt99=0;
            loop99:
            do {
                int alt99=2;
                int LA99_0 = input.LA(1);

                if ( (LA99_0==FEATURE_SPECIFICATION) ) {
                    alt99=1;
                }


                switch (alt99) {
            	case 1 :
            	    // BONTCTreeWalker.g:632:29: feature_specification
            	    {
            	    pushFollow(FOLLOW_feature_specification_in_feature_specifications9836);
            	    feature_specification();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt99 >= 1 ) break loop99;
                        EarlyExitException eee =
                            new EarlyExitException(99, input);
                        throw eee;
                }
                cnt99++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end feature_specifications


    // $ANTLR start feature_specification
    // BONTCTreeWalker.g:636:1: feature_specification : ^( FEATURE_SPECIFICATION ( 'deferred' )? ( 'effective' )? ( 'redefined' )? feature_name_list ( has_type )? ( rename_clause )? ( COMMENT )? ( feature_arguments )? ( contract_clause )? ) ;
    public final void feature_specification() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:636:24: ( ^( FEATURE_SPECIFICATION ( 'deferred' )? ( 'effective' )? ( 'redefined' )? feature_name_list ( has_type )? ( rename_clause )? ( COMMENT )? ( feature_arguments )? ( contract_clause )? ) )
            // BONTCTreeWalker.g:636:25: ^( FEATURE_SPECIFICATION ( 'deferred' )? ( 'effective' )? ( 'redefined' )? feature_name_list ( has_type )? ( rename_clause )? ( COMMENT )? ( feature_arguments )? ( contract_clause )? )
            {
            match(input,FEATURE_SPECIFICATION,FOLLOW_FEATURE_SPECIFICATION_in_feature_specification9951); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:638:27: ( 'deferred' )?
            int alt100=2;
            int LA100_0 = input.LA(1);

            if ( (LA100_0==218) ) {
                alt100=1;
            }
            switch (alt100) {
                case 1 :
                    // BONTCTreeWalker.g:638:28: 'deferred'
                    {
                    match(input,218,FOLLOW_218_in_feature_specification9980); 

                    }
                    break;

            }

            // BONTCTreeWalker.g:638:41: ( 'effective' )?
            int alt101=2;
            int LA101_0 = input.LA(1);

            if ( (LA101_0==219) ) {
                alt101=1;
            }
            switch (alt101) {
                case 1 :
                    // BONTCTreeWalker.g:638:42: 'effective'
                    {
                    match(input,219,FOLLOW_219_in_feature_specification9985); 

                    }
                    break;

            }

            // BONTCTreeWalker.g:638:56: ( 'redefined' )?
            int alt102=2;
            int LA102_0 = input.LA(1);

            if ( (LA102_0==235) ) {
                alt102=1;
            }
            switch (alt102) {
                case 1 :
                    // BONTCTreeWalker.g:638:57: 'redefined'
                    {
                    match(input,235,FOLLOW_235_in_feature_specification9990); 

                    }
                    break;

            }

            pushFollow(FOLLOW_feature_name_list_in_feature_specification10020);
            feature_name_list();
            _fsp--;

            // BONTCTreeWalker.g:639:45: ( has_type )?
            int alt103=2;
            int LA103_0 = input.LA(1);

            if ( (LA103_0==HAS_TYPE) ) {
                alt103=1;
            }
            switch (alt103) {
                case 1 :
                    // BONTCTreeWalker.g:639:46: has_type
                    {
                    pushFollow(FOLLOW_has_type_in_feature_specification10023);
                    has_type();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:640:27: ( rename_clause )?
            int alt104=2;
            int LA104_0 = input.LA(1);

            if ( (LA104_0==RENAME_CLAUSE) ) {
                alt104=1;
            }
            switch (alt104) {
                case 1 :
                    // BONTCTreeWalker.g:640:28: rename_clause
                    {
                    pushFollow(FOLLOW_rename_clause_in_feature_specification10054);
                    rename_clause();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:641:27: ( COMMENT )?
            int alt105=2;
            int LA105_0 = input.LA(1);

            if ( (LA105_0==COMMENT) ) {
                alt105=1;
            }
            switch (alt105) {
                case 1 :
                    // BONTCTreeWalker.g:641:28: COMMENT
                    {
                    match(input,COMMENT,FOLLOW_COMMENT_in_feature_specification10085); 

                    }
                    break;

            }

            // BONTCTreeWalker.g:642:27: ( feature_arguments )?
            int alt106=2;
            int LA106_0 = input.LA(1);

            if ( (LA106_0==FEATURE_ARGUMENTS) ) {
                alt106=1;
            }
            switch (alt106) {
                case 1 :
                    // BONTCTreeWalker.g:642:28: feature_arguments
                    {
                    pushFollow(FOLLOW_feature_arguments_in_feature_specification10116);
                    feature_arguments();
                    _fsp--;


                    }
                    break;

            }

            // BONTCTreeWalker.g:643:27: ( contract_clause )?
            int alt107=2;
            int LA107_0 = input.LA(1);

            if ( (LA107_0==CONTRACT_CLAUSE) ) {
                alt107=1;
            }
            switch (alt107) {
                case 1 :
                    // BONTCTreeWalker.g:643:28: contract_clause
                    {
                    pushFollow(FOLLOW_contract_clause_in_feature_specification10147);
                    contract_clause();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end feature_specification


    // $ANTLR start has_type
    // BONTCTreeWalker.g:647:1: has_type : ^( HAS_TYPE type_mark type ) ;
    public final void has_type() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:647:11: ( ^( HAS_TYPE type_mark type ) )
            // BONTCTreeWalker.g:647:13: ^( HAS_TYPE type_mark type )
            {
            match(input,HAS_TYPE,FOLLOW_HAS_TYPE_in_has_type10211); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_type_mark_in_has_type10213);
            type_mark();
            _fsp--;

            pushFollow(FOLLOW_type_in_has_type10215);
            type();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end has_type


    // $ANTLR start contract_clause
    // BONTCTreeWalker.g:650:1: contract_clause : ^( CONTRACT_CLAUSE contracting_conditions ) ;
    public final void contract_clause() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:652:18: ( ^( CONTRACT_CLAUSE contracting_conditions ) )
            // BONTCTreeWalker.g:652:19: ^( CONTRACT_CLAUSE contracting_conditions )
            {
            match(input,CONTRACT_CLAUSE,FOLLOW_CONTRACT_CLAUSE_in_contract_clause10260); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_contracting_conditions_in_contract_clause10262);
            contracting_conditions();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end contract_clause


    // $ANTLR start contracting_conditions
    // BONTCTreeWalker.g:657:1: contracting_conditions : ^( CONTRACTING_CONDITIONS ( precondition )? ( postcondition )? ) ;
    public final void contracting_conditions() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:657:25: ( ^( CONTRACTING_CONDITIONS ( precondition )? ( postcondition )? ) )
            // BONTCTreeWalker.g:657:26: ^( CONTRACTING_CONDITIONS ( precondition )? ( postcondition )? )
            {
            match(input,CONTRACTING_CONDITIONS,FOLLOW_CONTRACTING_CONDITIONS_in_contracting_conditions10352); 

            if ( input.LA(1)==Token.DOWN ) {
                match(input, Token.DOWN, null); 
                // BONTCTreeWalker.g:658:51: ( precondition )?
                int alt108=2;
                int LA108_0 = input.LA(1);

                if ( (LA108_0==PRECONDITION) ) {
                    alt108=1;
                }
                switch (alt108) {
                    case 1 :
                        // BONTCTreeWalker.g:658:52: precondition
                        {
                        pushFollow(FOLLOW_precondition_in_contracting_conditions10355);
                        precondition();
                        _fsp--;


                        }
                        break;

                }

                // BONTCTreeWalker.g:658:67: ( postcondition )?
                int alt109=2;
                int LA109_0 = input.LA(1);

                if ( (LA109_0==POSTCONDITION) ) {
                    alt109=1;
                }
                switch (alt109) {
                    case 1 :
                        // BONTCTreeWalker.g:658:68: postcondition
                        {
                        pushFollow(FOLLOW_postcondition_in_contracting_conditions10360);
                        postcondition();
                        _fsp--;


                        }
                        break;

                }


                match(input, Token.UP, null); 
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
    // $ANTLR end contracting_conditions


    // $ANTLR start precondition
    // BONTCTreeWalker.g:662:1: precondition : ^( PRECONDITION assertion ) ;
    public final void precondition() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:662:15: ( ^( PRECONDITION assertion ) )
            // BONTCTreeWalker.g:662:16: ^( PRECONDITION assertion )
            {
            match(input,PRECONDITION,FOLLOW_PRECONDITION_in_precondition10450); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_assertion_in_precondition10452);
            assertion();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end precondition


    // $ANTLR start postcondition
    // BONTCTreeWalker.g:667:1: postcondition : ^( POSTCONDITION assertion ) ;
    public final void postcondition() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:667:16: ( ^( POSTCONDITION assertion ) )
            // BONTCTreeWalker.g:667:17: ^( POSTCONDITION assertion )
            {
            match(input,POSTCONDITION,FOLLOW_POSTCONDITION_in_postcondition10527); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_assertion_in_postcondition10529);
            assertion();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end postcondition


    // $ANTLR start selective_export
    // BONTCTreeWalker.g:672:1: selective_export : ^( SELECTIVE_EXPORT class_name_list ) ;
    public final void selective_export() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:674:19: ( ^( SELECTIVE_EXPORT class_name_list ) )
            // BONTCTreeWalker.g:674:20: ^( SELECTIVE_EXPORT class_name_list )
            {
            match(input,SELECTIVE_EXPORT,FOLLOW_SELECTIVE_EXPORT_in_selective_export10598); 

             getContext().enterSelectiveExport(); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_class_name_list_in_selective_export10645);
            class_name_list();
            _fsp--;

             getContext().leaveSelectiveExport(); 

            match(input, Token.UP, null); 

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
    // $ANTLR end selective_export


    // $ANTLR start feature_name_list
    // BONTCTreeWalker.g:682:1: feature_name_list : ^( FEATURE_NAME_LIST ( feature_name )+ ) ;
    public final void feature_name_list() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:682:20: ( ^( FEATURE_NAME_LIST ( feature_name )+ ) )
            // BONTCTreeWalker.g:682:21: ^( FEATURE_NAME_LIST ( feature_name )+ )
            {
            match(input,FEATURE_NAME_LIST,FOLLOW_FEATURE_NAME_LIST_in_feature_name_list10759); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:683:41: ( feature_name )+
            int cnt110=0;
            loop110:
            do {
                int alt110=2;
                int LA110_0 = input.LA(1);

                if ( (LA110_0==FEATURE_NAME) ) {
                    alt110=1;
                }


                switch (alt110) {
            	case 1 :
            	    // BONTCTreeWalker.g:683:42: feature_name
            	    {
            	    pushFollow(FOLLOW_feature_name_in_feature_name_list10762);
            	    feature_name();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt110 >= 1 ) break loop110;
                        EarlyExitException eee =
                            new EarlyExitException(110, input);
                        throw eee;
                }
                cnt110++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end feature_name_list

    public static class feature_name_return extends TreeRuleReturnScope {
    };

    // $ANTLR start feature_name
    // BONTCTreeWalker.g:687:1: feature_name : ( ^( FEATURE_NAME IDENTIFIER ) | ^( FEATURE_NAME prefix ) | ^( FEATURE_NAME infix ) );
    public final feature_name_return feature_name() throws RecognitionException {
        feature_name_return retval = new feature_name_return();
        retval.start = input.LT(1);

        try {
            // BONTCTreeWalker.g:687:15: ( ^( FEATURE_NAME IDENTIFIER ) | ^( FEATURE_NAME prefix ) | ^( FEATURE_NAME infix ) )
            int alt111=3;
            int LA111_0 = input.LA(1);

            if ( (LA111_0==FEATURE_NAME) ) {
                int LA111_1 = input.LA(2);

                if ( (LA111_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case IDENTIFIER:
                        {
                        alt111=1;
                        }
                        break;
                    case INFIX:
                        {
                        alt111=3;
                        }
                        break;
                    case PREFIX:
                        {
                        alt111=2;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("687:1: feature_name : ( ^( FEATURE_NAME IDENTIFIER ) | ^( FEATURE_NAME prefix ) | ^( FEATURE_NAME infix ) );", 111, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("687:1: feature_name : ( ^( FEATURE_NAME IDENTIFIER ) | ^( FEATURE_NAME prefix ) | ^( FEATURE_NAME infix ) );", 111, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("687:1: feature_name : ( ^( FEATURE_NAME IDENTIFIER ) | ^( FEATURE_NAME prefix ) | ^( FEATURE_NAME infix ) );", 111, 0, input);

                throw nvae;
            }
            switch (alt111) {
                case 1 :
                    // BONTCTreeWalker.g:687:16: ^( FEATURE_NAME IDENTIFIER )
                    {
                    match(input,FEATURE_NAME,FOLLOW_FEATURE_NAME_in_feature_name10853); 

                    match(input, Token.DOWN, null); 
                    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_feature_name10855); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:691:16: ^( FEATURE_NAME prefix )
                    {
                    match(input,FEATURE_NAME,FOLLOW_FEATURE_NAME_in_feature_name10927); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_prefix_in_feature_name10929);
                    prefix();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 3 :
                    // BONTCTreeWalker.g:695:16: ^( FEATURE_NAME infix )
                    {
                    match(input,FEATURE_NAME,FOLLOW_FEATURE_NAME_in_feature_name11001); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_infix_in_feature_name11003);
                    infix();
                    _fsp--;


                    match(input, Token.UP, null); 

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
        return retval;
    }
    // $ANTLR end feature_name


    // $ANTLR start rename_clause
    // BONTCTreeWalker.g:700:1: rename_clause : ^( RENAME_CLAUSE renaming ) ;
    public final void rename_clause() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:700:16: ( ^( RENAME_CLAUSE renaming ) )
            // BONTCTreeWalker.g:700:17: ^( RENAME_CLAUSE renaming )
            {
            match(input,RENAME_CLAUSE,FOLLOW_RENAME_CLAUSE_in_rename_clause11078); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_renaming_in_rename_clause11080);
            renaming();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end rename_clause


    // $ANTLR start renaming
    // BONTCTreeWalker.g:705:1: renaming : ^( RENAMING class_name feature_name ) ;
    public final void renaming() throws RecognitionException {
        class_name_return class_name13 = null;

        feature_name_return feature_name14 = null;


        try {
            // BONTCTreeWalker.g:705:11: ( ^( RENAMING class_name feature_name ) )
            // BONTCTreeWalker.g:705:12: ^( RENAMING class_name feature_name )
            {
            match(input,RENAMING,FOLLOW_RENAMING_in_renaming11153); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_class_name_in_renaming11155);
            class_name13=class_name();
            _fsp--;

            pushFollow(FOLLOW_feature_name_in_renaming11157);
            feature_name14=feature_name();
            _fsp--;

             getFTC().checkRenaming(input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(class_name13.start),
              input.getTreeAdaptor().getTokenStopIndex(class_name13.start)), input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(feature_name14.start),
              input.getTreeAdaptor().getTokenStopIndex(feature_name14.start)), getSLoc(((CommonTree)class_name13.start).token)); 

            match(input, Token.UP, null); 

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
    // $ANTLR end renaming


    // $ANTLR start feature_arguments
    // BONTCTreeWalker.g:710:1: feature_arguments : ^( FEATURE_ARGUMENTS ( feature_argument )+ ) ;
    public final void feature_arguments() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:710:20: ( ^( FEATURE_ARGUMENTS ( feature_argument )+ ) )
            // BONTCTreeWalker.g:710:21: ^( FEATURE_ARGUMENTS ( feature_argument )+ )
            {
            match(input,FEATURE_ARGUMENTS,FOLLOW_FEATURE_ARGUMENTS_in_feature_arguments11226); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:711:41: ( feature_argument )+
            int cnt112=0;
            loop112:
            do {
                int alt112=2;
                int LA112_0 = input.LA(1);

                if ( (LA112_0==FEATURE_ARGUMENT) ) {
                    alt112=1;
                }


                switch (alt112) {
            	case 1 :
            	    // BONTCTreeWalker.g:711:42: feature_argument
            	    {
            	    pushFollow(FOLLOW_feature_argument_in_feature_arguments11229);
            	    feature_argument();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt112 >= 1 ) break loop112;
                        EarlyExitException eee =
                            new EarlyExitException(112, input);
                        throw eee;
                }
                cnt112++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end feature_arguments


    // $ANTLR start feature_argument
    // BONTCTreeWalker.g:715:1: feature_argument : ^( FEATURE_ARGUMENT ( identifier_list )? type ) ;
    public final void feature_argument() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:715:19: ( ^( FEATURE_ARGUMENT ( identifier_list )? type ) )
            // BONTCTreeWalker.g:715:20: ^( FEATURE_ARGUMENT ( identifier_list )? type )
            {
            match(input,FEATURE_ARGUMENT,FOLLOW_FEATURE_ARGUMENT_in_feature_argument11325); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:716:39: ( identifier_list )?
            int alt113=2;
            int LA113_0 = input.LA(1);

            if ( (LA113_0==IDENTIFIER_LIST) ) {
                alt113=1;
            }
            switch (alt113) {
                case 1 :
                    // BONTCTreeWalker.g:716:40: identifier_list
                    {
                    pushFollow(FOLLOW_identifier_list_in_feature_argument11328);
                    identifier_list();
                    _fsp--;


                    }
                    break;

            }

            pushFollow(FOLLOW_type_in_feature_argument11332);
            type();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end feature_argument


    // $ANTLR start identifier_list
    // BONTCTreeWalker.g:720:1: identifier_list : ^( IDENTIFIER_LIST ( IDENTIFIER )+ ) ;
    public final void identifier_list() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:720:18: ( ^( IDENTIFIER_LIST ( IDENTIFIER )+ ) )
            // BONTCTreeWalker.g:720:19: ^( IDENTIFIER_LIST ( IDENTIFIER )+ )
            {
            match(input,IDENTIFIER_LIST,FOLLOW_IDENTIFIER_LIST_in_identifier_list11421); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:721:37: ( IDENTIFIER )+
            int cnt114=0;
            loop114:
            do {
                int alt114=2;
                int LA114_0 = input.LA(1);

                if ( (LA114_0==IDENTIFIER) ) {
                    alt114=1;
                }


                switch (alt114) {
            	case 1 :
            	    // BONTCTreeWalker.g:721:38: IDENTIFIER
            	    {
            	    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_identifier_list11424); 

            	    }
            	    break;

            	default :
            	    if ( cnt114 >= 1 ) break loop114;
                        EarlyExitException eee =
                            new EarlyExitException(114, input);
                        throw eee;
                }
                cnt114++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end identifier_list


    // $ANTLR start prefix
    // BONTCTreeWalker.g:725:1: prefix : ^( PREFIX prefix_operator ) ;
    public final void prefix() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:725:9: ( ^( PREFIX prefix_operator ) )
            // BONTCTreeWalker.g:725:10: ^( PREFIX prefix_operator )
            {
            match(input,PREFIX,FOLLOW_PREFIX_in_prefix11500); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_prefix_operator_in_prefix11502);
            prefix_operator();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end prefix


    // $ANTLR start infix
    // BONTCTreeWalker.g:730:1: infix : ^( INFIX infix_operator ) ;
    public final void infix() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:730:8: ( ^( INFIX infix_operator ) )
            // BONTCTreeWalker.g:730:9: ^( INFIX infix_operator )
            {
            match(input,INFIX,FOLLOW_INFIX_in_infix11551); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_infix_operator_in_infix11553);
            infix_operator();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end infix


    // $ANTLR start prefix_operator
    // BONTCTreeWalker.g:735:1: prefix_operator : ^( PREFIX_OPERATOR unary ) ;
    public final void prefix_operator() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:735:18: ( ^( PREFIX_OPERATOR unary ) )
            // BONTCTreeWalker.g:735:19: ^( PREFIX_OPERATOR unary )
            {
            match(input,PREFIX_OPERATOR,FOLLOW_PREFIX_OPERATOR_in_prefix_operator11609); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_unary_in_prefix_operator11611);
            unary();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end prefix_operator


    // $ANTLR start infix_operator
    // BONTCTreeWalker.g:740:1: infix_operator : ^( INFIX_OPERATOR binary ) ;
    public final void infix_operator() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:740:17: ( ^( INFIX_OPERATOR binary ) )
            // BONTCTreeWalker.g:740:18: ^( INFIX_OPERATOR binary )
            {
            match(input,INFIX_OPERATOR,FOLLOW_INFIX_OPERATOR_in_infix_operator11695); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_binary_in_infix_operator11697);
            binary();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end infix_operator


    // $ANTLR start formal_generics
    // BONTCTreeWalker.g:745:1: formal_generics : ^( FORMAL_GENERICS formal_generic_list ) ;
    public final void formal_generics() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:747:18: ( ^( FORMAL_GENERICS formal_generic_list ) )
            // BONTCTreeWalker.g:747:19: ^( FORMAL_GENERICS formal_generic_list )
            {
            match(input,FORMAL_GENERICS,FOLLOW_FORMAL_GENERICS_in_formal_generics11767); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_formal_generic_list_in_formal_generics11769);
            formal_generic_list();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end formal_generics


    // $ANTLR start formal_generic_list
    // BONTCTreeWalker.g:752:1: formal_generic_list : ^( FORMAL_GENERIC_LIST ( formal_generic )+ ) ;
    public final void formal_generic_list() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:752:22: ( ^( FORMAL_GENERIC_LIST ( formal_generic )+ ) )
            // BONTCTreeWalker.g:752:23: ^( FORMAL_GENERIC_LIST ( formal_generic )+ )
            {
            match(input,FORMAL_GENERIC_LIST,FOLLOW_FORMAL_GENERIC_LIST_in_formal_generic_list11859); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:753:45: ( formal_generic )+
            int cnt115=0;
            loop115:
            do {
                int alt115=2;
                int LA115_0 = input.LA(1);

                if ( (LA115_0==FORMAL_GENERIC) ) {
                    alt115=1;
                }


                switch (alt115) {
            	case 1 :
            	    // BONTCTreeWalker.g:753:46: formal_generic
            	    {
            	    pushFollow(FOLLOW_formal_generic_in_formal_generic_list11862);
            	    formal_generic();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt115 >= 1 ) break loop115;
                        EarlyExitException eee =
                            new EarlyExitException(115, input);
                        throw eee;
                }
                cnt115++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end formal_generic_list


    // $ANTLR start formal_generic
    // BONTCTreeWalker.g:757:1: formal_generic : ^( FORMAL_GENERIC formal_generic_name ( class_type )? ) ;
    public final void formal_generic() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:757:17: ( ^( FORMAL_GENERIC formal_generic_name ( class_type )? ) )
            // BONTCTreeWalker.g:757:18: ^( FORMAL_GENERIC formal_generic_name ( class_type )? )
            {
            match(input,FORMAL_GENERIC,FOLLOW_FORMAL_GENERIC_in_formal_generic11961); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_formal_generic_name_in_formal_generic11963);
            formal_generic_name();
            _fsp--;

            // BONTCTreeWalker.g:758:55: ( class_type )?
            int alt116=2;
            int LA116_0 = input.LA(1);

            if ( (LA116_0==CLASS_TYPE) ) {
                alt116=1;
            }
            switch (alt116) {
                case 1 :
                    // BONTCTreeWalker.g:758:56: class_type
                    {
                    pushFollow(FOLLOW_class_type_in_formal_generic11966);
                    class_type();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end formal_generic


    // $ANTLR start formal_generic_name
    // BONTCTreeWalker.g:762:1: formal_generic_name : ^( FORMAL_GENERIC_NAME IDENTIFIER ) ;
    public final void formal_generic_name() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:762:22: ( ^( FORMAL_GENERIC_NAME IDENTIFIER ) )
            // BONTCTreeWalker.g:762:23: ^( FORMAL_GENERIC_NAME IDENTIFIER )
            {
            match(input,FORMAL_GENERIC_NAME,FOLLOW_FORMAL_GENERIC_NAME_in_formal_generic_name12055); 

            match(input, Token.DOWN, null); 
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_formal_generic_name12057); 

            match(input, Token.UP, null); 

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
    // $ANTLR end formal_generic_name

    public static class class_type_return extends TreeRuleReturnScope {
    };

    // $ANTLR start class_type
    // BONTCTreeWalker.g:767:1: class_type : ^( CLASS_TYPE class_name ( actual_generics )? ) ;
    public final class_type_return class_type() throws RecognitionException {
        class_type_return retval = new class_type_return();
        retval.start = input.LT(1);

        try {
            // BONTCTreeWalker.g:767:13: ( ^( CLASS_TYPE class_name ( actual_generics )? ) )
            // BONTCTreeWalker.g:767:14: ^( CLASS_TYPE class_name ( actual_generics )? )
            {
            match(input,CLASS_TYPE,FOLLOW_CLASS_TYPE_in_class_type12150); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_class_name_in_class_type12152);
            class_name();
            _fsp--;

            // BONTCTreeWalker.g:768:38: ( actual_generics )?
            int alt117=2;
            int LA117_0 = input.LA(1);

            if ( (LA117_0==ACTUAL_GENERICS) ) {
                alt117=1;
            }
            switch (alt117) {
                case 1 :
                    // BONTCTreeWalker.g:768:39: actual_generics
                    {
                    pushFollow(FOLLOW_actual_generics_in_class_type12155);
                    actual_generics();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end class_type


    // $ANTLR start actual_generics
    // BONTCTreeWalker.g:772:1: actual_generics : ^( ACTUAL_GENERICS type_list ) ;
    public final void actual_generics() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:772:18: ( ^( ACTUAL_GENERICS type_list ) )
            // BONTCTreeWalker.g:772:19: ^( ACTUAL_GENERICS type_list )
            {
            match(input,ACTUAL_GENERICS,FOLLOW_ACTUAL_GENERICS_in_actual_generics12229); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_type_list_in_actual_generics12231);
            type_list();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end actual_generics


    // $ANTLR start type_list
    // BONTCTreeWalker.g:777:1: type_list : ^( TYPE_LIST ( type )+ ) ;
    public final void type_list() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:777:12: ( ^( TYPE_LIST ( type )+ ) )
            // BONTCTreeWalker.g:777:13: ^( TYPE_LIST ( type )+ )
            {
            match(input,TYPE_LIST,FOLLOW_TYPE_LIST_in_type_list12311); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:778:25: ( type )+
            int cnt118=0;
            loop118:
            do {
                int alt118=2;
                int LA118_0 = input.LA(1);

                if ( (LA118_0==TYPE) ) {
                    alt118=1;
                }


                switch (alt118) {
            	case 1 :
            	    // BONTCTreeWalker.g:778:26: type
            	    {
            	    pushFollow(FOLLOW_type_in_type_list12314);
            	    type();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt118 >= 1 ) break loop118;
                        EarlyExitException eee =
                            new EarlyExitException(118, input);
                        throw eee;
                }
                cnt118++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end type_list


    // $ANTLR start type
    // BONTCTreeWalker.g:782:1: type : ^( TYPE IDENTIFIER ( actual_generics )? ) ;
    public final void type() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:782:7: ( ^( TYPE IDENTIFIER ( actual_generics )? ) )
            // BONTCTreeWalker.g:782:8: ^( TYPE IDENTIFIER ( actual_generics )? )
            {
            match(input,TYPE,FOLLOW_TYPE_in_type12362); 

            match(input, Token.DOWN, null); 
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_type12364); 
            // BONTCTreeWalker.g:783:26: ( actual_generics )?
            int alt119=2;
            int LA119_0 = input.LA(1);

            if ( (LA119_0==ACTUAL_GENERICS) ) {
                alt119=1;
            }
            switch (alt119) {
                case 1 :
                    // BONTCTreeWalker.g:783:27: actual_generics
                    {
                    pushFollow(FOLLOW_actual_generics_in_type12367);
                    actual_generics();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end type


    // $ANTLR start assertion
    // BONTCTreeWalker.g:787:1: assertion : ^( ASSERTION ( assertion_clause )+ ) ;
    public final void assertion() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:791:12: ( ^( ASSERTION ( assertion_clause )+ ) )
            // BONTCTreeWalker.g:791:13: ^( ASSERTION ( assertion_clause )+ )
            {
            match(input,ASSERTION,FOLLOW_ASSERTION_in_assertion12413); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:792:25: ( assertion_clause )+
            int cnt120=0;
            loop120:
            do {
                int alt120=2;
                int LA120_0 = input.LA(1);

                if ( (LA120_0==ASSERTION_CLAUSE) ) {
                    alt120=1;
                }


                switch (alt120) {
            	case 1 :
            	    // BONTCTreeWalker.g:792:26: assertion_clause
            	    {
            	    pushFollow(FOLLOW_assertion_clause_in_assertion12416);
            	    assertion_clause();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt120 >= 1 ) break loop120;
                        EarlyExitException eee =
                            new EarlyExitException(120, input);
                        throw eee;
                }
                cnt120++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end assertion


    // $ANTLR start assertion_clause
    // BONTCTreeWalker.g:796:1: assertion_clause : ^( ASSERTION_CLAUSE boolean_expression ) ;
    public final void assertion_clause() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:796:19: ( ^( ASSERTION_CLAUSE boolean_expression ) )
            // BONTCTreeWalker.g:796:20: ^( ASSERTION_CLAUSE boolean_expression )
            {
            match(input,ASSERTION_CLAUSE,FOLLOW_ASSERTION_CLAUSE_in_assertion_clause12487); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_boolean_expression_in_assertion_clause12489);
            boolean_expression();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end assertion_clause


    // $ANTLR start boolean_expression
    // BONTCTreeWalker.g:801:1: boolean_expression : ^(be= BOOLEAN_EXPRESSION expression ) ;
    public final void boolean_expression() throws RecognitionException {
        CommonTree be=null;

        try {
            // BONTCTreeWalker.g:801:21: ( ^(be= BOOLEAN_EXPRESSION expression ) )
            // BONTCTreeWalker.g:801:22: ^(be= BOOLEAN_EXPRESSION expression )
            {
            be=(CommonTree)input.LT(1);
            match(input,BOOLEAN_EXPRESSION,FOLLOW_BOOLEAN_EXPRESSION_in_boolean_expression12582); 

             getFTC().checkType("BOOL", getSLoc(be.token)); 
             getContext().addTypeRequirement(getFTC().getType("BOOL")); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_expression_in_boolean_expression12659);
            expression();
            _fsp--;

             getContext().removeTypeRequirement(); 

            match(input, Token.UP, null); 

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
    // $ANTLR end boolean_expression


    // $ANTLR start quantification
    // BONTCTreeWalker.g:810:1: quantification : ^(q= QUANTIFICATION quantifier range_expression ( restriction )? proposition ) ;
    public final void quantification() throws RecognitionException {
        CommonTree q=null;

        try {
            // BONTCTreeWalker.g:810:17: ( ^(q= QUANTIFICATION quantifier range_expression ( restriction )? proposition ) )
            // BONTCTreeWalker.g:810:18: ^(q= QUANTIFICATION quantifier range_expression ( restriction )? proposition )
            {
            q=(CommonTree)input.LT(1);
            match(input,QUANTIFICATION,FOLLOW_QUANTIFICATION_in_quantification12772); 

             getFTC().checkType("BOOL", getSLoc(q.token)); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_quantifier_in_quantification12814);
            quantifier();
            _fsp--;

             getContext().enterQuantification(); 
            pushFollow(FOLLOW_range_expression_in_quantification12878);
            range_expression();
            _fsp--;

            // BONTCTreeWalker.g:818:20: ( restriction )?
            int alt121=2;
            int LA121_0 = input.LA(1);

            if ( (LA121_0==RESTRICTION) ) {
                alt121=1;
            }
            switch (alt121) {
                case 1 :
                    // BONTCTreeWalker.g:818:21: restriction
                    {
                    pushFollow(FOLLOW_restriction_in_quantification12921);
                    restriction();
                    _fsp--;


                    }
                    break;

            }

            pushFollow(FOLLOW_proposition_in_quantification12945);
            proposition();
            _fsp--;

             getContext().enterQuantification(); 

            match(input, Token.UP, null); 

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
    // $ANTLR end quantification


    // $ANTLR start quantifier
    // BONTCTreeWalker.g:825:1: quantifier : ( ^( QUANTIFIER 'for_all' ) | ^( QUANTIFIER 'exists' ) );
    public final void quantifier() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:825:13: ( ^( QUANTIFIER 'for_all' ) | ^( QUANTIFIER 'exists' ) )
            int alt122=2;
            int LA122_0 = input.LA(1);

            if ( (LA122_0==QUANTIFIER) ) {
                int LA122_1 = input.LA(2);

                if ( (LA122_1==DOWN) ) {
                    int LA122_2 = input.LA(3);

                    if ( (LA122_2==243) ) {
                        alt122=2;
                    }
                    else if ( (LA122_2==242) ) {
                        alt122=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("825:1: quantifier : ( ^( QUANTIFIER 'for_all' ) | ^( QUANTIFIER 'exists' ) );", 122, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("825:1: quantifier : ( ^( QUANTIFIER 'for_all' ) | ^( QUANTIFIER 'exists' ) );", 122, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("825:1: quantifier : ( ^( QUANTIFIER 'for_all' ) | ^( QUANTIFIER 'exists' ) );", 122, 0, input);

                throw nvae;
            }
            switch (alt122) {
                case 1 :
                    // BONTCTreeWalker.g:825:14: ^( QUANTIFIER 'for_all' )
                    {
                    match(input,QUANTIFIER,FOLLOW_QUANTIFIER_in_quantifier13065); 

                    match(input, Token.DOWN, null); 
                    match(input,242,FOLLOW_242_in_quantifier13067); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:829:14: ^( QUANTIFIER 'exists' )
                    {
                    match(input,QUANTIFIER,FOLLOW_QUANTIFIER_in_quantifier13130); 

                    match(input, Token.DOWN, null); 
                    match(input,243,FOLLOW_243_in_quantifier13132); 

                    match(input, Token.UP, null); 

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
    // $ANTLR end quantifier


    // $ANTLR start range_expression
    // BONTCTreeWalker.g:834:1: range_expression : ^( RANGE_EXPRESSION ( variable_range )+ ) ;
    public final void range_expression() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:834:19: ( ^( RANGE_EXPRESSION ( variable_range )+ ) )
            // BONTCTreeWalker.g:834:20: ^( RANGE_EXPRESSION ( variable_range )+ )
            {
            match(input,RANGE_EXPRESSION,FOLLOW_RANGE_EXPRESSION_in_range_expression13204); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:835:39: ( variable_range )+
            int cnt123=0;
            loop123:
            do {
                int alt123=2;
                int LA123_0 = input.LA(1);

                if ( (LA123_0==VARIABLE_RANGE) ) {
                    alt123=1;
                }


                switch (alt123) {
            	case 1 :
            	    // BONTCTreeWalker.g:835:40: variable_range
            	    {
            	    pushFollow(FOLLOW_variable_range_in_range_expression13207);
            	    variable_range();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt123 >= 1 ) break loop123;
                        EarlyExitException eee =
                            new EarlyExitException(123, input);
                        throw eee;
                }
                cnt123++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end range_expression


    // $ANTLR start restriction
    // BONTCTreeWalker.g:839:1: restriction : ^( RESTRICTION boolean_expression ) ;
    public final void restriction() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:839:14: ( ^( RESTRICTION boolean_expression ) )
            // BONTCTreeWalker.g:839:15: ^( RESTRICTION boolean_expression )
            {
            match(input,RESTRICTION,FOLLOW_RESTRICTION_in_restriction13294); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_boolean_expression_in_restriction13296);
            boolean_expression();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end restriction


    // $ANTLR start proposition
    // BONTCTreeWalker.g:844:1: proposition : ^( PROPOSITION boolean_expression ) ;
    public final void proposition() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:844:14: ( ^( PROPOSITION boolean_expression ) )
            // BONTCTreeWalker.g:844:15: ^( PROPOSITION boolean_expression )
            {
            match(input,PROPOSITION,FOLLOW_PROPOSITION_in_proposition13366); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_boolean_expression_in_proposition13368);
            boolean_expression();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end proposition


    // $ANTLR start variable_range
    // BONTCTreeWalker.g:849:1: variable_range : ( ^( VARIABLE_RANGE member_range ) | ^( VARIABLE_RANGE type_range ) );
    public final void variable_range() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:849:17: ( ^( VARIABLE_RANGE member_range ) | ^( VARIABLE_RANGE type_range ) )
            int alt124=2;
            int LA124_0 = input.LA(1);

            if ( (LA124_0==VARIABLE_RANGE) ) {
                int LA124_1 = input.LA(2);

                if ( (LA124_1==DOWN) ) {
                    int LA124_2 = input.LA(3);

                    if ( (LA124_2==TYPE_RANGE) ) {
                        alt124=2;
                    }
                    else if ( (LA124_2==MEMBER_RANGE) ) {
                        alt124=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("849:1: variable_range : ( ^( VARIABLE_RANGE member_range ) | ^( VARIABLE_RANGE type_range ) );", 124, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("849:1: variable_range : ( ^( VARIABLE_RANGE member_range ) | ^( VARIABLE_RANGE type_range ) );", 124, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("849:1: variable_range : ( ^( VARIABLE_RANGE member_range ) | ^( VARIABLE_RANGE type_range ) );", 124, 0, input);

                throw nvae;
            }
            switch (alt124) {
                case 1 :
                    // BONTCTreeWalker.g:849:18: ^( VARIABLE_RANGE member_range )
                    {
                    match(input,VARIABLE_RANGE,FOLLOW_VARIABLE_RANGE_in_variable_range13441); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_member_range_in_variable_range13443);
                    member_range();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:853:18: ^( VARIABLE_RANGE type_range )
                    {
                    match(input,VARIABLE_RANGE,FOLLOW_VARIABLE_RANGE_in_variable_range13522); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_type_range_in_variable_range13524);
                    type_range();
                    _fsp--;


                    match(input, Token.UP, null); 

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
    // $ANTLR end variable_range


    // $ANTLR start member_range
    // BONTCTreeWalker.g:858:1: member_range : ^( MEMBER_RANGE identifier_list expression ) ;
    public final void member_range() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:858:15: ( ^( MEMBER_RANGE identifier_list expression ) )
            // BONTCTreeWalker.g:858:16: ^( MEMBER_RANGE identifier_list expression )
            {
            match(input,MEMBER_RANGE,FOLLOW_MEMBER_RANGE_in_member_range13604); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_identifier_list_in_member_range13606);
            identifier_list();
            _fsp--;

            pushFollow(FOLLOW_expression_in_member_range13608);
            expression();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end member_range


    // $ANTLR start type_range
    // BONTCTreeWalker.g:863:1: type_range : ^( TYPE_RANGE identifier_list type ) ;
    public final void type_range() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:863:13: ( ^( TYPE_RANGE identifier_list type ) )
            // BONTCTreeWalker.g:863:14: ^( TYPE_RANGE identifier_list type )
            {
            match(input,TYPE_RANGE,FOLLOW_TYPE_RANGE_in_type_range13680); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_identifier_list_in_type_range13682);
            identifier_list();
            _fsp--;

            pushFollow(FOLLOW_type_in_type_range13684);
            type();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end type_range


    // $ANTLR start call_chain
    // BONTCTreeWalker.g:868:1: call_chain : ^( CALL_CHAIN ( unqualified_call )+ ) ;
    public final void call_chain() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:876:13: ( ^( CALL_CHAIN ( unqualified_call )+ ) )
            // BONTCTreeWalker.g:876:14: ^( CALL_CHAIN ( unqualified_call )+ )
            {
            match(input,CALL_CHAIN,FOLLOW_CALL_CHAIN_in_call_chain13772); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:877:27: ( unqualified_call )+
            int cnt125=0;
            loop125:
            do {
                int alt125=2;
                int LA125_0 = input.LA(1);

                if ( (LA125_0==UNQUALIFIED_CALL) ) {
                    alt125=1;
                }


                switch (alt125) {
            	case 1 :
            	    // BONTCTreeWalker.g:877:28: unqualified_call
            	    {
            	    pushFollow(FOLLOW_unqualified_call_in_call_chain13775);
            	    unqualified_call();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt125 >= 1 ) break loop125;
                        EarlyExitException eee =
                            new EarlyExitException(125, input);
                        throw eee;
                }
                cnt125++;
            } while (true);

             getContext().clearLastCallChainType(); 

            match(input, Token.UP, null); 

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
    // $ANTLR end call_chain


    // $ANTLR start unqualified_call
    // BONTCTreeWalker.g:881:1: unqualified_call : ^( UNQUALIFIED_CALL i= IDENTIFIER ( actual_arguments )? ) ;
    public final void unqualified_call() throws RecognitionException {
        CommonTree i=null;

         Type t = null; 
        try {
            // BONTCTreeWalker.g:883:19: ( ^( UNQUALIFIED_CALL i= IDENTIFIER ( actual_arguments )? ) )
            // BONTCTreeWalker.g:883:20: ^( UNQUALIFIED_CALL i= IDENTIFIER ( actual_arguments )? )
            {
            match(input,UNQUALIFIED_CALL,FOLLOW_UNQUALIFIED_CALL_in_unqualified_call13875); 

            match(input, Token.DOWN, null); 
            i=(CommonTree)input.LT(1);
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_unqualified_call13901); 
             t = getFTC().getTypeForCall(i.getText(),getSLoc(i.token)); 
            // BONTCTreeWalker.g:887:22: ( actual_arguments )?
            int alt126=2;
            int LA126_0 = input.LA(1);

            if ( (LA126_0==ACTUAL_ARGUMENTS) ) {
                alt126=1;
            }
            switch (alt126) {
                case 1 :
                    // BONTCTreeWalker.g:887:23: actual_arguments
                    {
                    pushFollow(FOLLOW_actual_arguments_in_unqualified_call13949);
                    actual_arguments();
                    _fsp--;


                    }
                    break;

            }

             if (t!=null) { getContext().setLastCallChainType(t); } 

            match(input, Token.UP, null); 

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
    // $ANTLR end unqualified_call


    // $ANTLR start actual_arguments
    // BONTCTreeWalker.g:892:1: actual_arguments : ^( ACTUAL_ARGUMENTS ( expression_list )? ) ;
    public final void actual_arguments() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:892:19: ( ^( ACTUAL_ARGUMENTS ( expression_list )? ) )
            // BONTCTreeWalker.g:892:20: ^( ACTUAL_ARGUMENTS ( expression_list )? )
            {
            match(input,ACTUAL_ARGUMENTS,FOLLOW_ACTUAL_ARGUMENTS_in_actual_arguments14064); 

            if ( input.LA(1)==Token.DOWN ) {
                match(input, Token.DOWN, null); 
                // BONTCTreeWalker.g:893:39: ( expression_list )?
                int alt127=2;
                int LA127_0 = input.LA(1);

                if ( (LA127_0==EXPRESSION_LIST) ) {
                    alt127=1;
                }
                switch (alt127) {
                    case 1 :
                        // BONTCTreeWalker.g:893:39: expression_list
                        {
                        pushFollow(FOLLOW_expression_list_in_actual_arguments14066);
                        expression_list();
                        _fsp--;


                        }
                        break;

                }


                match(input, Token.UP, null); 
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
    // $ANTLR end actual_arguments


    // $ANTLR start expression_list
    // BONTCTreeWalker.g:897:1: expression_list : ^( EXPRESSION_LIST ( expression )+ ) ;
    public final void expression_list() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:897:18: ( ^( EXPRESSION_LIST ( expression )+ ) )
            // BONTCTreeWalker.g:897:19: ^( EXPRESSION_LIST ( expression )+ )
            {
            match(input,EXPRESSION_LIST,FOLLOW_EXPRESSION_LIST_in_expression_list14152); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:898:37: ( expression )+
            int cnt128=0;
            loop128:
            do {
                int alt128=2;
                int LA128_0 = input.LA(1);

                if ( (LA128_0==EXPRESSION) ) {
                    alt128=1;
                }


                switch (alt128) {
            	case 1 :
            	    // BONTCTreeWalker.g:898:38: expression
            	    {
            	    pushFollow(FOLLOW_expression_in_expression_list14155);
            	    expression();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt128 >= 1 ) break loop128;
                        EarlyExitException eee =
                            new EarlyExitException(128, input);
                        throw eee;
                }
                cnt128++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end expression_list


    // $ANTLR start enumerated_set
    // BONTCTreeWalker.g:902:1: enumerated_set : ^( ENUMERATED_SET enumeration_list ) ;
    public final void enumerated_set() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:904:17: ( ^( ENUMERATED_SET enumeration_list ) )
            // BONTCTreeWalker.g:904:18: ^( ENUMERATED_SET enumeration_list )
            {
            match(input,ENUMERATED_SET,FOLLOW_ENUMERATED_SET_in_enumerated_set14244); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_enumeration_list_in_enumerated_set14246);
            enumeration_list();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end enumerated_set


    // $ANTLR start enumeration_list
    // BONTCTreeWalker.g:909:1: enumeration_list : ^( ENUMERATION_LIST ( enumeration_element )+ ) ;
    public final void enumeration_list() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:909:19: ( ^( ENUMERATION_LIST ( enumeration_element )+ ) )
            // BONTCTreeWalker.g:909:20: ^( ENUMERATION_LIST ( enumeration_element )+ )
            {
            match(input,ENUMERATION_LIST,FOLLOW_ENUMERATION_LIST_in_enumeration_list14330); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:910:39: ( enumeration_element )+
            int cnt129=0;
            loop129:
            do {
                int alt129=2;
                int LA129_0 = input.LA(1);

                if ( (LA129_0==ENUMERATION_ELEMENT) ) {
                    alt129=1;
                }


                switch (alt129) {
            	case 1 :
            	    // BONTCTreeWalker.g:910:40: enumeration_element
            	    {
            	    pushFollow(FOLLOW_enumeration_element_in_enumeration_list14333);
            	    enumeration_element();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt129 >= 1 ) break loop129;
                        EarlyExitException eee =
                            new EarlyExitException(129, input);
                        throw eee;
                }
                cnt129++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end enumeration_list


    // $ANTLR start enumeration_element
    // BONTCTreeWalker.g:914:1: enumeration_element : ( ^( ENUMERATION_ELEMENT expression ) | ^( ENUMERATION_ELEMENT interval ) );
    public final void enumeration_element() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:914:22: ( ^( ENUMERATION_ELEMENT expression ) | ^( ENUMERATION_ELEMENT interval ) )
            int alt130=2;
            int LA130_0 = input.LA(1);

            if ( (LA130_0==ENUMERATION_ELEMENT) ) {
                int LA130_1 = input.LA(2);

                if ( (LA130_1==DOWN) ) {
                    int LA130_2 = input.LA(3);

                    if ( (LA130_2==INTERVAL) ) {
                        alt130=2;
                    }
                    else if ( (LA130_2==EXPRESSION) ) {
                        alt130=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("914:1: enumeration_element : ( ^( ENUMERATION_ELEMENT expression ) | ^( ENUMERATION_ELEMENT interval ) );", 130, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("914:1: enumeration_element : ( ^( ENUMERATION_ELEMENT expression ) | ^( ENUMERATION_ELEMENT interval ) );", 130, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("914:1: enumeration_element : ( ^( ENUMERATION_ELEMENT expression ) | ^( ENUMERATION_ELEMENT interval ) );", 130, 0, input);

                throw nvae;
            }
            switch (alt130) {
                case 1 :
                    // BONTCTreeWalker.g:914:23: ^( ENUMERATION_ELEMENT expression )
                    {
                    match(input,ENUMERATION_ELEMENT,FOLLOW_ENUMERATION_ELEMENT_in_enumeration_element14419); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_expression_in_enumeration_element14421);
                    expression();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:918:23: ^( ENUMERATION_ELEMENT interval )
                    {
                    match(input,ENUMERATION_ELEMENT,FOLLOW_ENUMERATION_ELEMENT_in_enumeration_element14521); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_interval_in_enumeration_element14523);
                    interval();
                    _fsp--;


                    match(input, Token.UP, null); 

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
    // $ANTLR end enumeration_element


    // $ANTLR start interval
    // BONTCTreeWalker.g:923:1: interval : ( ^( INTERVAL integer_interval ) | ^( INTERVAL character_interval ) );
    public final void interval() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:923:11: ( ^( INTERVAL integer_interval ) | ^( INTERVAL character_interval ) )
            int alt131=2;
            int LA131_0 = input.LA(1);

            if ( (LA131_0==INTERVAL) ) {
                int LA131_1 = input.LA(2);

                if ( (LA131_1==DOWN) ) {
                    int LA131_2 = input.LA(3);

                    if ( (LA131_2==CHARACTER_INTERVAL) ) {
                        alt131=2;
                    }
                    else if ( (LA131_2==INTEGER_INTERVAL) ) {
                        alt131=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("923:1: interval : ( ^( INTERVAL integer_interval ) | ^( INTERVAL character_interval ) );", 131, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("923:1: interval : ( ^( INTERVAL integer_interval ) | ^( INTERVAL character_interval ) );", 131, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("923:1: interval : ( ^( INTERVAL integer_interval ) | ^( INTERVAL character_interval ) );", 131, 0, input);

                throw nvae;
            }
            switch (alt131) {
                case 1 :
                    // BONTCTreeWalker.g:923:12: ^( INTERVAL integer_interval )
                    {
                    match(input,INTERVAL,FOLLOW_INTERVAL_in_interval14614); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_integer_interval_in_interval14616);
                    integer_interval();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:927:12: ^( INTERVAL character_interval )
                    {
                    match(input,INTERVAL,FOLLOW_INTERVAL_in_interval14673); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_character_interval_in_interval14675);
                    character_interval();
                    _fsp--;


                    match(input, Token.UP, null); 

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
    // $ANTLR end interval


    // $ANTLR start integer_interval
    // BONTCTreeWalker.g:932:1: integer_interval : ^( INTEGER_INTERVAL integer_constant integer_constant ) ;
    public final void integer_interval() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:932:19: ( ^( INTEGER_INTERVAL integer_constant integer_constant ) )
            // BONTCTreeWalker.g:932:20: ^( INTEGER_INTERVAL integer_constant integer_constant )
            {
            match(input,INTEGER_INTERVAL,FOLLOW_INTEGER_INTERVAL_in_integer_interval14742); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_integer_constant_in_integer_interval14744);
            integer_constant();
            _fsp--;

            pushFollow(FOLLOW_integer_constant_in_integer_interval14746);
            integer_constant();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end integer_interval


    // $ANTLR start character_interval
    // BONTCTreeWalker.g:937:1: character_interval : ^( CHARACTER_INTERVAL CHARACTER_CONSTANT CHARACTER_CONSTANT ) ;
    public final void character_interval() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:937:21: ( ^( CHARACTER_INTERVAL CHARACTER_CONSTANT CHARACTER_CONSTANT ) )
            // BONTCTreeWalker.g:937:22: ^( CHARACTER_INTERVAL CHARACTER_CONSTANT CHARACTER_CONSTANT )
            {
            match(input,CHARACTER_INTERVAL,FOLLOW_CHARACTER_INTERVAL_in_character_interval14838); 

            match(input, Token.DOWN, null); 
            match(input,CHARACTER_CONSTANT,FOLLOW_CHARACTER_CONSTANT_in_character_interval14840); 
            match(input,CHARACTER_CONSTANT,FOLLOW_CHARACTER_CONSTANT_in_character_interval14842); 

            match(input, Token.UP, null); 

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
    // $ANTLR end character_interval


    // $ANTLR start constant
    // BONTCTreeWalker.g:941:1: constant : ( ^( CONSTANT manifest_constant ) | ^(c= CONSTANT 'Current' ) | ^(c= CONSTANT 'Void' ) );
    public final void constant() throws RecognitionException {
        CommonTree c=null;

        try {
            // BONTCTreeWalker.g:943:11: ( ^( CONSTANT manifest_constant ) | ^(c= CONSTANT 'Current' ) | ^(c= CONSTANT 'Void' ) )
            int alt132=3;
            int LA132_0 = input.LA(1);

            if ( (LA132_0==CONSTANT) ) {
                int LA132_1 = input.LA(2);

                if ( (LA132_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case 249:
                        {
                        alt132=3;
                        }
                        break;
                    case 248:
                        {
                        alt132=2;
                        }
                        break;
                    case MANIFEST_CONSTANT:
                        {
                        alt132=1;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("941:1: constant : ( ^( CONSTANT manifest_constant ) | ^(c= CONSTANT 'Current' ) | ^(c= CONSTANT 'Void' ) );", 132, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("941:1: constant : ( ^( CONSTANT manifest_constant ) | ^(c= CONSTANT 'Current' ) | ^(c= CONSTANT 'Void' ) );", 132, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("941:1: constant : ( ^( CONSTANT manifest_constant ) | ^(c= CONSTANT 'Current' ) | ^(c= CONSTANT 'Void' ) );", 132, 0, input);

                throw nvae;
            }
            switch (alt132) {
                case 1 :
                    // BONTCTreeWalker.g:943:12: ^( CONSTANT manifest_constant )
                    {
                    match(input,CONSTANT,FOLLOW_CONSTANT_in_constant14912); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_manifest_constant_in_constant14914);
                    manifest_constant();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:947:12: ^(c= CONSTANT 'Current' )
                    {
                    c=(CommonTree)input.LT(1);
                    match(input,CONSTANT,FOLLOW_CONSTANT_in_constant14971); 

                     getFTC().checkType(getContext().getClassName(),getSLoc(c.token)); 

                    match(input, Token.DOWN, null); 
                    match(input,248,FOLLOW_248_in_constant14975); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 3 :
                    // BONTCTreeWalker.g:951:12: ^(c= CONSTANT 'Void' )
                    {
                    c=(CommonTree)input.LT(1);
                    match(input,CONSTANT,FOLLOW_CONSTANT_in_constant15032); 

                     getFTC().checkType("Void",getSLoc(c.token)); 

                    match(input, Token.DOWN, null); 
                    match(input,249,FOLLOW_249_in_constant15036); 

                    match(input, Token.UP, null); 

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
    // $ANTLR end constant


    // $ANTLR start manifest_constant
    // BONTCTreeWalker.g:956:1: manifest_constant : ( ^( MANIFEST_CONSTANT boolean_constant ) | ^(mc= MANIFEST_CONSTANT CHARACTER_CONSTANT ) | ^( MANIFEST_CONSTANT integer_constant ) | ^( MANIFEST_CONSTANT real_constant ) | ^(mc= MANIFEST_CONSTANT MANIFEST_STRING ) | ^( MANIFEST_CONSTANT enumerated_set ) );
    public final void manifest_constant() throws RecognitionException {
        CommonTree mc=null;

        try {
            // BONTCTreeWalker.g:956:20: ( ^( MANIFEST_CONSTANT boolean_constant ) | ^(mc= MANIFEST_CONSTANT CHARACTER_CONSTANT ) | ^( MANIFEST_CONSTANT integer_constant ) | ^( MANIFEST_CONSTANT real_constant ) | ^(mc= MANIFEST_CONSTANT MANIFEST_STRING ) | ^( MANIFEST_CONSTANT enumerated_set ) )
            int alt133=6;
            int LA133_0 = input.LA(1);

            if ( (LA133_0==MANIFEST_CONSTANT) ) {
                int LA133_1 = input.LA(2);

                if ( (LA133_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case CHARACTER_CONSTANT:
                        {
                        alt133=2;
                        }
                        break;
                    case MANIFEST_STRING:
                        {
                        alt133=5;
                        }
                        break;
                    case ENUMERATED_SET:
                        {
                        alt133=6;
                        }
                        break;
                    case BOOLEAN_CONSTANT:
                        {
                        alt133=1;
                        }
                        break;
                    case REAL_CONSTANT:
                        {
                        alt133=4;
                        }
                        break;
                    case INTEGER_CONSTANT:
                        {
                        alt133=3;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("956:1: manifest_constant : ( ^( MANIFEST_CONSTANT boolean_constant ) | ^(mc= MANIFEST_CONSTANT CHARACTER_CONSTANT ) | ^( MANIFEST_CONSTANT integer_constant ) | ^( MANIFEST_CONSTANT real_constant ) | ^(mc= MANIFEST_CONSTANT MANIFEST_STRING ) | ^( MANIFEST_CONSTANT enumerated_set ) );", 133, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("956:1: manifest_constant : ( ^( MANIFEST_CONSTANT boolean_constant ) | ^(mc= MANIFEST_CONSTANT CHARACTER_CONSTANT ) | ^( MANIFEST_CONSTANT integer_constant ) | ^( MANIFEST_CONSTANT real_constant ) | ^(mc= MANIFEST_CONSTANT MANIFEST_STRING ) | ^( MANIFEST_CONSTANT enumerated_set ) );", 133, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("956:1: manifest_constant : ( ^( MANIFEST_CONSTANT boolean_constant ) | ^(mc= MANIFEST_CONSTANT CHARACTER_CONSTANT ) | ^( MANIFEST_CONSTANT integer_constant ) | ^( MANIFEST_CONSTANT real_constant ) | ^(mc= MANIFEST_CONSTANT MANIFEST_STRING ) | ^( MANIFEST_CONSTANT enumerated_set ) );", 133, 0, input);

                throw nvae;
            }
            switch (alt133) {
                case 1 :
                    // BONTCTreeWalker.g:956:22: ^( MANIFEST_CONSTANT boolean_constant )
                    {
                    match(input,MANIFEST_CONSTANT,FOLLOW_MANIFEST_CONSTANT_in_manifest_constant15095); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_boolean_constant_in_manifest_constant15097);
                    boolean_constant();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:960:22: ^(mc= MANIFEST_CONSTANT CHARACTER_CONSTANT )
                    {
                    mc=(CommonTree)input.LT(1);
                    match(input,MANIFEST_CONSTANT,FOLLOW_MANIFEST_CONSTANT_in_manifest_constant15195); 

                     getFTC().checkType("CHAR",getSLoc(mc.token)); 

                    match(input, Token.DOWN, null); 
                    match(input,CHARACTER_CONSTANT,FOLLOW_CHARACTER_CONSTANT_in_manifest_constant15199); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 3 :
                    // BONTCTreeWalker.g:964:22: ^( MANIFEST_CONSTANT integer_constant )
                    {
                    match(input,MANIFEST_CONSTANT,FOLLOW_MANIFEST_CONSTANT_in_manifest_constant15295); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_integer_constant_in_manifest_constant15297);
                    integer_constant();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 4 :
                    // BONTCTreeWalker.g:968:22: ^( MANIFEST_CONSTANT real_constant )
                    {
                    match(input,MANIFEST_CONSTANT,FOLLOW_MANIFEST_CONSTANT_in_manifest_constant15393); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_real_constant_in_manifest_constant15395);
                    real_constant();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 5 :
                    // BONTCTreeWalker.g:972:22: ^(mc= MANIFEST_CONSTANT MANIFEST_STRING )
                    {
                    mc=(CommonTree)input.LT(1);
                    match(input,MANIFEST_CONSTANT,FOLLOW_MANIFEST_CONSTANT_in_manifest_constant15493); 

                     getFTC().checkType("STRING",getSLoc(mc.token)); 

                    match(input, Token.DOWN, null); 
                    match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_manifest_constant15497); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 6 :
                    // BONTCTreeWalker.g:976:22: ^( MANIFEST_CONSTANT enumerated_set )
                    {
                    match(input,MANIFEST_CONSTANT,FOLLOW_MANIFEST_CONSTANT_in_manifest_constant15593); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_enumerated_set_in_manifest_constant15595);
                    enumerated_set();
                    _fsp--;


                    match(input, Token.UP, null); 

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
    // $ANTLR end manifest_constant


    // $ANTLR start sign
    // BONTCTreeWalker.g:981:1: sign : ^( SIGN add_sub_op ) ;
    public final void sign() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:981:7: ( ^( SIGN add_sub_op ) )
            // BONTCTreeWalker.g:981:8: ^( SIGN add_sub_op )
            {
            match(input,SIGN,FOLLOW_SIGN_in_sign15677); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_add_sub_op_in_sign15679);
            add_sub_op();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end sign


    // $ANTLR start boolean_constant
    // BONTCTreeWalker.g:986:1: boolean_constant : ( ^(bc= BOOLEAN_CONSTANT 'true' ) | ^(bc= BOOLEAN_CONSTANT 'false' ) );
    public final void boolean_constant() throws RecognitionException {
        CommonTree bc=null;

        try {
            // BONTCTreeWalker.g:986:19: ( ^(bc= BOOLEAN_CONSTANT 'true' ) | ^(bc= BOOLEAN_CONSTANT 'false' ) )
            int alt134=2;
            int LA134_0 = input.LA(1);

            if ( (LA134_0==BOOLEAN_CONSTANT) ) {
                int LA134_1 = input.LA(2);

                if ( (LA134_1==DOWN) ) {
                    int LA134_2 = input.LA(3);

                    if ( (LA134_2==251) ) {
                        alt134=2;
                    }
                    else if ( (LA134_2==250) ) {
                        alt134=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("986:1: boolean_constant : ( ^(bc= BOOLEAN_CONSTANT 'true' ) | ^(bc= BOOLEAN_CONSTANT 'false' ) );", 134, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("986:1: boolean_constant : ( ^(bc= BOOLEAN_CONSTANT 'true' ) | ^(bc= BOOLEAN_CONSTANT 'false' ) );", 134, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("986:1: boolean_constant : ( ^(bc= BOOLEAN_CONSTANT 'true' ) | ^(bc= BOOLEAN_CONSTANT 'false' ) );", 134, 0, input);

                throw nvae;
            }
            switch (alt134) {
                case 1 :
                    // BONTCTreeWalker.g:986:20: ^(bc= BOOLEAN_CONSTANT 'true' )
                    {
                    bc=(CommonTree)input.LT(1);
                    match(input,BOOLEAN_CONSTANT,FOLLOW_BOOLEAN_CONSTANT_in_boolean_constant15735); 

                     getFTC().checkType("BOOL",getSLoc(bc.token)); 

                    match(input, Token.DOWN, null); 
                    match(input,250,FOLLOW_250_in_boolean_constant15739); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:990:20: ^(bc= BOOLEAN_CONSTANT 'false' )
                    {
                    bc=(CommonTree)input.LT(1);
                    match(input,BOOLEAN_CONSTANT,FOLLOW_BOOLEAN_CONSTANT_in_boolean_constant15828); 

                     getFTC().checkType("BOOL",getSLoc(bc.token)); 

                    match(input, Token.DOWN, null); 
                    match(input,251,FOLLOW_251_in_boolean_constant15832); 

                    match(input, Token.UP, null); 

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
    // $ANTLR end boolean_constant


    // $ANTLR start integer_constant
    // BONTCTreeWalker.g:995:1: integer_constant : ^(ic= INTEGER_CONSTANT ( sign )? INTEGER ) ;
    public final void integer_constant() throws RecognitionException {
        CommonTree ic=null;

        try {
            // BONTCTreeWalker.g:995:19: ( ^(ic= INTEGER_CONSTANT ( sign )? INTEGER ) )
            // BONTCTreeWalker.g:995:20: ^(ic= INTEGER_CONSTANT ( sign )? INTEGER )
            {
            ic=(CommonTree)input.LT(1);
            match(input,INTEGER_CONSTANT,FOLLOW_INTEGER_CONSTANT_in_integer_constant15926); 

             getFTC().checkType("VALUE",getSLoc(ic.token)); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:998:22: ( sign )?
            int alt135=2;
            int LA135_0 = input.LA(1);

            if ( (LA135_0==SIGN) ) {
                alt135=1;
            }
            switch (alt135) {
                case 1 :
                    // BONTCTreeWalker.g:998:23: sign
                    {
                    pushFollow(FOLLOW_sign_in_integer_constant15973);
                    sign();
                    _fsp--;


                    }
                    break;

            }

            match(input,INTEGER,FOLLOW_INTEGER_in_integer_constant15977); 

            match(input, Token.UP, null); 

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
    // $ANTLR end integer_constant


    // $ANTLR start real_constant
    // BONTCTreeWalker.g:1002:1: real_constant : ^(rc= REAL_CONSTANT ( sign )? REAL ) ;
    public final void real_constant() throws RecognitionException {
        CommonTree rc=null;

        try {
            // BONTCTreeWalker.g:1002:16: ( ^(rc= REAL_CONSTANT ( sign )? REAL ) )
            // BONTCTreeWalker.g:1002:17: ^(rc= REAL_CONSTANT ( sign )? REAL )
            {
            rc=(CommonTree)input.LT(1);
            match(input,REAL_CONSTANT,FOLLOW_REAL_CONSTANT_in_real_constant16066); 

             getFTC().checkType("VALUE",getSLoc(rc.token)); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:1005:19: ( sign )?
            int alt136=2;
            int LA136_0 = input.LA(1);

            if ( (LA136_0==SIGN) ) {
                alt136=1;
            }
            switch (alt136) {
                case 1 :
                    // BONTCTreeWalker.g:1005:20: sign
                    {
                    pushFollow(FOLLOW_sign_in_real_constant16107);
                    sign();
                    _fsp--;


                    }
                    break;

            }

            match(input,REAL,FOLLOW_REAL_in_real_constant16111); 

            match(input, Token.UP, null); 

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
    // $ANTLR end real_constant


    // $ANTLR start dynamic_diagram
    // BONTCTreeWalker.g:1009:1: dynamic_diagram : ^( DYNAMIC_DIAGRAM ( extended_id )? ( COMMENT )? ( dynamic_block )? ) ;
    public final void dynamic_diagram() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1013:18: ( ^( DYNAMIC_DIAGRAM ( extended_id )? ( COMMENT )? ( dynamic_block )? ) )
            // BONTCTreeWalker.g:1013:19: ^( DYNAMIC_DIAGRAM ( extended_id )? ( COMMENT )? ( dynamic_block )? )
            {
            match(input,DYNAMIC_DIAGRAM,FOLLOW_DYNAMIC_DIAGRAM_in_dynamic_diagram16179); 

            if ( input.LA(1)==Token.DOWN ) {
                match(input, Token.DOWN, null); 
                // BONTCTreeWalker.g:1015:21: ( extended_id )?
                int alt137=2;
                int LA137_0 = input.LA(1);

                if ( (LA137_0==EXTENDED_ID) ) {
                    alt137=1;
                }
                switch (alt137) {
                    case 1 :
                        // BONTCTreeWalker.g:1015:22: extended_id
                        {
                        pushFollow(FOLLOW_extended_id_in_dynamic_diagram16202);
                        extended_id();
                        _fsp--;


                        }
                        break;

                }

                // BONTCTreeWalker.g:1015:36: ( COMMENT )?
                int alt138=2;
                int LA138_0 = input.LA(1);

                if ( (LA138_0==COMMENT) ) {
                    alt138=1;
                }
                switch (alt138) {
                    case 1 :
                        // BONTCTreeWalker.g:1015:37: COMMENT
                        {
                        match(input,COMMENT,FOLLOW_COMMENT_in_dynamic_diagram16207); 

                        }
                        break;

                }

                // BONTCTreeWalker.g:1016:21: ( dynamic_block )?
                int alt139=2;
                int LA139_0 = input.LA(1);

                if ( (LA139_0==DYNAMIC_BLOCK) ) {
                    alt139=1;
                }
                switch (alt139) {
                    case 1 :
                        // BONTCTreeWalker.g:1016:22: dynamic_block
                        {
                        pushFollow(FOLLOW_dynamic_block_in_dynamic_diagram16232);
                        dynamic_block();
                        _fsp--;


                        }
                        break;

                }


                match(input, Token.UP, null); 
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
    // $ANTLR end dynamic_diagram


    // $ANTLR start dynamic_block
    // BONTCTreeWalker.g:1020:1: dynamic_block : ^( DYNAMIC_BLOCK ( dynamic_component )+ ) ;
    public final void dynamic_block() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1020:16: ( ^( DYNAMIC_BLOCK ( dynamic_component )+ ) )
            // BONTCTreeWalker.g:1020:17: ^( DYNAMIC_BLOCK ( dynamic_component )+ )
            {
            match(input,DYNAMIC_BLOCK,FOLLOW_DYNAMIC_BLOCK_in_dynamic_block16318); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:1022:19: ( dynamic_component )+
            int cnt140=0;
            loop140:
            do {
                int alt140=2;
                int LA140_0 = input.LA(1);

                if ( (LA140_0==DYNAMIC_COMPONENT) ) {
                    alt140=1;
                }


                switch (alt140) {
            	case 1 :
            	    // BONTCTreeWalker.g:1022:20: dynamic_component
            	    {
            	    pushFollow(FOLLOW_dynamic_component_in_dynamic_block16339);
            	    dynamic_component();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt140 >= 1 ) break loop140;
                        EarlyExitException eee =
                            new EarlyExitException(140, input);
                        throw eee;
                }
                cnt140++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end dynamic_block


    // $ANTLR start dynamic_component
    // BONTCTreeWalker.g:1026:1: dynamic_component : ( ^( DYNAMIC_COMPONENT scenario_description ) | ^( DYNAMIC_COMPONENT object_group ) | ^( DYNAMIC_COMPONENT object_stack ) | ^( DYNAMIC_COMPONENT object ) | ^( DYNAMIC_COMPONENT message_relation ) );
    public final void dynamic_component() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1026:20: ( ^( DYNAMIC_COMPONENT scenario_description ) | ^( DYNAMIC_COMPONENT object_group ) | ^( DYNAMIC_COMPONENT object_stack ) | ^( DYNAMIC_COMPONENT object ) | ^( DYNAMIC_COMPONENT message_relation ) )
            int alt141=5;
            int LA141_0 = input.LA(1);

            if ( (LA141_0==DYNAMIC_COMPONENT) ) {
                int LA141_1 = input.LA(2);

                if ( (LA141_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case SCENARIO_DESCRIPTION:
                        {
                        alt141=1;
                        }
                        break;
                    case OBJECT_STACK:
                        {
                        alt141=3;
                        }
                        break;
                    case OBJECT_GROUP:
                        {
                        alt141=2;
                        }
                        break;
                    case OBJECT:
                        {
                        alt141=4;
                        }
                        break;
                    case MESSAGE_RELATION:
                        {
                        alt141=5;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("1026:1: dynamic_component : ( ^( DYNAMIC_COMPONENT scenario_description ) | ^( DYNAMIC_COMPONENT object_group ) | ^( DYNAMIC_COMPONENT object_stack ) | ^( DYNAMIC_COMPONENT object ) | ^( DYNAMIC_COMPONENT message_relation ) );", 141, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1026:1: dynamic_component : ( ^( DYNAMIC_COMPONENT scenario_description ) | ^( DYNAMIC_COMPONENT object_group ) | ^( DYNAMIC_COMPONENT object_stack ) | ^( DYNAMIC_COMPONENT object ) | ^( DYNAMIC_COMPONENT message_relation ) );", 141, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1026:1: dynamic_component : ( ^( DYNAMIC_COMPONENT scenario_description ) | ^( DYNAMIC_COMPONENT object_group ) | ^( DYNAMIC_COMPONENT object_stack ) | ^( DYNAMIC_COMPONENT object ) | ^( DYNAMIC_COMPONENT message_relation ) );", 141, 0, input);

                throw nvae;
            }
            switch (alt141) {
                case 1 :
                    // BONTCTreeWalker.g:1026:22: ^( DYNAMIC_COMPONENT scenario_description )
                    {
                    match(input,DYNAMIC_COMPONENT,FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component16425); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_scenario_description_in_dynamic_component16427);
                    scenario_description();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1030:22: ^( DYNAMIC_COMPONENT object_group )
                    {
                    match(input,DYNAMIC_COMPONENT,FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component16522); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_object_group_in_dynamic_component16524);
                    object_group();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 3 :
                    // BONTCTreeWalker.g:1034:22: ^( DYNAMIC_COMPONENT object_stack )
                    {
                    match(input,DYNAMIC_COMPONENT,FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component16619); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_object_stack_in_dynamic_component16621);
                    object_stack();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 4 :
                    // BONTCTreeWalker.g:1038:22: ^( DYNAMIC_COMPONENT object )
                    {
                    match(input,DYNAMIC_COMPONENT,FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component16717); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_object_in_dynamic_component16719);
                    object();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 5 :
                    // BONTCTreeWalker.g:1042:22: ^( DYNAMIC_COMPONENT message_relation )
                    {
                    match(input,DYNAMIC_COMPONENT,FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component16815); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_message_relation_in_dynamic_component16817);
                    message_relation();
                    _fsp--;


                    match(input, Token.UP, null); 

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
    // $ANTLR end dynamic_component


    // $ANTLR start scenario_description
    // BONTCTreeWalker.g:1047:1: scenario_description : ^( SCENARIO_DESCRIPTION scenario_name ( COMMENT )? labelled_actions ) ;
    public final void scenario_description() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1049:23: ( ^( SCENARIO_DESCRIPTION scenario_name ( COMMENT )? labelled_actions ) )
            // BONTCTreeWalker.g:1049:24: ^( SCENARIO_DESCRIPTION scenario_name ( COMMENT )? labelled_actions )
            {
            match(input,SCENARIO_DESCRIPTION,FOLLOW_SCENARIO_DESCRIPTION_in_scenario_description16900); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_scenario_name_in_scenario_description16928);
            scenario_name();
            _fsp--;

            // BONTCTreeWalker.g:1051:40: ( COMMENT )?
            int alt142=2;
            int LA142_0 = input.LA(1);

            if ( (LA142_0==COMMENT) ) {
                alt142=1;
            }
            switch (alt142) {
                case 1 :
                    // BONTCTreeWalker.g:1051:41: COMMENT
                    {
                    match(input,COMMENT,FOLLOW_COMMENT_in_scenario_description16931); 

                    }
                    break;

            }

            pushFollow(FOLLOW_labelled_actions_in_scenario_description16960);
            labelled_actions();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end scenario_description


    // $ANTLR start labelled_actions
    // BONTCTreeWalker.g:1056:1: labelled_actions : ^( LABELLED_ACTIONS ( labelled_action )+ ) ;
    public final void labelled_actions() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1056:19: ( ^( LABELLED_ACTIONS ( labelled_action )+ ) )
            // BONTCTreeWalker.g:1056:20: ^( LABELLED_ACTIONS ( labelled_action )+ )
            {
            match(input,LABELLED_ACTIONS,FOLLOW_LABELLED_ACTIONS_in_labelled_actions17063); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:1057:39: ( labelled_action )+
            int cnt143=0;
            loop143:
            do {
                int alt143=2;
                int LA143_0 = input.LA(1);

                if ( (LA143_0==LABELLED_ACTION) ) {
                    alt143=1;
                }


                switch (alt143) {
            	case 1 :
            	    // BONTCTreeWalker.g:1057:40: labelled_action
            	    {
            	    pushFollow(FOLLOW_labelled_action_in_labelled_actions17066);
            	    labelled_action();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt143 >= 1 ) break loop143;
                        EarlyExitException eee =
                            new EarlyExitException(143, input);
                        throw eee;
                }
                cnt143++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end labelled_actions


    // $ANTLR start labelled_action
    // BONTCTreeWalker.g:1061:1: labelled_action : ^( LABELLED_ACTION action_label action_description ) ;
    public final void labelled_action() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1061:18: ( ^( LABELLED_ACTION action_label action_description ) )
            // BONTCTreeWalker.g:1061:19: ^( LABELLED_ACTION action_label action_description )
            {
            match(input,LABELLED_ACTION,FOLLOW_LABELLED_ACTION_in_labelled_action17157); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_action_label_in_labelled_action17159);
            action_label();
            _fsp--;

            pushFollow(FOLLOW_action_description_in_labelled_action17161);
            action_description();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end labelled_action


    // $ANTLR start action_label
    // BONTCTreeWalker.g:1066:1: action_label : ^( ACTION_LABEL MANIFEST_STRING ) ;
    public final void action_label() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1066:15: ( ^( ACTION_LABEL MANIFEST_STRING ) )
            // BONTCTreeWalker.g:1066:16: ^( ACTION_LABEL MANIFEST_STRING )
            {
            match(input,ACTION_LABEL,FOLLOW_ACTION_LABEL_in_action_label17244); 

            match(input, Token.DOWN, null); 
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_action_label17246); 

            match(input, Token.UP, null); 

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
    // $ANTLR end action_label


    // $ANTLR start action_description
    // BONTCTreeWalker.g:1071:1: action_description : ^( ACTION_DESCRIPTION manifest_textblock ) ;
    public final void action_description() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1071:21: ( ^( ACTION_DESCRIPTION manifest_textblock ) )
            // BONTCTreeWalker.g:1071:22: ^( ACTION_DESCRIPTION manifest_textblock )
            {
            match(input,ACTION_DESCRIPTION,FOLLOW_ACTION_DESCRIPTION_in_action_description17326); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_manifest_textblock_in_action_description17328);
            manifest_textblock();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end action_description


    // $ANTLR start scenario_name
    // BONTCTreeWalker.g:1076:1: scenario_name : ^( SCENARIO_NAME manifest_textblock ) ;
    public final void scenario_name() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1076:16: ( ^( SCENARIO_NAME manifest_textblock ) )
            // BONTCTreeWalker.g:1076:17: ^( SCENARIO_NAME manifest_textblock )
            {
            match(input,SCENARIO_NAME,FOLLOW_SCENARIO_NAME_in_scenario_name17421); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_manifest_textblock_in_scenario_name17423);
            manifest_textblock();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end scenario_name


    // $ANTLR start object_group
    // BONTCTreeWalker.g:1081:1: object_group : ^( OBJECT_GROUP ( 'nameless' )? group_name ( COMMENT )? ( group_components )? ) ;
    public final void object_group() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1083:15: ( ^( OBJECT_GROUP ( 'nameless' )? group_name ( COMMENT )? ( group_components )? ) )
            // BONTCTreeWalker.g:1083:16: ^( OBJECT_GROUP ( 'nameless' )? group_name ( COMMENT )? ( group_components )? )
            {
            match(input,OBJECT_GROUP,FOLLOW_OBJECT_GROUP_in_object_group17488); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:1084:31: ( 'nameless' )?
            int alt144=2;
            int LA144_0 = input.LA(1);

            if ( (LA144_0==254) ) {
                alt144=1;
            }
            switch (alt144) {
                case 1 :
                    // BONTCTreeWalker.g:1084:32: 'nameless'
                    {
                    match(input,254,FOLLOW_254_in_object_group17491); 

                    }
                    break;

            }

            pushFollow(FOLLOW_group_name_in_object_group17495);
            group_name();
            _fsp--;

            // BONTCTreeWalker.g:1084:56: ( COMMENT )?
            int alt145=2;
            int LA145_0 = input.LA(1);

            if ( (LA145_0==COMMENT) ) {
                alt145=1;
            }
            switch (alt145) {
                case 1 :
                    // BONTCTreeWalker.g:1084:57: COMMENT
                    {
                    match(input,COMMENT,FOLLOW_COMMENT_in_object_group17498); 

                    }
                    break;

            }

            // BONTCTreeWalker.g:1084:67: ( group_components )?
            int alt146=2;
            int LA146_0 = input.LA(1);

            if ( (LA146_0==GROUP_COMPONENTS) ) {
                alt146=1;
            }
            switch (alt146) {
                case 1 :
                    // BONTCTreeWalker.g:1084:68: group_components
                    {
                    pushFollow(FOLLOW_group_components_in_object_group17503);
                    group_components();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end object_group


    // $ANTLR start group_components
    // BONTCTreeWalker.g:1088:1: group_components : ^( GROUP_COMPONENTS dynamic_block ) ;
    public final void group_components() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1088:19: ( ^( GROUP_COMPONENTS dynamic_block ) )
            // BONTCTreeWalker.g:1088:20: ^( GROUP_COMPONENTS dynamic_block )
            {
            match(input,GROUP_COMPONENTS,FOLLOW_GROUP_COMPONENTS_in_group_components17584); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_dynamic_block_in_group_components17586);
            dynamic_block();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end group_components


    // $ANTLR start object_stack
    // BONTCTreeWalker.g:1093:1: object_stack : ^( OBJECT_STACK object_name ( COMMENT )? ) ;
    public final void object_stack() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1093:15: ( ^( OBJECT_STACK object_name ( COMMENT )? ) )
            // BONTCTreeWalker.g:1093:16: ^( OBJECT_STACK object_name ( COMMENT )? )
            {
            match(input,OBJECT_STACK,FOLLOW_OBJECT_STACK_in_object_stack17672); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_object_name_in_object_stack17674);
            object_name();
            _fsp--;

            // BONTCTreeWalker.g:1094:43: ( COMMENT )?
            int alt147=2;
            int LA147_0 = input.LA(1);

            if ( (LA147_0==COMMENT) ) {
                alt147=1;
            }
            switch (alt147) {
                case 1 :
                    // BONTCTreeWalker.g:1094:44: COMMENT
                    {
                    match(input,COMMENT,FOLLOW_COMMENT_in_object_stack17677); 

                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end object_stack


    // $ANTLR start object
    // BONTCTreeWalker.g:1098:1: object : ^( OBJECT object_name ( COMMENT )? ) ;
    public final void object() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1098:9: ( ^( OBJECT object_name ( COMMENT )? ) )
            // BONTCTreeWalker.g:1098:10: ^( OBJECT object_name ( COMMENT )? )
            {
            match(input,OBJECT,FOLLOW_OBJECT_in_object17747); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_object_name_in_object17749);
            object_name();
            _fsp--;

            // BONTCTreeWalker.g:1099:31: ( COMMENT )?
            int alt148=2;
            int LA148_0 = input.LA(1);

            if ( (LA148_0==COMMENT) ) {
                alt148=1;
            }
            switch (alt148) {
                case 1 :
                    // BONTCTreeWalker.g:1099:32: COMMENT
                    {
                    match(input,COMMENT,FOLLOW_COMMENT_in_object17752); 

                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end object


    // $ANTLR start message_relation
    // BONTCTreeWalker.g:1103:1: message_relation : ^( MESSAGE_RELATION caller receiver ( message_label )? ) ;
    public final void message_relation() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1105:19: ( ^( MESSAGE_RELATION caller receiver ( message_label )? ) )
            // BONTCTreeWalker.g:1105:20: ^( MESSAGE_RELATION caller receiver ( message_label )? )
            {
            match(input,MESSAGE_RELATION,FOLLOW_MESSAGE_RELATION_in_message_relation17809); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_caller_in_message_relation17811);
            caller();
            _fsp--;

            pushFollow(FOLLOW_receiver_in_message_relation17813);
            receiver();
            _fsp--;

            // BONTCTreeWalker.g:1106:55: ( message_label )?
            int alt149=2;
            int LA149_0 = input.LA(1);

            if ( (LA149_0==MESSAGE_LABEL) ) {
                alt149=1;
            }
            switch (alt149) {
                case 1 :
                    // BONTCTreeWalker.g:1106:56: message_label
                    {
                    pushFollow(FOLLOW_message_label_in_message_relation17816);
                    message_label();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end message_relation


    // $ANTLR start caller
    // BONTCTreeWalker.g:1110:1: caller : ^( RECEIVER dynamic_ref ) ;
    public final void caller() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1110:9: ( ^( RECEIVER dynamic_ref ) )
            // BONTCTreeWalker.g:1110:10: ^( RECEIVER dynamic_ref )
            {
            match(input,RECEIVER,FOLLOW_RECEIVER_in_caller17898); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_dynamic_ref_in_caller17900);
            dynamic_ref();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end caller


    // $ANTLR start receiver
    // BONTCTreeWalker.g:1115:1: receiver : ^( RECEIVER dynamic_ref ) ;
    public final void receiver() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1115:11: ( ^( RECEIVER dynamic_ref ) )
            // BONTCTreeWalker.g:1115:12: ^( RECEIVER dynamic_ref )
            {
            match(input,RECEIVER,FOLLOW_RECEIVER_in_receiver17952); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_dynamic_ref_in_receiver17954);
            dynamic_ref();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end receiver


    // $ANTLR start dynamic_ref
    // BONTCTreeWalker.g:1120:1: dynamic_ref : ^( DYNAMIC_REF ( extended_id )+ ) ;
    public final void dynamic_ref() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1120:14: ( ^( DYNAMIC_REF ( extended_id )+ ) )
            // BONTCTreeWalker.g:1120:15: ^( DYNAMIC_REF ( extended_id )+ )
            {
            match(input,DYNAMIC_REF,FOLLOW_DYNAMIC_REF_in_dynamic_ref18015); 

            match(input, Token.DOWN, null); 
            // BONTCTreeWalker.g:1121:29: ( extended_id )+
            int cnt150=0;
            loop150:
            do {
                int alt150=2;
                int LA150_0 = input.LA(1);

                if ( (LA150_0==EXTENDED_ID) ) {
                    alt150=1;
                }


                switch (alt150) {
            	case 1 :
            	    // BONTCTreeWalker.g:1121:30: extended_id
            	    {
            	    pushFollow(FOLLOW_extended_id_in_dynamic_ref18018);
            	    extended_id();
            	    _fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt150 >= 1 ) break loop150;
                        EarlyExitException eee =
                            new EarlyExitException(150, input);
                        throw eee;
                }
                cnt150++;
            } while (true);


            match(input, Token.UP, null); 

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
    // $ANTLR end dynamic_ref


    // $ANTLR start dynamic_component_name
    // BONTCTreeWalker.g:1125:1: dynamic_component_name : ( ^( DYNAMIC_COMPONENT_NAME IDENTIFIER ( extended_id )? ) | ^( DYNAMIC_COMPONENT_NAME INTEGER ) );
    public final void dynamic_component_name() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1125:25: ( ^( DYNAMIC_COMPONENT_NAME IDENTIFIER ( extended_id )? ) | ^( DYNAMIC_COMPONENT_NAME INTEGER ) )
            int alt152=2;
            int LA152_0 = input.LA(1);

            if ( (LA152_0==DYNAMIC_COMPONENT_NAME) ) {
                int LA152_1 = input.LA(2);

                if ( (LA152_1==DOWN) ) {
                    int LA152_2 = input.LA(3);

                    if ( (LA152_2==INTEGER) ) {
                        alt152=2;
                    }
                    else if ( (LA152_2==IDENTIFIER) ) {
                        alt152=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("1125:1: dynamic_component_name : ( ^( DYNAMIC_COMPONENT_NAME IDENTIFIER ( extended_id )? ) | ^( DYNAMIC_COMPONENT_NAME INTEGER ) );", 152, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1125:1: dynamic_component_name : ( ^( DYNAMIC_COMPONENT_NAME IDENTIFIER ( extended_id )? ) | ^( DYNAMIC_COMPONENT_NAME INTEGER ) );", 152, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1125:1: dynamic_component_name : ( ^( DYNAMIC_COMPONENT_NAME IDENTIFIER ( extended_id )? ) | ^( DYNAMIC_COMPONENT_NAME INTEGER ) );", 152, 0, input);

                throw nvae;
            }
            switch (alt152) {
                case 1 :
                    // BONTCTreeWalker.g:1125:26: ^( DYNAMIC_COMPONENT_NAME IDENTIFIER ( extended_id )? )
                    {
                    match(input,DYNAMIC_COMPONENT_NAME,FOLLOW_DYNAMIC_COMPONENT_NAME_in_dynamic_component_name18088); 

                    match(input, Token.DOWN, null); 
                    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_dynamic_component_name18090); 
                    // BONTCTreeWalker.g:1126:62: ( extended_id )?
                    int alt151=2;
                    int LA151_0 = input.LA(1);

                    if ( (LA151_0==EXTENDED_ID) ) {
                        alt151=1;
                    }
                    switch (alt151) {
                        case 1 :
                            // BONTCTreeWalker.g:1126:63: extended_id
                            {
                            pushFollow(FOLLOW_extended_id_in_dynamic_component_name18093);
                            extended_id();
                            _fsp--;


                            }
                            break;

                    }


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1129:26: ^( DYNAMIC_COMPONENT_NAME INTEGER )
                    {
                    match(input,DYNAMIC_COMPONENT_NAME,FOLLOW_DYNAMIC_COMPONENT_NAME_in_dynamic_component_name18206); 

                    match(input, Token.DOWN, null); 
                    match(input,INTEGER,FOLLOW_INTEGER_in_dynamic_component_name18208); 

                    match(input, Token.UP, null); 

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
    // $ANTLR end dynamic_component_name


    // $ANTLR start object_name
    // BONTCTreeWalker.g:1134:1: object_name : ^( OBJECT_NAME class_name ( extended_id )? ) ;
    public final void object_name() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1134:14: ( ^( OBJECT_NAME class_name ( extended_id )? ) )
            // BONTCTreeWalker.g:1134:15: ^( OBJECT_NAME class_name ( extended_id )? )
            {
            match(input,OBJECT_NAME,FOLLOW_OBJECT_NAME_in_object_name18287); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_class_name_in_object_name18289);
            class_name();
            _fsp--;

            // BONTCTreeWalker.g:1135:40: ( extended_id )?
            int alt153=2;
            int LA153_0 = input.LA(1);

            if ( (LA153_0==EXTENDED_ID) ) {
                alt153=1;
            }
            switch (alt153) {
                case 1 :
                    // BONTCTreeWalker.g:1135:41: extended_id
                    {
                    pushFollow(FOLLOW_extended_id_in_object_name18292);
                    extended_id();
                    _fsp--;


                    }
                    break;

            }


            match(input, Token.UP, null); 

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
    // $ANTLR end object_name


    // $ANTLR start group_name
    // BONTCTreeWalker.g:1139:1: group_name : ^( GROUP_NAME extended_id ) ;
    public final void group_name() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1139:13: ( ^( GROUP_NAME extended_id ) )
            // BONTCTreeWalker.g:1139:14: ^( GROUP_NAME extended_id )
            {
            match(input,GROUP_NAME,FOLLOW_GROUP_NAME_in_group_name18363); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_extended_id_in_group_name18365);
            extended_id();
            _fsp--;


            match(input, Token.UP, null); 

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
    // $ANTLR end group_name


    // $ANTLR start message_label
    // BONTCTreeWalker.g:1144:1: message_label : ^( MESSAGE_LABEL MANIFEST_STRING ) ;
    public final void message_label() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1144:16: ( ^( MESSAGE_LABEL MANIFEST_STRING ) )
            // BONTCTreeWalker.g:1144:17: ^( MESSAGE_LABEL MANIFEST_STRING )
            {
            match(input,MESSAGE_LABEL,FOLLOW_MESSAGE_LABEL_in_message_label18434); 

            match(input, Token.DOWN, null); 
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_message_label18436); 

            match(input, Token.UP, null); 

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
    // $ANTLR end message_label


    // $ANTLR start notational_tuning
    // BONTCTreeWalker.g:1149:1: notational_tuning : ( ^( NOTATIONAL_TUNING change_string_marks ) | ^( NOTATIONAL_TUNING change_concatenator ) | ^( NOTATIONAL_TUNING change_prefix ) );
    public final void notational_tuning() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1152:20: ( ^( NOTATIONAL_TUNING change_string_marks ) | ^( NOTATIONAL_TUNING change_concatenator ) | ^( NOTATIONAL_TUNING change_prefix ) )
            int alt154=3;
            int LA154_0 = input.LA(1);

            if ( (LA154_0==NOTATIONAL_TUNING) ) {
                int LA154_1 = input.LA(2);

                if ( (LA154_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case CHANGE_STRING_MARKS:
                        {
                        alt154=1;
                        }
                        break;
                    case CHANGE_PREFIX:
                        {
                        alt154=3;
                        }
                        break;
                    case CHANGE_CONCATENATOR:
                        {
                        alt154=2;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("1149:1: notational_tuning : ( ^( NOTATIONAL_TUNING change_string_marks ) | ^( NOTATIONAL_TUNING change_concatenator ) | ^( NOTATIONAL_TUNING change_prefix ) );", 154, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1149:1: notational_tuning : ( ^( NOTATIONAL_TUNING change_string_marks ) | ^( NOTATIONAL_TUNING change_concatenator ) | ^( NOTATIONAL_TUNING change_prefix ) );", 154, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1149:1: notational_tuning : ( ^( NOTATIONAL_TUNING change_string_marks ) | ^( NOTATIONAL_TUNING change_concatenator ) | ^( NOTATIONAL_TUNING change_prefix ) );", 154, 0, input);

                throw nvae;
            }
            switch (alt154) {
                case 1 :
                    // BONTCTreeWalker.g:1152:21: ^( NOTATIONAL_TUNING change_string_marks )
                    {
                    match(input,NOTATIONAL_TUNING,FOLLOW_NOTATIONAL_TUNING_in_notational_tuning18505); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_change_string_marks_in_notational_tuning18507);
                    change_string_marks();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1156:21: ^( NOTATIONAL_TUNING change_concatenator )
                    {
                    match(input,NOTATIONAL_TUNING,FOLLOW_NOTATIONAL_TUNING_in_notational_tuning18598); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_change_concatenator_in_notational_tuning18600);
                    change_concatenator();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 3 :
                    // BONTCTreeWalker.g:1160:21: ^( NOTATIONAL_TUNING change_prefix )
                    {
                    match(input,NOTATIONAL_TUNING,FOLLOW_NOTATIONAL_TUNING_in_notational_tuning18692); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_change_prefix_in_notational_tuning18694);
                    change_prefix();
                    _fsp--;


                    match(input, Token.UP, null); 

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
    // $ANTLR end notational_tuning


    // $ANTLR start change_string_marks
    // BONTCTreeWalker.g:1165:1: change_string_marks : ^( CHANGE_STRING_MARKS MANIFEST_STRING MANIFEST_STRING ) ;
    public final void change_string_marks() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1165:22: ( ^( CHANGE_STRING_MARKS MANIFEST_STRING MANIFEST_STRING ) )
            // BONTCTreeWalker.g:1165:23: ^( CHANGE_STRING_MARKS MANIFEST_STRING MANIFEST_STRING )
            {
            match(input,CHANGE_STRING_MARKS,FOLLOW_CHANGE_STRING_MARKS_in_change_string_marks18790); 

            match(input, Token.DOWN, null); 
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_string_marks18792); 
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_string_marks18794); 

            match(input, Token.UP, null); 

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
    // $ANTLR end change_string_marks


    // $ANTLR start change_concatenator
    // BONTCTreeWalker.g:1170:1: change_concatenator : ^( CHANGE_CONCATENATOR MANIFEST_STRING ) ;
    public final void change_concatenator() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1170:22: ( ^( CHANGE_CONCATENATOR MANIFEST_STRING ) )
            // BONTCTreeWalker.g:1170:23: ^( CHANGE_CONCATENATOR MANIFEST_STRING )
            {
            match(input,CHANGE_CONCATENATOR,FOLLOW_CHANGE_CONCATENATOR_in_change_concatenator18896); 

            match(input, Token.DOWN, null); 
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_concatenator18898); 

            match(input, Token.UP, null); 

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
    // $ANTLR end change_concatenator


    // $ANTLR start change_prefix
    // BONTCTreeWalker.g:1175:1: change_prefix : ^( CHANGE_PREFIX MANIFEST_STRING ) ;
    public final void change_prefix() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1175:16: ( ^( CHANGE_PREFIX MANIFEST_STRING ) )
            // BONTCTreeWalker.g:1175:17: ^( CHANGE_PREFIX MANIFEST_STRING )
            {
            match(input,CHANGE_PREFIX,FOLLOW_CHANGE_PREFIX_in_change_prefix18994); 

            match(input, Token.DOWN, null); 
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_prefix18996); 

            match(input, Token.UP, null); 

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
    // $ANTLR end change_prefix


    // $ANTLR start expression
    // BONTCTreeWalker.g:1180:1: expression : ( ^( EXPRESSION equivalence_expression ) | ^( EXPRESSION quantification ) );
    public final void expression() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1184:13: ( ^( EXPRESSION equivalence_expression ) | ^( EXPRESSION quantification ) )
            int alt155=2;
            int LA155_0 = input.LA(1);

            if ( (LA155_0==EXPRESSION) ) {
                int LA155_1 = input.LA(2);

                if ( (LA155_1==DOWN) ) {
                    int LA155_2 = input.LA(3);

                    if ( (LA155_2==QUANTIFICATION) ) {
                        alt155=2;
                    }
                    else if ( (LA155_2==CALL_CHAIN||LA155_2==CONSTANT||LA155_2==NOT_MEMBER_OF||LA155_2==MOD_POW_OP||LA155_2==196||LA155_2==225||LA155_2==227||LA155_2==246||(LA155_2>=262 && LA155_2<=278)||LA155_2==280) ) {
                        alt155=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("1180:1: expression : ( ^( EXPRESSION equivalence_expression ) | ^( EXPRESSION quantification ) );", 155, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1180:1: expression : ( ^( EXPRESSION equivalence_expression ) | ^( EXPRESSION quantification ) );", 155, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1180:1: expression : ( ^( EXPRESSION equivalence_expression ) | ^( EXPRESSION quantification ) );", 155, 0, input);

                throw nvae;
            }
            switch (alt155) {
                case 1 :
                    // BONTCTreeWalker.g:1184:14: ^( EXPRESSION equivalence_expression )
                    {
                    match(input,EXPRESSION,FOLLOW_EXPRESSION_in_expression19063); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_equivalence_expression_in_expression19065);
                    equivalence_expression();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1188:14: ^( EXPRESSION quantification )
                    {
                    match(input,EXPRESSION,FOLLOW_EXPRESSION_in_expression19129); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_quantification_in_expression19131);
                    quantification();
                    _fsp--;


                    match(input, Token.UP, null); 

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
    // $ANTLR end expression


    // $ANTLR start equivalence_expression
    // BONTCTreeWalker.g:1193:1: equivalence_expression : ( ^(s= '<->' equivalence_expression equivalence_expression ) | implies_expression );
    public final void equivalence_expression() throws RecognitionException {
        CommonTree s=null;

        try {
            // BONTCTreeWalker.g:1193:24: ( ^(s= '<->' equivalence_expression equivalence_expression ) | implies_expression )
            int alt156=2;
            int LA156_0 = input.LA(1);

            if ( (LA156_0==262) ) {
                alt156=1;
            }
            else if ( (LA156_0==CALL_CHAIN||LA156_0==CONSTANT||LA156_0==NOT_MEMBER_OF||LA156_0==MOD_POW_OP||LA156_0==196||LA156_0==225||LA156_0==227||LA156_0==246||(LA156_0>=263 && LA156_0<=278)||LA156_0==280) ) {
                alt156=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1193:1: equivalence_expression : ( ^(s= '<->' equivalence_expression equivalence_expression ) | implies_expression );", 156, 0, input);

                throw nvae;
            }
            switch (alt156) {
                case 1 :
                    // BONTCTreeWalker.g:1193:27: ^(s= '<->' equivalence_expression equivalence_expression )
                    {
                    s=(CommonTree)input.LT(1);
                    match(input,262,FOLLOW_262_in_equivalence_expression19175); 

                     getFTC().checkType("BOOL",getSLoc(s.token)); 
                     getContext().addTypeRequirement(getFTC().getType("BOOL")); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_equivalence_expression_in_equivalence_expression19272);
                    equivalence_expression();
                    _fsp--;

                    pushFollow(FOLLOW_equivalence_expression_in_equivalence_expression19305);
                    equivalence_expression();
                    _fsp--;

                     getContext().removeTypeRequirement(); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1200:16: implies_expression
                    {
                    pushFollow(FOLLOW_implies_expression_in_equivalence_expression19385);
                    implies_expression();
                    _fsp--;


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
    // $ANTLR end equivalence_expression


    // $ANTLR start implies_expression
    // BONTCTreeWalker.g:1204:1: implies_expression : ( ^(s= '->' implies_expression implies_expression ) | and_or_xor_expression );
    public final void implies_expression() throws RecognitionException {
        CommonTree s=null;

        try {
            // BONTCTreeWalker.g:1204:21: ( ^(s= '->' implies_expression implies_expression ) | and_or_xor_expression )
            int alt157=2;
            int LA157_0 = input.LA(1);

            if ( (LA157_0==227) ) {
                alt157=1;
            }
            else if ( (LA157_0==CALL_CHAIN||LA157_0==CONSTANT||LA157_0==NOT_MEMBER_OF||LA157_0==MOD_POW_OP||LA157_0==196||LA157_0==225||LA157_0==246||(LA157_0>=263 && LA157_0<=278)||LA157_0==280) ) {
                alt157=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1204:1: implies_expression : ( ^(s= '->' implies_expression implies_expression ) | and_or_xor_expression );", 157, 0, input);

                throw nvae;
            }
            switch (alt157) {
                case 1 :
                    // BONTCTreeWalker.g:1204:24: ^(s= '->' implies_expression implies_expression )
                    {
                    s=(CommonTree)input.LT(1);
                    match(input,227,FOLLOW_227_in_implies_expression19425); 

                     getFTC().checkType("BOOL",getSLoc(s.token)); 
                     getContext().addTypeRequirement(getFTC().getType("BOOL")); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_implies_expression_in_implies_expression19510);
                    implies_expression();
                    _fsp--;

                    pushFollow(FOLLOW_implies_expression_in_implies_expression19539);
                    implies_expression();
                    _fsp--;

                     getContext().removeTypeRequirement(); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1211:25: and_or_xor_expression
                    {
                    pushFollow(FOLLOW_and_or_xor_expression_in_implies_expression19620);
                    and_or_xor_expression();
                    _fsp--;


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
    // $ANTLR end implies_expression


    // $ANTLR start and_or_xor_expression
    // BONTCTreeWalker.g:1214:1: and_or_xor_expression : ( ^(s= and_or_xor_op and_or_xor_expression and_or_xor_expression ) | comparison_expression );
    public final void and_or_xor_expression() throws RecognitionException {
        and_or_xor_op_return s = null;


        try {
            // BONTCTreeWalker.g:1214:24: ( ^(s= and_or_xor_op and_or_xor_expression and_or_xor_expression ) | comparison_expression )
            int alt158=2;
            int LA158_0 = input.LA(1);

            if ( ((LA158_0>=265 && LA158_0<=267)) ) {
                alt158=1;
            }
            else if ( (LA158_0==CALL_CHAIN||LA158_0==CONSTANT||LA158_0==NOT_MEMBER_OF||LA158_0==MOD_POW_OP||LA158_0==196||LA158_0==225||LA158_0==246||(LA158_0>=263 && LA158_0<=264)||(LA158_0>=268 && LA158_0<=278)||LA158_0==280) ) {
                alt158=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1214:1: and_or_xor_expression : ( ^(s= and_or_xor_op and_or_xor_expression and_or_xor_expression ) | comparison_expression );", 158, 0, input);

                throw nvae;
            }
            switch (alt158) {
                case 1 :
                    // BONTCTreeWalker.g:1214:27: ^(s= and_or_xor_op and_or_xor_expression and_or_xor_expression )
                    {
                    pushFollow(FOLLOW_and_or_xor_op_in_and_or_xor_expression19655);
                    s=and_or_xor_op();
                    _fsp--;


                     getFTC().checkType("BOOL",getSLoc(((CommonTree)s.start).token)); 
                     getContext().addTypeRequirement(getFTC().getType("BOOL")); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_and_or_xor_expression_in_and_or_xor_expression19749);
                    and_or_xor_expression();
                    _fsp--;

                    pushFollow(FOLLOW_and_or_xor_expression_in_and_or_xor_expression19781);
                    and_or_xor_expression();
                    _fsp--;

                     getContext().removeTypeRequirement(); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1221:16: comparison_expression
                    {
                    pushFollow(FOLLOW_comparison_expression_in_and_or_xor_expression19858);
                    comparison_expression();
                    _fsp--;


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
    // $ANTLR end and_or_xor_expression


    // $ANTLR start comparison_expression
    // BONTCTreeWalker.g:1224:1: comparison_expression : ( ^(n= normal_comparison_op comparison_expression comparison_expression ) | ^( member_type_comparison_op comparison_expression comparison_expression ) | add_sub_expression );
    public final void comparison_expression() throws RecognitionException {
        normal_comparison_op_return n = null;


        try {
            // BONTCTreeWalker.g:1224:24: ( ^(n= normal_comparison_op comparison_expression comparison_expression ) | ^( member_type_comparison_op comparison_expression comparison_expression ) | add_sub_expression )
            int alt159=3;
            switch ( input.LA(1) ) {
            case 271:
            case 272:
            case 273:
            case 274:
            case 275:
            case 276:
                {
                alt159=1;
                }
                break;
            case NOT_MEMBER_OF:
            case 196:
            case 246:
                {
                alt159=2;
                }
                break;
            case CALL_CHAIN:
            case CONSTANT:
            case MOD_POW_OP:
            case 225:
            case 263:
            case 264:
            case 268:
            case 269:
            case 270:
            case 277:
            case 278:
            case 280:
                {
                alt159=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("1224:1: comparison_expression : ( ^(n= normal_comparison_op comparison_expression comparison_expression ) | ^( member_type_comparison_op comparison_expression comparison_expression ) | add_sub_expression );", 159, 0, input);

                throw nvae;
            }

            switch (alt159) {
                case 1 :
                    // BONTCTreeWalker.g:1224:27: ^(n= normal_comparison_op comparison_expression comparison_expression )
                    {
                    pushFollow(FOLLOW_normal_comparison_op_in_comparison_expression19896);
                    n=normal_comparison_op();
                    _fsp--;


                     getFTC().checkType("BOOL",getSLoc(((CommonTree)n.start).token)); 
                     getContext().addTypeRequirement(getFTC().getType("VALUE")); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_comparison_expression_in_comparison_expression19989);
                    comparison_expression();
                    _fsp--;

                    pushFollow(FOLLOW_comparison_expression_in_comparison_expression20021);
                    comparison_expression();
                    _fsp--;

                     getContext().removeTypeRequirement(); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1232:27: ^( member_type_comparison_op comparison_expression comparison_expression )
                    {
                    pushFollow(FOLLOW_member_type_comparison_op_in_comparison_expression20138);
                    member_type_comparison_op();
                    _fsp--;


                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_comparison_expression_in_comparison_expression20169);
                    comparison_expression();
                    _fsp--;

                    pushFollow(FOLLOW_comparison_expression_in_comparison_expression20201);
                    comparison_expression();
                    _fsp--;


                    match(input, Token.UP, null); 

                    }
                    break;
                case 3 :
                    // BONTCTreeWalker.g:1236:16: add_sub_expression
                    {
                    pushFollow(FOLLOW_add_sub_expression_in_comparison_expression20247);
                    add_sub_expression();
                    _fsp--;


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
    // $ANTLR end comparison_expression


    // $ANTLR start add_sub_expression
    // BONTCTreeWalker.g:1239:1: add_sub_expression : ( ^(a= add_sub_op add_sub_expression add_sub_expression ) | mul_div_expression );
    public final void add_sub_expression() throws RecognitionException {
        add_sub_op_return a = null;


        try {
            // BONTCTreeWalker.g:1239:21: ( ^(a= add_sub_op add_sub_expression add_sub_expression ) | mul_div_expression )
            int alt160=2;
            int LA160_0 = input.LA(1);

            if ( ((LA160_0>=263 && LA160_0<=264)) ) {
                int LA160_1 = input.LA(2);

                if ( (LA160_1==CALL_CHAIN||LA160_1==CONSTANT||LA160_1==225||(LA160_1>=263 && LA160_1<=264)||(LA160_1>=268 && LA160_1<=270)) ) {
                    alt160=2;
                }
                else if ( (LA160_1==DOWN) ) {
                    alt160=1;
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1239:1: add_sub_expression : ( ^(a= add_sub_op add_sub_expression add_sub_expression ) | mul_div_expression );", 160, 1, input);

                    throw nvae;
                }
            }
            else if ( (LA160_0==CALL_CHAIN||LA160_0==CONSTANT||LA160_0==MOD_POW_OP||LA160_0==225||(LA160_0>=268 && LA160_0<=270)||(LA160_0>=277 && LA160_0<=278)||LA160_0==280) ) {
                alt160=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1239:1: add_sub_expression : ( ^(a= add_sub_op add_sub_expression add_sub_expression ) | mul_div_expression );", 160, 0, input);

                throw nvae;
            }
            switch (alt160) {
                case 1 :
                    // BONTCTreeWalker.g:1239:24: ^(a= add_sub_op add_sub_expression add_sub_expression )
                    {
                    pushFollow(FOLLOW_add_sub_op_in_add_sub_expression20285);
                    a=add_sub_op();
                    _fsp--;


                     getFTC().checkType("VALUE",getSLoc(((CommonTree)a.start).token)); 
                     getContext().addTypeRequirement(getFTC().getType("VALUE")); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_add_sub_expression_in_add_sub_expression20370);
                    add_sub_expression();
                    _fsp--;

                    pushFollow(FOLLOW_add_sub_expression_in_add_sub_expression20399);
                    add_sub_expression();
                    _fsp--;

                     getContext().removeTypeRequirement(); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1246:14: mul_div_expression
                    {
                    pushFollow(FOLLOW_mul_div_expression_in_add_sub_expression20468);
                    mul_div_expression();
                    _fsp--;


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
    // $ANTLR end add_sub_expression


    // $ANTLR start mul_div_expression
    // BONTCTreeWalker.g:1249:1: mul_div_expression : ( ^(m= mul_div_op mul_div_expression mul_div_expression ) | mod_pow_expression );
    public final void mul_div_expression() throws RecognitionException {
        mul_div_op_return m = null;


        try {
            // BONTCTreeWalker.g:1249:21: ( ^(m= mul_div_op mul_div_expression mul_div_expression ) | mod_pow_expression )
            int alt161=2;
            int LA161_0 = input.LA(1);

            if ( ((LA161_0>=277 && LA161_0<=278)||LA161_0==280) ) {
                alt161=1;
            }
            else if ( (LA161_0==CALL_CHAIN||LA161_0==CONSTANT||LA161_0==MOD_POW_OP||LA161_0==225||(LA161_0>=263 && LA161_0<=264)||(LA161_0>=268 && LA161_0<=270)) ) {
                alt161=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1249:1: mul_div_expression : ( ^(m= mul_div_op mul_div_expression mul_div_expression ) | mod_pow_expression );", 161, 0, input);

                throw nvae;
            }
            switch (alt161) {
                case 1 :
                    // BONTCTreeWalker.g:1249:25: ^(m= mul_div_op mul_div_expression mul_div_expression )
                    {
                    pushFollow(FOLLOW_mul_div_op_in_mul_div_expression20504);
                    m=mul_div_op();
                    _fsp--;


                     getFTC().checkType("VALUE",getSLoc(((CommonTree)m.start).token)); 
                     getContext().addTypeRequirement(getFTC().getType("VALUE")); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_mul_div_expression_in_mul_div_expression20592);
                    mul_div_expression();
                    _fsp--;

                    pushFollow(FOLLOW_mul_div_expression_in_mul_div_expression20622);
                    mul_div_expression();
                    _fsp--;

                     getContext().removeTypeRequirement(); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1256:14: mod_pow_expression
                    {
                    pushFollow(FOLLOW_mod_pow_expression_in_mul_div_expression20693);
                    mod_pow_expression();
                    _fsp--;


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
    // $ANTLR end mul_div_expression


    // $ANTLR start mod_pow_expression
    // BONTCTreeWalker.g:1260:1: mod_pow_expression : ( ^(m= MOD_POW_OP mod_pow_expression mod_pow_expression ) | lowest_expression );
    public final void mod_pow_expression() throws RecognitionException {
        CommonTree m=null;

        try {
            // BONTCTreeWalker.g:1260:21: ( ^(m= MOD_POW_OP mod_pow_expression mod_pow_expression ) | lowest_expression )
            int alt162=2;
            int LA162_0 = input.LA(1);

            if ( (LA162_0==MOD_POW_OP) ) {
                alt162=1;
            }
            else if ( (LA162_0==CALL_CHAIN||LA162_0==CONSTANT||LA162_0==225||(LA162_0>=263 && LA162_0<=264)||(LA162_0>=268 && LA162_0<=270)) ) {
                alt162=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1260:1: mod_pow_expression : ( ^(m= MOD_POW_OP mod_pow_expression mod_pow_expression ) | lowest_expression );", 162, 0, input);

                throw nvae;
            }
            switch (alt162) {
                case 1 :
                    // BONTCTreeWalker.g:1260:24: ^(m= MOD_POW_OP mod_pow_expression mod_pow_expression )
                    {
                    m=(CommonTree)input.LT(1);
                    match(input,MOD_POW_OP,FOLLOW_MOD_POW_OP_in_mod_pow_expression20729); 

                     getFTC().checkType("VALUE",getSLoc(m.token)); 
                     getContext().addTypeRequirement(getFTC().getType("VALUE")); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_mod_pow_expression_in_mod_pow_expression20814);
                    mod_pow_expression();
                    _fsp--;

                    pushFollow(FOLLOW_mod_pow_expression_in_mod_pow_expression20843);
                    mod_pow_expression();
                    _fsp--;

                     getContext().removeTypeRequirement(); 

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1267:24: lowest_expression
                    {
                    pushFollow(FOLLOW_lowest_expression_in_mod_pow_expression20922);
                    lowest_expression();
                    _fsp--;


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
    // $ANTLR end mod_pow_expression


    // $ANTLR start lowest_expression
    // BONTCTreeWalker.g:1270:1: lowest_expression : ( constant | a= add_sub_op lowest_expression | d= delta lowest_expression | old lowest_expression | n= not lowest_expression | '(' expression ')' ( '.' call_chain )? | call_chain );
    public final void lowest_expression() throws RecognitionException {
        add_sub_op_return a = null;

        delta_return d = null;

        not_return n = null;


        try {
            // BONTCTreeWalker.g:1270:20: ( constant | a= add_sub_op lowest_expression | d= delta lowest_expression | old lowest_expression | n= not lowest_expression | '(' expression ')' ( '.' call_chain )? | call_chain )
            int alt164=7;
            switch ( input.LA(1) ) {
            case CONSTANT:
                {
                alt164=1;
                }
                break;
            case 263:
            case 264:
                {
                alt164=2;
                }
                break;
            case 268:
                {
                alt164=3;
                }
                break;
            case 269:
                {
                alt164=4;
                }
                break;
            case 270:
                {
                alt164=5;
                }
                break;
            case 225:
                {
                alt164=6;
                }
                break;
            case CALL_CHAIN:
                {
                alt164=7;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("1270:1: lowest_expression : ( constant | a= add_sub_op lowest_expression | d= delta lowest_expression | old lowest_expression | n= not lowest_expression | '(' expression ')' ( '.' call_chain )? | call_chain );", 164, 0, input);

                throw nvae;
            }

            switch (alt164) {
                case 1 :
                    // BONTCTreeWalker.g:1270:23: constant
                    {
                    pushFollow(FOLLOW_constant_in_lowest_expression20953);
                    constant();
                    _fsp--;


                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1271:23: a= add_sub_op lowest_expression
                    {
                    pushFollow(FOLLOW_add_sub_op_in_lowest_expression20979);
                    a=add_sub_op();
                    _fsp--;

                     getFTC().checkType("VALUE",getSLoc(((CommonTree)a.start).token)); 
                     getContext().addTypeRequirement(getFTC().getType("VALUE")); 
                    pushFollow(FOLLOW_lowest_expression_in_lowest_expression21052);
                    lowest_expression();
                    _fsp--;

                     getContext().removeTypeRequirement(); 

                    }
                    break;
                case 3 :
                    // BONTCTreeWalker.g:1276:13: d= delta lowest_expression
                    {
                    pushFollow(FOLLOW_delta_in_lowest_expression21092);
                    d=delta();
                    _fsp--;

                     getFTC().checkType("VALUE",getSLoc(((CommonTree)d.start).token)); 
                    pushFollow(FOLLOW_lowest_expression_in_lowest_expression21133);
                    lowest_expression();
                    _fsp--;


                    }
                    break;
                case 4 :
                    // BONTCTreeWalker.g:1280:13: old lowest_expression
                    {
                    pushFollow(FOLLOW_old_in_lowest_expression21147);
                    old();
                    _fsp--;

                    pushFollow(FOLLOW_lowest_expression_in_lowest_expression21149);
                    lowest_expression();
                    _fsp--;


                    }
                    break;
                case 5 :
                    // BONTCTreeWalker.g:1281:13: n= not lowest_expression
                    {
                    pushFollow(FOLLOW_not_in_lowest_expression21165);
                    n=not();
                    _fsp--;

                     getFTC().checkType("BOOL",getSLoc(((CommonTree)n.start).token)); 
                     getContext().addTypeRequirement(getFTC().getType("BOOL")); 
                    pushFollow(FOLLOW_lowest_expression_in_lowest_expression21218);
                    lowest_expression();
                    _fsp--;

                     getContext().removeTypeRequirement(); 

                    }
                    break;
                case 6 :
                    // BONTCTreeWalker.g:1286:18: '(' expression ')' ( '.' call_chain )?
                    {
                    match(input,225,FOLLOW_225_in_lowest_expression21251); 
                    pushFollow(FOLLOW_expression_in_lowest_expression21271);
                    expression();
                    _fsp--;

                    match(input,226,FOLLOW_226_in_lowest_expression21291); 
                    // BONTCTreeWalker.g:1289:18: ( '.' call_chain )?
                    int alt163=2;
                    int LA163_0 = input.LA(1);

                    if ( (LA163_0==232) ) {
                        alt163=1;
                    }
                    switch (alt163) {
                        case 1 :
                            // BONTCTreeWalker.g:1289:19: '.' call_chain
                            {
                            match(input,232,FOLLOW_232_in_lowest_expression21312); 
                            pushFollow(FOLLOW_call_chain_in_lowest_expression21314);
                            call_chain();
                            _fsp--;


                            }
                            break;

                    }


                    }
                    break;
                case 7 :
                    // BONTCTreeWalker.g:1290:18: call_chain
                    {
                    pushFollow(FOLLOW_call_chain_in_lowest_expression21335);
                    call_chain();
                    _fsp--;


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
    // $ANTLR end lowest_expression


    // $ANTLR start manifest_textblock
    // BONTCTreeWalker.g:1300:1: manifest_textblock : ( MANIFEST_STRING | MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END );
    public final void manifest_textblock() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1300:21: ( MANIFEST_STRING | MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END )
            int alt166=2;
            int LA166_0 = input.LA(1);

            if ( (LA166_0==MANIFEST_STRING) ) {
                alt166=1;
            }
            else if ( (LA166_0==MANIFEST_TEXTBLOCK_START) ) {
                alt166=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1300:1: manifest_textblock : ( MANIFEST_STRING | MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END );", 166, 0, input);

                throw nvae;
            }
            switch (alt166) {
                case 1 :
                    // BONTCTreeWalker.g:1300:25: MANIFEST_STRING
                    {
                    match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_manifest_textblock21366); 

                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1301:14: MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END
                    {
                    match(input,MANIFEST_TEXTBLOCK_START,FOLLOW_MANIFEST_TEXTBLOCK_START_in_manifest_textblock21381); 
                    // BONTCTreeWalker.g:1302:13: ( MANIFEST_TEXTBLOCK_MIDDLE )*
                    loop165:
                    do {
                        int alt165=2;
                        int LA165_0 = input.LA(1);

                        if ( (LA165_0==MANIFEST_TEXTBLOCK_MIDDLE) ) {
                            alt165=1;
                        }


                        switch (alt165) {
                    	case 1 :
                    	    // BONTCTreeWalker.g:1302:14: MANIFEST_TEXTBLOCK_MIDDLE
                    	    {
                    	    match(input,MANIFEST_TEXTBLOCK_MIDDLE,FOLLOW_MANIFEST_TEXTBLOCK_MIDDLE_in_manifest_textblock21396); 

                    	    }
                    	    break;

                    	default :
                    	    break loop165;
                        }
                    } while (true);

                    match(input,MANIFEST_TEXTBLOCK_END,FOLLOW_MANIFEST_TEXTBLOCK_END_in_manifest_textblock21412); 

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
    // $ANTLR end manifest_textblock

    public static class add_sub_op_return extends TreeRuleReturnScope {
    };

    // $ANTLR start add_sub_op
    // BONTCTreeWalker.g:1307:1: add_sub_op : ( '+' | '-' );
    public final add_sub_op_return add_sub_op() throws RecognitionException {
        add_sub_op_return retval = new add_sub_op_return();
        retval.start = input.LT(1);

        try {
            // BONTCTreeWalker.g:1311:13: ( '+' | '-' )
            // BONTCTreeWalker.g:
            {
            if ( (input.LA(1)>=263 && input.LA(1)<=264) ) {
                input.consume();
                errorRecovery=false;
            }
            else {
                MismatchedSetException mse =
                    new MismatchedSetException(null,input);
                recoverFromMismatchedSet(input,mse,FOLLOW_set_in_add_sub_op0);    throw mse;
            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end add_sub_op

    public static class and_or_xor_op_return extends TreeRuleReturnScope {
    };

    // $ANTLR start and_or_xor_op
    // BONTCTreeWalker.g:1315:1: and_or_xor_op : ( 'and' | 'or' | 'xor' );
    public final and_or_xor_op_return and_or_xor_op() throws RecognitionException {
        and_or_xor_op_return retval = new and_or_xor_op_return();
        retval.start = input.LT(1);

        try {
            // BONTCTreeWalker.g:1315:16: ( 'and' | 'or' | 'xor' )
            // BONTCTreeWalker.g:
            {
            if ( (input.LA(1)>=265 && input.LA(1)<=267) ) {
                input.consume();
                errorRecovery=false;
            }
            else {
                MismatchedSetException mse =
                    new MismatchedSetException(null,input);
                recoverFromMismatchedSet(input,mse,FOLLOW_set_in_and_or_xor_op0);    throw mse;
            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end and_or_xor_op


    // $ANTLR start unary
    // BONTCTreeWalker.g:1320:1: unary : ( other_unary | add_sub_op );
    public final void unary() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1320:9: ( other_unary | add_sub_op )
            int alt167=2;
            int LA167_0 = input.LA(1);

            if ( ((LA167_0>=268 && LA167_0<=270)) ) {
                alt167=1;
            }
            else if ( ((LA167_0>=263 && LA167_0<=264)) ) {
                alt167=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1320:1: unary : ( other_unary | add_sub_op );", 167, 0, input);

                throw nvae;
            }
            switch (alt167) {
                case 1 :
                    // BONTCTreeWalker.g:1320:13: other_unary
                    {
                    pushFollow(FOLLOW_other_unary_in_unary21557);
                    other_unary();
                    _fsp--;


                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1321:13: add_sub_op
                    {
                    pushFollow(FOLLOW_add_sub_op_in_unary21571);
                    add_sub_op();
                    _fsp--;


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
    // $ANTLR end unary


    // $ANTLR start other_unary
    // BONTCTreeWalker.g:1324:1: other_unary : ( delta | old | not );
    public final void other_unary() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1324:14: ( delta | old | not )
            int alt168=3;
            switch ( input.LA(1) ) {
            case 268:
                {
                alt168=1;
                }
                break;
            case 269:
                {
                alt168=2;
                }
                break;
            case 270:
                {
                alt168=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("1324:1: other_unary : ( delta | old | not );", 168, 0, input);

                throw nvae;
            }

            switch (alt168) {
                case 1 :
                    // BONTCTreeWalker.g:1324:17: delta
                    {
                    pushFollow(FOLLOW_delta_in_other_unary21590);
                    delta();
                    _fsp--;


                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1325:17: old
                    {
                    pushFollow(FOLLOW_old_in_other_unary21609);
                    old();
                    _fsp--;


                    }
                    break;
                case 3 :
                    // BONTCTreeWalker.g:1326:17: not
                    {
                    pushFollow(FOLLOW_not_in_other_unary21628);
                    not();
                    _fsp--;


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
    // $ANTLR end other_unary

    public static class delta_return extends TreeRuleReturnScope {
    };

    // $ANTLR start delta
    // BONTCTreeWalker.g:1329:1: delta : 'delta' ;
    public final delta_return delta() throws RecognitionException {
        delta_return retval = new delta_return();
        retval.start = input.LT(1);

        try {
            // BONTCTreeWalker.g:1329:7: ( 'delta' )
            // BONTCTreeWalker.g:1329:9: 'delta'
            {
            match(input,268,FOLLOW_268_in_delta21663); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end delta


    // $ANTLR start old
    // BONTCTreeWalker.g:1332:1: old : 'old' ;
    public final void old() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1332:5: ( 'old' )
            // BONTCTreeWalker.g:1332:7: 'old'
            {
            match(input,269,FOLLOW_269_in_old21678); 

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
    // $ANTLR end old

    public static class not_return extends TreeRuleReturnScope {
    };

    // $ANTLR start not
    // BONTCTreeWalker.g:1335:1: not : 'not' ;
    public final not_return not() throws RecognitionException {
        not_return retval = new not_return();
        retval.start = input.LT(1);

        try {
            // BONTCTreeWalker.g:1335:5: ( 'not' )
            // BONTCTreeWalker.g:1335:7: 'not'
            {
            match(input,270,FOLLOW_270_in_not21695); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end not


    // $ANTLR start binary
    // BONTCTreeWalker.g:1338:1: binary : ( add_sub_op | mul_div_op | comparison_op | MOD_POW_OP | and_or_xor_op | '->' | '<->' );
    public final void binary() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1338:9: ( add_sub_op | mul_div_op | comparison_op | MOD_POW_OP | and_or_xor_op | '->' | '<->' )
            int alt169=7;
            switch ( input.LA(1) ) {
            case 263:
            case 264:
                {
                alt169=1;
                }
                break;
            case 277:
            case 278:
            case 280:
                {
                alt169=2;
                }
                break;
            case NOT_MEMBER_OF:
            case 196:
            case 246:
            case 271:
            case 272:
            case 273:
            case 274:
            case 275:
            case 276:
                {
                alt169=3;
                }
                break;
            case MOD_POW_OP:
                {
                alt169=4;
                }
                break;
            case 265:
            case 266:
            case 267:
                {
                alt169=5;
                }
                break;
            case 227:
                {
                alt169=6;
                }
                break;
            case 262:
                {
                alt169=7;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("1338:1: binary : ( add_sub_op | mul_div_op | comparison_op | MOD_POW_OP | and_or_xor_op | '->' | '<->' );", 169, 0, input);

                throw nvae;
            }

            switch (alt169) {
                case 1 :
                    // BONTCTreeWalker.g:1338:13: add_sub_op
                    {
                    pushFollow(FOLLOW_add_sub_op_in_binary21739);
                    add_sub_op();
                    _fsp--;


                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1339:13: mul_div_op
                    {
                    pushFollow(FOLLOW_mul_div_op_in_binary21753);
                    mul_div_op();
                    _fsp--;


                    }
                    break;
                case 3 :
                    // BONTCTreeWalker.g:1340:13: comparison_op
                    {
                    pushFollow(FOLLOW_comparison_op_in_binary21767);
                    comparison_op();
                    _fsp--;


                    }
                    break;
                case 4 :
                    // BONTCTreeWalker.g:1341:13: MOD_POW_OP
                    {
                    match(input,MOD_POW_OP,FOLLOW_MOD_POW_OP_in_binary21781); 

                    }
                    break;
                case 5 :
                    // BONTCTreeWalker.g:1342:13: and_or_xor_op
                    {
                    pushFollow(FOLLOW_and_or_xor_op_in_binary21795);
                    and_or_xor_op();
                    _fsp--;


                    }
                    break;
                case 6 :
                    // BONTCTreeWalker.g:1343:13: '->'
                    {
                    match(input,227,FOLLOW_227_in_binary21809); 

                    }
                    break;
                case 7 :
                    // BONTCTreeWalker.g:1344:13: '<->'
                    {
                    match(input,262,FOLLOW_262_in_binary21824); 

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
    // $ANTLR end binary


    // $ANTLR start comparison_op
    // BONTCTreeWalker.g:1347:1: comparison_op : ( normal_comparison_op | member_type_comparison_op );
    public final void comparison_op() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1347:16: ( normal_comparison_op | member_type_comparison_op )
            int alt170=2;
            int LA170_0 = input.LA(1);

            if ( ((LA170_0>=271 && LA170_0<=276)) ) {
                alt170=1;
            }
            else if ( (LA170_0==NOT_MEMBER_OF||LA170_0==196||LA170_0==246) ) {
                alt170=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1347:1: comparison_op : ( normal_comparison_op | member_type_comparison_op );", 170, 0, input);

                throw nvae;
            }
            switch (alt170) {
                case 1 :
                    // BONTCTreeWalker.g:1347:20: normal_comparison_op
                    {
                    pushFollow(FOLLOW_normal_comparison_op_in_comparison_op21846);
                    normal_comparison_op();
                    _fsp--;


                    }
                    break;
                case 2 :
                    // BONTCTreeWalker.g:1348:20: member_type_comparison_op
                    {
                    pushFollow(FOLLOW_member_type_comparison_op_in_comparison_op21867);
                    member_type_comparison_op();
                    _fsp--;


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
    // $ANTLR end comparison_op

    public static class normal_comparison_op_return extends TreeRuleReturnScope {
    };

    // $ANTLR start normal_comparison_op
    // BONTCTreeWalker.g:1351:1: normal_comparison_op : ( '<' | '>' | '<=' | '>=' | '=' | '/=' );
    public final normal_comparison_op_return normal_comparison_op() throws RecognitionException {
        normal_comparison_op_return retval = new normal_comparison_op_return();
        retval.start = input.LT(1);

        try {
            // BONTCTreeWalker.g:1351:22: ( '<' | '>' | '<=' | '>=' | '=' | '/=' )
            // BONTCTreeWalker.g:
            {
            if ( (input.LA(1)>=271 && input.LA(1)<=276) ) {
                input.consume();
                errorRecovery=false;
            }
            else {
                MismatchedSetException mse =
                    new MismatchedSetException(null,input);
                recoverFromMismatchedSet(input,mse,FOLLOW_set_in_normal_comparison_op0);    throw mse;
            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end normal_comparison_op


    // $ANTLR start member_type_comparison_op
    // BONTCTreeWalker.g:1359:1: member_type_comparison_op : ( 'member_of' | NOT_MEMBER_OF | ':' );
    public final void member_type_comparison_op() throws RecognitionException {
        try {
            // BONTCTreeWalker.g:1359:27: ( 'member_of' | NOT_MEMBER_OF | ':' )
            // BONTCTreeWalker.g:
            {
            if ( input.LA(1)==NOT_MEMBER_OF||input.LA(1)==196||input.LA(1)==246 ) {
                input.consume();
                errorRecovery=false;
            }
            else {
                MismatchedSetException mse =
                    new MismatchedSetException(null,input);
                recoverFromMismatchedSet(input,mse,FOLLOW_set_in_member_type_comparison_op0);    throw mse;
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
    // $ANTLR end member_type_comparison_op

    public static class mul_div_op_return extends TreeRuleReturnScope {
    };

    // $ANTLR start mul_div_op
    // BONTCTreeWalker.g:1365:1: mul_div_op : ( '*' | '/' | '//' );
    public final mul_div_op_return mul_div_op() throws RecognitionException {
        mul_div_op_return retval = new mul_div_op_return();
        retval.start = input.LT(1);

        try {
            // BONTCTreeWalker.g:1365:13: ( '*' | '/' | '//' )
            // BONTCTreeWalker.g:
            {
            if ( (input.LA(1)>=277 && input.LA(1)<=278)||input.LA(1)==280 ) {
                input.consume();
                errorRecovery=false;
            }
            else {
                MismatchedSetException mse =
                    new MismatchedSetException(null,input);
                recoverFromMismatchedSet(input,mse,FOLLOW_set_in_mul_div_op0);    throw mse;
            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end mul_div_op


 

    public static final BitSet FOLLOW_PROG_in_prog56 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_indexing_in_prog58 = new BitSet(new long[]{0x0000004920100160L,0x0000000000000000L,0x0000000000400004L});
    public static final BitSet FOLLOW_bon_specification_in_prog61 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PROG_in_prog86 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_prog88 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_specification_element_in_bon_specification111 = new BitSet(new long[]{0x0000004920100162L,0x0000000000000000L,0x0000000000400004L});
    public static final BitSet FOLLOW_informal_chart_in_specification_element148 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_dictionary_in_specification_element178 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_diagram_in_specification_element208 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_dynamic_diagram_in_specification_element238 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_notational_tuning_in_specification_element268 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_system_chart_in_informal_chart307 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cluster_chart_in_informal_chart330 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_chart_in_informal_chart353 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_event_chart_in_informal_chart376 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_scenario_chart_in_informal_chart399 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_creation_chart_in_informal_chart422 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CLASS_DICTIONARY_in_class_dictionary473 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_system_name_in_class_dictionary475 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_dictionary_entry_in_class_dictionary523 = new BitSet(new long[]{0x0000000000000088L});
    public static final BitSet FOLLOW_CLASS_DICTIONARY_in_class_dictionary592 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_class_dictionary595 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DICTIONARY_ENTRY_in_dictionary_entry650 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_dictionary_entry652 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_cluster_name_in_dictionary_entry698 = new BitSet(new long[]{0x0000000000001000L});
    public static final BitSet FOLLOW_description_in_dictionary_entry789 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SYSTEM_CHART_in_system_chart861 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_system_name_in_system_chart863 = new BitSet(new long[]{0x0000000000002E08L});
    public static final BitSet FOLLOW_indexing_in_system_chart883 = new BitSet(new long[]{0x0000000000002A08L});
    public static final BitSet FOLLOW_explanation_in_system_chart905 = new BitSet(new long[]{0x0000000000002808L});
    public static final BitSet FOLLOW_part_in_system_chart928 = new BitSet(new long[]{0x0000000000002008L});
    public static final BitSet FOLLOW_cluster_entries_in_system_chart951 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EXPLANATION_in_explanation1013 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_textblock_in_explanation1015 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EXPLANATION_in_explanation1066 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_explanation1068 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDEXING_in_indexing1107 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_index_list_in_indexing1109 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDEXING_in_indexing1151 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_indexing1153 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PART_in_part1185 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_part1187 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PART_in_part1217 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_part1219 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DESCRIPTION_in_description1254 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_textblock_in_description1256 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLUSTER_ENTRIES_in_cluster_entries1317 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cluster_entry_in_cluster_entries1320 = new BitSet(new long[]{0x0000000000004008L});
    public static final BitSet FOLLOW_CLUSTER_ENTRY_in_cluster_entry1407 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_entry1409 = new BitSet(new long[]{0x0000000000001000L});
    public static final BitSet FOLLOW_description_in_cluster_entry1411 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SYSTEM_NAME_in_system_name1508 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_system_name1510 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDEX_LIST_in_index_list1569 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_index_clause_in_index_list1572 = new BitSet(new long[]{0x0000000000020008L});
    public static final BitSet FOLLOW_INDEX_CLAUSE_in_index_clause1642 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_index_clause1644 = new BitSet(new long[]{0x0000000000040000L});
    public static final BitSet FOLLOW_index_term_list_in_index_clause1646 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDEX_CLAUSE_in_index_clause1701 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_index_clause1703 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDEX_TERM_LIST_in_index_term_list1766 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_index_string_in_index_term_list1769 = new BitSet(new long[]{0x0000000000080008L});
    public static final BitSet FOLLOW_INDEX_STRING_in_index_string1854 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_index_string1856 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLUSTER_CHART_in_cluster_chart1920 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_chart1922 = new BitSet(new long[]{0x0000000000202E08L});
    public static final BitSet FOLLOW_indexing_in_cluster_chart1944 = new BitSet(new long[]{0x0000000000202A08L});
    public static final BitSet FOLLOW_explanation_in_cluster_chart1968 = new BitSet(new long[]{0x0000000000202808L});
    public static final BitSet FOLLOW_part_in_cluster_chart1992 = new BitSet(new long[]{0x0000000000202008L});
    public static final BitSet FOLLOW_class_entries_in_cluster_chart2016 = new BitSet(new long[]{0x0000000000002008L});
    public static final BitSet FOLLOW_cluster_entries_in_cluster_chart2040 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLASS_ENTRIES_in_class_entries2121 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_entry_in_class_entries2124 = new BitSet(new long[]{0x0000000000400008L});
    public static final BitSet FOLLOW_CLASS_ENTRY_in_class_entry2203 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_class_entry2205 = new BitSet(new long[]{0x0000000000001000L});
    public static final BitSet FOLLOW_description_in_class_entry2207 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLUSTER_NAME_in_cluster_name2297 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_cluster_name2299 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLASS_CHART_in_class_chart2362 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_class_chart2364 = new BitSet(new long[]{0x0000000000000E08L,0x0000000000000000L,0x0000000780000000L});
    public static final BitSet FOLLOW_indexing_in_class_chart2383 = new BitSet(new long[]{0x0000000000000A08L,0x0000000000000000L,0x0000000780000000L});
    public static final BitSet FOLLOW_explanation_in_class_chart2405 = new BitSet(new long[]{0x0000000000000808L,0x0000000000000000L,0x0000000780000000L});
    public static final BitSet FOLLOW_part_in_class_chart2427 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000780000000L});
    public static final BitSet FOLLOW_inherits_in_class_chart2449 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000700000000L});
    public static final BitSet FOLLOW_queries_in_class_chart2470 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000600000000L});
    public static final BitSet FOLLOW_commands_in_class_chart2492 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000400000000L});
    public static final BitSet FOLLOW_constraints_in_class_chart2514 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INHERITS_in_inherits2574 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_list_in_inherits2609 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INHERITS_in_inherits2673 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_inherits2675 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_QUERIES_in_queries2698 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_query_list_in_queries2700 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_COMMANDS_in_commands2730 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_command_list_in_commands2732 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CONSTRAINTS_in_constraints2754 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_constraint_list_in_constraints2756 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_QUERY_LIST_in_query_list2796 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_textblock_in_query_list2799 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_COMMAND_LIST_in_command_list2869 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_textblock_in_command_list2872 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_CONSTRAINT_LIST_in_constraint_list2951 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_textblock_in_constraint_list2954 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_CLASS_NAME_LIST_in_class_name_list3025 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_class_name_list3050 = new BitSet(new long[]{0x0000000010000008L});
    public static final BitSet FOLLOW_CLASS_NAME_in_class_name3159 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_class_name3161 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EVENT_CHART_in_event_chart3219 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_system_name_in_event_chart3237 = new BitSet(new long[]{0x0000000040000E08L,0x0000000000000000L,0x0000000000000000L,0x0000000000006000L});
    public static final BitSet FOLLOW_205_in_event_chart3276 = new BitSet(new long[]{0x0000000040000E08L,0x0000000000000000L,0x0000000000000000L,0x0000000000004000L});
    public static final BitSet FOLLOW_206_in_event_chart3281 = new BitSet(new long[]{0x0000000040000E08L});
    public static final BitSet FOLLOW_indexing_in_event_chart3302 = new BitSet(new long[]{0x0000000040000A08L});
    public static final BitSet FOLLOW_explanation_in_event_chart3323 = new BitSet(new long[]{0x0000000040000808L});
    public static final BitSet FOLLOW_part_in_event_chart3344 = new BitSet(new long[]{0x0000000040000008L});
    public static final BitSet FOLLOW_event_entries_in_event_chart3365 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EVENT_ENTRIES_in_event_entries3439 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_event_entry_in_event_entries3460 = new BitSet(new long[]{0x0000000080000008L});
    public static final BitSet FOLLOW_EVENT_ENTRY_in_event_entry3538 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_textblock_in_event_entry3574 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_class_name_list_in_event_entry3592 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EVENT_ENTRY_in_event_entry3660 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_event_entry3662 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SCENARIO_CHART_in_scenario_chart3709 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_system_name_in_scenario_chart3730 = new BitSet(new long[]{0x0000000200000E08L});
    public static final BitSet FOLLOW_indexing_in_scenario_chart3773 = new BitSet(new long[]{0x0000000200000A08L});
    public static final BitSet FOLLOW_explanation_in_scenario_chart3797 = new BitSet(new long[]{0x0000000200000808L});
    public static final BitSet FOLLOW_part_in_scenario_chart3821 = new BitSet(new long[]{0x0000000200000008L});
    public static final BitSet FOLLOW_scenario_entries_in_scenario_chart3845 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SCENARIO_ENTRIES_in_scenario_entries3931 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_scenario_entry_in_scenario_entries3955 = new BitSet(new long[]{0x0000000400000008L});
    public static final BitSet FOLLOW_SCENARIO_ENTRY_in_scenario_entry4063 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_scenario_entry4084 = new BitSet(new long[]{0x0000000000001000L});
    public static final BitSet FOLLOW_description_in_scenario_entry4086 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CREATION_CHART_in_creation_chart4156 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_system_name_in_creation_chart4177 = new BitSet(new long[]{0x0000001000000E08L});
    public static final BitSet FOLLOW_indexing_in_creation_chart4220 = new BitSet(new long[]{0x0000001000000A08L});
    public static final BitSet FOLLOW_explanation_in_creation_chart4244 = new BitSet(new long[]{0x0000001000000808L});
    public static final BitSet FOLLOW_part_in_creation_chart4268 = new BitSet(new long[]{0x0000001000000008L});
    public static final BitSet FOLLOW_creation_entries_in_creation_chart4292 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CREATION_ENTRIES_in_creation_entries4378 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_creation_entry_in_creation_entries4402 = new BitSet(new long[]{0x0000002000000008L});
    public static final BitSet FOLLOW_CREATION_ENTRY_in_creation_entry4492 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_creation_entry4513 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_class_name_list_in_creation_entry4556 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STATIC_DIAGRAM_in_static_diagram4648 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_extended_id_in_static_diagram4670 = new BitSet(new long[]{0x0000010000000008L,0x0000000000000000L,0x0000008000000000L});
    public static final BitSet FOLLOW_COMMENT_in_static_diagram4675 = new BitSet(new long[]{0x0000010000000008L});
    public static final BitSet FOLLOW_static_block_in_static_diagram4701 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EXTENDED_ID_in_extended_id4783 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_extended_id4785 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EXTENDED_ID_in_extended_id4852 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_INTEGER_in_extended_id4854 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STATIC_BLOCK_in_static_block4925 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_static_component_in_static_block4928 = new BitSet(new long[]{0x0000020000000008L});
    public static final BitSet FOLLOW_STATIC_COMPONENT_in_static_component4997 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cluster_in_static_component4999 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STATIC_COMPONENT_in_static_component5090 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_classX_in_static_component5092 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STATIC_COMPONENT_in_static_component5183 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_static_relation_in_static_component5185 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLUSTER_in_cluster5252 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cluster_name_in_cluster5254 = new BitSet(new long[]{0x0000080000000008L,0x0000000000000000L,0x0000008000000000L,0x0000000001000000L});
    public static final BitSet FOLLOW_216_in_cluster5269 = new BitSet(new long[]{0x0000080000000008L,0x0000000000000000L,0x0000008000000000L});
    public static final BitSet FOLLOW_COMMENT_in_cluster5274 = new BitSet(new long[]{0x0000080000000008L});
    public static final BitSet FOLLOW_cluster_components_in_cluster5292 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLUSTER_COMPONENTS_in_cluster_components5359 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_static_block_in_cluster_components5362 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLASS_in_classX5450 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_217_in_classX5464 = new BitSet(new long[]{0x0000000010000000L,0x0000000000000000L,0x0000000000000000L,0x000000000C000000L});
    public static final BitSet FOLLOW_218_in_classX5469 = new BitSet(new long[]{0x0000000010000000L,0x0000000000000000L,0x0000000000000000L,0x0000000008000000L});
    public static final BitSet FOLLOW_219_in_classX5474 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_class_name_in_classX5490 = new BitSet(new long[]{0x0000000000000008L,0x0000000040000080L,0x0000008000000000L,0x0000000031000000L});
    public static final BitSet FOLLOW_formal_generics_in_classX5518 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000080L,0x0000008000000000L,0x0000000031000000L});
    public static final BitSet FOLLOW_216_in_classX5534 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000080L,0x0000008000000000L,0x0000000030000000L});
    public static final BitSet FOLLOW_220_in_classX5539 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000080L,0x0000008000000000L,0x0000000020000000L});
    public static final BitSet FOLLOW_221_in_classX5545 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000080L,0x0000008000000000L});
    public static final BitSet FOLLOW_COMMENT_in_classX5550 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000080L});
    public static final BitSet FOLLOW_class_interface_in_classX5566 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STATIC_RELATION_in_static_relation5645 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_inheritance_relation_in_static_relation5647 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STATIC_RELATION_in_static_relation5730 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_client_relation_in_static_relation5732 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INHERITENCE_RELATION_in_inheritance_relation5809 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_child_in_inheritance_relation5836 = new BitSet(new long[]{0x8000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_multiplicity_in_inheritance_relation5839 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_parent_in_inheritance_relation5869 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000040L});
    public static final BitSet FOLLOW_semantic_label_in_inheritance_relation5872 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_RELATION_in_client_relation5973 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_client_in_client_relation5995 = new BitSet(new long[]{0x1001000000000000L,0x0000000000000002L});
    public static final BitSet FOLLOW_client_entities_in_client_relation5998 = new BitSet(new long[]{0x1000000000000000L,0x0000000000000002L});
    public static final BitSet FOLLOW_type_mark_in_client_relation6003 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000002L});
    public static final BitSet FOLLOW_supplier_in_client_relation6028 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000040L});
    public static final BitSet FOLLOW_semantic_label_in_client_relation6031 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_ENTITIES_in_client_entities6120 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_client_entity_expression_in_client_entities6142 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_ENTITY_EXPRESSION_in_client_entity_expression6237 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_client_entity_list_in_client_entity_expression6239 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_ENTITY_EXPRESSION_in_client_entity_expression6358 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_multiplicity_in_client_entity_expression6360 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_ENTITY_LIST_in_client_entity_list6476 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_client_entity_in_client_entity_list6479 = new BitSet(new long[]{0x0010000000000008L});
    public static final BitSet FOLLOW_CLIENT_ENTITY_in_client_entity6578 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_prefix_in_client_entity6580 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_ENTITY_in_client_entity6664 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_infix_in_client_entity6666 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_ENTITY_in_client_entity6750 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_supplier_indirection_in_client_entity6752 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_ENTITY_in_client_entity6836 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_parent_indirection_in_client_entity6838 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SUPPLIER_INDIRECTION_in_supplier_indirection6925 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_indirection_feature_part_in_supplier_indirection6928 = new BitSet(new long[]{0x0200000000000000L});
    public static final BitSet FOLLOW_generic_indirection_in_supplier_indirection6932 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDIRECTION_FEATURE_PART_in_indirection_feature_part7043 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_feature_name_in_indirection_feature_part7045 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDIRECTION_FEATURE_PART_in_indirection_feature_part7164 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_indirection_feature_list_in_indirection_feature_part7166 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDIRECTION_FEATURE_LIST_in_indirection_feature_list7289 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_feature_name_list_in_indirection_feature_list7291 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PARENT_INDIRECTION_in_parent_indirection7407 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_generic_indirection_in_parent_indirection7409 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_GENERIC_INDIRECTION_in_generic_indirection7518 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_indirection_element_in_generic_indirection7520 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_NAMED_INDIRECTION_in_named_indirection7620 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_named_indirection7622 = new BitSet(new long[]{0x0800000000000000L});
    public static final BitSet FOLLOW_indirection_list_in_named_indirection7624 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_NAMED_INDIRECTION_in_named_indirection7692 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_named_indirection7694 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDIRECTION_LIST_in_indirection_list7765 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_indirection_element_in_indirection_list7768 = new BitSet(new long[]{0x0002000000000008L});
    public static final BitSet FOLLOW_INDIRECTION_ELEMENT_in_indirection_element7865 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_230_in_indirection_element7867 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDIRECTION_ELEMENT_in_indirection_element7970 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_named_indirection_in_indirection_element7972 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDIRECTION_ELEMENT_in_indirection_element8075 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_indirection_element8077 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_TYPE_MARK_in_type_mark8171 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_196_in_type_mark8173 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_TYPE_MARK_in_type_mark8232 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_231_in_type_mark8234 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_TYPE_MARK_in_type_mark8294 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_shared_mark_in_type_mark8296 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SHARED_MARK_in_shared_mark8360 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_multiplicity_in_shared_mark8362 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CHILD_in_child8416 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_static_ref_in_child8418 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PARENT_in_parent8465 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_static_ref_in_parent8467 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_in_client8517 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_static_ref_in_client8519 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SUPPLIER_in_supplier8571 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_static_ref_in_supplier8573 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STATIC_REF_in_static_ref8635 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cluster_prefix_in_static_ref8639 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
    public static final BitSet FOLLOW_static_component_name_in_static_ref8643 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STATIC_REF_in_static_ref8728 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_static_component_name_in_static_ref8732 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLUSTER_PREFIX_in_cluster_prefix8821 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_prefix8824 = new BitSet(new long[]{0x0000000000800008L});
    public static final BitSet FOLLOW_STATIC_COMPONENT_NAME_in_static_component_name8901 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_static_component_name8903 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MULTIPLICITY_in_multiplicity9004 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_INTEGER_in_multiplicity9006 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SEMANTIC_LABEL_in_semantic_label9082 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_semantic_label9084 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLASS_INTERFACE_in_class_interface9154 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_indexing_in_class_interface9177 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000600L});
    public static final BitSet FOLLOW_parent_class_list_in_class_interface9202 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000400L});
    public static final BitSet FOLLOW_features_in_class_interface9226 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000100L});
    public static final BitSet FOLLOW_class_invariant_in_class_interface9249 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLASS_INVARIANT_in_class_invariant9340 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_assertion_in_class_invariant9342 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PARENT_CLASS_LIST_in_parent_class_list9430 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_type_in_parent_class_list9433 = new BitSet(new long[]{0x0000000000000008L,0x0000000400000000L});
    public static final BitSet FOLLOW_PARENT_CLASS_LIST_in_parent_class_list9506 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_parent_class_list9508 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FEATURES_in_features9572 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_feature_clause_in_features9575 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000800L});
    public static final BitSet FOLLOW_FEATURE_CLAUSE_in_feature_clause9644 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_selective_export_in_feature_clause9666 = new BitSet(new long[]{0x0000000000000000L,0x0000000000001000L,0x0000008000000000L});
    public static final BitSet FOLLOW_COMMENT_in_feature_clause9691 = new BitSet(new long[]{0x0000000000000000L,0x0000000000001000L});
    public static final BitSet FOLLOW_feature_specifications_in_feature_clause9715 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FEATURE_SPECIFICATIONS_in_feature_specifications9806 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_feature_specification_in_feature_specifications9836 = new BitSet(new long[]{0x0000000000000008L,0x0000000000002000L});
    public static final BitSet FOLLOW_FEATURE_SPECIFICATION_in_feature_specification9951 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_218_in_feature_specification9980 = new BitSet(new long[]{0x0000000000000000L,0x0000000000080000L,0x0000000000000000L,0x0000080008000000L});
    public static final BitSet FOLLOW_219_in_feature_specification9985 = new BitSet(new long[]{0x0000000000000000L,0x0000000000080000L,0x0000000000000000L,0x0000080000000000L});
    public static final BitSet FOLLOW_235_in_feature_specification9990 = new BitSet(new long[]{0x0000000000000000L,0x0000000000080000L});
    public static final BitSet FOLLOW_feature_name_list_in_feature_specification10020 = new BitSet(new long[]{0x0000000000000008L,0x0000000000A04000L,0x0000008800000000L});
    public static final BitSet FOLLOW_has_type_in_feature_specification10023 = new BitSet(new long[]{0x0000000000000008L,0x0000000000A04000L,0x0000008000000000L});
    public static final BitSet FOLLOW_rename_clause_in_feature_specification10054 = new BitSet(new long[]{0x0000000000000008L,0x0000000000804000L,0x0000008000000000L});
    public static final BitSet FOLLOW_COMMENT_in_feature_specification10085 = new BitSet(new long[]{0x0000000000000008L,0x0000000000804000L});
    public static final BitSet FOLLOW_feature_arguments_in_feature_specification10116 = new BitSet(new long[]{0x0000000000000008L,0x0000000000004000L});
    public static final BitSet FOLLOW_contract_clause_in_feature_specification10147 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_HAS_TYPE_in_has_type10211 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_type_mark_in_has_type10213 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_type_in_has_type10215 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CONTRACT_CLAUSE_in_contract_clause10260 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_contracting_conditions_in_contract_clause10262 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CONTRACTING_CONDITIONS_in_contracting_conditions10352 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_precondition_in_contracting_conditions10355 = new BitSet(new long[]{0x0000000000000008L,0x0000000000020000L});
    public static final BitSet FOLLOW_postcondition_in_contracting_conditions10360 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PRECONDITION_in_precondition10450 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_assertion_in_precondition10452 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_POSTCONDITION_in_postcondition10527 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_assertion_in_postcondition10529 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SELECTIVE_EXPORT_in_selective_export10598 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_list_in_selective_export10645 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FEATURE_NAME_LIST_in_feature_name_list10759 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_feature_name_in_feature_name_list10762 = new BitSet(new long[]{0x0000000000000008L,0x0000000000100000L});
    public static final BitSet FOLLOW_FEATURE_NAME_in_feature_name10853 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_feature_name10855 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FEATURE_NAME_in_feature_name10927 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_prefix_in_feature_name10929 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FEATURE_NAME_in_feature_name11001 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_infix_in_feature_name11003 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_RENAME_CLAUSE_in_rename_clause11078 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_renaming_in_rename_clause11080 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_RENAMING_in_renaming11153 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_renaming11155 = new BitSet(new long[]{0x0000000000000000L,0x0000000000100000L});
    public static final BitSet FOLLOW_feature_name_in_renaming11157 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FEATURE_ARGUMENTS_in_feature_arguments11226 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_feature_argument_in_feature_arguments11229 = new BitSet(new long[]{0x0000000000000008L,0x0000000001000000L});
    public static final BitSet FOLLOW_FEATURE_ARGUMENT_in_feature_argument11325 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_identifier_list_in_feature_argument11328 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_type_in_feature_argument11332 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_IDENTIFIER_LIST_in_identifier_list11421 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_identifier_list11424 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_PREFIX_in_prefix11500 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_prefix_operator_in_prefix11502 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INFIX_in_infix11551 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_infix_operator_in_infix11553 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PREFIX_OPERATOR_in_prefix_operator11609 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_unary_in_prefix_operator11611 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INFIX_OPERATOR_in_infix_operator11695 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_binary_in_infix_operator11697 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FORMAL_GENERICS_in_formal_generics11767 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_formal_generic_list_in_formal_generics11769 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FORMAL_GENERIC_LIST_in_formal_generic_list11859 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_formal_generic_in_formal_generic_list11862 = new BitSet(new long[]{0x0000000000000008L,0x0000000100000000L});
    public static final BitSet FOLLOW_FORMAL_GENERIC_in_formal_generic11961 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_formal_generic_name_in_formal_generic11963 = new BitSet(new long[]{0x0000000000000008L,0x0000000400000000L});
    public static final BitSet FOLLOW_class_type_in_formal_generic11966 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FORMAL_GENERIC_NAME_in_formal_generic_name12055 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_formal_generic_name12057 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLASS_TYPE_in_class_type12150 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_class_type12152 = new BitSet(new long[]{0x0000000000000008L,0x0000000800000000L});
    public static final BitSet FOLLOW_actual_generics_in_class_type12155 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_ACTUAL_GENERICS_in_actual_generics12229 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_type_list_in_actual_generics12231 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_TYPE_LIST_in_type_list12311 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_type_in_type_list12314 = new BitSet(new long[]{0x0000000000000008L,0x0000002000000000L});
    public static final BitSet FOLLOW_TYPE_in_type12362 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_type12364 = new BitSet(new long[]{0x0000000000000008L,0x0000000800000000L});
    public static final BitSet FOLLOW_actual_generics_in_type12367 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_ASSERTION_in_assertion12413 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_assertion_clause_in_assertion12416 = new BitSet(new long[]{0x0000000000000008L,0x0000008000000000L});
    public static final BitSet FOLLOW_ASSERTION_CLAUSE_in_assertion_clause12487 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_boolean_expression_in_assertion_clause12489 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_BOOLEAN_EXPRESSION_in_boolean_expression12582 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_expression_in_boolean_expression12659 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_QUANTIFICATION_in_quantification12772 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_quantifier_in_quantification12814 = new BitSet(new long[]{0x0000000000000000L,0x0000080000000000L});
    public static final BitSet FOLLOW_range_expression_in_quantification12878 = new BitSet(new long[]{0x0000000000000000L,0x0000300000000000L});
    public static final BitSet FOLLOW_restriction_in_quantification12921 = new BitSet(new long[]{0x0000000000000000L,0x0000200000000000L});
    public static final BitSet FOLLOW_proposition_in_quantification12945 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_QUANTIFIER_in_quantifier13065 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_242_in_quantifier13067 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_QUANTIFIER_in_quantifier13130 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_243_in_quantifier13132 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_RANGE_EXPRESSION_in_range_expression13204 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_variable_range_in_range_expression13207 = new BitSet(new long[]{0x0000000000000008L,0x0000400000000000L});
    public static final BitSet FOLLOW_RESTRICTION_in_restriction13294 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_boolean_expression_in_restriction13296 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PROPOSITION_in_proposition13366 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_boolean_expression_in_proposition13368 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_VARIABLE_RANGE_in_variable_range13441 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_member_range_in_variable_range13443 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_VARIABLE_RANGE_in_variable_range13522 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_type_range_in_variable_range13524 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MEMBER_RANGE_in_member_range13604 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_identifier_list_in_member_range13606 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000020000000L});
    public static final BitSet FOLLOW_expression_in_member_range13608 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_TYPE_RANGE_in_type_range13680 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_identifier_list_in_type_range13682 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_type_in_type_range13684 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CALL_CHAIN_in_call_chain13772 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_unqualified_call_in_call_chain13775 = new BitSet(new long[]{0x0000000000000008L,0x0008000000000000L});
    public static final BitSet FOLLOW_UNQUALIFIED_CALL_in_unqualified_call13875 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_unqualified_call13901 = new BitSet(new long[]{0x0000000000000008L,0x0010000000000000L});
    public static final BitSet FOLLOW_actual_arguments_in_unqualified_call13949 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_ACTUAL_ARGUMENTS_in_actual_arguments14064 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_expression_list_in_actual_arguments14066 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EXPRESSION_LIST_in_expression_list14152 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_expression_in_expression_list14155 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000020000000L});
    public static final BitSet FOLLOW_ENUMERATED_SET_in_enumerated_set14244 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_enumeration_list_in_enumerated_set14246 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_ENUMERATION_LIST_in_enumeration_list14330 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_enumeration_element_in_enumeration_list14333 = new BitSet(new long[]{0x0000000000000008L,0x0100000000000000L});
    public static final BitSet FOLLOW_ENUMERATION_ELEMENT_in_enumeration_element14419 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_expression_in_enumeration_element14421 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_ENUMERATION_ELEMENT_in_enumeration_element14521 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_interval_in_enumeration_element14523 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INTERVAL_in_interval14614 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_integer_interval_in_interval14616 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INTERVAL_in_interval14673 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_character_interval_in_interval14675 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INTEGER_INTERVAL_in_integer_interval14742 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_integer_constant_in_integer_interval14744 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000001L});
    public static final BitSet FOLLOW_integer_constant_in_integer_interval14746 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CHARACTER_INTERVAL_in_character_interval14838 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_CHARACTER_CONSTANT_in_character_interval14840 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000020000000000L});
    public static final BitSet FOLLOW_CHARACTER_CONSTANT_in_character_interval14842 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CONSTANT_in_constant14912 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_constant_in_constant14914 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CONSTANT_in_constant14971 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_248_in_constant14975 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CONSTANT_in_constant15032 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_249_in_constant15036 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MANIFEST_CONSTANT_in_manifest_constant15095 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_boolean_constant_in_manifest_constant15097 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MANIFEST_CONSTANT_in_manifest_constant15195 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_CHARACTER_CONSTANT_in_manifest_constant15199 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MANIFEST_CONSTANT_in_manifest_constant15295 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_integer_constant_in_manifest_constant15297 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MANIFEST_CONSTANT_in_manifest_constant15393 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_real_constant_in_manifest_constant15395 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MANIFEST_CONSTANT_in_manifest_constant15493 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_manifest_constant15497 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MANIFEST_CONSTANT_in_manifest_constant15593 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_enumerated_set_in_manifest_constant15595 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SIGN_in_sign15677 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_add_sub_op_in_sign15679 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_BOOLEAN_CONSTANT_in_boolean_constant15735 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_250_in_boolean_constant15739 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_BOOLEAN_CONSTANT_in_boolean_constant15828 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_251_in_boolean_constant15832 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INTEGER_CONSTANT_in_integer_constant15926 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_sign_in_integer_constant15973 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_INTEGER_in_integer_constant15977 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_REAL_CONSTANT_in_real_constant16066 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_sign_in_real_constant16107 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000040000000000L});
    public static final BitSet FOLLOW_REAL_in_real_constant16111 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DYNAMIC_DIAGRAM_in_dynamic_diagram16179 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_diagram16202 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000008000000008L});
    public static final BitSet FOLLOW_COMMENT_in_dynamic_diagram16207 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_dynamic_block_in_dynamic_diagram16232 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DYNAMIC_BLOCK_in_dynamic_block16318 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_dynamic_component_in_dynamic_block16339 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000000000010L});
    public static final BitSet FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component16425 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_scenario_description_in_dynamic_component16427 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component16522 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_object_group_in_dynamic_component16524 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component16619 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_object_stack_in_dynamic_component16621 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component16717 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_object_in_dynamic_component16719 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component16815 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_message_relation_in_dynamic_component16817 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SCENARIO_DESCRIPTION_in_scenario_description16900 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_scenario_name_in_scenario_description16928 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000008000000040L});
    public static final BitSet FOLLOW_COMMENT_in_scenario_description16931 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000040L});
    public static final BitSet FOLLOW_labelled_actions_in_scenario_description16960 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_LABELLED_ACTIONS_in_labelled_actions17063 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_labelled_action_in_labelled_actions17066 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000000000080L});
    public static final BitSet FOLLOW_LABELLED_ACTION_in_labelled_action17157 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_action_label_in_labelled_action17159 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000200L});
    public static final BitSet FOLLOW_action_description_in_labelled_action17161 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_ACTION_LABEL_in_action_label17244 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_action_label17246 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_ACTION_DESCRIPTION_in_action_description17326 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_textblock_in_action_description17328 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SCENARIO_NAME_in_scenario_name17421 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_textblock_in_scenario_name17423 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_OBJECT_GROUP_in_object_group17488 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_254_in_object_group17491 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000100000L});
    public static final BitSet FOLLOW_group_name_in_object_group17495 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000008000001000L});
    public static final BitSet FOLLOW_COMMENT_in_object_group17498 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000000001000L});
    public static final BitSet FOLLOW_group_components_in_object_group17503 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_GROUP_COMPONENTS_in_group_components17584 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_dynamic_block_in_group_components17586 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_OBJECT_STACK_in_object_stack17672 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_object_name_in_object_stack17674 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000008000000000L});
    public static final BitSet FOLLOW_COMMENT_in_object_stack17677 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_OBJECT_in_object17747 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_object_name_in_object17749 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000008000000000L});
    public static final BitSet FOLLOW_COMMENT_in_object17752 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MESSAGE_RELATION_in_message_relation17809 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_caller_in_message_relation17811 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000010000L});
    public static final BitSet FOLLOW_receiver_in_message_relation17813 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000000200000L});
    public static final BitSet FOLLOW_message_label_in_message_relation17816 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_RECEIVER_in_caller17898 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_dynamic_ref_in_caller17900 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_RECEIVER_in_receiver17952 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_dynamic_ref_in_receiver17954 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DYNAMIC_REF_in_dynamic_ref18015 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_ref18018 = new BitSet(new long[]{0x0000008000000008L});
    public static final BitSet FOLLOW_DYNAMIC_COMPONENT_NAME_in_dynamic_component_name18088 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_dynamic_component_name18090 = new BitSet(new long[]{0x0000008000000008L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_component_name18093 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DYNAMIC_COMPONENT_NAME_in_dynamic_component_name18206 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_INTEGER_in_dynamic_component_name18208 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_OBJECT_NAME_in_object_name18287 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_object_name18289 = new BitSet(new long[]{0x0000008000000008L});
    public static final BitSet FOLLOW_extended_id_in_object_name18292 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_GROUP_NAME_in_group_name18363 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_extended_id_in_group_name18365 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MESSAGE_LABEL_in_message_label18434 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_message_label18436 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_NOTATIONAL_TUNING_in_notational_tuning18505 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_change_string_marks_in_notational_tuning18507 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_NOTATIONAL_TUNING_in_notational_tuning18598 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_change_concatenator_in_notational_tuning18600 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_NOTATIONAL_TUNING_in_notational_tuning18692 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_change_prefix_in_notational_tuning18694 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CHANGE_STRING_MARKS_in_change_string_marks18790 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_string_marks18792 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_string_marks18794 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CHANGE_CONCATENATOR_in_change_concatenator18896 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_concatenator18898 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CHANGE_PREFIX_in_change_prefix18994 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_prefix18996 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EXPRESSION_in_expression19063 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_equivalence_expression_in_expression19065 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EXPRESSION_in_expression19129 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_quantification_in_expression19131 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_262_in_equivalence_expression19175 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_equivalence_expression_in_equivalence_expression19272 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000080040000000L,0x0040000A00000010L,0x00000000017FFFC0L});
    public static final BitSet FOLLOW_equivalence_expression_in_equivalence_expression19305 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_implies_expression_in_equivalence_expression19385 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_227_in_implies_expression19425 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_implies_expression_in_implies_expression19510 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000080040000000L,0x0040000A00000010L,0x00000000017FFF80L});
    public static final BitSet FOLLOW_implies_expression_in_implies_expression19539 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_and_or_xor_expression_in_implies_expression19620 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_and_or_xor_op_in_and_or_xor_expression19655 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_and_or_xor_expression_in_and_or_xor_expression19749 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000080040000000L,0x0040000200000010L,0x00000000017FFF80L});
    public static final BitSet FOLLOW_and_or_xor_expression_in_and_or_xor_expression19781 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_comparison_expression_in_and_or_xor_expression19858 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_normal_comparison_op_in_comparison_expression19896 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_comparison_expression_in_comparison_expression19989 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000080040000000L,0x0040000200000010L,0x00000000017FF180L});
    public static final BitSet FOLLOW_comparison_expression_in_comparison_expression20021 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_member_type_comparison_op_in_comparison_expression20138 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_comparison_expression_in_comparison_expression20169 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000080040000000L,0x0040000200000010L,0x00000000017FF180L});
    public static final BitSet FOLLOW_comparison_expression_in_comparison_expression20201 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_add_sub_expression_in_comparison_expression20247 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_in_add_sub_expression20285 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_add_sub_expression_in_add_sub_expression20370 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000080000000000L,0x0000000200000000L,0x0000000001607180L});
    public static final BitSet FOLLOW_add_sub_expression_in_add_sub_expression20399 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_mul_div_expression_in_add_sub_expression20468 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_mul_div_op_in_mul_div_expression20504 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_mul_div_expression_in_mul_div_expression20592 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000080000000000L,0x0000000200000000L,0x0000000001607180L});
    public static final BitSet FOLLOW_mul_div_expression_in_mul_div_expression20622 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mul_div_expression20693 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MOD_POW_OP_in_mod_pow_expression20729 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mod_pow_expression20814 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000080000000000L,0x0000000200000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mod_pow_expression20843 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_lowest_expression_in_mod_pow_expression20922 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constant_in_lowest_expression20953 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_in_lowest_expression20979 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000000000000000L,0x0000000200000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_lowest_expression_in_lowest_expression21052 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_delta_in_lowest_expression21092 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000000000000000L,0x0000000200000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_lowest_expression_in_lowest_expression21133 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_old_in_lowest_expression21147 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000000000000000L,0x0000000200000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_lowest_expression_in_lowest_expression21149 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_not_in_lowest_expression21165 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000000000000000L,0x0000000200000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_lowest_expression_in_lowest_expression21218 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_225_in_lowest_expression21251 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000020000000L});
    public static final BitSet FOLLOW_expression_in_lowest_expression21271 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000400000000L});
    public static final BitSet FOLLOW_226_in_lowest_expression21291 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_232_in_lowest_expression21312 = new BitSet(new long[]{0x0000000000000000L,0x0004000000000000L});
    public static final BitSet FOLLOW_call_chain_in_lowest_expression21314 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_call_chain_in_lowest_expression21335 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_manifest_textblock21366 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_START_in_manifest_textblock21381 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000C00000000000L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_MIDDLE_in_manifest_textblock21396 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000C00000000000L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_END_in_manifest_textblock21412 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_set_in_add_sub_op0 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_set_in_and_or_xor_op0 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_other_unary_in_unary21557 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_in_unary21571 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_delta_in_other_unary21590 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_old_in_other_unary21609 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_not_in_other_unary21628 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_268_in_delta21663 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_269_in_old21678 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_270_in_not21695 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_in_binary21739 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_mul_div_op_in_binary21753 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_comparison_op_in_binary21767 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MOD_POW_OP_in_binary21781 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_and_or_xor_op_in_binary21795 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_227_in_binary21809 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_262_in_binary21824 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_normal_comparison_op_in_comparison_op21846 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_member_type_comparison_op_in_comparison_op21867 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_set_in_normal_comparison_op0 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_set_in_member_type_comparison_op0 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_set_in_mul_div_op0 = new BitSet(new long[]{0x0000000000000002L});

}