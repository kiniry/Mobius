// $ANTLR 3.0.1 BON.g 2008-02-20 14:22:00

  package ie.ucd.bon.parser; 
  
  import ie.ucd.bon.parser.errors.MissingElementParseError;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;

import org.antlr.runtime.tree.*;

/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
public class BONParser extends AbstractBONParser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "PROG", "CLASS_CHART", "CLASS_DICTIONARY", "DICTIONARY_ENTRY", "SYSTEM_CHART", "EXPLANATION", "INDEXING", "PART", "DESCRIPTION", "CLUSTER_ENTRIES", "CLUSTER_ENTRY", "SYSTEM_NAME", "INDEX_LIST", "INDEX_CLAUSE", "INDEX_TERM_LIST", "INDEX_STRING", "CLUSTER_CHART", "CLASS_ENTRIES", "CLASS_ENTRY", "CLUSTER_NAME", "QUERY_LIST", "COMMAND_LIST", "CONSTRAINT_LIST", "CLASS_NAME_LIST", "CLASS_NAME", "EVENT_CHART", "EVENT_ENTRIES", "EVENT_ENTRY", "SCENARIO_CHART", "SCENARIO_ENTRIES", "SCENARIO_ENTRY", "CREATION_CHART", "CREATION_ENTRIES", "CREATION_ENTRY", "STATIC_DIAGRAM", "EXTENDED_ID", "STATIC_BLOCK", "STATIC_COMPONENT", "CLUSTER", "CLUSTER_COMPONENTS", "CLASS", "STATIC_RELATION", "INHERITENCE_RELATION", "CLIENT_RELATION", "CLIENT_ENTITIES", "INDIRECTION_ELEMENT", "CLIENT_ENTITY_EXPRESSION", "CLIENT_ENTITY_LIST", "CLIENT_ENTITY", "SUPPLIER_INDIRECTION", "INDIRECTION_FEATURE_PART", "INDIRECTION_FEATURE_LIST", "PARENT_INDIRECTION", "GENERIC_INDIRECTION", "NAMED_INDIRECTION", "INDIRECTION_LIST", "TYPE_MARK", "SHARED_MARK", "CHILD", "PARENT", "CLIENT", "SUPPLIER", "STATIC_REF", "CLUSTER_PREFIX", "STATIC_COMPONENT_NAME", "MULTIPLICITY", "SEMANTIC_LABEL", "CLASS_INTERFACE", "CLASS_INVARIANT", "PARENT_CLASS_LIST", "FEATURES", "FEATURE_CLAUSE", "FEATURE_SPECIFICATIONS", "FEATURE_SPECIFICATION", "CONTRACT_CLAUSE", "CONTRACTING_CONDITIONS", "PRECONDITION", "POSTCONDITION", "SELECTIVE_EXPORT", "FEATURE_NAME_LIST", "FEATURE_NAME", "RENAME_CLAUSE", "RENAMING", "FEATURE_ARGUMENTS", "FEATURE_ARGUMENT", "IDENTIFIER_LIST", "PREFIX", "INFIX", "PREFIX_OPERATOR", "INFIX_OPERATOR", "FORMAL_GENERICS", "FORMAL_GENERIC_LIST", "FORMAL_GENERIC", "FORMAL_GENERIC_NAME", "CLASS_TYPE", "ACTUAL_GENERICS", "TYPE_LIST", "TYPE", "ASSERTION", "ASSERTION_CLAUSE", "BOOLEAN_EXPRESSION", "QUANTIFICATION", "QUANTIFIER", "RANGE_EXPRESSION", "RESTRICTION", "PROPOSITION", "VARIABLE_RANGE", "MEMBER_RANGE", "TYPE_RANGE", "CALL", "CALL_CHAIN", "UNQUALIFIED_CALL", "ACTUAL_ARGUMENTS", "EXPRESSION_LIST", "ENUMERATED_SET", "ENUMERATION_LIST", "ENUMERATION_ELEMENT", "INTERVAL", "INTEGER_INTERVAL", "CHARACTER_INTERVAL", "CONSTANT", "MANIFEST_CONSTANT", "SIGN", "BOOLEAN_CONSTANT", "INTEGER_CONSTANT", "REAL_CONSTANT", "DYNAMIC_DIAGRAM", "DYNAMIC_BLOCK", "DYNAMIC_COMPONENT", "SCENARIO_DESCRIPTION", "LABELLED_ACTIONS", "LABELLED_ACTION", "ACTION_LABEL", "ACTION_DESCRIPTION", "SCENARIO_NAME", "OBJECT_GROUP", "GROUP_COMPONENTS", "OBJECT_STACK", "OBJECT", "MESSAGE_RELATION", "RECEIVER", "DYNAMIC_REF", "DYNAMIC_COMPONENT_NAME", "OBJECT_NAME", "GROUP_NAME", "MESSAGE_LABEL", "NOTATIONAL_TUNING", "CHANGE_STRING_MARKS", "CHANGE_CONCATENATOR", "MANFIEST_STRING", "CHANGE_PREFIX", "LOWEST", "SET_EXPRESSION", "EXPRESSION", "NOT_MEMBER_OF", "INHERITS", "QUERIES", "COMMANDS", "CONSTRAINTS", "HAS_TYPE", "PARSE_ERROR", "MANIFEST_STRING", "IDENTIFIER", "COMMENT", "INTEGER", "CHARACTER_CONSTANT", "REAL", "MOD_POW_OP", "NEWLINE", "MANIFEST_TEXTBLOCK_START", "MANIFEST_TEXTBLOCK_MIDDLE", "MANIFEST_TEXTBLOCK_END", "LINE_COMMENT", "COMMENT_START", "DIGIT", "ALPHA", "ALPHANUMERIC_OR_UNDERSCORE", "ALPHANUMERIC", "UNDERSCORE", "LOWER", "UPPER", "WHITESPACE", "'dictionary'", "'end'", "'class'", "'cluster'", "'system_chart'", "'explanation'", "'indexing'", "'part'", "'description'", "';'", "':'", "','", "'cluster_chart'", "'class_chart'", "'inherit'", "'query'", "'command'", "'constraint'", "'event_chart'", "'incoming'", "'outgoing'", "'event'", "'involves'", "'scenario_chart'", "'scenario'", "'creation_chart'", "'creator'", "'creates'", "'static_diagram'", "'component'", "'reused'", "'root'", "'deferred'", "'effective'", "'persistent'", "'interfaced'", "'{'", "'}'", "'client'", "'('", "')'", "'->'", "'['", "']'", "'...'", "':{'", "'.'", "'invariant'", "'feature'", "'redefined'", "'require'", "'ensure'", "'^'", "'prefix'", "'\"'", "'infix'", "'for_all'", "'exists'", "'such_that'", "'it_holds'", "'member_of'", "'..'", "'Current'", "'Void'", "'true'", "'false'", "'dynamic_diagram'", "'action'", "'nameless'", "'object_group'", "'object_stack'", "'object'", "'calls'", "'string_marks'", "'concatenator'", "'keyword_prefix'", "'<->'", "'+'", "'-'", "'and'", "'or'", "'xor'", "'delta'", "'old'", "'not'", "'<'", "'>'", "'<='", "'>='", "'='", "'/='", "'*'", "'/'", "'\\\\'"
    };
    public static final int SIGN=126;
    public static final int ENUMERATED_SET=118;
    public static final int CLASS_TYPE=98;
    public static final int CREATION_ENTRIES=36;
    public static final int PREFIX=90;
    public static final int UNQUALIFIED_CALL=115;
    public static final int SUPPLIER=65;
    public static final int ENUMERATION_LIST=119;
    public static final int STATIC_RELATION=45;
    public static final int INDEX_LIST=16;
    public static final int FEATURE_ARGUMENTS=87;
    public static final int SCENARIO_DESCRIPTION=133;
    public static final int SET_EXPRESSION=156;
    public static final int EOF=-1;
    public static final int INDEXING=10;
    public static final int CONTRACTING_CONDITIONS=79;
    public static final int TYPE=101;
    public static final int COMMAND_LIST=25;
    public static final int OBJECT_NAME=147;
    public static final int MULTIPLICITY=69;
    public static final int CALL_CHAIN=114;
    public static final int DESCRIPTION=12;
    public static final int COMMANDS=161;
    public static final int MEMBER_RANGE=111;
    public static final int INHERITS=159;
    public static final int MANIFEST_TEXTBLOCK_END=175;
    public static final int SCENARIO_NAME=138;
    public static final int PARSE_ERROR=164;
    public static final int ALPHANUMERIC_OR_UNDERSCORE=180;
    public static final int FEATURE_SPECIFICATIONS=76;
    public static final int BOOLEAN_CONSTANT=127;
    public static final int DYNAMIC_DIAGRAM=130;
    public static final int SCENARIO_ENTRIES=33;
    public static final int INDIRECTION_FEATURE_LIST=55;
    public static final int INFIX=91;
    public static final int RENAME_CLAUSE=85;
    public static final int PARENT_CLASS_LIST=73;
    public static final int FEATURE_CLAUSE=75;
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
    public static final int ASSERTION=102;
    public static final int FORMAL_GENERIC_LIST=95;
    public static final int NOT_MEMBER_OF=158;
    public static final int CLUSTER_COMPONENTS=43;
    public static final int INFIX_OPERATOR=93;
    public static final int SYSTEM_CHART=8;
    public static final int CLUSTER_NAME=23;
    public static final int DYNAMIC_COMPONENT=132;
    public static final int TYPE_LIST=100;
    public static final int CLASS_ENTRY=22;
    public static final int SYSTEM_NAME=15;
    public static final int COMMENT_START=177;
    public static final int REAL_CONSTANT=129;
    public static final int BOOLEAN_EXPRESSION=104;
    public static final int INTERVAL=121;
    public static final int TYPE_RANGE=112;
    public static final int CLIENT_RELATION=47;
    public static final int INDIRECTION_ELEMENT=49;
    public static final int PARENT=63;
    public static final int STATIC_DIAGRAM=38;
    public static final int CREATION_ENTRY=37;
    public static final int PROG=4;
    public static final int NOTATIONAL_TUNING=150;
    public static final int EXPRESSION_LIST=117;
    public static final int INDEX_TERM_LIST=18;
    public static final int OBJECT=142;
    public static final int IDENTIFIER=166;
    public static final int ALPHANUMERIC=181;
    public static final int CHANGE_CONCATENATOR=152;
    public static final int EVENT_CHART=29;
    public static final int FEATURE_NAME_LIST=83;
    public static final int MANIFEST_TEXTBLOCK_START=173;
    public static final int MANFIEST_STRING=153;
    public static final int GROUP_COMPONENTS=140;
    public static final int STATIC_REF=66;
    public static final int CLASS_CHART=5;
    public static final int SEMANTIC_LABEL=70;
    public static final int INDIRECTION_FEATURE_PART=54;
    public static final int CLASS_DICTIONARY=6;
    public static final int FEATURE_ARGUMENT=88;
    public static final int OBJECT_GROUP=139;
    public static final int DIGIT=178;
    public static final int INTEGER_CONSTANT=128;
    public static final int SCENARIO_CHART=32;
    public static final int EXPRESSION=157;
    public static final int DYNAMIC_BLOCK=131;
    public static final int CREATION_CHART=35;
    public static final int INTEGER=168;
    public static final int CLIENT_ENTITY=52;
    public static final int ACTUAL_GENERICS=99;
    public static final int CLASS_NAME=28;
    public static final int QUERY_LIST=24;
    public static final int EXPLANATION=9;
    public static final int FEATURES=74;
    public static final int MANIFEST_CONSTANT=125;
    public static final int CHANGE_PREFIX=154;
    public static final int CLASS_INVARIANT=72;
    public static final int GROUP_NAME=148;
    public static final int CLIENT_ENTITY_EXPRESSION=50;
    public static final int GENERIC_INDIRECTION=57;
    public static final int FEATURE_SPECIFICATION=77;
    public static final int ACTION_DESCRIPTION=137;
    public static final int INDEX_STRING=19;
    public static final int SELECTIVE_EXPORT=82;
    public static final int TYPE_MARK=60;
    public static final int RESTRICTION=108;
    public static final int MANIFEST_STRING=165;
    public static final int PROPOSITION=109;
    public static final int POSTCONDITION=81;
    public static final int NEWLINE=172;
    public static final int STATIC_COMPONENT_NAME=68;
    public static final int MESSAGE_LABEL=149;
    public static final int SCENARIO_ENTRY=34;
    public static final int PRECONDITION=80;
    public static final int ASSERTION_CLAUSE=103;
    public static final int NAMED_INDIRECTION=58;
    public static final int MANIFEST_TEXTBLOCK_MIDDLE=174;
    public static final int CLUSTER=42;
    public static final int FORMAL_GENERICS=94;
    public static final int QUANTIFIER=106;
    public static final int EVENT_ENTRY=31;
    public static final int STATIC_COMPONENT=41;
    public static final int INDIRECTION_LIST=59;
    public static final int ACTION_LABEL=136;

        public BONParser(TokenStream input) {
            super(input);
            ruleMemo = new HashMap[179+1];
         }
        
    protected TreeAdaptor adaptor = new CommonTreeAdaptor();

    public void setTreeAdaptor(TreeAdaptor adaptor) {
        this.adaptor = adaptor;
    }
    public TreeAdaptor getTreeAdaptor() {
        return adaptor;
    }

    public String[] getTokenNames() { return tokenNames; }
    public String getGrammarFileName() { return "BON.g"; }


    //Currently nothing, everything in BONAbstractParser	


    public static class prog_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start prog
    // BON.g:199:1: prog : ( ( indexing )? bon_specification EOF -> ^( PROG ( indexing )? bon_specification ) | ( indexing )? e= EOF -> ^( PROG PARSE_ERROR ) );
    public final prog_return prog() throws RecognitionException {
        prog_return retval = new prog_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token e=null;
        Token EOF3=null;
        indexing_return indexing1 = null;

        bon_specification_return bon_specification2 = null;

        indexing_return indexing4 = null;


        CommonTree e_tree=null;
        CommonTree EOF3_tree=null;
        RewriteRuleTokenStream stream_EOF=new RewriteRuleTokenStream(adaptor,"token EOF");
        RewriteRuleSubtreeStream stream_indexing=new RewriteRuleSubtreeStream(adaptor,"rule indexing");
        RewriteRuleSubtreeStream stream_bon_specification=new RewriteRuleSubtreeStream(adaptor,"rule bon_specification");
        try {
            // BON.g:205:7: ( ( indexing )? bon_specification EOF -> ^( PROG ( indexing )? bon_specification ) | ( indexing )? e= EOF -> ^( PROG PARSE_ERROR ) )
            int alt3=2;
            alt3 = dfa3.predict(input);
            switch (alt3) {
                case 1 :
                    // BON.g:205:10: ( indexing )? bon_specification EOF
                    {
                    // BON.g:205:10: ( indexing )?
                    int alt1=2;
                    int LA1_0 = input.LA(1);

                    if ( (LA1_0==192) ) {
                        alt1=1;
                    }
                    switch (alt1) {
                        case 1 :
                            // BON.g:205:10: indexing
                            {
                            pushFollow(FOLLOW_indexing_in_prog882);
                            indexing1=indexing();
                            _fsp--;
                            if (failed) return retval;
                            if ( backtracking==0 ) stream_indexing.add(indexing1.getTree());

                            }
                            break;

                    }

                    pushFollow(FOLLOW_bon_specification_in_prog885);
                    bon_specification2=bon_specification();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_bon_specification.add(bon_specification2.getTree());
                    EOF3=(Token)input.LT(1);
                    match(input,EOF,FOLLOW_EOF_in_prog887); if (failed) return retval;
                    if ( backtracking==0 ) stream_EOF.add(EOF3);


                    // AST REWRITE
                    // elements: indexing, bon_specification
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 206:8: -> ^( PROG ( indexing )? bon_specification )
                    {
                        // BON.g:207:10: ^( PROG ( indexing )? bon_specification )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(PROG, "PROG"), root_1);

                        // BON.g:207:18: ( indexing )?
                        if ( stream_indexing.hasNext() ) {
                            adaptor.addChild(root_1, stream_indexing.next());

                        }
                        stream_indexing.reset();
                        adaptor.addChild(root_1, stream_bon_specification.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:209:10: ( indexing )? e= EOF
                    {
                    // BON.g:209:10: ( indexing )?
                    int alt2=2;
                    int LA2_0 = input.LA(1);

                    if ( (LA2_0==192) ) {
                        alt2=1;
                    }
                    switch (alt2) {
                        case 1 :
                            // BON.g:209:10: indexing
                            {
                            pushFollow(FOLLOW_indexing_in_prog936);
                            indexing4=indexing();
                            _fsp--;
                            if (failed) return retval;
                            if ( backtracking==0 ) stream_indexing.add(indexing4.getTree());

                            }
                            break;

                    }

                    e=(Token)input.LT(1);
                    match(input,EOF,FOLLOW_EOF_in_prog941); if (failed) return retval;
                    if ( backtracking==0 ) stream_EOF.add(e);

                    if ( backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(e), "at least one specification entry", "in source file", true)); 
                    }

                    // AST REWRITE
                    // elements: 
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 211:8: -> ^( PROG PARSE_ERROR )
                    {
                        // BON.g:212:10: ^( PROG PARSE_ERROR )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(PROG, "PROG"), root_1);

                        adaptor.addChild(root_1, adaptor.create(PARSE_ERROR, "PARSE_ERROR"));

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end prog

    public static class bon_specification_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start bon_specification
    // BON.g:216:1: bon_specification : ( specification_element )+ ;
    public final bon_specification_return bon_specification() throws RecognitionException {
        bon_specification_return retval = new bon_specification_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        specification_element_return specification_element5 = null;



        try {
            // BON.g:220:20: ( ( specification_element )+ )
            // BON.g:220:23: ( specification_element )+
            {
            root_0 = (CommonTree)adaptor.nil();

            // BON.g:220:23: ( specification_element )+
            int cnt4=0;
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( (LA4_0==186||LA4_0==190||(LA4_0>=198 && LA4_0<=199)||LA4_0==204||LA4_0==209||LA4_0==211||LA4_0==214||LA4_0==252||(LA4_0>=259 && LA4_0<=261)) ) {
                    alt4=1;
                }


                switch (alt4) {
            	case 1 :
            	    // BON.g:220:24: specification_element
            	    {
            	    pushFollow(FOLLOW_specification_element_in_bon_specification1010);
            	    specification_element5=specification_element();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) adaptor.addChild(root_0, specification_element5.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt4 >= 1 ) break loop4;
            	    if (backtracking>0) {failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(4, input);
                        throw eee;
                }
                cnt4++;
            } while (true);


            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end bon_specification

    public static class specification_element_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start specification_element
    // BON.g:223:1: specification_element : ( informal_chart | class_dictionary | static_diagram | dynamic_diagram | notational_tuning );
    public final specification_element_return specification_element() throws RecognitionException {
        specification_element_return retval = new specification_element_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        informal_chart_return informal_chart6 = null;

        class_dictionary_return class_dictionary7 = null;

        static_diagram_return static_diagram8 = null;

        dynamic_diagram_return dynamic_diagram9 = null;

        notational_tuning_return notational_tuning10 = null;



        try {
            // BON.g:223:24: ( informal_chart | class_dictionary | static_diagram | dynamic_diagram | notational_tuning )
            int alt5=5;
            switch ( input.LA(1) ) {
            case 190:
            case 198:
            case 199:
            case 204:
            case 209:
            case 211:
                {
                alt5=1;
                }
                break;
            case 186:
                {
                alt5=2;
                }
                break;
            case 214:
                {
                alt5=3;
                }
                break;
            case 252:
                {
                alt5=4;
                }
                break;
            case 259:
            case 260:
            case 261:
                {
                alt5=5;
                }
                break;
            default:
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("223:1: specification_element : ( informal_chart | class_dictionary | static_diagram | dynamic_diagram | notational_tuning );", 5, 0, input);

                throw nvae;
            }

            switch (alt5) {
                case 1 :
                    // BON.g:223:29: informal_chart
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_informal_chart_in_specification_element1045);
                    informal_chart6=informal_chart();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, informal_chart6.getTree());

                    }
                    break;
                case 2 :
                    // BON.g:224:29: class_dictionary
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_class_dictionary_in_specification_element1075);
                    class_dictionary7=class_dictionary();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, class_dictionary7.getTree());

                    }
                    break;
                case 3 :
                    // BON.g:225:29: static_diagram
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_static_diagram_in_specification_element1105);
                    static_diagram8=static_diagram();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, static_diagram8.getTree());

                    }
                    break;
                case 4 :
                    // BON.g:226:29: dynamic_diagram
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_dynamic_diagram_in_specification_element1135);
                    dynamic_diagram9=dynamic_diagram();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, dynamic_diagram9.getTree());

                    }
                    break;
                case 5 :
                    // BON.g:227:29: notational_tuning
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_notational_tuning_in_specification_element1165);
                    notational_tuning10=notational_tuning();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, notational_tuning10.getTree());

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end specification_element

    public static class informal_chart_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start informal_chart
    // BON.g:230:1: informal_chart : ( system_chart | cluster_chart | class_chart | event_chart | scenario_chart | creation_chart );
    public final informal_chart_return informal_chart() throws RecognitionException {
        informal_chart_return retval = new informal_chart_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        system_chart_return system_chart11 = null;

        cluster_chart_return cluster_chart12 = null;

        class_chart_return class_chart13 = null;

        event_chart_return event_chart14 = null;

        scenario_chart_return scenario_chart15 = null;

        creation_chart_return creation_chart16 = null;



        try {
            // BON.g:234:17: ( system_chart | cluster_chart | class_chart | event_chart | scenario_chart | creation_chart )
            int alt6=6;
            switch ( input.LA(1) ) {
            case 190:
                {
                alt6=1;
                }
                break;
            case 198:
                {
                alt6=2;
                }
                break;
            case 199:
                {
                alt6=3;
                }
                break;
            case 204:
                {
                alt6=4;
                }
                break;
            case 209:
                {
                alt6=5;
                }
                break;
            case 211:
                {
                alt6=6;
                }
                break;
            default:
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("230:1: informal_chart : ( system_chart | cluster_chart | class_chart | event_chart | scenario_chart | creation_chart );", 6, 0, input);

                throw nvae;
            }

            switch (alt6) {
                case 1 :
                    // BON.g:234:22: system_chart
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_system_chart_in_informal_chart1205);
                    system_chart11=system_chart();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, system_chart11.getTree());

                    }
                    break;
                case 2 :
                    // BON.g:235:22: cluster_chart
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_cluster_chart_in_informal_chart1228);
                    cluster_chart12=cluster_chart();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, cluster_chart12.getTree());

                    }
                    break;
                case 3 :
                    // BON.g:236:22: class_chart
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_class_chart_in_informal_chart1251);
                    class_chart13=class_chart();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, class_chart13.getTree());

                    }
                    break;
                case 4 :
                    // BON.g:237:22: event_chart
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_event_chart_in_informal_chart1274);
                    event_chart14=event_chart();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, event_chart14.getTree());

                    }
                    break;
                case 5 :
                    // BON.g:238:22: scenario_chart
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_scenario_chart_in_informal_chart1297);
                    scenario_chart15=scenario_chart();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, scenario_chart15.getTree());

                    }
                    break;
                case 6 :
                    // BON.g:239:22: creation_chart
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_creation_chart_in_informal_chart1320);
                    creation_chart16=creation_chart();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, creation_chart16.getTree());

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end informal_chart

    public static class class_dictionary_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start class_dictionary
    // BON.g:242:1: class_dictionary : (d= 'dictionary' system_name ( dictionary_entry )+ 'end' -> ^( CLASS_DICTIONARY[$d] system_name ( dictionary_entry )+ ) | d= 'dictionary' system_name 'end' -> ^( CLASS_DICTIONARY PARSE_ERROR ) );
    public final class_dictionary_return class_dictionary() throws RecognitionException {
        class_dictionary_return retval = new class_dictionary_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token d=null;
        Token string_literal19=null;
        Token string_literal21=null;
        system_name_return system_name17 = null;

        dictionary_entry_return dictionary_entry18 = null;

        system_name_return system_name20 = null;


        CommonTree d_tree=null;
        CommonTree string_literal19_tree=null;
        CommonTree string_literal21_tree=null;
        RewriteRuleTokenStream stream_186=new RewriteRuleTokenStream(adaptor,"token 186");
        RewriteRuleTokenStream stream_187=new RewriteRuleTokenStream(adaptor,"token 187");
        RewriteRuleSubtreeStream stream_system_name=new RewriteRuleSubtreeStream(adaptor,"rule system_name");
        RewriteRuleSubtreeStream stream_dictionary_entry=new RewriteRuleSubtreeStream(adaptor,"rule dictionary_entry");
        try {
            // BON.g:242:19: (d= 'dictionary' system_name ( dictionary_entry )+ 'end' -> ^( CLASS_DICTIONARY[$d] system_name ( dictionary_entry )+ ) | d= 'dictionary' system_name 'end' -> ^( CLASS_DICTIONARY PARSE_ERROR ) )
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( (LA8_0==186) ) {
                int LA8_1 = input.LA(2);

                if ( (LA8_1==IDENTIFIER) ) {
                    int LA8_2 = input.LA(3);

                    if ( (LA8_2==187) ) {
                        alt8=2;
                    }
                    else if ( (LA8_2==188) ) {
                        alt8=1;
                    }
                    else {
                        if (backtracking>0) {failed=true; return retval;}
                        NoViableAltException nvae =
                            new NoViableAltException("242:1: class_dictionary : (d= 'dictionary' system_name ( dictionary_entry )+ 'end' -> ^( CLASS_DICTIONARY[$d] system_name ( dictionary_entry )+ ) | d= 'dictionary' system_name 'end' -> ^( CLASS_DICTIONARY PARSE_ERROR ) );", 8, 2, input);

                        throw nvae;
                    }
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("242:1: class_dictionary : (d= 'dictionary' system_name ( dictionary_entry )+ 'end' -> ^( CLASS_DICTIONARY[$d] system_name ( dictionary_entry )+ ) | d= 'dictionary' system_name 'end' -> ^( CLASS_DICTIONARY PARSE_ERROR ) );", 8, 1, input);

                    throw nvae;
                }
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("242:1: class_dictionary : (d= 'dictionary' system_name ( dictionary_entry )+ 'end' -> ^( CLASS_DICTIONARY[$d] system_name ( dictionary_entry )+ ) | d= 'dictionary' system_name 'end' -> ^( CLASS_DICTIONARY PARSE_ERROR ) );", 8, 0, input);

                throw nvae;
            }
            switch (alt8) {
                case 1 :
                    // BON.g:242:22: d= 'dictionary' system_name ( dictionary_entry )+ 'end'
                    {
                    d=(Token)input.LT(1);
                    match(input,186,FOLLOW_186_in_class_dictionary1353); if (failed) return retval;
                    if ( backtracking==0 ) stream_186.add(d);

                    pushFollow(FOLLOW_system_name_in_class_dictionary1355);
                    system_name17=system_name();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_system_name.add(system_name17.getTree());
                    // BON.g:243:22: ( dictionary_entry )+
                    int cnt7=0;
                    loop7:
                    do {
                        int alt7=2;
                        int LA7_0 = input.LA(1);

                        if ( (LA7_0==188) ) {
                            alt7=1;
                        }


                        switch (alt7) {
                    	case 1 :
                    	    // BON.g:243:23: dictionary_entry
                    	    {
                    	    pushFollow(FOLLOW_dictionary_entry_in_class_dictionary1380);
                    	    dictionary_entry18=dictionary_entry();
                    	    _fsp--;
                    	    if (failed) return retval;
                    	    if ( backtracking==0 ) stream_dictionary_entry.add(dictionary_entry18.getTree());

                    	    }
                    	    break;

                    	default :
                    	    if ( cnt7 >= 1 ) break loop7;
                    	    if (backtracking>0) {failed=true; return retval;}
                                EarlyExitException eee =
                                    new EarlyExitException(7, input);
                                throw eee;
                        }
                        cnt7++;
                    } while (true);

                    string_literal19=(Token)input.LT(1);
                    match(input,187,FOLLOW_187_in_class_dictionary1406); if (failed) return retval;
                    if ( backtracking==0 ) stream_187.add(string_literal19);


                    // AST REWRITE
                    // elements: dictionary_entry, system_name
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 245:20: -> ^( CLASS_DICTIONARY[$d] system_name ( dictionary_entry )+ )
                    {
                        // BON.g:246:20: ^( CLASS_DICTIONARY[$d] system_name ( dictionary_entry )+ )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLASS_DICTIONARY, d), root_1);

                        adaptor.addChild(root_1, stream_system_name.next());
                        if ( !(stream_dictionary_entry.hasNext()) ) {
                            throw new RewriteEarlyExitException();
                        }
                        while ( stream_dictionary_entry.hasNext() ) {
                            adaptor.addChild(root_1, stream_dictionary_entry.next());

                        }
                        stream_dictionary_entry.reset();

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:251:22: d= 'dictionary' system_name 'end'
                    {
                    d=(Token)input.LT(1);
                    match(input,186,FOLLOW_186_in_class_dictionary1570); if (failed) return retval;
                    if ( backtracking==0 ) stream_186.add(d);

                    pushFollow(FOLLOW_system_name_in_class_dictionary1572);
                    system_name20=system_name();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_system_name.add(system_name20.getTree());
                    string_literal21=(Token)input.LT(1);
                    match(input,187,FOLLOW_187_in_class_dictionary1574); if (failed) return retval;
                    if ( backtracking==0 ) stream_187.add(string_literal21);

                    if ( backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(d), "dictionary entries", "in system dictionary", false)); 
                    }

                    // AST REWRITE
                    // elements: 
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 253:20: -> ^( CLASS_DICTIONARY PARSE_ERROR )
                    {
                        // BON.g:254:20: ^( CLASS_DICTIONARY PARSE_ERROR )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLASS_DICTIONARY, "CLASS_DICTIONARY"), root_1);

                        adaptor.addChild(root_1, adaptor.create(PARSE_ERROR, "PARSE_ERROR"));

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end class_dictionary

    public static class dictionary_entry_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start dictionary_entry
    // BON.g:257:1: dictionary_entry : c= 'class' class_name 'cluster' cluster_name description -> ^( DICTIONARY_ENTRY[$c] class_name cluster_name description ) ;
    public final dictionary_entry_return dictionary_entry() throws RecognitionException {
        dictionary_entry_return retval = new dictionary_entry_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token c=null;
        Token string_literal23=null;
        class_name_return class_name22 = null;

        cluster_name_return cluster_name24 = null;

        description_return description25 = null;


        CommonTree c_tree=null;
        CommonTree string_literal23_tree=null;
        RewriteRuleTokenStream stream_188=new RewriteRuleTokenStream(adaptor,"token 188");
        RewriteRuleTokenStream stream_189=new RewriteRuleTokenStream(adaptor,"token 189");
        RewriteRuleSubtreeStream stream_cluster_name=new RewriteRuleSubtreeStream(adaptor,"rule cluster_name");
        RewriteRuleSubtreeStream stream_description=new RewriteRuleSubtreeStream(adaptor,"rule description");
        RewriteRuleSubtreeStream stream_class_name=new RewriteRuleSubtreeStream(adaptor,"rule class_name");
        try {
            // BON.g:257:19: (c= 'class' class_name 'cluster' cluster_name description -> ^( DICTIONARY_ENTRY[$c] class_name cluster_name description ) )
            // BON.g:257:22: c= 'class' class_name 'cluster' cluster_name description
            {
            c=(Token)input.LT(1);
            match(input,188,FOLLOW_188_in_dictionary_entry1681); if (failed) return retval;
            if ( backtracking==0 ) stream_188.add(c);

            pushFollow(FOLLOW_class_name_in_dictionary_entry1683);
            class_name22=class_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_class_name.add(class_name22.getTree());
            string_literal23=(Token)input.LT(1);
            match(input,189,FOLLOW_189_in_dictionary_entry1707); if (failed) return retval;
            if ( backtracking==0 ) stream_189.add(string_literal23);

            pushFollow(FOLLOW_cluster_name_in_dictionary_entry1709);
            cluster_name24=cluster_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_cluster_name.add(cluster_name24.getTree());
            pushFollow(FOLLOW_description_in_dictionary_entry1733);
            description25=description();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_description.add(description25.getTree());

            // AST REWRITE
            // elements: description, cluster_name, class_name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 260:20: -> ^( DICTIONARY_ENTRY[$c] class_name cluster_name description )
            {
                // BON.g:261:20: ^( DICTIONARY_ENTRY[$c] class_name cluster_name description )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(DICTIONARY_ENTRY, c), root_1);

                adaptor.addChild(root_1, stream_class_name.next());
                adaptor.addChild(root_1, stream_cluster_name.next());
                adaptor.addChild(root_1, stream_description.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end dictionary_entry

    public static class system_chart_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start system_chart
    // BON.g:267:1: system_chart : s= 'system_chart' system_name ( indexing )? ( explanation )? ( part )? ( cluster_entries )? 'end' -> ^( SYSTEM_CHART[$s] system_name ( indexing )? ( explanation )? ( part )? ( cluster_entries )? ) ;
    public final system_chart_return system_chart() throws RecognitionException {
        system_chart_return retval = new system_chart_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token s=null;
        Token string_literal31=null;
        system_name_return system_name26 = null;

        indexing_return indexing27 = null;

        explanation_return explanation28 = null;

        part_return part29 = null;

        cluster_entries_return cluster_entries30 = null;


        CommonTree s_tree=null;
        CommonTree string_literal31_tree=null;
        RewriteRuleTokenStream stream_187=new RewriteRuleTokenStream(adaptor,"token 187");
        RewriteRuleTokenStream stream_190=new RewriteRuleTokenStream(adaptor,"token 190");
        RewriteRuleSubtreeStream stream_system_name=new RewriteRuleSubtreeStream(adaptor,"rule system_name");
        RewriteRuleSubtreeStream stream_indexing=new RewriteRuleSubtreeStream(adaptor,"rule indexing");
        RewriteRuleSubtreeStream stream_explanation=new RewriteRuleSubtreeStream(adaptor,"rule explanation");
        RewriteRuleSubtreeStream stream_part=new RewriteRuleSubtreeStream(adaptor,"rule part");
        RewriteRuleSubtreeStream stream_cluster_entries=new RewriteRuleSubtreeStream(adaptor,"rule cluster_entries");
        try {
            // BON.g:269:15: (s= 'system_chart' system_name ( indexing )? ( explanation )? ( part )? ( cluster_entries )? 'end' -> ^( SYSTEM_CHART[$s] system_name ( indexing )? ( explanation )? ( part )? ( cluster_entries )? ) )
            // BON.g:269:18: s= 'system_chart' system_name ( indexing )? ( explanation )? ( part )? ( cluster_entries )? 'end'
            {
            s=(Token)input.LT(1);
            match(input,190,FOLLOW_190_in_system_chart1884); if (failed) return retval;
            if ( backtracking==0 ) stream_190.add(s);

            pushFollow(FOLLOW_system_name_in_system_chart1886);
            system_name26=system_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_system_name.add(system_name26.getTree());
            if ( backtracking==0 ) {
               getTI().informal().setSystem(input.toString(system_name26.start,system_name26.stop), getSLoc(s));
                                 getContext().enterSystemChart(input.toString(system_name26.start,system_name26.stop)); 
            }
            // BON.g:272:18: ( indexing )?
            int alt9=2;
            int LA9_0 = input.LA(1);

            if ( (LA9_0==192) ) {
                alt9=1;
            }
            switch (alt9) {
                case 1 :
                    // BON.g:272:19: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_system_chart1926);
                    indexing27=indexing();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_indexing.add(indexing27.getTree());

                    }
                    break;

            }

            // BON.g:273:18: ( explanation )?
            int alt10=2;
            int LA10_0 = input.LA(1);

            if ( (LA10_0==191) ) {
                alt10=1;
            }
            switch (alt10) {
                case 1 :
                    // BON.g:273:19: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_system_chart1948);
                    explanation28=explanation();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_explanation.add(explanation28.getTree());

                    }
                    break;

            }

            // BON.g:274:18: ( part )?
            int alt11=2;
            int LA11_0 = input.LA(1);

            if ( (LA11_0==193) ) {
                alt11=1;
            }
            switch (alt11) {
                case 1 :
                    // BON.g:274:19: part
                    {
                    pushFollow(FOLLOW_part_in_system_chart1971);
                    part29=part();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_part.add(part29.getTree());

                    }
                    break;

            }

            // BON.g:275:18: ( cluster_entries )?
            int alt12=2;
            int LA12_0 = input.LA(1);

            if ( (LA12_0==189) ) {
                alt12=1;
            }
            switch (alt12) {
                case 1 :
                    // BON.g:275:19: cluster_entries
                    {
                    pushFollow(FOLLOW_cluster_entries_in_system_chart1994);
                    cluster_entries30=cluster_entries();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_cluster_entries.add(cluster_entries30.getTree());

                    }
                    break;

            }

            string_literal31=(Token)input.LT(1);
            match(input,187,FOLLOW_187_in_system_chart2016); if (failed) return retval;
            if ( backtracking==0 ) stream_187.add(string_literal31);

            if ( backtracking==0 ) {
               getContext().leaveSystemChart(); 
            }

            // AST REWRITE
            // elements: explanation, indexing, cluster_entries, system_name, part
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 278:16: -> ^( SYSTEM_CHART[$s] system_name ( indexing )? ( explanation )? ( part )? ( cluster_entries )? )
            {
                // BON.g:279:16: ^( SYSTEM_CHART[$s] system_name ( indexing )? ( explanation )? ( part )? ( cluster_entries )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(SYSTEM_CHART, s), root_1);

                adaptor.addChild(root_1, stream_system_name.next());
                // BON.g:281:18: ( indexing )?
                if ( stream_indexing.hasNext() ) {
                    adaptor.addChild(root_1, stream_indexing.next());

                }
                stream_indexing.reset();
                // BON.g:282:18: ( explanation )?
                if ( stream_explanation.hasNext() ) {
                    adaptor.addChild(root_1, stream_explanation.next());

                }
                stream_explanation.reset();
                // BON.g:283:18: ( part )?
                if ( stream_part.hasNext() ) {
                    adaptor.addChild(root_1, stream_part.next());

                }
                stream_part.reset();
                // BON.g:284:18: ( cluster_entries )?
                if ( stream_cluster_entries.hasNext() ) {
                    adaptor.addChild(root_1, stream_cluster_entries.next());

                }
                stream_cluster_entries.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end system_chart

    public static class explanation_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start explanation
    // BON.g:288:1: explanation : (e= 'explanation' manifest_textblock -> ^( EXPLANATION[$e] manifest_textblock ) | e= 'explanation' -> ^( EXPLANATION[$e] PARSE_ERROR ) );
    public final explanation_return explanation() throws RecognitionException {
        explanation_return retval = new explanation_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token e=null;
        manifest_textblock_return manifest_textblock32 = null;


        CommonTree e_tree=null;
        RewriteRuleTokenStream stream_191=new RewriteRuleTokenStream(adaptor,"token 191");
        RewriteRuleSubtreeStream stream_manifest_textblock=new RewriteRuleSubtreeStream(adaptor,"rule manifest_textblock");
        try {
            // BON.g:288:14: (e= 'explanation' manifest_textblock -> ^( EXPLANATION[$e] manifest_textblock ) | e= 'explanation' -> ^( EXPLANATION[$e] PARSE_ERROR ) )
            int alt13=2;
            int LA13_0 = input.LA(1);

            if ( (LA13_0==191) ) {
                int LA13_1 = input.LA(2);

                if ( ((LA13_1>=187 && LA13_1<=189)||LA13_1==193||(LA13_1>=200 && LA13_1<=203)||LA13_1==207||LA13_1==210||LA13_1==212) ) {
                    alt13=2;
                }
                else if ( (LA13_1==MANIFEST_STRING||LA13_1==MANIFEST_TEXTBLOCK_START) ) {
                    alt13=1;
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("288:1: explanation : (e= 'explanation' manifest_textblock -> ^( EXPLANATION[$e] manifest_textblock ) | e= 'explanation' -> ^( EXPLANATION[$e] PARSE_ERROR ) );", 13, 1, input);

                    throw nvae;
                }
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("288:1: explanation : (e= 'explanation' manifest_textblock -> ^( EXPLANATION[$e] manifest_textblock ) | e= 'explanation' -> ^( EXPLANATION[$e] PARSE_ERROR ) );", 13, 0, input);

                throw nvae;
            }
            switch (alt13) {
                case 1 :
                    // BON.g:288:17: e= 'explanation' manifest_textblock
                    {
                    e=(Token)input.LT(1);
                    match(input,191,FOLLOW_191_in_explanation2227); if (failed) return retval;
                    if ( backtracking==0 ) stream_191.add(e);

                    pushFollow(FOLLOW_manifest_textblock_in_explanation2229);
                    manifest_textblock32=manifest_textblock();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_manifest_textblock.add(manifest_textblock32.getTree());

                    // AST REWRITE
                    // elements: manifest_textblock
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 289:15: -> ^( EXPLANATION[$e] manifest_textblock )
                    {
                        // BON.g:290:15: ^( EXPLANATION[$e] manifest_textblock )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(EXPLANATION, e), root_1);

                        adaptor.addChild(root_1, stream_manifest_textblock.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:294:16: e= 'explanation'
                    {
                    e=(Token)input.LT(1);
                    match(input,191,FOLLOW_191_in_explanation2334); if (failed) return retval;
                    if ( backtracking==0 ) stream_191.add(e);

                    if ( backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(e), "explanation text", "after 'explanation'", false)); 
                    }

                    // AST REWRITE
                    // elements: 
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 295:15: -> ^( EXPLANATION[$e] PARSE_ERROR )
                    {
                        // BON.g:296:15: ^( EXPLANATION[$e] PARSE_ERROR )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(EXPLANATION, e), root_1);

                        adaptor.addChild(root_1, adaptor.create(PARSE_ERROR, "PARSE_ERROR"));

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end explanation

    public static class indexing_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start indexing
    // BON.g:299:1: indexing : (i= 'indexing' index_list -> ^( INDEXING[$i] index_list ) | i= 'indexing' -> ^( INDEXING[$i] PARSE_ERROR ) );
    public final indexing_return indexing() throws RecognitionException {
        indexing_return retval = new indexing_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token i=null;
        index_list_return index_list33 = null;


        CommonTree i_tree=null;
        RewriteRuleTokenStream stream_192=new RewriteRuleTokenStream(adaptor,"token 192");
        RewriteRuleSubtreeStream stream_index_list=new RewriteRuleSubtreeStream(adaptor,"rule index_list");
        try {
            // BON.g:299:11: (i= 'indexing' index_list -> ^( INDEXING[$i] index_list ) | i= 'indexing' -> ^( INDEXING[$i] PARSE_ERROR ) )
            int alt14=2;
            int LA14_0 = input.LA(1);

            if ( (LA14_0==192) ) {
                int LA14_1 = input.LA(2);

                if ( (LA14_1==IDENTIFIER) ) {
                    alt14=1;
                }
                else if ( (LA14_1==EOF||(LA14_1>=186 && LA14_1<=191)||LA14_1==193||(LA14_1>=198 && LA14_1<=204)||LA14_1==207||(LA14_1>=209 && LA14_1<=212)||LA14_1==214||LA14_1==234||LA14_1==252||(LA14_1>=259 && LA14_1<=261)) ) {
                    alt14=2;
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("299:1: indexing : (i= 'indexing' index_list -> ^( INDEXING[$i] index_list ) | i= 'indexing' -> ^( INDEXING[$i] PARSE_ERROR ) );", 14, 1, input);

                    throw nvae;
                }
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("299:1: indexing : (i= 'indexing' index_list -> ^( INDEXING[$i] index_list ) | i= 'indexing' -> ^( INDEXING[$i] PARSE_ERROR ) );", 14, 0, input);

                throw nvae;
            }
            switch (alt14) {
                case 1 :
                    // BON.g:299:14: i= 'indexing' index_list
                    {
                    i=(Token)input.LT(1);
                    match(input,192,FOLLOW_192_in_indexing2401); if (failed) return retval;
                    if ( backtracking==0 ) stream_192.add(i);

                    pushFollow(FOLLOW_index_list_in_indexing2403);
                    index_list33=index_list();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_index_list.add(index_list33.getTree());

                    // AST REWRITE
                    // elements: index_list
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 300:12: -> ^( INDEXING[$i] index_list )
                    {
                        // BON.g:301:12: ^( INDEXING[$i] index_list )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INDEXING, i), root_1);

                        adaptor.addChild(root_1, stream_index_list.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:305:14: i= 'indexing'
                    {
                    i=(Token)input.LT(1);
                    match(input,192,FOLLOW_192_in_indexing2492); if (failed) return retval;
                    if ( backtracking==0 ) stream_192.add(i);

                    if ( backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(i), "indexing entries", "after 'indexing'", false)); 
                    }

                    // AST REWRITE
                    // elements: 
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 306:12: -> ^( INDEXING[$i] PARSE_ERROR )
                    {
                        // BON.g:307:12: ^( INDEXING[$i] PARSE_ERROR )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INDEXING, i), root_1);

                        adaptor.addChild(root_1, adaptor.create(PARSE_ERROR, "PARSE_ERROR"));

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end indexing

    public static class part_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start part
    // BON.g:310:1: part : (p= 'part' MANIFEST_STRING -> ^( PART[$p] MANIFEST_STRING ) | p= 'part' -> ^( PART PARSE_ERROR ) );
    public final part_return part() throws RecognitionException {
        part_return retval = new part_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token p=null;
        Token MANIFEST_STRING34=null;

        CommonTree p_tree=null;
        CommonTree MANIFEST_STRING34_tree=null;
        RewriteRuleTokenStream stream_MANIFEST_STRING=new RewriteRuleTokenStream(adaptor,"token MANIFEST_STRING");
        RewriteRuleTokenStream stream_193=new RewriteRuleTokenStream(adaptor,"token 193");

        try {
            // BON.g:310:7: (p= 'part' MANIFEST_STRING -> ^( PART[$p] MANIFEST_STRING ) | p= 'part' -> ^( PART PARSE_ERROR ) )
            int alt15=2;
            int LA15_0 = input.LA(1);

            if ( (LA15_0==193) ) {
                int LA15_1 = input.LA(2);

                if ( (LA15_1==MANIFEST_STRING) ) {
                    alt15=1;
                }
                else if ( ((LA15_1>=187 && LA15_1<=189)||(LA15_1>=200 && LA15_1<=203)||LA15_1==207||LA15_1==210||LA15_1==212) ) {
                    alt15=2;
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("310:1: part : (p= 'part' MANIFEST_STRING -> ^( PART[$p] MANIFEST_STRING ) | p= 'part' -> ^( PART PARSE_ERROR ) );", 15, 1, input);

                    throw nvae;
                }
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("310:1: part : (p= 'part' MANIFEST_STRING -> ^( PART[$p] MANIFEST_STRING ) | p= 'part' -> ^( PART PARSE_ERROR ) );", 15, 0, input);

                throw nvae;
            }
            switch (alt15) {
                case 1 :
                    // BON.g:310:10: p= 'part' MANIFEST_STRING
                    {
                    p=(Token)input.LT(1);
                    match(input,193,FOLLOW_193_in_part2550); if (failed) return retval;
                    if ( backtracking==0 ) stream_193.add(p);

                    MANIFEST_STRING34=(Token)input.LT(1);
                    match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_part2552); if (failed) return retval;
                    if ( backtracking==0 ) stream_MANIFEST_STRING.add(MANIFEST_STRING34);


                    // AST REWRITE
                    // elements: MANIFEST_STRING
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 311:8: -> ^( PART[$p] MANIFEST_STRING )
                    {
                        // BON.g:312:8: ^( PART[$p] MANIFEST_STRING )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(PART, p), root_1);

                        adaptor.addChild(root_1, stream_MANIFEST_STRING.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:316:10: p= 'part'
                    {
                    p=(Token)input.LT(1);
                    match(input,193,FOLLOW_193_in_part2616); if (failed) return retval;
                    if ( backtracking==0 ) stream_193.add(p);

                    if ( backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(p), "part text", "after 'part'", false)); 
                    }

                    // AST REWRITE
                    // elements: 
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 317:8: -> ^( PART PARSE_ERROR )
                    {
                        // BON.g:318:10: ^( PART PARSE_ERROR )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(PART, "PART"), root_1);

                        adaptor.addChild(root_1, adaptor.create(PARSE_ERROR, "PARSE_ERROR"));

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end part

    public static class description_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start description
    // BON.g:321:1: description : d= 'description' manifest_textblock -> ^( DESCRIPTION[$d] manifest_textblock ) ;
    public final description_return description() throws RecognitionException {
        description_return retval = new description_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token d=null;
        manifest_textblock_return manifest_textblock35 = null;


        CommonTree d_tree=null;
        RewriteRuleTokenStream stream_194=new RewriteRuleTokenStream(adaptor,"token 194");
        RewriteRuleSubtreeStream stream_manifest_textblock=new RewriteRuleSubtreeStream(adaptor,"rule manifest_textblock");
        try {
            // BON.g:321:14: (d= 'description' manifest_textblock -> ^( DESCRIPTION[$d] manifest_textblock ) )
            // BON.g:321:17: d= 'description' manifest_textblock
            {
            d=(Token)input.LT(1);
            match(input,194,FOLLOW_194_in_description2664); if (failed) return retval;
            if ( backtracking==0 ) stream_194.add(d);

            pushFollow(FOLLOW_manifest_textblock_in_description2666);
            manifest_textblock35=manifest_textblock();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_manifest_textblock.add(manifest_textblock35.getTree());

            // AST REWRITE
            // elements: manifest_textblock
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 322:15: -> ^( DESCRIPTION[$d] manifest_textblock )
            {
                // BON.g:323:15: ^( DESCRIPTION[$d] manifest_textblock )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(DESCRIPTION, d), root_1);

                adaptor.addChild(root_1, stream_manifest_textblock.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end description

    public static class cluster_entries_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start cluster_entries
    // BON.g:328:1: cluster_entries : ( cluster_entry )+ -> ^( CLUSTER_ENTRIES ( cluster_entry )+ ) ;
    public final cluster_entries_return cluster_entries() throws RecognitionException {
        cluster_entries_return retval = new cluster_entries_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        cluster_entry_return cluster_entry36 = null;


        RewriteRuleSubtreeStream stream_cluster_entry=new RewriteRuleSubtreeStream(adaptor,"rule cluster_entry");
        try {
            // BON.g:328:18: ( ( cluster_entry )+ -> ^( CLUSTER_ENTRIES ( cluster_entry )+ ) )
            // BON.g:328:21: ( cluster_entry )+
            {
            // BON.g:328:21: ( cluster_entry )+
            int cnt16=0;
            loop16:
            do {
                int alt16=2;
                int LA16_0 = input.LA(1);

                if ( (LA16_0==189) ) {
                    alt16=1;
                }


                switch (alt16) {
            	case 1 :
            	    // BON.g:328:22: cluster_entry
            	    {
            	    pushFollow(FOLLOW_cluster_entry_in_cluster_entries2763);
            	    cluster_entry36=cluster_entry();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_cluster_entry.add(cluster_entry36.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt16 >= 1 ) break loop16;
            	    if (backtracking>0) {failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(16, input);
                        throw eee;
                }
                cnt16++;
            } while (true);


            // AST REWRITE
            // elements: cluster_entry
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 329:19: -> ^( CLUSTER_ENTRIES ( cluster_entry )+ )
            {
                // BON.g:330:19: ^( CLUSTER_ENTRIES ( cluster_entry )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLUSTER_ENTRIES, "CLUSTER_ENTRIES"), root_1);

                if ( !(stream_cluster_entry.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_cluster_entry.hasNext() ) {
                    adaptor.addChild(root_1, stream_cluster_entry.next());

                }
                stream_cluster_entry.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end cluster_entries

    public static class cluster_entry_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start cluster_entry
    // BON.g:335:1: cluster_entry : c= 'cluster' cluster_name description -> ^( CLUSTER_ENTRY[$c] cluster_name description ) ;
    public final cluster_entry_return cluster_entry() throws RecognitionException {
        cluster_entry_return retval = new cluster_entry_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token c=null;
        cluster_name_return cluster_name37 = null;

        description_return description38 = null;


        CommonTree c_tree=null;
        RewriteRuleTokenStream stream_189=new RewriteRuleTokenStream(adaptor,"token 189");
        RewriteRuleSubtreeStream stream_cluster_name=new RewriteRuleSubtreeStream(adaptor,"rule cluster_name");
        RewriteRuleSubtreeStream stream_description=new RewriteRuleSubtreeStream(adaptor,"rule description");
        try {
            // BON.g:335:16: (c= 'cluster' cluster_name description -> ^( CLUSTER_ENTRY[$c] cluster_name description ) )
            // BON.g:335:19: c= 'cluster' cluster_name description
            {
            c=(Token)input.LT(1);
            match(input,189,FOLLOW_189_in_cluster_entry2902); if (failed) return retval;
            if ( backtracking==0 ) stream_189.add(c);

            pushFollow(FOLLOW_cluster_name_in_cluster_entry2904);
            cluster_name37=cluster_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_cluster_name.add(cluster_name37.getTree());
            pushFollow(FOLLOW_description_in_cluster_entry2906);
            description38=description();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_description.add(description38.getTree());
            if ( backtracking==0 ) {
               getTI().informal().addClusterEntry(input.toString(cluster_name37.start,cluster_name37.stop)); 
            }

            // AST REWRITE
            // elements: description, cluster_name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 337:17: -> ^( CLUSTER_ENTRY[$c] cluster_name description )
            {
                // BON.g:338:17: ^( CLUSTER_ENTRY[$c] cluster_name description )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLUSTER_ENTRY, c), root_1);

                adaptor.addChild(root_1, stream_cluster_name.next());
                adaptor.addChild(root_1, stream_description.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end cluster_entry

    public static class system_name_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start system_name
    // BON.g:343:1: system_name : i= IDENTIFIER -> ^( SYSTEM_NAME[$i] IDENTIFIER ) ;
    public final system_name_return system_name() throws RecognitionException {
        system_name_return retval = new system_name_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token i=null;

        CommonTree i_tree=null;
        RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");

        try {
            // BON.g:343:14: (i= IDENTIFIER -> ^( SYSTEM_NAME[$i] IDENTIFIER ) )
            // BON.g:343:17: i= IDENTIFIER
            {
            i=(Token)input.LT(1);
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_system_name3050); if (failed) return retval;
            if ( backtracking==0 ) stream_IDENTIFIER.add(i);


            // AST REWRITE
            // elements: IDENTIFIER
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 344:15: -> ^( SYSTEM_NAME[$i] IDENTIFIER )
            {
                // BON.g:345:15: ^( SYSTEM_NAME[$i] IDENTIFIER )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(SYSTEM_NAME, i), root_1);

                adaptor.addChild(root_1, stream_IDENTIFIER.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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

    public static class index_list_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start index_list
    // BON.g:350:1: index_list : i1= index_clause ( ( ';' index_clause ) | i= index_clause )* ( ';' )? -> ^( INDEX_LIST[$i1.start] ( index_clause )+ ) ;
    public final index_list_return index_list() throws RecognitionException {
        index_list_return retval = new index_list_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal39=null;
        Token char_literal41=null;
        index_clause_return i1 = null;

        index_clause_return i = null;

        index_clause_return index_clause40 = null;


        CommonTree char_literal39_tree=null;
        CommonTree char_literal41_tree=null;
        RewriteRuleTokenStream stream_195=new RewriteRuleTokenStream(adaptor,"token 195");
        RewriteRuleSubtreeStream stream_index_clause=new RewriteRuleSubtreeStream(adaptor,"rule index_clause");
        try {
            // BON.g:352:13: (i1= index_clause ( ( ';' index_clause ) | i= index_clause )* ( ';' )? -> ^( INDEX_LIST[$i1.start] ( index_clause )+ ) )
            // BON.g:352:16: i1= index_clause ( ( ';' index_clause ) | i= index_clause )* ( ';' )?
            {
            pushFollow(FOLLOW_index_clause_in_index_list3150);
            i1=index_clause();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_index_clause.add(i1.getTree());
            // BON.g:353:16: ( ( ';' index_clause ) | i= index_clause )*
            loop17:
            do {
                int alt17=3;
                int LA17_0 = input.LA(1);

                if ( (LA17_0==195) ) {
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
            	    // BON.g:353:19: ( ';' index_clause )
            	    {
            	    // BON.g:353:19: ( ';' index_clause )
            	    // BON.g:353:20: ';' index_clause
            	    {
            	    char_literal39=(Token)input.LT(1);
            	    match(input,195,FOLLOW_195_in_index_list3172); if (failed) return retval;
            	    if ( backtracking==0 ) stream_195.add(char_literal39);

            	    pushFollow(FOLLOW_index_clause_in_index_list3174);
            	    index_clause40=index_clause();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_index_clause.add(index_clause40.getTree());

            	    }


            	    }
            	    break;
            	case 2 :
            	    // BON.g:354:19: i= index_clause
            	    {
            	    pushFollow(FOLLOW_index_clause_in_index_list3197);
            	    i=index_clause();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_index_clause.add(i.getTree());
            	    if ( backtracking==0 ) {
            	       addParseProblem(new MissingElementParseError(getSourceLocation(((Token)i.start)), "semi-colon", "before additional index clause", false)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop17;
                }
            } while (true);

            // BON.g:356:16: ( ';' )?
            int alt18=2;
            int LA18_0 = input.LA(1);

            if ( (LA18_0==195) ) {
                alt18=1;
            }
            switch (alt18) {
                case 1 :
                    // BON.g:356:16: ';'
                    {
                    char_literal41=(Token)input.LT(1);
                    match(input,195,FOLLOW_195_in_index_list3235); if (failed) return retval;
                    if ( backtracking==0 ) stream_195.add(char_literal41);


                    }
                    break;

            }


            // AST REWRITE
            // elements: index_clause
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 357:14: -> ^( INDEX_LIST[$i1.start] ( index_clause )+ )
            {
                // BON.g:358:14: ^( INDEX_LIST[$i1.start] ( index_clause )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INDEX_LIST, ((Token)i1.start)), root_1);

                if ( !(stream_index_clause.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_index_clause.hasNext() ) {
                    adaptor.addChild(root_1, stream_index_clause.next());

                }
                stream_index_clause.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end index_list

    public static class index_clause_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start index_clause
    // BON.g:363:1: index_clause : (i= IDENTIFIER ':' index_term_list -> ^( INDEX_CLAUSE[$i] IDENTIFIER index_term_list ) | i= IDENTIFIER ':' -> ^( INDEX_CLAUSE PARSE_ERROR ) );
    public final index_clause_return index_clause() throws RecognitionException {
        index_clause_return retval = new index_clause_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token i=null;
        Token char_literal42=null;
        Token char_literal44=null;
        index_term_list_return index_term_list43 = null;


        CommonTree i_tree=null;
        CommonTree char_literal42_tree=null;
        CommonTree char_literal44_tree=null;
        RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
        RewriteRuleTokenStream stream_196=new RewriteRuleTokenStream(adaptor,"token 196");
        RewriteRuleSubtreeStream stream_index_term_list=new RewriteRuleSubtreeStream(adaptor,"rule index_term_list");
        try {
            // BON.g:363:15: (i= IDENTIFIER ':' index_term_list -> ^( INDEX_CLAUSE[$i] IDENTIFIER index_term_list ) | i= IDENTIFIER ':' -> ^( INDEX_CLAUSE PARSE_ERROR ) )
            int alt19=2;
            int LA19_0 = input.LA(1);

            if ( (LA19_0==IDENTIFIER) ) {
                int LA19_1 = input.LA(2);

                if ( (LA19_1==196) ) {
                    int LA19_2 = input.LA(3);

                    if ( (LA19_2==EOF||LA19_2==IDENTIFIER||(LA19_2>=186 && LA19_2<=191)||LA19_2==193||LA19_2==195||(LA19_2>=198 && LA19_2<=204)||LA19_2==207||(LA19_2>=209 && LA19_2<=212)||LA19_2==214||LA19_2==234||LA19_2==252||(LA19_2>=259 && LA19_2<=261)) ) {
                        alt19=2;
                    }
                    else if ( (LA19_2==MANIFEST_STRING) ) {
                        alt19=1;
                    }
                    else {
                        if (backtracking>0) {failed=true; return retval;}
                        NoViableAltException nvae =
                            new NoViableAltException("363:1: index_clause : (i= IDENTIFIER ':' index_term_list -> ^( INDEX_CLAUSE[$i] IDENTIFIER index_term_list ) | i= IDENTIFIER ':' -> ^( INDEX_CLAUSE PARSE_ERROR ) );", 19, 2, input);

                        throw nvae;
                    }
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("363:1: index_clause : (i= IDENTIFIER ':' index_term_list -> ^( INDEX_CLAUSE[$i] IDENTIFIER index_term_list ) | i= IDENTIFIER ':' -> ^( INDEX_CLAUSE PARSE_ERROR ) );", 19, 1, input);

                    throw nvae;
                }
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("363:1: index_clause : (i= IDENTIFIER ':' index_term_list -> ^( INDEX_CLAUSE[$i] IDENTIFIER index_term_list ) | i= IDENTIFIER ':' -> ^( INDEX_CLAUSE PARSE_ERROR ) );", 19, 0, input);

                throw nvae;
            }
            switch (alt19) {
                case 1 :
                    // BON.g:363:18: i= IDENTIFIER ':' index_term_list
                    {
                    i=(Token)input.LT(1);
                    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_index_clause3342); if (failed) return retval;
                    if ( backtracking==0 ) stream_IDENTIFIER.add(i);

                    char_literal42=(Token)input.LT(1);
                    match(input,196,FOLLOW_196_in_index_clause3344); if (failed) return retval;
                    if ( backtracking==0 ) stream_196.add(char_literal42);

                    pushFollow(FOLLOW_index_term_list_in_index_clause3346);
                    index_term_list43=index_term_list();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_index_term_list.add(index_term_list43.getTree());

                    // AST REWRITE
                    // elements: index_term_list, IDENTIFIER
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 364:16: -> ^( INDEX_CLAUSE[$i] IDENTIFIER index_term_list )
                    {
                        // BON.g:365:16: ^( INDEX_CLAUSE[$i] IDENTIFIER index_term_list )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INDEX_CLAUSE, i), root_1);

                        adaptor.addChild(root_1, stream_IDENTIFIER.next());
                        adaptor.addChild(root_1, stream_index_term_list.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:369:18: i= IDENTIFIER ':'
                    {
                    i=(Token)input.LT(1);
                    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_index_clause3461); if (failed) return retval;
                    if ( backtracking==0 ) stream_IDENTIFIER.add(i);

                    char_literal44=(Token)input.LT(1);
                    match(input,196,FOLLOW_196_in_index_clause3463); if (failed) return retval;
                    if ( backtracking==0 ) stream_196.add(char_literal44);

                    if ( backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(i), "index term(s)", "in index clause", true)); 
                    }

                    // AST REWRITE
                    // elements: 
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 370:16: -> ^( INDEX_CLAUSE PARSE_ERROR )
                    {
                        // BON.g:371:18: ^( INDEX_CLAUSE PARSE_ERROR )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INDEX_CLAUSE, "INDEX_CLAUSE"), root_1);

                        adaptor.addChild(root_1, adaptor.create(PARSE_ERROR, "PARSE_ERROR"));

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end index_clause

    public static class index_term_list_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start index_term_list
    // BON.g:374:1: index_term_list : i1= index_string ( ',' index_string )* -> ^( INDEX_TERM_LIST[$i1.start] ( index_string )+ ) ;
    public final index_term_list_return index_term_list() throws RecognitionException {
        index_term_list_return retval = new index_term_list_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal45=null;
        index_string_return i1 = null;

        index_string_return index_string46 = null;


        CommonTree char_literal45_tree=null;
        RewriteRuleTokenStream stream_197=new RewriteRuleTokenStream(adaptor,"token 197");
        RewriteRuleSubtreeStream stream_index_string=new RewriteRuleSubtreeStream(adaptor,"rule index_string");
        try {
            // BON.g:374:18: (i1= index_string ( ',' index_string )* -> ^( INDEX_TERM_LIST[$i1.start] ( index_string )+ ) )
            // BON.g:374:21: i1= index_string ( ',' index_string )*
            {
            pushFollow(FOLLOW_index_string_in_index_term_list3548);
            i1=index_string();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_index_string.add(i1.getTree());
            // BON.g:374:37: ( ',' index_string )*
            loop20:
            do {
                int alt20=2;
                int LA20_0 = input.LA(1);

                if ( (LA20_0==197) ) {
                    alt20=1;
                }


                switch (alt20) {
            	case 1 :
            	    // BON.g:374:38: ',' index_string
            	    {
            	    char_literal45=(Token)input.LT(1);
            	    match(input,197,FOLLOW_197_in_index_term_list3551); if (failed) return retval;
            	    if ( backtracking==0 ) stream_197.add(char_literal45);

            	    pushFollow(FOLLOW_index_string_in_index_term_list3553);
            	    index_string46=index_string();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_index_string.add(index_string46.getTree());

            	    }
            	    break;

            	default :
            	    break loop20;
                }
            } while (true);


            // AST REWRITE
            // elements: index_string
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 375:19: -> ^( INDEX_TERM_LIST[$i1.start] ( index_string )+ )
            {
                // BON.g:376:19: ^( INDEX_TERM_LIST[$i1.start] ( index_string )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INDEX_TERM_LIST, ((Token)i1.start)), root_1);

                if ( !(stream_index_string.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_index_string.hasNext() ) {
                    adaptor.addChild(root_1, stream_index_string.next());

                }
                stream_index_string.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end index_term_list

    public static class index_string_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start index_string
    // BON.g:381:1: index_string : m= MANIFEST_STRING -> ^( INDEX_STRING[$m] MANIFEST_STRING ) ;
    public final index_string_return index_string() throws RecognitionException {
        index_string_return retval = new index_string_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token m=null;

        CommonTree m_tree=null;
        RewriteRuleTokenStream stream_MANIFEST_STRING=new RewriteRuleTokenStream(adaptor,"token MANIFEST_STRING");

        try {
            // BON.g:381:15: (m= MANIFEST_STRING -> ^( INDEX_STRING[$m] MANIFEST_STRING ) )
            // BON.g:381:18: m= MANIFEST_STRING
            {
            m=(Token)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_index_string3691); if (failed) return retval;
            if ( backtracking==0 ) stream_MANIFEST_STRING.add(m);


            // AST REWRITE
            // elements: MANIFEST_STRING
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 382:16: -> ^( INDEX_STRING[$m] MANIFEST_STRING )
            {
                // BON.g:383:16: ^( INDEX_STRING[$m] MANIFEST_STRING )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INDEX_STRING, m), root_1);

                adaptor.addChild(root_1, stream_MANIFEST_STRING.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end index_string

    public static class cluster_chart_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start cluster_chart
    // BON.g:388:1: cluster_chart : c= 'cluster_chart' cluster_name ( indexing )? ( explanation )? ( part )? ( class_entries )? ( cluster_entries )? 'end' -> ^( CLUSTER_CHART[$c] cluster_name ( indexing )? ( explanation )? ( part )? ( class_entries )? ( cluster_entries )? ) ;
    public final cluster_chart_return cluster_chart() throws RecognitionException {
        cluster_chart_return retval = new cluster_chart_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token c=null;
        Token string_literal53=null;
        cluster_name_return cluster_name47 = null;

        indexing_return indexing48 = null;

        explanation_return explanation49 = null;

        part_return part50 = null;

        class_entries_return class_entries51 = null;

        cluster_entries_return cluster_entries52 = null;


        CommonTree c_tree=null;
        CommonTree string_literal53_tree=null;
        RewriteRuleTokenStream stream_198=new RewriteRuleTokenStream(adaptor,"token 198");
        RewriteRuleTokenStream stream_187=new RewriteRuleTokenStream(adaptor,"token 187");
        RewriteRuleSubtreeStream stream_cluster_name=new RewriteRuleSubtreeStream(adaptor,"rule cluster_name");
        RewriteRuleSubtreeStream stream_indexing=new RewriteRuleSubtreeStream(adaptor,"rule indexing");
        RewriteRuleSubtreeStream stream_explanation=new RewriteRuleSubtreeStream(adaptor,"rule explanation");
        RewriteRuleSubtreeStream stream_class_entries=new RewriteRuleSubtreeStream(adaptor,"rule class_entries");
        RewriteRuleSubtreeStream stream_part=new RewriteRuleSubtreeStream(adaptor,"rule part");
        RewriteRuleSubtreeStream stream_cluster_entries=new RewriteRuleSubtreeStream(adaptor,"rule cluster_entries");
        try {
            // BON.g:390:16: (c= 'cluster_chart' cluster_name ( indexing )? ( explanation )? ( part )? ( class_entries )? ( cluster_entries )? 'end' -> ^( CLUSTER_CHART[$c] cluster_name ( indexing )? ( explanation )? ( part )? ( class_entries )? ( cluster_entries )? ) )
            // BON.g:390:19: c= 'cluster_chart' cluster_name ( indexing )? ( explanation )? ( part )? ( class_entries )? ( cluster_entries )? 'end'
            {
            c=(Token)input.LT(1);
            match(input,198,FOLLOW_198_in_cluster_chart3799); if (failed) return retval;
            if ( backtracking==0 ) stream_198.add(c);

            pushFollow(FOLLOW_cluster_name_in_cluster_chart3801);
            cluster_name47=cluster_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_cluster_name.add(cluster_name47.getTree());
            if ( backtracking==0 ) {
               getTI().informal().addCluster(input.toString(cluster_name47.start,cluster_name47.stop), getSLoc(c));
                                  getContext().enterClusterChart(input.toString(cluster_name47.start,cluster_name47.stop)); 
            }
            // BON.g:393:19: ( indexing )?
            int alt21=2;
            int LA21_0 = input.LA(1);

            if ( (LA21_0==192) ) {
                alt21=1;
            }
            switch (alt21) {
                case 1 :
                    // BON.g:393:20: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_cluster_chart3843);
                    indexing48=indexing();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_indexing.add(indexing48.getTree());

                    }
                    break;

            }

            // BON.g:394:19: ( explanation )?
            int alt22=2;
            int LA22_0 = input.LA(1);

            if ( (LA22_0==191) ) {
                alt22=1;
            }
            switch (alt22) {
                case 1 :
                    // BON.g:394:20: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_cluster_chart3867);
                    explanation49=explanation();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_explanation.add(explanation49.getTree());

                    }
                    break;

            }

            // BON.g:395:19: ( part )?
            int alt23=2;
            int LA23_0 = input.LA(1);

            if ( (LA23_0==193) ) {
                alt23=1;
            }
            switch (alt23) {
                case 1 :
                    // BON.g:395:20: part
                    {
                    pushFollow(FOLLOW_part_in_cluster_chart3891);
                    part50=part();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_part.add(part50.getTree());

                    }
                    break;

            }

            // BON.g:396:19: ( class_entries )?
            int alt24=2;
            int LA24_0 = input.LA(1);

            if ( (LA24_0==188) ) {
                alt24=1;
            }
            switch (alt24) {
                case 1 :
                    // BON.g:396:20: class_entries
                    {
                    pushFollow(FOLLOW_class_entries_in_cluster_chart3915);
                    class_entries51=class_entries();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_class_entries.add(class_entries51.getTree());

                    }
                    break;

            }

            // BON.g:397:19: ( cluster_entries )?
            int alt25=2;
            int LA25_0 = input.LA(1);

            if ( (LA25_0==189) ) {
                alt25=1;
            }
            switch (alt25) {
                case 1 :
                    // BON.g:397:20: cluster_entries
                    {
                    pushFollow(FOLLOW_cluster_entries_in_cluster_chart3939);
                    cluster_entries52=cluster_entries();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_cluster_entries.add(cluster_entries52.getTree());

                    }
                    break;

            }

            string_literal53=(Token)input.LT(1);
            match(input,187,FOLLOW_187_in_cluster_chart3962); if (failed) return retval;
            if ( backtracking==0 ) stream_187.add(string_literal53);

            if ( backtracking==0 ) {
               getContext().leaveClusterChart(); 
            }

            // AST REWRITE
            // elements: explanation, cluster_name, indexing, cluster_entries, part, class_entries
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 400:17: -> ^( CLUSTER_CHART[$c] cluster_name ( indexing )? ( explanation )? ( part )? ( class_entries )? ( cluster_entries )? )
            {
                // BON.g:401:17: ^( CLUSTER_CHART[$c] cluster_name ( indexing )? ( explanation )? ( part )? ( class_entries )? ( cluster_entries )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLUSTER_CHART, c), root_1);

                adaptor.addChild(root_1, stream_cluster_name.next());
                // BON.g:403:19: ( indexing )?
                if ( stream_indexing.hasNext() ) {
                    adaptor.addChild(root_1, stream_indexing.next());

                }
                stream_indexing.reset();
                // BON.g:404:19: ( explanation )?
                if ( stream_explanation.hasNext() ) {
                    adaptor.addChild(root_1, stream_explanation.next());

                }
                stream_explanation.reset();
                // BON.g:405:19: ( part )?
                if ( stream_part.hasNext() ) {
                    adaptor.addChild(root_1, stream_part.next());

                }
                stream_part.reset();
                // BON.g:406:19: ( class_entries )?
                if ( stream_class_entries.hasNext() ) {
                    adaptor.addChild(root_1, stream_class_entries.next());

                }
                stream_class_entries.reset();
                // BON.g:407:19: ( cluster_entries )?
                if ( stream_cluster_entries.hasNext() ) {
                    adaptor.addChild(root_1, stream_cluster_entries.next());

                }
                stream_cluster_entries.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end cluster_chart

    public static class class_entries_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start class_entries
    // BON.g:411:1: class_entries : ( class_entry )+ -> ^( CLASS_ENTRIES ( class_entry )+ ) ;
    public final class_entries_return class_entries() throws RecognitionException {
        class_entries_return retval = new class_entries_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        class_entry_return class_entry54 = null;


        RewriteRuleSubtreeStream stream_class_entry=new RewriteRuleSubtreeStream(adaptor,"rule class_entry");
        try {
            // BON.g:411:16: ( ( class_entry )+ -> ^( CLASS_ENTRIES ( class_entry )+ ) )
            // BON.g:411:19: ( class_entry )+
            {
            // BON.g:411:19: ( class_entry )+
            int cnt26=0;
            loop26:
            do {
                int alt26=2;
                int LA26_0 = input.LA(1);

                if ( (LA26_0==188) ) {
                    alt26=1;
                }


                switch (alt26) {
            	case 1 :
            	    // BON.g:411:20: class_entry
            	    {
            	    pushFollow(FOLLOW_class_entry_in_class_entries4223);
            	    class_entry54=class_entry();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_class_entry.add(class_entry54.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt26 >= 1 ) break loop26;
            	    if (backtracking>0) {failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(26, input);
                        throw eee;
                }
                cnt26++;
            } while (true);


            // AST REWRITE
            // elements: class_entry
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 412:17: -> ^( CLASS_ENTRIES ( class_entry )+ )
            {
                // BON.g:413:17: ^( CLASS_ENTRIES ( class_entry )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLASS_ENTRIES, "CLASS_ENTRIES"), root_1);

                if ( !(stream_class_entry.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_class_entry.hasNext() ) {
                    adaptor.addChild(root_1, stream_class_entry.next());

                }
                stream_class_entry.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end class_entries

    public static class class_entry_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start class_entry
    // BON.g:418:1: class_entry : c= 'class' class_name description -> ^( CLASS_ENTRY[$c] class_name description ) ;
    public final class_entry_return class_entry() throws RecognitionException {
        class_entry_return retval = new class_entry_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token c=null;
        class_name_return class_name55 = null;

        description_return description56 = null;


        CommonTree c_tree=null;
        RewriteRuleTokenStream stream_188=new RewriteRuleTokenStream(adaptor,"token 188");
        RewriteRuleSubtreeStream stream_description=new RewriteRuleSubtreeStream(adaptor,"rule description");
        RewriteRuleSubtreeStream stream_class_name=new RewriteRuleSubtreeStream(adaptor,"rule class_name");
        try {
            // BON.g:418:14: (c= 'class' class_name description -> ^( CLASS_ENTRY[$c] class_name description ) )
            // BON.g:418:17: c= 'class' class_name description
            {
            c=(Token)input.LT(1);
            match(input,188,FOLLOW_188_in_class_entry4350); if (failed) return retval;
            if ( backtracking==0 ) stream_188.add(c);

            pushFollow(FOLLOW_class_name_in_class_entry4352);
            class_name55=class_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_class_name.add(class_name55.getTree());
            pushFollow(FOLLOW_description_in_class_entry4354);
            description56=description();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_description.add(description56.getTree());
            if ( backtracking==0 ) {
               getTI().informal().addClassEntry(input.toString(class_name55.start,class_name55.stop)); 
            }

            // AST REWRITE
            // elements: class_name, description
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 420:15: -> ^( CLASS_ENTRY[$c] class_name description )
            {
                // BON.g:421:15: ^( CLASS_ENTRY[$c] class_name description )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLASS_ENTRY, c), root_1);

                adaptor.addChild(root_1, stream_class_name.next());
                adaptor.addChild(root_1, stream_description.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end class_entry

    public static class cluster_name_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start cluster_name
    // BON.g:426:1: cluster_name : i= IDENTIFIER -> ^( CLUSTER_NAME[$i] IDENTIFIER ) ;
    public final cluster_name_return cluster_name() throws RecognitionException {
        cluster_name_return retval = new cluster_name_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token i=null;

        CommonTree i_tree=null;
        RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");

        try {
            // BON.g:426:15: (i= IDENTIFIER -> ^( CLUSTER_NAME[$i] IDENTIFIER ) )
            // BON.g:426:18: i= IDENTIFIER
            {
            i=(Token)input.LT(1);
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_cluster_name4483); if (failed) return retval;
            if ( backtracking==0 ) stream_IDENTIFIER.add(i);


            // AST REWRITE
            // elements: IDENTIFIER
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 427:16: -> ^( CLUSTER_NAME[$i] IDENTIFIER )
            {
                // BON.g:428:16: ^( CLUSTER_NAME[$i] IDENTIFIER )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLUSTER_NAME, i), root_1);

                adaptor.addChild(root_1, stream_IDENTIFIER.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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

    public static class class_chart_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start class_chart
    // BON.g:433:1: class_chart : c= 'class_chart' class_name ( indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? 'end' -> ^( CLASS_CHART[$c] class_name ( indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? ) ;
    public final class_chart_return class_chart() throws RecognitionException {
        class_chart_return retval = new class_chart_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token c=null;
        Token string_literal65=null;
        class_name_return class_name57 = null;

        indexing_return indexing58 = null;

        explanation_return explanation59 = null;

        part_return part60 = null;

        inherits_return inherits61 = null;

        queries_return queries62 = null;

        commands_return commands63 = null;

        constraints_return constraints64 = null;


        CommonTree c_tree=null;
        CommonTree string_literal65_tree=null;
        RewriteRuleTokenStream stream_199=new RewriteRuleTokenStream(adaptor,"token 199");
        RewriteRuleTokenStream stream_187=new RewriteRuleTokenStream(adaptor,"token 187");
        RewriteRuleSubtreeStream stream_inherits=new RewriteRuleSubtreeStream(adaptor,"rule inherits");
        RewriteRuleSubtreeStream stream_indexing=new RewriteRuleSubtreeStream(adaptor,"rule indexing");
        RewriteRuleSubtreeStream stream_explanation=new RewriteRuleSubtreeStream(adaptor,"rule explanation");
        RewriteRuleSubtreeStream stream_commands=new RewriteRuleSubtreeStream(adaptor,"rule commands");
        RewriteRuleSubtreeStream stream_constraints=new RewriteRuleSubtreeStream(adaptor,"rule constraints");
        RewriteRuleSubtreeStream stream_queries=new RewriteRuleSubtreeStream(adaptor,"rule queries");
        RewriteRuleSubtreeStream stream_class_name=new RewriteRuleSubtreeStream(adaptor,"rule class_name");
        RewriteRuleSubtreeStream stream_part=new RewriteRuleSubtreeStream(adaptor,"rule part");
        try {
            // BON.g:435:14: (c= 'class_chart' class_name ( indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? 'end' -> ^( CLASS_CHART[$c] class_name ( indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? ) )
            // BON.g:435:17: c= 'class_chart' class_name ( indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? 'end'
            {
            c=(Token)input.LT(1);
            match(input,199,FOLLOW_199_in_class_chart4588); if (failed) return retval;
            if ( backtracking==0 ) stream_199.add(c);

            pushFollow(FOLLOW_class_name_in_class_chart4590);
            class_name57=class_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_class_name.add(class_name57.getTree());
            if ( backtracking==0 ) {
               getTI().informal().addClass(input.toString(class_name57.start,class_name57.stop), getSLoc(c));
                                getContext().enterClassChart(input.toString(class_name57.start,class_name57.stop)); 
            }
            // BON.g:438:17: ( indexing )?
            int alt27=2;
            int LA27_0 = input.LA(1);

            if ( (LA27_0==192) ) {
                alt27=1;
            }
            switch (alt27) {
                case 1 :
                    // BON.g:438:18: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_class_chart4628);
                    indexing58=indexing();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_indexing.add(indexing58.getTree());

                    }
                    break;

            }

            // BON.g:439:17: ( explanation )?
            int alt28=2;
            int LA28_0 = input.LA(1);

            if ( (LA28_0==191) ) {
                alt28=1;
            }
            switch (alt28) {
                case 1 :
                    // BON.g:439:18: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_class_chart4650);
                    explanation59=explanation();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_explanation.add(explanation59.getTree());

                    }
                    break;

            }

            // BON.g:440:17: ( part )?
            int alt29=2;
            int LA29_0 = input.LA(1);

            if ( (LA29_0==193) ) {
                alt29=1;
            }
            switch (alt29) {
                case 1 :
                    // BON.g:440:18: part
                    {
                    pushFollow(FOLLOW_part_in_class_chart4672);
                    part60=part();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_part.add(part60.getTree());

                    }
                    break;

            }

            // BON.g:441:17: ( inherits )?
            int alt30=2;
            int LA30_0 = input.LA(1);

            if ( (LA30_0==200) ) {
                alt30=1;
            }
            switch (alt30) {
                case 1 :
                    // BON.g:441:18: inherits
                    {
                    pushFollow(FOLLOW_inherits_in_class_chart4694);
                    inherits61=inherits();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_inherits.add(inherits61.getTree());

                    }
                    break;

            }

            // BON.g:442:17: ( queries )?
            int alt31=2;
            int LA31_0 = input.LA(1);

            if ( (LA31_0==201) ) {
                alt31=1;
            }
            switch (alt31) {
                case 1 :
                    // BON.g:442:18: queries
                    {
                    pushFollow(FOLLOW_queries_in_class_chart4715);
                    queries62=queries();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_queries.add(queries62.getTree());

                    }
                    break;

            }

            // BON.g:443:17: ( commands )?
            int alt32=2;
            int LA32_0 = input.LA(1);

            if ( (LA32_0==202) ) {
                alt32=1;
            }
            switch (alt32) {
                case 1 :
                    // BON.g:443:18: commands
                    {
                    pushFollow(FOLLOW_commands_in_class_chart4737);
                    commands63=commands();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_commands.add(commands63.getTree());

                    }
                    break;

            }

            // BON.g:444:17: ( constraints )?
            int alt33=2;
            int LA33_0 = input.LA(1);

            if ( (LA33_0==203) ) {
                alt33=1;
            }
            switch (alt33) {
                case 1 :
                    // BON.g:444:18: constraints
                    {
                    pushFollow(FOLLOW_constraints_in_class_chart4759);
                    constraints64=constraints();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_constraints.add(constraints64.getTree());

                    }
                    break;

            }

            string_literal65=(Token)input.LT(1);
            match(input,187,FOLLOW_187_in_class_chart4780); if (failed) return retval;
            if ( backtracking==0 ) stream_187.add(string_literal65);

            if ( backtracking==0 ) {
               getContext().leaveClassChart(); 
            }

            // AST REWRITE
            // elements: constraints, inherits, class_name, commands, indexing, part, explanation, queries
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 447:15: -> ^( CLASS_CHART[$c] class_name ( indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? )
            {
                // BON.g:448:15: ^( CLASS_CHART[$c] class_name ( indexing )? ( explanation )? ( part )? ( inherits )? ( queries )? ( commands )? ( constraints )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLASS_CHART, c), root_1);

                adaptor.addChild(root_1, stream_class_name.next());
                // BON.g:450:17: ( indexing )?
                if ( stream_indexing.hasNext() ) {
                    adaptor.addChild(root_1, stream_indexing.next());

                }
                stream_indexing.reset();
                // BON.g:451:17: ( explanation )?
                if ( stream_explanation.hasNext() ) {
                    adaptor.addChild(root_1, stream_explanation.next());

                }
                stream_explanation.reset();
                // BON.g:452:17: ( part )?
                if ( stream_part.hasNext() ) {
                    adaptor.addChild(root_1, stream_part.next());

                }
                stream_part.reset();
                // BON.g:453:17: ( inherits )?
                if ( stream_inherits.hasNext() ) {
                    adaptor.addChild(root_1, stream_inherits.next());

                }
                stream_inherits.reset();
                // BON.g:454:17: ( queries )?
                if ( stream_queries.hasNext() ) {
                    adaptor.addChild(root_1, stream_queries.next());

                }
                stream_queries.reset();
                // BON.g:455:17: ( commands )?
                if ( stream_commands.hasNext() ) {
                    adaptor.addChild(root_1, stream_commands.next());

                }
                stream_commands.reset();
                // BON.g:456:17: ( constraints )?
                if ( stream_constraints.hasNext() ) {
                    adaptor.addChild(root_1, stream_constraints.next());

                }
                stream_constraints.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end class_chart

    public static class inherits_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start inherits
    // BON.g:460:1: inherits : (i= 'inherit' class_name_list -> ^( INHERITS[$i] class_name_list ) | i= 'inherit' -> ^( INHERITS PARSE_ERROR ) );
    public final inherits_return inherits() throws RecognitionException {
        inherits_return retval = new inherits_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token i=null;
        class_name_list_return class_name_list66 = null;


        CommonTree i_tree=null;
        RewriteRuleTokenStream stream_200=new RewriteRuleTokenStream(adaptor,"token 200");
        RewriteRuleSubtreeStream stream_class_name_list=new RewriteRuleSubtreeStream(adaptor,"rule class_name_list");
        try {
            // BON.g:460:11: (i= 'inherit' class_name_list -> ^( INHERITS[$i] class_name_list ) | i= 'inherit' -> ^( INHERITS PARSE_ERROR ) )
            int alt34=2;
            int LA34_0 = input.LA(1);

            if ( (LA34_0==200) ) {
                int LA34_1 = input.LA(2);

                if ( (LA34_1==IDENTIFIER) ) {
                    alt34=1;
                }
                else if ( (LA34_1==187||(LA34_1>=201 && LA34_1<=203)) ) {
                    alt34=2;
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("460:1: inherits : (i= 'inherit' class_name_list -> ^( INHERITS[$i] class_name_list ) | i= 'inherit' -> ^( INHERITS PARSE_ERROR ) );", 34, 1, input);

                    throw nvae;
                }
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("460:1: inherits : (i= 'inherit' class_name_list -> ^( INHERITS[$i] class_name_list ) | i= 'inherit' -> ^( INHERITS PARSE_ERROR ) );", 34, 0, input);

                throw nvae;
            }
            switch (alt34) {
                case 1 :
                    // BON.g:460:14: i= 'inherit' class_name_list
                    {
                    i=(Token)input.LT(1);
                    match(input,200,FOLLOW_200_in_inherits5060); if (failed) return retval;
                    if ( backtracking==0 ) stream_200.add(i);

                    if ( backtracking==0 ) {
                       getContext().enterInheritsClause(); 
                    }
                    pushFollow(FOLLOW_class_name_list_in_inherits5078);
                    class_name_list66=class_name_list();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_class_name_list.add(class_name_list66.getTree());
                    if ( backtracking==0 ) {
                       getContext().leaveInheritsClause(); 
                    }

                    // AST REWRITE
                    // elements: class_name_list
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 463:11: -> ^( INHERITS[$i] class_name_list )
                    {
                        // BON.g:463:14: ^( INHERITS[$i] class_name_list )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INHERITS, i), root_1);

                        adaptor.addChild(root_1, stream_class_name_list.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:464:14: i= 'inherit'
                    {
                    i=(Token)input.LT(1);
                    match(input,200,FOLLOW_200_in_inherits5131); if (failed) return retval;
                    if ( backtracking==0 ) stream_200.add(i);

                    if ( backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(i), "class name(s)", "in inherits clause", true)); 
                    }

                    // AST REWRITE
                    // elements: 
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 465:11: -> ^( INHERITS PARSE_ERROR )
                    {
                        // BON.g:465:14: ^( INHERITS PARSE_ERROR )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INHERITS, "INHERITS"), root_1);

                        adaptor.addChild(root_1, adaptor.create(PARSE_ERROR, "PARSE_ERROR"));

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end inherits

    public static class queries_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start queries
    // BON.g:469:1: queries : q= 'query' query_list -> ^( QUERIES[$q] query_list ) ;
    public final queries_return queries() throws RecognitionException {
        queries_return retval = new queries_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token q=null;
        query_list_return query_list67 = null;


        CommonTree q_tree=null;
        RewriteRuleTokenStream stream_201=new RewriteRuleTokenStream(adaptor,"token 201");
        RewriteRuleSubtreeStream stream_query_list=new RewriteRuleSubtreeStream(adaptor,"rule query_list");
        try {
            // BON.g:469:10: (q= 'query' query_list -> ^( QUERIES[$q] query_list ) )
            // BON.g:469:12: q= 'query' query_list
            {
            q=(Token)input.LT(1);
            match(input,201,FOLLOW_201_in_queries5188); if (failed) return retval;
            if ( backtracking==0 ) stream_201.add(q);

            pushFollow(FOLLOW_query_list_in_queries5190);
            query_list67=query_list();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_query_list.add(query_list67.getTree());

            // AST REWRITE
            // elements: query_list
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 469:34: -> ^( QUERIES[$q] query_list )
            {
                // BON.g:469:37: ^( QUERIES[$q] query_list )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(QUERIES, q), root_1);

                adaptor.addChild(root_1, stream_query_list.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end queries

    public static class commands_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start commands
    // BON.g:472:1: commands : c= 'command' command_list -> ^( COMMANDS[$c] command_list ) ;
    public final commands_return commands() throws RecognitionException {
        commands_return retval = new commands_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token c=null;
        command_list_return command_list68 = null;


        CommonTree c_tree=null;
        RewriteRuleTokenStream stream_202=new RewriteRuleTokenStream(adaptor,"token 202");
        RewriteRuleSubtreeStream stream_command_list=new RewriteRuleSubtreeStream(adaptor,"rule command_list");
        try {
            // BON.g:472:11: (c= 'command' command_list -> ^( COMMANDS[$c] command_list ) )
            // BON.g:472:13: c= 'command' command_list
            {
            c=(Token)input.LT(1);
            match(input,202,FOLLOW_202_in_commands5230); if (failed) return retval;
            if ( backtracking==0 ) stream_202.add(c);

            pushFollow(FOLLOW_command_list_in_commands5232);
            command_list68=command_list();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_command_list.add(command_list68.getTree());

            // AST REWRITE
            // elements: command_list
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 472:39: -> ^( COMMANDS[$c] command_list )
            {
                // BON.g:472:42: ^( COMMANDS[$c] command_list )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(COMMANDS, c), root_1);

                adaptor.addChild(root_1, stream_command_list.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end commands

    public static class constraints_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start constraints
    // BON.g:475:1: constraints : c= 'constraint' constraint_list -> ^( CONSTRAINTS[$c] constraint_list ) ;
    public final constraints_return constraints() throws RecognitionException {
        constraints_return retval = new constraints_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token c=null;
        constraint_list_return constraint_list69 = null;


        CommonTree c_tree=null;
        RewriteRuleTokenStream stream_203=new RewriteRuleTokenStream(adaptor,"token 203");
        RewriteRuleSubtreeStream stream_constraint_list=new RewriteRuleSubtreeStream(adaptor,"rule constraint_list");
        try {
            // BON.g:475:14: (c= 'constraint' constraint_list -> ^( CONSTRAINTS[$c] constraint_list ) )
            // BON.g:475:16: c= 'constraint' constraint_list
            {
            c=(Token)input.LT(1);
            match(input,203,FOLLOW_203_in_constraints5264); if (failed) return retval;
            if ( backtracking==0 ) stream_203.add(c);

            pushFollow(FOLLOW_constraint_list_in_constraints5266);
            constraint_list69=constraint_list();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_constraint_list.add(constraint_list69.getTree());

            // AST REWRITE
            // elements: constraint_list
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 475:48: -> ^( CONSTRAINTS[$c] constraint_list )
            {
                // BON.g:475:51: ^( CONSTRAINTS[$c] constraint_list )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CONSTRAINTS, c), root_1);

                adaptor.addChild(root_1, stream_constraint_list.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end constraints

    public static class query_list_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start query_list
    // BON.g:479:1: query_list : m1= manifest_textblock ( ( ',' manifest_textblock ) | m= manifest_textblock )* ( ',' )? -> ^( QUERY_LIST[$m1.start] ( manifest_textblock )+ ) ;
    public final query_list_return query_list() throws RecognitionException {
        query_list_return retval = new query_list_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal70=null;
        Token char_literal72=null;
        manifest_textblock_return m1 = null;

        manifest_textblock_return m = null;

        manifest_textblock_return manifest_textblock71 = null;


        CommonTree char_literal70_tree=null;
        CommonTree char_literal72_tree=null;
        RewriteRuleTokenStream stream_197=new RewriteRuleTokenStream(adaptor,"token 197");
        RewriteRuleSubtreeStream stream_manifest_textblock=new RewriteRuleSubtreeStream(adaptor,"rule manifest_textblock");
        try {
            // BON.g:479:13: (m1= manifest_textblock ( ( ',' manifest_textblock ) | m= manifest_textblock )* ( ',' )? -> ^( QUERY_LIST[$m1.start] ( manifest_textblock )+ ) )
            // BON.g:479:16: m1= manifest_textblock ( ( ',' manifest_textblock ) | m= manifest_textblock )* ( ',' )?
            {
            pushFollow(FOLLOW_manifest_textblock_in_query_list5303);
            m1=manifest_textblock();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_manifest_textblock.add(m1.getTree());
            // BON.g:480:16: ( ( ',' manifest_textblock ) | m= manifest_textblock )*
            loop35:
            do {
                int alt35=3;
                int LA35_0 = input.LA(1);

                if ( (LA35_0==197) ) {
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
            	    // BON.g:480:19: ( ',' manifest_textblock )
            	    {
            	    // BON.g:480:19: ( ',' manifest_textblock )
            	    // BON.g:480:20: ',' manifest_textblock
            	    {
            	    char_literal70=(Token)input.LT(1);
            	    match(input,197,FOLLOW_197_in_query_list5325); if (failed) return retval;
            	    if ( backtracking==0 ) stream_197.add(char_literal70);

            	    pushFollow(FOLLOW_manifest_textblock_in_query_list5327);
            	    manifest_textblock71=manifest_textblock();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_manifest_textblock.add(manifest_textblock71.getTree());

            	    }


            	    }
            	    break;
            	case 2 :
            	    // BON.g:481:19: m= manifest_textblock
            	    {
            	    pushFollow(FOLLOW_manifest_textblock_in_query_list5351);
            	    m=manifest_textblock();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_manifest_textblock.add(m.getTree());
            	    if ( backtracking==0 ) {
            	       addParseProblem(new MissingElementParseError(getSourceLocation(((Token)m.start)), "comma", "before additional query item", false)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop35;
                }
            } while (true);

            // BON.g:483:16: ( ',' )?
            int alt36=2;
            int LA36_0 = input.LA(1);

            if ( (LA36_0==197) ) {
                alt36=1;
            }
            switch (alt36) {
                case 1 :
                    // BON.g:483:16: ','
                    {
                    char_literal72=(Token)input.LT(1);
                    match(input,197,FOLLOW_197_in_query_list5390); if (failed) return retval;
                    if ( backtracking==0 ) stream_197.add(char_literal72);


                    }
                    break;

            }


            // AST REWRITE
            // elements: manifest_textblock
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 484:14: -> ^( QUERY_LIST[$m1.start] ( manifest_textblock )+ )
            {
                // BON.g:485:14: ^( QUERY_LIST[$m1.start] ( manifest_textblock )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(QUERY_LIST, ((Token)m1.start)), root_1);

                if ( !(stream_manifest_textblock.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_manifest_textblock.hasNext() ) {
                    adaptor.addChild(root_1, stream_manifest_textblock.next());

                }
                stream_manifest_textblock.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end query_list

    public static class command_list_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start command_list
    // BON.g:490:1: command_list : m1= manifest_textblock ( ( ',' manifest_textblock ) | m= manifest_textblock )* ( ',' )? -> ^( COMMAND_LIST[$m1.start] ( manifest_textblock )+ ) ;
    public final command_list_return command_list() throws RecognitionException {
        command_list_return retval = new command_list_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal73=null;
        Token char_literal75=null;
        manifest_textblock_return m1 = null;

        manifest_textblock_return m = null;

        manifest_textblock_return manifest_textblock74 = null;


        CommonTree char_literal73_tree=null;
        CommonTree char_literal75_tree=null;
        RewriteRuleTokenStream stream_197=new RewriteRuleTokenStream(adaptor,"token 197");
        RewriteRuleSubtreeStream stream_manifest_textblock=new RewriteRuleSubtreeStream(adaptor,"rule manifest_textblock");
        try {
            // BON.g:490:15: (m1= manifest_textblock ( ( ',' manifest_textblock ) | m= manifest_textblock )* ( ',' )? -> ^( COMMAND_LIST[$m1.start] ( manifest_textblock )+ ) )
            // BON.g:490:18: m1= manifest_textblock ( ( ',' manifest_textblock ) | m= manifest_textblock )* ( ',' )?
            {
            pushFollow(FOLLOW_manifest_textblock_in_command_list5509);
            m1=manifest_textblock();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_manifest_textblock.add(m1.getTree());
            // BON.g:491:18: ( ( ',' manifest_textblock ) | m= manifest_textblock )*
            loop37:
            do {
                int alt37=3;
                int LA37_0 = input.LA(1);

                if ( (LA37_0==197) ) {
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
            	    // BON.g:491:21: ( ',' manifest_textblock )
            	    {
            	    // BON.g:491:21: ( ',' manifest_textblock )
            	    // BON.g:491:22: ',' manifest_textblock
            	    {
            	    char_literal73=(Token)input.LT(1);
            	    match(input,197,FOLLOW_197_in_command_list5533); if (failed) return retval;
            	    if ( backtracking==0 ) stream_197.add(char_literal73);

            	    pushFollow(FOLLOW_manifest_textblock_in_command_list5535);
            	    manifest_textblock74=manifest_textblock();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_manifest_textblock.add(manifest_textblock74.getTree());

            	    }


            	    }
            	    break;
            	case 2 :
            	    // BON.g:492:21: m= manifest_textblock
            	    {
            	    pushFollow(FOLLOW_manifest_textblock_in_command_list5560);
            	    m=manifest_textblock();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_manifest_textblock.add(m.getTree());
            	    if ( backtracking==0 ) {
            	       addParseProblem(new MissingElementParseError(getSourceLocation(((Token)m.start)), "comma", "before additional command item", false)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop37;
                }
            } while (true);

            // BON.g:494:18: ( ',' )?
            int alt38=2;
            int LA38_0 = input.LA(1);

            if ( (LA38_0==197) ) {
                alt38=1;
            }
            switch (alt38) {
                case 1 :
                    // BON.g:494:18: ','
                    {
                    char_literal75=(Token)input.LT(1);
                    match(input,197,FOLLOW_197_in_command_list5602); if (failed) return retval;
                    if ( backtracking==0 ) stream_197.add(char_literal75);


                    }
                    break;

            }


            // AST REWRITE
            // elements: manifest_textblock
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 495:16: -> ^( COMMAND_LIST[$m1.start] ( manifest_textblock )+ )
            {
                // BON.g:496:16: ^( COMMAND_LIST[$m1.start] ( manifest_textblock )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(COMMAND_LIST, ((Token)m1.start)), root_1);

                if ( !(stream_manifest_textblock.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_manifest_textblock.hasNext() ) {
                    adaptor.addChild(root_1, stream_manifest_textblock.next());

                }
                stream_manifest_textblock.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end command_list

    public static class constraint_list_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start constraint_list
    // BON.g:501:1: constraint_list : m1= manifest_textblock ( ( ',' manifest_textblock ) | m= manifest_textblock )* ( ',' )? -> ^( CONSTRAINT_LIST[$m1.start] ( manifest_textblock )+ ) ;
    public final constraint_list_return constraint_list() throws RecognitionException {
        constraint_list_return retval = new constraint_list_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal76=null;
        Token char_literal78=null;
        manifest_textblock_return m1 = null;

        manifest_textblock_return m = null;

        manifest_textblock_return manifest_textblock77 = null;


        CommonTree char_literal76_tree=null;
        CommonTree char_literal78_tree=null;
        RewriteRuleTokenStream stream_197=new RewriteRuleTokenStream(adaptor,"token 197");
        RewriteRuleSubtreeStream stream_manifest_textblock=new RewriteRuleSubtreeStream(adaptor,"rule manifest_textblock");
        try {
            // BON.g:501:18: (m1= manifest_textblock ( ( ',' manifest_textblock ) | m= manifest_textblock )* ( ',' )? -> ^( CONSTRAINT_LIST[$m1.start] ( manifest_textblock )+ ) )
            // BON.g:501:21: m1= manifest_textblock ( ( ',' manifest_textblock ) | m= manifest_textblock )* ( ',' )?
            {
            pushFollow(FOLLOW_manifest_textblock_in_constraint_list5719);
            m1=manifest_textblock();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_manifest_textblock.add(m1.getTree());
            // BON.g:502:21: ( ( ',' manifest_textblock ) | m= manifest_textblock )*
            loop39:
            do {
                int alt39=3;
                int LA39_0 = input.LA(1);

                if ( (LA39_0==197) ) {
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
            	    // BON.g:502:24: ( ',' manifest_textblock )
            	    {
            	    // BON.g:502:24: ( ',' manifest_textblock )
            	    // BON.g:502:25: ',' manifest_textblock
            	    {
            	    char_literal76=(Token)input.LT(1);
            	    match(input,197,FOLLOW_197_in_constraint_list5746); if (failed) return retval;
            	    if ( backtracking==0 ) stream_197.add(char_literal76);

            	    pushFollow(FOLLOW_manifest_textblock_in_constraint_list5748);
            	    manifest_textblock77=manifest_textblock();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_manifest_textblock.add(manifest_textblock77.getTree());

            	    }


            	    }
            	    break;
            	case 2 :
            	    // BON.g:503:24: m= manifest_textblock
            	    {
            	    pushFollow(FOLLOW_manifest_textblock_in_constraint_list5776);
            	    m=manifest_textblock();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_manifest_textblock.add(m.getTree());
            	    if ( backtracking==0 ) {
            	       addParseProblem(new MissingElementParseError(getSourceLocation(((Token)m.start)), "comma", "before additional constraint item", false)); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop39;
                }
            } while (true);

            // BON.g:505:21: ( ',' )?
            int alt40=2;
            int LA40_0 = input.LA(1);

            if ( (LA40_0==197) ) {
                alt40=1;
            }
            switch (alt40) {
                case 1 :
                    // BON.g:505:21: ','
                    {
                    char_literal78=(Token)input.LT(1);
                    match(input,197,FOLLOW_197_in_constraint_list5823); if (failed) return retval;
                    if ( backtracking==0 ) stream_197.add(char_literal78);


                    }
                    break;

            }


            // AST REWRITE
            // elements: manifest_textblock
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 506:19: -> ^( CONSTRAINT_LIST[$m1.start] ( manifest_textblock )+ )
            {
                // BON.g:507:19: ^( CONSTRAINT_LIST[$m1.start] ( manifest_textblock )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CONSTRAINT_LIST, ((Token)m1.start)), root_1);

                if ( !(stream_manifest_textblock.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_manifest_textblock.hasNext() ) {
                    adaptor.addChild(root_1, stream_manifest_textblock.next());

                }
                stream_manifest_textblock.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end constraint_list

    public static class class_name_list_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start class_name_list
    // BON.g:512:1: class_name_list : c1= class_name ( ( ',' c= class_name ) | (c= class_name ) )* -> ^( CLASS_NAME_LIST[$c1.start] ( class_name )+ ) ;
    public final class_name_list_return class_name_list() throws RecognitionException {
        class_name_list_return retval = new class_name_list_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal79=null;
        class_name_return c1 = null;

        class_name_return c = null;


        CommonTree char_literal79_tree=null;
        RewriteRuleTokenStream stream_197=new RewriteRuleTokenStream(adaptor,"token 197");
        RewriteRuleSubtreeStream stream_class_name=new RewriteRuleSubtreeStream(adaptor,"rule class_name");
        try {
            // BON.g:512:18: (c1= class_name ( ( ',' c= class_name ) | (c= class_name ) )* -> ^( CLASS_NAME_LIST[$c1.start] ( class_name )+ ) )
            // BON.g:512:21: c1= class_name ( ( ',' c= class_name ) | (c= class_name ) )*
            {
            pushFollow(FOLLOW_class_name_in_class_name_list5942);
            c1=class_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_class_name.add(c1.getTree());
            if ( backtracking==0 ) {
               getTI().classNameListEntry(input.toString(c1.start,c1.stop), getSLoc(((Token)c1.start))); 
            }
            // BON.g:513:11: ( ( ',' c= class_name ) | (c= class_name ) )*
            loop41:
            do {
                int alt41=3;
                int LA41_0 = input.LA(1);

                if ( (LA41_0==197) ) {
                    alt41=1;
                }
                else if ( (LA41_0==IDENTIFIER) ) {
                    alt41=2;
                }


                switch (alt41) {
            	case 1 :
            	    // BON.g:513:14: ( ',' c= class_name )
            	    {
            	    // BON.g:513:14: ( ',' c= class_name )
            	    // BON.g:513:16: ',' c= class_name
            	    {
            	    char_literal79=(Token)input.LT(1);
            	    match(input,197,FOLLOW_197_in_class_name_list5961); if (failed) return retval;
            	    if ( backtracking==0 ) stream_197.add(char_literal79);

            	    pushFollow(FOLLOW_class_name_in_class_name_list5965);
            	    c=class_name();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_class_name.add(c.getTree());
            	    if ( backtracking==0 ) {
            	       getTI().classNameListEntry(input.toString(c.start,c.stop), getSLoc(((Token)c.start))); 
            	    }

            	    }


            	    }
            	    break;
            	case 2 :
            	    // BON.g:514:14: (c= class_name )
            	    {
            	    // BON.g:514:14: (c= class_name )
            	    // BON.g:514:16: c= class_name
            	    {
            	    pushFollow(FOLLOW_class_name_in_class_name_list5988);
            	    c=class_name();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_class_name.add(c.getTree());
            	    if ( backtracking==0 ) {
            	       getTI().classNameListEntry(input.toString(c.start,c.stop), getSLoc(((Token)c.start))); 
            	      										       addParseProblem(new MissingElementParseError(getSourceLocation(((Token)c.start)), "comma", "before additional class name", false)); 
            	    }

            	    }


            	    }
            	    break;

            	default :
            	    break loop41;
                }
            } while (true);


            // AST REWRITE
            // elements: class_name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 519:19: -> ^( CLASS_NAME_LIST[$c1.start] ( class_name )+ )
            {
                // BON.g:520:19: ^( CLASS_NAME_LIST[$c1.start] ( class_name )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLASS_NAME_LIST, ((Token)c1.start)), root_1);

                if ( !(stream_class_name.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_class_name.hasNext() ) {
                    adaptor.addChild(root_1, stream_class_name.next());

                }
                stream_class_name.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end class_name_list

    public static class class_name_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start class_name
    // BON.g:525:1: class_name : i= IDENTIFIER -> ^( CLASS_NAME[$i] IDENTIFIER ) ;
    public final class_name_return class_name() throws RecognitionException {
        class_name_return retval = new class_name_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token i=null;

        CommonTree i_tree=null;
        RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");

        try {
            // BON.g:525:13: (i= IDENTIFIER -> ^( CLASS_NAME[$i] IDENTIFIER ) )
            // BON.g:525:16: i= IDENTIFIER
            {
            i=(Token)input.LT(1);
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_class_name6203); if (failed) return retval;
            if ( backtracking==0 ) stream_IDENTIFIER.add(i);


            // AST REWRITE
            // elements: IDENTIFIER
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 526:14: -> ^( CLASS_NAME[$i] IDENTIFIER )
            {
                // BON.g:527:14: ^( CLASS_NAME[$i] IDENTIFIER )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLASS_NAME, i), root_1);

                adaptor.addChild(root_1, stream_IDENTIFIER.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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

    public static class event_chart_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start event_chart
    // BON.g:532:1: event_chart : e= 'event_chart' system_name ( 'incoming' | 'outgoing' )? ( indexing )? ( explanation )? ( part )? ( event_entries )? 'end' -> ^( EVENT_CHART[$e] system_name ( 'incoming' )? ( 'outgoing' )? ( indexing )? ( explanation )? ( part )? ( event_entries )? ) ;
    public final event_chart_return event_chart() throws RecognitionException {
        event_chart_return retval = new event_chart_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token e=null;
        Token string_literal81=null;
        Token string_literal82=null;
        Token string_literal87=null;
        system_name_return system_name80 = null;

        indexing_return indexing83 = null;

        explanation_return explanation84 = null;

        part_return part85 = null;

        event_entries_return event_entries86 = null;


        CommonTree e_tree=null;
        CommonTree string_literal81_tree=null;
        CommonTree string_literal82_tree=null;
        CommonTree string_literal87_tree=null;
        RewriteRuleTokenStream stream_204=new RewriteRuleTokenStream(adaptor,"token 204");
        RewriteRuleTokenStream stream_205=new RewriteRuleTokenStream(adaptor,"token 205");
        RewriteRuleTokenStream stream_187=new RewriteRuleTokenStream(adaptor,"token 187");
        RewriteRuleTokenStream stream_206=new RewriteRuleTokenStream(adaptor,"token 206");
        RewriteRuleSubtreeStream stream_system_name=new RewriteRuleSubtreeStream(adaptor,"rule system_name");
        RewriteRuleSubtreeStream stream_indexing=new RewriteRuleSubtreeStream(adaptor,"rule indexing");
        RewriteRuleSubtreeStream stream_explanation=new RewriteRuleSubtreeStream(adaptor,"rule explanation");
        RewriteRuleSubtreeStream stream_event_entries=new RewriteRuleSubtreeStream(adaptor,"rule event_entries");
        RewriteRuleSubtreeStream stream_part=new RewriteRuleSubtreeStream(adaptor,"rule part");
        try {
            // BON.g:534:14: (e= 'event_chart' system_name ( 'incoming' | 'outgoing' )? ( indexing )? ( explanation )? ( part )? ( event_entries )? 'end' -> ^( EVENT_CHART[$e] system_name ( 'incoming' )? ( 'outgoing' )? ( indexing )? ( explanation )? ( part )? ( event_entries )? ) )
            // BON.g:534:17: e= 'event_chart' system_name ( 'incoming' | 'outgoing' )? ( indexing )? ( explanation )? ( part )? ( event_entries )? 'end'
            {
            e=(Token)input.LT(1);
            match(input,204,FOLLOW_204_in_event_chart6298); if (failed) return retval;
            if ( backtracking==0 ) stream_204.add(e);

            pushFollow(FOLLOW_system_name_in_event_chart6300);
            system_name80=system_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_system_name.add(system_name80.getTree());
            // BON.g:535:17: ( 'incoming' | 'outgoing' )?
            int alt42=3;
            int LA42_0 = input.LA(1);

            if ( (LA42_0==205) ) {
                alt42=1;
            }
            else if ( (LA42_0==206) ) {
                alt42=2;
            }
            switch (alt42) {
                case 1 :
                    // BON.g:535:18: 'incoming'
                    {
                    string_literal81=(Token)input.LT(1);
                    match(input,205,FOLLOW_205_in_event_chart6320); if (failed) return retval;
                    if ( backtracking==0 ) stream_205.add(string_literal81);


                    }
                    break;
                case 2 :
                    // BON.g:535:31: 'outgoing'
                    {
                    string_literal82=(Token)input.LT(1);
                    match(input,206,FOLLOW_206_in_event_chart6324); if (failed) return retval;
                    if ( backtracking==0 ) stream_206.add(string_literal82);


                    }
                    break;

            }

            // BON.g:536:17: ( indexing )?
            int alt43=2;
            int LA43_0 = input.LA(1);

            if ( (LA43_0==192) ) {
                alt43=1;
            }
            switch (alt43) {
                case 1 :
                    // BON.g:536:18: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_event_chart6345);
                    indexing83=indexing();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_indexing.add(indexing83.getTree());

                    }
                    break;

            }

            // BON.g:537:17: ( explanation )?
            int alt44=2;
            int LA44_0 = input.LA(1);

            if ( (LA44_0==191) ) {
                alt44=1;
            }
            switch (alt44) {
                case 1 :
                    // BON.g:537:18: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_event_chart6366);
                    explanation84=explanation();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_explanation.add(explanation84.getTree());

                    }
                    break;

            }

            // BON.g:538:17: ( part )?
            int alt45=2;
            int LA45_0 = input.LA(1);

            if ( (LA45_0==193) ) {
                alt45=1;
            }
            switch (alt45) {
                case 1 :
                    // BON.g:538:18: part
                    {
                    pushFollow(FOLLOW_part_in_event_chart6387);
                    part85=part();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_part.add(part85.getTree());

                    }
                    break;

            }

            // BON.g:539:17: ( event_entries )?
            int alt46=2;
            int LA46_0 = input.LA(1);

            if ( (LA46_0==207) ) {
                alt46=1;
            }
            switch (alt46) {
                case 1 :
                    // BON.g:539:18: event_entries
                    {
                    pushFollow(FOLLOW_event_entries_in_event_chart6408);
                    event_entries86=event_entries();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_event_entries.add(event_entries86.getTree());

                    }
                    break;

            }

            string_literal87=(Token)input.LT(1);
            match(input,187,FOLLOW_187_in_event_chart6428); if (failed) return retval;
            if ( backtracking==0 ) stream_187.add(string_literal87);


            // AST REWRITE
            // elements: indexing, part, explanation, event_entries, 206, 205, system_name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 541:15: -> ^( EVENT_CHART[$e] system_name ( 'incoming' )? ( 'outgoing' )? ( indexing )? ( explanation )? ( part )? ( event_entries )? )
            {
                // BON.g:542:15: ^( EVENT_CHART[$e] system_name ( 'incoming' )? ( 'outgoing' )? ( indexing )? ( explanation )? ( part )? ( event_entries )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(EVENT_CHART, e), root_1);

                adaptor.addChild(root_1, stream_system_name.next());
                // BON.g:545:17: ( 'incoming' )?
                if ( stream_205.hasNext() ) {
                    adaptor.addChild(root_1, stream_205.next());

                }
                stream_205.reset();
                // BON.g:545:31: ( 'outgoing' )?
                if ( stream_206.hasNext() ) {
                    adaptor.addChild(root_1, stream_206.next());

                }
                stream_206.reset();
                // BON.g:546:17: ( indexing )?
                if ( stream_indexing.hasNext() ) {
                    adaptor.addChild(root_1, stream_indexing.next());

                }
                stream_indexing.reset();
                // BON.g:547:17: ( explanation )?
                if ( stream_explanation.hasNext() ) {
                    adaptor.addChild(root_1, stream_explanation.next());

                }
                stream_explanation.reset();
                // BON.g:548:17: ( part )?
                if ( stream_part.hasNext() ) {
                    adaptor.addChild(root_1, stream_part.next());

                }
                stream_part.reset();
                // BON.g:549:17: ( event_entries )?
                if ( stream_event_entries.hasNext() ) {
                    adaptor.addChild(root_1, stream_event_entries.next());

                }
                stream_event_entries.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end event_chart

    public static class event_entries_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start event_entries
    // BON.g:553:1: event_entries : ( event_entry )+ -> ^( EVENT_ENTRIES ( event_entry )+ ) ;
    public final event_entries_return event_entries() throws RecognitionException {
        event_entries_return retval = new event_entries_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        event_entry_return event_entry88 = null;


        RewriteRuleSubtreeStream stream_event_entry=new RewriteRuleSubtreeStream(adaptor,"rule event_entry");
        try {
            // BON.g:553:16: ( ( event_entry )+ -> ^( EVENT_ENTRIES ( event_entry )+ ) )
            // BON.g:553:19: ( event_entry )+
            {
            // BON.g:553:19: ( event_entry )+
            int cnt47=0;
            loop47:
            do {
                int alt47=2;
                int LA47_0 = input.LA(1);

                if ( (LA47_0==207) ) {
                    alt47=1;
                }


                switch (alt47) {
            	case 1 :
            	    // BON.g:553:20: event_entry
            	    {
            	    pushFollow(FOLLOW_event_entry_in_event_entries6663);
            	    event_entry88=event_entry();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_event_entry.add(event_entry88.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt47 >= 1 ) break loop47;
            	    if (backtracking>0) {failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(47, input);
                        throw eee;
                }
                cnt47++;
            } while (true);


            // AST REWRITE
            // elements: event_entry
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 554:17: -> ^( EVENT_ENTRIES ( event_entry )+ )
            {
                // BON.g:555:17: ^( EVENT_ENTRIES ( event_entry )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(EVENT_ENTRIES, "EVENT_ENTRIES"), root_1);

                if ( !(stream_event_entry.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_event_entry.hasNext() ) {
                    adaptor.addChild(root_1, stream_event_entry.next());

                }
                stream_event_entry.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end event_entries

    public static class event_entry_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start event_entry
    // BON.g:561:1: event_entry : ( (e= 'event' manifest_textblock ) | e= 'event' ) ( ( 'involves' class_name_list ) | i= 'involves' ) -> {!mok}? ^( EVENT_ENTRY PARSE_ERROR ) -> {!cok}? ^( EVENT_ENTRY PARSE_ERROR ) -> ^( EVENT_ENTRY[$e] manifest_textblock class_name_list ) ;
    public final event_entry_return event_entry() throws RecognitionException {
        event_entry_return retval = new event_entry_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token e=null;
        Token i=null;
        Token string_literal90=null;
        manifest_textblock_return manifest_textblock89 = null;

        class_name_list_return class_name_list91 = null;


        CommonTree e_tree=null;
        CommonTree i_tree=null;
        CommonTree string_literal90_tree=null;
        RewriteRuleTokenStream stream_207=new RewriteRuleTokenStream(adaptor,"token 207");
        RewriteRuleTokenStream stream_208=new RewriteRuleTokenStream(adaptor,"token 208");
        RewriteRuleSubtreeStream stream_class_name_list=new RewriteRuleSubtreeStream(adaptor,"rule class_name_list");
        RewriteRuleSubtreeStream stream_manifest_textblock=new RewriteRuleSubtreeStream(adaptor,"rule manifest_textblock");
         boolean mok=false; boolean cok=false; 
        try {
            // BON.g:563:14: ( ( (e= 'event' manifest_textblock ) | e= 'event' ) ( ( 'involves' class_name_list ) | i= 'involves' ) -> {!mok}? ^( EVENT_ENTRY PARSE_ERROR ) -> {!cok}? ^( EVENT_ENTRY PARSE_ERROR ) -> ^( EVENT_ENTRY[$e] manifest_textblock class_name_list ) )
            // BON.g:563:17: ( (e= 'event' manifest_textblock ) | e= 'event' ) ( ( 'involves' class_name_list ) | i= 'involves' )
            {
            // BON.g:563:17: ( (e= 'event' manifest_textblock ) | e= 'event' )
            int alt48=2;
            int LA48_0 = input.LA(1);

            if ( (LA48_0==207) ) {
                int LA48_1 = input.LA(2);

                if ( (LA48_1==MANIFEST_STRING||LA48_1==MANIFEST_TEXTBLOCK_START) ) {
                    alt48=1;
                }
                else if ( (LA48_1==208) ) {
                    alt48=2;
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("563:17: ( (e= 'event' manifest_textblock ) | e= 'event' )", 48, 1, input);

                    throw nvae;
                }
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("563:17: ( (e= 'event' manifest_textblock ) | e= 'event' )", 48, 0, input);

                throw nvae;
            }
            switch (alt48) {
                case 1 :
                    // BON.g:563:19: (e= 'event' manifest_textblock )
                    {
                    // BON.g:563:19: (e= 'event' manifest_textblock )
                    // BON.g:563:20: e= 'event' manifest_textblock
                    {
                    e=(Token)input.LT(1);
                    match(input,207,FOLLOW_207_in_event_entry6829); if (failed) return retval;
                    if ( backtracking==0 ) stream_207.add(e);

                    pushFollow(FOLLOW_manifest_textblock_in_event_entry6831);
                    manifest_textblock89=manifest_textblock();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_manifest_textblock.add(manifest_textblock89.getTree());
                    if ( backtracking==0 ) {
                      mok=true;
                    }

                    }


                    }
                    break;
                case 2 :
                    // BON.g:564:20: e= 'event'
                    {
                    e=(Token)input.LT(1);
                    match(input,207,FOLLOW_207_in_event_entry6858); if (failed) return retval;
                    if ( backtracking==0 ) stream_207.add(e);

                    if ( backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(e), "event name", "in event entry clause", true)); 
                    }

                    }
                    break;

            }

            // BON.g:566:17: ( ( 'involves' class_name_list ) | i= 'involves' )
            int alt49=2;
            int LA49_0 = input.LA(1);

            if ( (LA49_0==208) ) {
                int LA49_1 = input.LA(2);

                if ( (LA49_1==187||LA49_1==207) ) {
                    alt49=2;
                }
                else if ( (LA49_1==IDENTIFIER) ) {
                    alt49=1;
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("566:17: ( ( 'involves' class_name_list ) | i= 'involves' )", 49, 1, input);

                    throw nvae;
                }
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("566:17: ( ( 'involves' class_name_list ) | i= 'involves' )", 49, 0, input);

                throw nvae;
            }
            switch (alt49) {
                case 1 :
                    // BON.g:566:19: ( 'involves' class_name_list )
                    {
                    // BON.g:566:19: ( 'involves' class_name_list )
                    // BON.g:566:20: 'involves' class_name_list
                    {
                    string_literal90=(Token)input.LT(1);
                    match(input,208,FOLLOW_208_in_event_entry6900); if (failed) return retval;
                    if ( backtracking==0 ) stream_208.add(string_literal90);

                    pushFollow(FOLLOW_class_name_list_in_event_entry6902);
                    class_name_list91=class_name_list();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_class_name_list.add(class_name_list91.getTree());
                    if ( backtracking==0 ) {
                      cok=true;
                    }

                    }


                    }
                    break;
                case 2 :
                    // BON.g:567:20: i= 'involves'
                    {
                    i=(Token)input.LT(1);
                    match(input,208,FOLLOW_208_in_event_entry6929); if (failed) return retval;
                    if ( backtracking==0 ) stream_208.add(i);

                    if ( backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(i), "class name list", "in involves clause of event entry", true)); 
                    }

                    }
                    break;

            }


            // AST REWRITE
            // elements: manifest_textblock, class_name_list
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 569:15: -> {!mok}? ^( EVENT_ENTRY PARSE_ERROR )
            if (!mok) {
                // BON.g:570:25: ^( EVENT_ENTRY PARSE_ERROR )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(EVENT_ENTRY, "EVENT_ENTRY"), root_1);

                adaptor.addChild(root_1, adaptor.create(PARSE_ERROR, "PARSE_ERROR"));

                adaptor.addChild(root_0, root_1);
                }

            }
            else // 571:15: -> {!cok}? ^( EVENT_ENTRY PARSE_ERROR )
            if (!cok) {
                // BON.g:572:25: ^( EVENT_ENTRY PARSE_ERROR )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(EVENT_ENTRY, "EVENT_ENTRY"), root_1);

                adaptor.addChild(root_1, adaptor.create(PARSE_ERROR, "PARSE_ERROR"));

                adaptor.addChild(root_0, root_1);
                }

            }
            else // 573:15: -> ^( EVENT_ENTRY[$e] manifest_textblock class_name_list )
            {
                // BON.g:574:15: ^( EVENT_ENTRY[$e] manifest_textblock class_name_list )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(EVENT_ENTRY, e), root_1);

                adaptor.addChild(root_1, stream_manifest_textblock.next());
                adaptor.addChild(root_1, stream_class_name_list.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end event_entry

    public static class scenario_chart_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start scenario_chart
    // BON.g:581:1: scenario_chart : s= 'scenario_chart' system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries )? 'end' -> ^( SCENARIO_CHART[$s] system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries )? ) ;
    public final scenario_chart_return scenario_chart() throws RecognitionException {
        scenario_chart_return retval = new scenario_chart_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token s=null;
        Token string_literal97=null;
        system_name_return system_name92 = null;

        indexing_return indexing93 = null;

        explanation_return explanation94 = null;

        part_return part95 = null;

        scenario_entries_return scenario_entries96 = null;


        CommonTree s_tree=null;
        CommonTree string_literal97_tree=null;
        RewriteRuleTokenStream stream_187=new RewriteRuleTokenStream(adaptor,"token 187");
        RewriteRuleTokenStream stream_209=new RewriteRuleTokenStream(adaptor,"token 209");
        RewriteRuleSubtreeStream stream_system_name=new RewriteRuleSubtreeStream(adaptor,"rule system_name");
        RewriteRuleSubtreeStream stream_indexing=new RewriteRuleSubtreeStream(adaptor,"rule indexing");
        RewriteRuleSubtreeStream stream_explanation=new RewriteRuleSubtreeStream(adaptor,"rule explanation");
        RewriteRuleSubtreeStream stream_scenario_entries=new RewriteRuleSubtreeStream(adaptor,"rule scenario_entries");
        RewriteRuleSubtreeStream stream_part=new RewriteRuleSubtreeStream(adaptor,"rule part");
        try {
            // BON.g:583:17: (s= 'scenario_chart' system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries )? 'end' -> ^( SCENARIO_CHART[$s] system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries )? ) )
            // BON.g:583:20: s= 'scenario_chart' system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries )? 'end'
            {
            s=(Token)input.LT(1);
            match(input,209,FOLLOW_209_in_scenario_chart7166); if (failed) return retval;
            if ( backtracking==0 ) stream_209.add(s);

            pushFollow(FOLLOW_system_name_in_scenario_chart7168);
            system_name92=system_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_system_name.add(system_name92.getTree());
            // BON.g:584:20: ( indexing )?
            int alt50=2;
            int LA50_0 = input.LA(1);

            if ( (LA50_0==192) ) {
                alt50=1;
            }
            switch (alt50) {
                case 1 :
                    // BON.g:584:21: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_scenario_chart7190);
                    indexing93=indexing();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_indexing.add(indexing93.getTree());

                    }
                    break;

            }

            // BON.g:585:20: ( explanation )?
            int alt51=2;
            int LA51_0 = input.LA(1);

            if ( (LA51_0==191) ) {
                alt51=1;
            }
            switch (alt51) {
                case 1 :
                    // BON.g:585:21: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_scenario_chart7214);
                    explanation94=explanation();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_explanation.add(explanation94.getTree());

                    }
                    break;

            }

            // BON.g:586:20: ( part )?
            int alt52=2;
            int LA52_0 = input.LA(1);

            if ( (LA52_0==193) ) {
                alt52=1;
            }
            switch (alt52) {
                case 1 :
                    // BON.g:586:21: part
                    {
                    pushFollow(FOLLOW_part_in_scenario_chart7238);
                    part95=part();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_part.add(part95.getTree());

                    }
                    break;

            }

            // BON.g:587:20: ( scenario_entries )?
            int alt53=2;
            int LA53_0 = input.LA(1);

            if ( (LA53_0==210) ) {
                alt53=1;
            }
            switch (alt53) {
                case 1 :
                    // BON.g:587:21: scenario_entries
                    {
                    pushFollow(FOLLOW_scenario_entries_in_scenario_chart7262);
                    scenario_entries96=scenario_entries();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_scenario_entries.add(scenario_entries96.getTree());

                    }
                    break;

            }

            string_literal97=(Token)input.LT(1);
            match(input,187,FOLLOW_187_in_scenario_chart7285); if (failed) return retval;
            if ( backtracking==0 ) stream_187.add(string_literal97);


            // AST REWRITE
            // elements: explanation, scenario_entries, part, indexing, system_name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 589:18: -> ^( SCENARIO_CHART[$s] system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries )? )
            {
                // BON.g:590:18: ^( SCENARIO_CHART[$s] system_name ( indexing )? ( explanation )? ( part )? ( scenario_entries )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(SCENARIO_CHART, s), root_1);

                adaptor.addChild(root_1, stream_system_name.next());
                // BON.g:593:20: ( indexing )?
                if ( stream_indexing.hasNext() ) {
                    adaptor.addChild(root_1, stream_indexing.next());

                }
                stream_indexing.reset();
                // BON.g:594:20: ( explanation )?
                if ( stream_explanation.hasNext() ) {
                    adaptor.addChild(root_1, stream_explanation.next());

                }
                stream_explanation.reset();
                // BON.g:595:20: ( part )?
                if ( stream_part.hasNext() ) {
                    adaptor.addChild(root_1, stream_part.next());

                }
                stream_part.reset();
                // BON.g:596:20: ( scenario_entries )?
                if ( stream_scenario_entries.hasNext() ) {
                    adaptor.addChild(root_1, stream_scenario_entries.next());

                }
                stream_scenario_entries.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end scenario_chart

    public static class scenario_entries_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start scenario_entries
    // BON.g:600:1: scenario_entries : ( scenario_entry )+ -> ^( SCENARIO_ENTRIES ( scenario_entry )+ ) ;
    public final scenario_entries_return scenario_entries() throws RecognitionException {
        scenario_entries_return retval = new scenario_entries_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        scenario_entry_return scenario_entry98 = null;


        RewriteRuleSubtreeStream stream_scenario_entry=new RewriteRuleSubtreeStream(adaptor,"rule scenario_entry");
        try {
            // BON.g:600:19: ( ( scenario_entry )+ -> ^( SCENARIO_ENTRIES ( scenario_entry )+ ) )
            // BON.g:600:22: ( scenario_entry )+
            {
            // BON.g:600:22: ( scenario_entry )+
            int cnt54=0;
            loop54:
            do {
                int alt54=2;
                int LA54_0 = input.LA(1);

                if ( (LA54_0==210) ) {
                    alt54=1;
                }


                switch (alt54) {
            	case 1 :
            	    // BON.g:600:23: scenario_entry
            	    {
            	    pushFollow(FOLLOW_scenario_entry_in_scenario_entries7526);
            	    scenario_entry98=scenario_entry();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_scenario_entry.add(scenario_entry98.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt54 >= 1 ) break loop54;
            	    if (backtracking>0) {failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(54, input);
                        throw eee;
                }
                cnt54++;
            } while (true);


            // AST REWRITE
            // elements: scenario_entry
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 601:20: -> ^( SCENARIO_ENTRIES ( scenario_entry )+ )
            {
                // BON.g:602:20: ^( SCENARIO_ENTRIES ( scenario_entry )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(SCENARIO_ENTRIES, "SCENARIO_ENTRIES"), root_1);

                if ( !(stream_scenario_entry.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_scenario_entry.hasNext() ) {
                    adaptor.addChild(root_1, stream_scenario_entry.next());

                }
                stream_scenario_entry.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end scenario_entries

    public static class scenario_entry_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start scenario_entry
    // BON.g:608:1: scenario_entry : s= 'scenario' MANIFEST_STRING description -> ^( SCENARIO_ENTRY[$s] MANIFEST_STRING description ) ;
    public final scenario_entry_return scenario_entry() throws RecognitionException {
        scenario_entry_return retval = new scenario_entry_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token s=null;
        Token MANIFEST_STRING99=null;
        description_return description100 = null;


        CommonTree s_tree=null;
        CommonTree MANIFEST_STRING99_tree=null;
        RewriteRuleTokenStream stream_MANIFEST_STRING=new RewriteRuleTokenStream(adaptor,"token MANIFEST_STRING");
        RewriteRuleTokenStream stream_210=new RewriteRuleTokenStream(adaptor,"token 210");
        RewriteRuleSubtreeStream stream_description=new RewriteRuleSubtreeStream(adaptor,"rule description");
        try {
            // BON.g:608:17: (s= 'scenario' MANIFEST_STRING description -> ^( SCENARIO_ENTRY[$s] MANIFEST_STRING description ) )
            // BON.g:608:20: s= 'scenario' MANIFEST_STRING description
            {
            s=(Token)input.LT(1);
            match(input,210,FOLLOW_210_in_scenario_entry7713); if (failed) return retval;
            if ( backtracking==0 ) stream_210.add(s);

            MANIFEST_STRING99=(Token)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_scenario_entry7715); if (failed) return retval;
            if ( backtracking==0 ) stream_MANIFEST_STRING.add(MANIFEST_STRING99);

            pushFollow(FOLLOW_description_in_scenario_entry7717);
            description100=description();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_description.add(description100.getTree());

            // AST REWRITE
            // elements: description, MANIFEST_STRING
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 609:18: -> ^( SCENARIO_ENTRY[$s] MANIFEST_STRING description )
            {
                // BON.g:610:18: ^( SCENARIO_ENTRY[$s] MANIFEST_STRING description )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(SCENARIO_ENTRY, s), root_1);

                adaptor.addChild(root_1, stream_MANIFEST_STRING.next());
                adaptor.addChild(root_1, stream_description.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end scenario_entry

    public static class creation_chart_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start creation_chart
    // BON.g:616:1: creation_chart : c= 'creation_chart' system_name ( indexing )? ( explanation )? ( part )? ( creation_entries )? 'end' -> ^( CREATION_CHART[$c] system_name ( indexing )? ( explanation )? ( part )? ( creation_entries )? ) ;
    public final creation_chart_return creation_chart() throws RecognitionException {
        creation_chart_return retval = new creation_chart_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token c=null;
        Token string_literal106=null;
        system_name_return system_name101 = null;

        indexing_return indexing102 = null;

        explanation_return explanation103 = null;

        part_return part104 = null;

        creation_entries_return creation_entries105 = null;


        CommonTree c_tree=null;
        CommonTree string_literal106_tree=null;
        RewriteRuleTokenStream stream_211=new RewriteRuleTokenStream(adaptor,"token 211");
        RewriteRuleTokenStream stream_187=new RewriteRuleTokenStream(adaptor,"token 187");
        RewriteRuleSubtreeStream stream_creation_entries=new RewriteRuleSubtreeStream(adaptor,"rule creation_entries");
        RewriteRuleSubtreeStream stream_system_name=new RewriteRuleSubtreeStream(adaptor,"rule system_name");
        RewriteRuleSubtreeStream stream_indexing=new RewriteRuleSubtreeStream(adaptor,"rule indexing");
        RewriteRuleSubtreeStream stream_explanation=new RewriteRuleSubtreeStream(adaptor,"rule explanation");
        RewriteRuleSubtreeStream stream_part=new RewriteRuleSubtreeStream(adaptor,"rule part");
        try {
            // BON.g:618:17: (c= 'creation_chart' system_name ( indexing )? ( explanation )? ( part )? ( creation_entries )? 'end' -> ^( CREATION_CHART[$c] system_name ( indexing )? ( explanation )? ( part )? ( creation_entries )? ) )
            // BON.g:618:20: c= 'creation_chart' system_name ( indexing )? ( explanation )? ( part )? ( creation_entries )? 'end'
            {
            c=(Token)input.LT(1);
            match(input,211,FOLLOW_211_in_creation_chart7854); if (failed) return retval;
            if ( backtracking==0 ) stream_211.add(c);

            pushFollow(FOLLOW_system_name_in_creation_chart7856);
            system_name101=system_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_system_name.add(system_name101.getTree());
            // BON.g:619:20: ( indexing )?
            int alt55=2;
            int LA55_0 = input.LA(1);

            if ( (LA55_0==192) ) {
                alt55=1;
            }
            switch (alt55) {
                case 1 :
                    // BON.g:619:21: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_creation_chart7878);
                    indexing102=indexing();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_indexing.add(indexing102.getTree());

                    }
                    break;

            }

            // BON.g:620:20: ( explanation )?
            int alt56=2;
            int LA56_0 = input.LA(1);

            if ( (LA56_0==191) ) {
                alt56=1;
            }
            switch (alt56) {
                case 1 :
                    // BON.g:620:21: explanation
                    {
                    pushFollow(FOLLOW_explanation_in_creation_chart7902);
                    explanation103=explanation();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_explanation.add(explanation103.getTree());

                    }
                    break;

            }

            // BON.g:621:20: ( part )?
            int alt57=2;
            int LA57_0 = input.LA(1);

            if ( (LA57_0==193) ) {
                alt57=1;
            }
            switch (alt57) {
                case 1 :
                    // BON.g:621:21: part
                    {
                    pushFollow(FOLLOW_part_in_creation_chart7926);
                    part104=part();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_part.add(part104.getTree());

                    }
                    break;

            }

            // BON.g:622:20: ( creation_entries )?
            int alt58=2;
            int LA58_0 = input.LA(1);

            if ( (LA58_0==212) ) {
                alt58=1;
            }
            switch (alt58) {
                case 1 :
                    // BON.g:622:21: creation_entries
                    {
                    pushFollow(FOLLOW_creation_entries_in_creation_chart7950);
                    creation_entries105=creation_entries();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_creation_entries.add(creation_entries105.getTree());

                    }
                    break;

            }

            string_literal106=(Token)input.LT(1);
            match(input,187,FOLLOW_187_in_creation_chart7973); if (failed) return retval;
            if ( backtracking==0 ) stream_187.add(string_literal106);


            // AST REWRITE
            // elements: creation_entries, part, explanation, indexing, system_name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 624:18: -> ^( CREATION_CHART[$c] system_name ( indexing )? ( explanation )? ( part )? ( creation_entries )? )
            {
                // BON.g:625:18: ^( CREATION_CHART[$c] system_name ( indexing )? ( explanation )? ( part )? ( creation_entries )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CREATION_CHART, c), root_1);

                adaptor.addChild(root_1, stream_system_name.next());
                // BON.g:628:20: ( indexing )?
                if ( stream_indexing.hasNext() ) {
                    adaptor.addChild(root_1, stream_indexing.next());

                }
                stream_indexing.reset();
                // BON.g:629:20: ( explanation )?
                if ( stream_explanation.hasNext() ) {
                    adaptor.addChild(root_1, stream_explanation.next());

                }
                stream_explanation.reset();
                // BON.g:630:20: ( part )?
                if ( stream_part.hasNext() ) {
                    adaptor.addChild(root_1, stream_part.next());

                }
                stream_part.reset();
                // BON.g:631:20: ( creation_entries )?
                if ( stream_creation_entries.hasNext() ) {
                    adaptor.addChild(root_1, stream_creation_entries.next());

                }
                stream_creation_entries.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end creation_chart

    public static class creation_entries_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start creation_entries
    // BON.g:635:1: creation_entries : ( creation_entry )+ -> ^( CREATION_ENTRIES ( creation_entry )+ ) ;
    public final creation_entries_return creation_entries() throws RecognitionException {
        creation_entries_return retval = new creation_entries_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        creation_entry_return creation_entry107 = null;


        RewriteRuleSubtreeStream stream_creation_entry=new RewriteRuleSubtreeStream(adaptor,"rule creation_entry");
        try {
            // BON.g:635:19: ( ( creation_entry )+ -> ^( CREATION_ENTRIES ( creation_entry )+ ) )
            // BON.g:635:22: ( creation_entry )+
            {
            // BON.g:635:22: ( creation_entry )+
            int cnt59=0;
            loop59:
            do {
                int alt59=2;
                int LA59_0 = input.LA(1);

                if ( (LA59_0==212) ) {
                    alt59=1;
                }


                switch (alt59) {
            	case 1 :
            	    // BON.g:635:23: creation_entry
            	    {
            	    pushFollow(FOLLOW_creation_entry_in_creation_entries8215);
            	    creation_entry107=creation_entry();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_creation_entry.add(creation_entry107.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt59 >= 1 ) break loop59;
            	    if (backtracking>0) {failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(59, input);
                        throw eee;
                }
                cnt59++;
            } while (true);


            // AST REWRITE
            // elements: creation_entry
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 636:20: -> ^( CREATION_ENTRIES ( creation_entry )+ )
            {
                // BON.g:637:20: ^( CREATION_ENTRIES ( creation_entry )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CREATION_ENTRIES, "CREATION_ENTRIES"), root_1);

                if ( !(stream_creation_entry.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_creation_entry.hasNext() ) {
                    adaptor.addChild(root_1, stream_creation_entry.next());

                }
                stream_creation_entry.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end creation_entries

    public static class creation_entry_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start creation_entry
    // BON.g:643:1: creation_entry : c= 'creator' class_name 'creates' class_name_list -> ^( CREATION_ENTRY[$c] class_name class_name_list ) ;
    public final creation_entry_return creation_entry() throws RecognitionException {
        creation_entry_return retval = new creation_entry_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token c=null;
        Token string_literal109=null;
        class_name_return class_name108 = null;

        class_name_list_return class_name_list110 = null;


        CommonTree c_tree=null;
        CommonTree string_literal109_tree=null;
        RewriteRuleTokenStream stream_212=new RewriteRuleTokenStream(adaptor,"token 212");
        RewriteRuleTokenStream stream_213=new RewriteRuleTokenStream(adaptor,"token 213");
        RewriteRuleSubtreeStream stream_class_name_list=new RewriteRuleSubtreeStream(adaptor,"rule class_name_list");
        RewriteRuleSubtreeStream stream_class_name=new RewriteRuleSubtreeStream(adaptor,"rule class_name");
        try {
            // BON.g:643:17: (c= 'creator' class_name 'creates' class_name_list -> ^( CREATION_ENTRY[$c] class_name class_name_list ) )
            // BON.g:643:20: c= 'creator' class_name 'creates' class_name_list
            {
            c=(Token)input.LT(1);
            match(input,212,FOLLOW_212_in_creation_entry8379); if (failed) return retval;
            if ( backtracking==0 ) stream_212.add(c);

            pushFollow(FOLLOW_class_name_in_creation_entry8381);
            class_name108=class_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_class_name.add(class_name108.getTree());
            string_literal109=(Token)input.LT(1);
            match(input,213,FOLLOW_213_in_creation_entry8403); if (failed) return retval;
            if ( backtracking==0 ) stream_213.add(string_literal109);

            pushFollow(FOLLOW_class_name_list_in_creation_entry8405);
            class_name_list110=class_name_list();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_class_name_list.add(class_name_list110.getTree());

            // AST REWRITE
            // elements: class_name, class_name_list
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 645:18: -> ^( CREATION_ENTRY[$c] class_name class_name_list )
            {
                // BON.g:646:18: ^( CREATION_ENTRY[$c] class_name class_name_list )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CREATION_ENTRY, c), root_1);

                adaptor.addChild(root_1, stream_class_name.next());
                adaptor.addChild(root_1, stream_class_name_list.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end creation_entry

    public static class static_diagram_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start static_diagram
    // BON.g:653:1: static_diagram : s= 'static_diagram' ( extended_id )? ( COMMENT )? 'component' ( static_block )? 'end' -> ^( STATIC_DIAGRAM[$s] ( extended_id )? ( COMMENT )? ( static_block )? ) ;
    public final static_diagram_return static_diagram() throws RecognitionException {
        static_diagram_return retval = new static_diagram_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token s=null;
        Token COMMENT112=null;
        Token string_literal113=null;
        Token string_literal115=null;
        extended_id_return extended_id111 = null;

        static_block_return static_block114 = null;


        CommonTree s_tree=null;
        CommonTree COMMENT112_tree=null;
        CommonTree string_literal113_tree=null;
        CommonTree string_literal115_tree=null;
        RewriteRuleTokenStream stream_215=new RewriteRuleTokenStream(adaptor,"token 215");
        RewriteRuleTokenStream stream_214=new RewriteRuleTokenStream(adaptor,"token 214");
        RewriteRuleTokenStream stream_COMMENT=new RewriteRuleTokenStream(adaptor,"token COMMENT");
        RewriteRuleTokenStream stream_187=new RewriteRuleTokenStream(adaptor,"token 187");
        RewriteRuleSubtreeStream stream_extended_id=new RewriteRuleSubtreeStream(adaptor,"rule extended_id");
        RewriteRuleSubtreeStream stream_static_block=new RewriteRuleSubtreeStream(adaptor,"rule static_block");
        try {
            // BON.g:657:17: (s= 'static_diagram' ( extended_id )? ( COMMENT )? 'component' ( static_block )? 'end' -> ^( STATIC_DIAGRAM[$s] ( extended_id )? ( COMMENT )? ( static_block )? ) )
            // BON.g:657:20: s= 'static_diagram' ( extended_id )? ( COMMENT )? 'component' ( static_block )? 'end'
            {
            s=(Token)input.LT(1);
            match(input,214,FOLLOW_214_in_static_diagram8563); if (failed) return retval;
            if ( backtracking==0 ) stream_214.add(s);

            // BON.g:657:39: ( extended_id )?
            int alt60=2;
            int LA60_0 = input.LA(1);

            if ( (LA60_0==IDENTIFIER||LA60_0==INTEGER) ) {
                alt60=1;
            }
            switch (alt60) {
                case 1 :
                    // BON.g:657:40: extended_id
                    {
                    pushFollow(FOLLOW_extended_id_in_static_diagram8566);
                    extended_id111=extended_id();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_extended_id.add(extended_id111.getTree());

                    }
                    break;

            }

            // BON.g:657:54: ( COMMENT )?
            int alt61=2;
            int LA61_0 = input.LA(1);

            if ( (LA61_0==COMMENT) ) {
                alt61=1;
            }
            switch (alt61) {
                case 1 :
                    // BON.g:657:55: COMMENT
                    {
                    COMMENT112=(Token)input.LT(1);
                    match(input,COMMENT,FOLLOW_COMMENT_in_static_diagram8571); if (failed) return retval;
                    if ( backtracking==0 ) stream_COMMENT.add(COMMENT112);


                    }
                    break;

            }

            string_literal113=(Token)input.LT(1);
            match(input,215,FOLLOW_215_in_static_diagram8595); if (failed) return retval;
            if ( backtracking==0 ) stream_215.add(string_literal113);

            // BON.g:659:20: ( static_block )?
            int alt62=2;
            int LA62_0 = input.LA(1);

            if ( (LA62_0==IDENTIFIER||(LA62_0>=188 && LA62_0<=189)||(LA62_0>=217 && LA62_0<=219)) ) {
                alt62=1;
            }
            switch (alt62) {
                case 1 :
                    // BON.g:659:21: static_block
                    {
                    pushFollow(FOLLOW_static_block_in_static_diagram8618);
                    static_block114=static_block();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_static_block.add(static_block114.getTree());

                    }
                    break;

            }

            string_literal115=(Token)input.LT(1);
            match(input,187,FOLLOW_187_in_static_diagram8642); if (failed) return retval;
            if ( backtracking==0 ) stream_187.add(string_literal115);


            // AST REWRITE
            // elements: static_block, extended_id, COMMENT
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 661:18: -> ^( STATIC_DIAGRAM[$s] ( extended_id )? ( COMMENT )? ( static_block )? )
            {
                // BON.g:662:18: ^( STATIC_DIAGRAM[$s] ( extended_id )? ( COMMENT )? ( static_block )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(STATIC_DIAGRAM, s), root_1);

                // BON.g:664:20: ( extended_id )?
                if ( stream_extended_id.hasNext() ) {
                    adaptor.addChild(root_1, stream_extended_id.next());

                }
                stream_extended_id.reset();
                // BON.g:664:35: ( COMMENT )?
                if ( stream_COMMENT.hasNext() ) {
                    adaptor.addChild(root_1, stream_COMMENT.next());

                }
                stream_COMMENT.reset();
                // BON.g:665:20: ( static_block )?
                if ( stream_static_block.hasNext() ) {
                    adaptor.addChild(root_1, stream_static_block.next());

                }
                stream_static_block.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end static_diagram

    public static class extended_id_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start extended_id
    // BON.g:669:1: extended_id : (i= IDENTIFIER -> ^( EXTENDED_ID[$i] IDENTIFIER ) | i= INTEGER -> ^( EXTENDED_ID[$i] INTEGER ) );
    public final extended_id_return extended_id() throws RecognitionException {
        extended_id_return retval = new extended_id_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token i=null;

        CommonTree i_tree=null;
        RewriteRuleTokenStream stream_INTEGER=new RewriteRuleTokenStream(adaptor,"token INTEGER");
        RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");

        try {
            // BON.g:669:14: (i= IDENTIFIER -> ^( EXTENDED_ID[$i] IDENTIFIER ) | i= INTEGER -> ^( EXTENDED_ID[$i] INTEGER ) )
            int alt63=2;
            int LA63_0 = input.LA(1);

            if ( (LA63_0==IDENTIFIER) ) {
                alt63=1;
            }
            else if ( (LA63_0==INTEGER) ) {
                alt63=2;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("669:1: extended_id : (i= IDENTIFIER -> ^( EXTENDED_ID[$i] IDENTIFIER ) | i= INTEGER -> ^( EXTENDED_ID[$i] INTEGER ) );", 63, 0, input);

                throw nvae;
            }
            switch (alt63) {
                case 1 :
                    // BON.g:669:17: i= IDENTIFIER
                    {
                    i=(Token)input.LT(1);
                    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_extended_id8841); if (failed) return retval;
                    if ( backtracking==0 ) stream_IDENTIFIER.add(i);


                    // AST REWRITE
                    // elements: IDENTIFIER
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 670:15: -> ^( EXTENDED_ID[$i] IDENTIFIER )
                    {
                        // BON.g:671:15: ^( EXTENDED_ID[$i] IDENTIFIER )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(EXTENDED_ID, i), root_1);

                        adaptor.addChild(root_1, stream_IDENTIFIER.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:674:17: i= INTEGER
                    {
                    i=(Token)input.LT(1);
                    match(input,INTEGER,FOLLOW_INTEGER_in_extended_id8932); if (failed) return retval;
                    if ( backtracking==0 ) stream_INTEGER.add(i);


                    // AST REWRITE
                    // elements: INTEGER
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 675:15: -> ^( EXTENDED_ID[$i] INTEGER )
                    {
                        // BON.g:676:15: ^( EXTENDED_ID[$i] INTEGER )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(EXTENDED_ID, i), root_1);

                        adaptor.addChild(root_1, stream_INTEGER.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end extended_id

    public static class static_block_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start static_block
    // BON.g:681:1: static_block : ( static_component )+ -> ^( STATIC_BLOCK ( static_component )+ ) ;
    public final static_block_return static_block() throws RecognitionException {
        static_block_return retval = new static_block_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        static_component_return static_component116 = null;


        RewriteRuleSubtreeStream stream_static_component=new RewriteRuleSubtreeStream(adaptor,"rule static_component");
        try {
            // BON.g:681:15: ( ( static_component )+ -> ^( STATIC_BLOCK ( static_component )+ ) )
            // BON.g:681:18: ( static_component )+
            {
            // BON.g:681:18: ( static_component )+
            int cnt64=0;
            loop64:
            do {
                int alt64=2;
                int LA64_0 = input.LA(1);

                if ( (LA64_0==IDENTIFIER||(LA64_0>=188 && LA64_0<=189)||(LA64_0>=217 && LA64_0<=219)) ) {
                    alt64=1;
                }


                switch (alt64) {
            	case 1 :
            	    // BON.g:681:19: static_component
            	    {
            	    pushFollow(FOLLOW_static_component_in_static_block9041);
            	    static_component116=static_component();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_static_component.add(static_component116.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt64 >= 1 ) break loop64;
            	    if (backtracking>0) {failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(64, input);
                        throw eee;
                }
                cnt64++;
            } while (true);


            // AST REWRITE
            // elements: static_component
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 682:16: -> ^( STATIC_BLOCK ( static_component )+ )
            {
                // BON.g:683:16: ^( STATIC_BLOCK ( static_component )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(STATIC_BLOCK, "STATIC_BLOCK"), root_1);

                if ( !(stream_static_component.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_static_component.hasNext() ) {
                    adaptor.addChild(root_1, stream_static_component.next());

                }
                stream_static_component.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end static_block

    public static class static_component_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start static_component
    // BON.g:689:1: static_component : (c1= cluster -> ^( STATIC_COMPONENT[$c1.start] cluster ) | c2= classX -> ^( STATIC_COMPONENT[$c2.start] classX ) | s= static_relation -> ^( STATIC_COMPONENT[$s.start] static_relation ) );
    public final static_component_return static_component() throws RecognitionException {
        static_component_return retval = new static_component_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        cluster_return c1 = null;

        classX_return c2 = null;

        static_relation_return s = null;


        RewriteRuleSubtreeStream stream_static_relation=new RewriteRuleSubtreeStream(adaptor,"rule static_relation");
        RewriteRuleSubtreeStream stream_classX=new RewriteRuleSubtreeStream(adaptor,"rule classX");
        RewriteRuleSubtreeStream stream_cluster=new RewriteRuleSubtreeStream(adaptor,"rule cluster");
        try {
            // BON.g:689:19: (c1= cluster -> ^( STATIC_COMPONENT[$c1.start] cluster ) | c2= classX -> ^( STATIC_COMPONENT[$c2.start] classX ) | s= static_relation -> ^( STATIC_COMPONENT[$s.start] static_relation ) )
            int alt65=3;
            switch ( input.LA(1) ) {
            case 189:
                {
                alt65=1;
                }
                break;
            case 188:
            case 217:
            case 218:
            case 219:
                {
                alt65=2;
                }
                break;
            case IDENTIFIER:
                {
                alt65=3;
                }
                break;
            default:
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("689:1: static_component : (c1= cluster -> ^( STATIC_COMPONENT[$c1.start] cluster ) | c2= classX -> ^( STATIC_COMPONENT[$c2.start] classX ) | s= static_relation -> ^( STATIC_COMPONENT[$s.start] static_relation ) );", 65, 0, input);

                throw nvae;
            }

            switch (alt65) {
                case 1 :
                    // BON.g:689:23: c1= cluster
                    {
                    pushFollow(FOLLOW_cluster_in_static_component9148);
                    c1=cluster();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_cluster.add(c1.getTree());

                    // AST REWRITE
                    // elements: cluster
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 690:21: -> ^( STATIC_COMPONENT[$c1.start] cluster )
                    {
                        // BON.g:691:21: ^( STATIC_COMPONENT[$c1.start] cluster )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(STATIC_COMPONENT, ((Token)c1.start)), root_1);

                        adaptor.addChild(root_1, stream_cluster.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:694:23: c2= classX
                    {
                    pushFollow(FOLLOW_classX_in_static_component9269);
                    c2=classX();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_classX.add(c2.getTree());

                    // AST REWRITE
                    // elements: classX
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 695:21: -> ^( STATIC_COMPONENT[$c2.start] classX )
                    {
                        // BON.g:696:21: ^( STATIC_COMPONENT[$c2.start] classX )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(STATIC_COMPONENT, ((Token)c2.start)), root_1);

                        adaptor.addChild(root_1, stream_classX.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 3 :
                    // BON.g:699:23: s= static_relation
                    {
                    pushFollow(FOLLOW_static_relation_in_static_component9390);
                    s=static_relation();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_static_relation.add(s.getTree());

                    // AST REWRITE
                    // elements: static_relation
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 700:21: -> ^( STATIC_COMPONENT[$s.start] static_relation )
                    {
                        // BON.g:701:21: ^( STATIC_COMPONENT[$s.start] static_relation )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(STATIC_COMPONENT, ((Token)s.start)), root_1);

                        adaptor.addChild(root_1, stream_static_relation.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end static_component

    public static class cluster_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start cluster
    // BON.g:706:1: cluster : c= 'cluster' cluster_name ( 'reused' )? ( COMMENT )? ( cluster_components )? -> ^( CLUSTER[$c] cluster_name ( 'reused' )? ( COMMENT )? ( cluster_components )? ) ;
    public final cluster_return cluster() throws RecognitionException {
        cluster_return retval = new cluster_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token c=null;
        Token string_literal118=null;
        Token COMMENT119=null;
        cluster_name_return cluster_name117 = null;

        cluster_components_return cluster_components120 = null;


        CommonTree c_tree=null;
        CommonTree string_literal118_tree=null;
        CommonTree COMMENT119_tree=null;
        RewriteRuleTokenStream stream_216=new RewriteRuleTokenStream(adaptor,"token 216");
        RewriteRuleTokenStream stream_COMMENT=new RewriteRuleTokenStream(adaptor,"token COMMENT");
        RewriteRuleTokenStream stream_189=new RewriteRuleTokenStream(adaptor,"token 189");
        RewriteRuleSubtreeStream stream_cluster_name=new RewriteRuleSubtreeStream(adaptor,"rule cluster_name");
        RewriteRuleSubtreeStream stream_cluster_components=new RewriteRuleSubtreeStream(adaptor,"rule cluster_components");
        try {
            // BON.g:708:10: (c= 'cluster' cluster_name ( 'reused' )? ( COMMENT )? ( cluster_components )? -> ^( CLUSTER[$c] cluster_name ( 'reused' )? ( COMMENT )? ( cluster_components )? ) )
            // BON.g:708:13: c= 'cluster' cluster_name ( 'reused' )? ( COMMENT )? ( cluster_components )?
            {
            c=(Token)input.LT(1);
            match(input,189,FOLLOW_189_in_cluster9519); if (failed) return retval;
            if ( backtracking==0 ) stream_189.add(c);

            pushFollow(FOLLOW_cluster_name_in_cluster9521);
            cluster_name117=cluster_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_cluster_name.add(cluster_name117.getTree());
            // BON.g:709:13: ( 'reused' )?
            int alt66=2;
            int LA66_0 = input.LA(1);

            if ( (LA66_0==216) ) {
                alt66=1;
            }
            switch (alt66) {
                case 1 :
                    // BON.g:709:14: 'reused'
                    {
                    string_literal118=(Token)input.LT(1);
                    match(input,216,FOLLOW_216_in_cluster9537); if (failed) return retval;
                    if ( backtracking==0 ) stream_216.add(string_literal118);


                    }
                    break;

            }

            // BON.g:709:25: ( COMMENT )?
            int alt67=2;
            int LA67_0 = input.LA(1);

            if ( (LA67_0==COMMENT) ) {
                alt67=1;
            }
            switch (alt67) {
                case 1 :
                    // BON.g:709:26: COMMENT
                    {
                    COMMENT119=(Token)input.LT(1);
                    match(input,COMMENT,FOLLOW_COMMENT_in_cluster9542); if (failed) return retval;
                    if ( backtracking==0 ) stream_COMMENT.add(COMMENT119);


                    }
                    break;

            }

            if ( backtracking==0 ) {
               getTI().addCluster(input.toString(cluster_name117.start,cluster_name117.stop), getSLoc(c)); 
            }
            // BON.g:711:13: ( cluster_components )?
            int alt68=2;
            int LA68_0 = input.LA(1);

            if ( (LA68_0==215) ) {
                alt68=1;
            }
            switch (alt68) {
                case 1 :
                    // BON.g:711:15: cluster_components
                    {
                    if ( backtracking==0 ) {
                       getContext().enterCluster(input.toString(cluster_name117.start,cluster_name117.stop)); 
                    }
                    pushFollow(FOLLOW_cluster_components_in_cluster9594);
                    cluster_components120=cluster_components();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_cluster_components.add(cluster_components120.getTree());
                    if ( backtracking==0 ) {
                       getContext().leaveCluster(); 
                    }

                    }
                    break;

            }


            // AST REWRITE
            // elements: 216, cluster_components, cluster_name, COMMENT
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 715:11: -> ^( CLUSTER[$c] cluster_name ( 'reused' )? ( COMMENT )? ( cluster_components )? )
            {
                // BON.g:716:11: ^( CLUSTER[$c] cluster_name ( 'reused' )? ( COMMENT )? ( cluster_components )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLUSTER, c), root_1);

                adaptor.addChild(root_1, stream_cluster_name.next());
                // BON.g:718:13: ( 'reused' )?
                if ( stream_216.hasNext() ) {
                    adaptor.addChild(root_1, stream_216.next());

                }
                stream_216.reset();
                // BON.g:718:25: ( COMMENT )?
                if ( stream_COMMENT.hasNext() ) {
                    adaptor.addChild(root_1, stream_COMMENT.next());

                }
                stream_COMMENT.reset();
                // BON.g:719:13: ( cluster_components )?
                if ( stream_cluster_components.hasNext() ) {
                    adaptor.addChild(root_1, stream_cluster_components.next());

                }
                stream_cluster_components.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end cluster

    public static class cluster_components_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start cluster_components
    // BON.g:723:1: cluster_components : c= 'component' ( static_block )? 'end' -> ^( CLUSTER_COMPONENTS[$c] ( static_block )? ) ;
    public final cluster_components_return cluster_components() throws RecognitionException {
        cluster_components_return retval = new cluster_components_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token c=null;
        Token string_literal122=null;
        static_block_return static_block121 = null;


        CommonTree c_tree=null;
        CommonTree string_literal122_tree=null;
        RewriteRuleTokenStream stream_215=new RewriteRuleTokenStream(adaptor,"token 215");
        RewriteRuleTokenStream stream_187=new RewriteRuleTokenStream(adaptor,"token 187");
        RewriteRuleSubtreeStream stream_static_block=new RewriteRuleSubtreeStream(adaptor,"rule static_block");
        try {
            // BON.g:723:21: (c= 'component' ( static_block )? 'end' -> ^( CLUSTER_COMPONENTS[$c] ( static_block )? ) )
            // BON.g:723:24: c= 'component' ( static_block )? 'end'
            {
            c=(Token)input.LT(1);
            match(input,215,FOLLOW_215_in_cluster_components9751); if (failed) return retval;
            if ( backtracking==0 ) stream_215.add(c);

            // BON.g:723:38: ( static_block )?
            int alt69=2;
            int LA69_0 = input.LA(1);

            if ( (LA69_0==IDENTIFIER||(LA69_0>=188 && LA69_0<=189)||(LA69_0>=217 && LA69_0<=219)) ) {
                alt69=1;
            }
            switch (alt69) {
                case 1 :
                    // BON.g:723:39: static_block
                    {
                    pushFollow(FOLLOW_static_block_in_cluster_components9754);
                    static_block121=static_block();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_static_block.add(static_block121.getTree());

                    }
                    break;

            }

            string_literal122=(Token)input.LT(1);
            match(input,187,FOLLOW_187_in_cluster_components9758); if (failed) return retval;
            if ( backtracking==0 ) stream_187.add(string_literal122);


            // AST REWRITE
            // elements: static_block
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 724:22: -> ^( CLUSTER_COMPONENTS[$c] ( static_block )? )
            {
                // BON.g:725:22: ^( CLUSTER_COMPONENTS[$c] ( static_block )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLUSTER_COMPONENTS, c), root_1);

                // BON.g:726:47: ( static_block )?
                if ( stream_static_block.hasNext() ) {
                    adaptor.addChild(root_1, stream_static_block.next());

                }
                stream_static_block.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end cluster_components

    public static class classX_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start classX
    // BON.g:730:1: classX : ( ( 'root' c= 'class' c1= class_name ) | ( 'deferred' c= 'class' c2= class_name ) | ( 'effective' c= 'class' c3= class_name ) | (c= 'class' c4= class_name ) ) ( formal_generics )? ( 'reused' )? ( 'persistent' )? ( 'interfaced' )? ( COMMENT )? ( class_interface )? -> ^( CLASS[$c] ( 'root' )? ( 'deferred' )? ( 'effective' )? class_name ( formal_generics )? ( 'reused' )? ( 'persistent' )? ( 'interfaced' )? ( COMMENT )? ( class_interface )? ) ;
    public final classX_return classX() throws RecognitionException {
        classX_return retval = new classX_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token c=null;
        Token string_literal123=null;
        Token string_literal124=null;
        Token string_literal125=null;
        Token string_literal127=null;
        Token string_literal128=null;
        Token string_literal129=null;
        Token COMMENT130=null;
        class_name_return c1 = null;

        class_name_return c2 = null;

        class_name_return c3 = null;

        class_name_return c4 = null;

        formal_generics_return formal_generics126 = null;

        class_interface_return class_interface131 = null;


        CommonTree c_tree=null;
        CommonTree string_literal123_tree=null;
        CommonTree string_literal124_tree=null;
        CommonTree string_literal125_tree=null;
        CommonTree string_literal127_tree=null;
        CommonTree string_literal128_tree=null;
        CommonTree string_literal129_tree=null;
        CommonTree COMMENT130_tree=null;
        RewriteRuleTokenStream stream_220=new RewriteRuleTokenStream(adaptor,"token 220");
        RewriteRuleTokenStream stream_221=new RewriteRuleTokenStream(adaptor,"token 221");
        RewriteRuleTokenStream stream_216=new RewriteRuleTokenStream(adaptor,"token 216");
        RewriteRuleTokenStream stream_COMMENT=new RewriteRuleTokenStream(adaptor,"token COMMENT");
        RewriteRuleTokenStream stream_219=new RewriteRuleTokenStream(adaptor,"token 219");
        RewriteRuleTokenStream stream_188=new RewriteRuleTokenStream(adaptor,"token 188");
        RewriteRuleTokenStream stream_217=new RewriteRuleTokenStream(adaptor,"token 217");
        RewriteRuleTokenStream stream_218=new RewriteRuleTokenStream(adaptor,"token 218");
        RewriteRuleSubtreeStream stream_formal_generics=new RewriteRuleSubtreeStream(adaptor,"rule formal_generics");
        RewriteRuleSubtreeStream stream_class_name=new RewriteRuleSubtreeStream(adaptor,"rule class_name");
        RewriteRuleSubtreeStream stream_class_interface=new RewriteRuleSubtreeStream(adaptor,"rule class_interface");
        try {
            // BON.g:730:9: ( ( ( 'root' c= 'class' c1= class_name ) | ( 'deferred' c= 'class' c2= class_name ) | ( 'effective' c= 'class' c3= class_name ) | (c= 'class' c4= class_name ) ) ( formal_generics )? ( 'reused' )? ( 'persistent' )? ( 'interfaced' )? ( COMMENT )? ( class_interface )? -> ^( CLASS[$c] ( 'root' )? ( 'deferred' )? ( 'effective' )? class_name ( formal_generics )? ( 'reused' )? ( 'persistent' )? ( 'interfaced' )? ( COMMENT )? ( class_interface )? ) )
            // BON.g:730:12: ( ( 'root' c= 'class' c1= class_name ) | ( 'deferred' c= 'class' c2= class_name ) | ( 'effective' c= 'class' c3= class_name ) | (c= 'class' c4= class_name ) ) ( formal_generics )? ( 'reused' )? ( 'persistent' )? ( 'interfaced' )? ( COMMENT )? ( class_interface )?
            {
            // BON.g:730:12: ( ( 'root' c= 'class' c1= class_name ) | ( 'deferred' c= 'class' c2= class_name ) | ( 'effective' c= 'class' c3= class_name ) | (c= 'class' c4= class_name ) )
            int alt70=4;
            switch ( input.LA(1) ) {
            case 217:
                {
                alt70=1;
                }
                break;
            case 218:
                {
                alt70=2;
                }
                break;
            case 219:
                {
                alt70=3;
                }
                break;
            case 188:
                {
                alt70=4;
                }
                break;
            default:
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("730:12: ( ( 'root' c= 'class' c1= class_name ) | ( 'deferred' c= 'class' c2= class_name ) | ( 'effective' c= 'class' c3= class_name ) | (c= 'class' c4= class_name ) )", 70, 0, input);

                throw nvae;
            }

            switch (alt70) {
                case 1 :
                    // BON.g:730:15: ( 'root' c= 'class' c1= class_name )
                    {
                    // BON.g:730:15: ( 'root' c= 'class' c1= class_name )
                    // BON.g:730:17: 'root' c= 'class' c1= class_name
                    {
                    string_literal123=(Token)input.LT(1);
                    match(input,217,FOLLOW_217_in_classX9917); if (failed) return retval;
                    if ( backtracking==0 ) stream_217.add(string_literal123);

                    c=(Token)input.LT(1);
                    match(input,188,FOLLOW_188_in_classX9921); if (failed) return retval;
                    if ( backtracking==0 ) stream_188.add(c);

                    pushFollow(FOLLOW_class_name_in_classX9925);
                    c1=class_name();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_class_name.add(c1.getTree());
                    if ( backtracking==0 ) {
                       getTI().addClass(input.toString(c1.start,c1.stop), getSLoc(c), "root"); getContext().enterClass(input.toString(c1.start,c1.stop)); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // BON.g:731:9: ( 'deferred' c= 'class' c2= class_name )
                    {
                    // BON.g:731:9: ( 'deferred' c= 'class' c2= class_name )
                    // BON.g:731:11: 'deferred' c= 'class' c2= class_name
                    {
                    string_literal124=(Token)input.LT(1);
                    match(input,218,FOLLOW_218_in_classX9951); if (failed) return retval;
                    if ( backtracking==0 ) stream_218.add(string_literal124);

                    c=(Token)input.LT(1);
                    match(input,188,FOLLOW_188_in_classX9955); if (failed) return retval;
                    if ( backtracking==0 ) stream_188.add(c);

                    pushFollow(FOLLOW_class_name_in_classX9959);
                    c2=class_name();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_class_name.add(c2.getTree());
                    if ( backtracking==0 ) {
                       getTI().addClass(input.toString(c2.start,c2.stop), getSLoc(c), "deferred"); getContext().enterClass(input.toString(c2.start,c2.stop)); 
                    }

                    }


                    }
                    break;
                case 3 :
                    // BON.g:732:9: ( 'effective' c= 'class' c3= class_name )
                    {
                    // BON.g:732:9: ( 'effective' c= 'class' c3= class_name )
                    // BON.g:732:11: 'effective' c= 'class' c3= class_name
                    {
                    string_literal125=(Token)input.LT(1);
                    match(input,219,FOLLOW_219_in_classX9978); if (failed) return retval;
                    if ( backtracking==0 ) stream_219.add(string_literal125);

                    c=(Token)input.LT(1);
                    match(input,188,FOLLOW_188_in_classX9982); if (failed) return retval;
                    if ( backtracking==0 ) stream_188.add(c);

                    pushFollow(FOLLOW_class_name_in_classX9986);
                    c3=class_name();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_class_name.add(c3.getTree());
                    if ( backtracking==0 ) {
                       getTI().addClass(input.toString(c3.start,c3.stop), getSLoc(c), "effective"); getContext().enterClass(input.toString(c3.start,c3.stop)); 
                    }

                    }


                    }
                    break;
                case 4 :
                    // BON.g:733:9: (c= 'class' c4= class_name )
                    {
                    // BON.g:733:9: (c= 'class' c4= class_name )
                    // BON.g:733:11: c= 'class' c4= class_name
                    {
                    c=(Token)input.LT(1);
                    match(input,188,FOLLOW_188_in_classX10005); if (failed) return retval;
                    if ( backtracking==0 ) stream_188.add(c);

                    pushFollow(FOLLOW_class_name_in_classX10009);
                    c4=class_name();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_class_name.add(c4.getTree());
                    if ( backtracking==0 ) {
                       getTI().addClass(input.toString(c4.start,c4.stop), getSLoc(c), null); getContext().enterClass(input.toString(c4.start,c4.stop)); 
                    }

                    }


                    }
                    break;

            }

            // BON.g:735:12: ( formal_generics )?
            int alt71=2;
            int LA71_0 = input.LA(1);

            if ( (LA71_0==228) ) {
                alt71=1;
            }
            switch (alt71) {
                case 1 :
                    // BON.g:735:13: formal_generics
                    {
                    pushFollow(FOLLOW_formal_generics_in_classX10068);
                    formal_generics126=formal_generics();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_formal_generics.add(formal_generics126.getTree());

                    }
                    break;

            }

            // BON.g:736:12: ( 'reused' )?
            int alt72=2;
            int LA72_0 = input.LA(1);

            if ( (LA72_0==216) ) {
                alt72=1;
            }
            switch (alt72) {
                case 1 :
                    // BON.g:736:13: 'reused'
                    {
                    string_literal127=(Token)input.LT(1);
                    match(input,216,FOLLOW_216_in_classX10084); if (failed) return retval;
                    if ( backtracking==0 ) stream_216.add(string_literal127);


                    }
                    break;

            }

            // BON.g:737:12: ( 'persistent' )?
            int alt73=2;
            int LA73_0 = input.LA(1);

            if ( (LA73_0==220) ) {
                alt73=1;
            }
            switch (alt73) {
                case 1 :
                    // BON.g:737:13: 'persistent'
                    {
                    string_literal128=(Token)input.LT(1);
                    match(input,220,FOLLOW_220_in_classX10101); if (failed) return retval;
                    if ( backtracking==0 ) stream_220.add(string_literal128);


                    }
                    break;

            }

            // BON.g:738:12: ( 'interfaced' )?
            int alt74=2;
            int LA74_0 = input.LA(1);

            if ( (LA74_0==221) ) {
                alt74=1;
            }
            switch (alt74) {
                case 1 :
                    // BON.g:738:13: 'interfaced'
                    {
                    string_literal129=(Token)input.LT(1);
                    match(input,221,FOLLOW_221_in_classX10120); if (failed) return retval;
                    if ( backtracking==0 ) stream_221.add(string_literal129);


                    }
                    break;

            }

            // BON.g:738:28: ( COMMENT )?
            int alt75=2;
            int LA75_0 = input.LA(1);

            if ( (LA75_0==COMMENT) ) {
                alt75=1;
            }
            switch (alt75) {
                case 1 :
                    // BON.g:738:29: COMMENT
                    {
                    COMMENT130=(Token)input.LT(1);
                    match(input,COMMENT,FOLLOW_COMMENT_in_classX10125); if (failed) return retval;
                    if ( backtracking==0 ) stream_COMMENT.add(COMMENT130);


                    }
                    break;

            }

            // BON.g:739:12: ( class_interface )?
            int alt76=2;
            int LA76_0 = input.LA(1);

            if ( (LA76_0==192||LA76_0==200||LA76_0==234) ) {
                alt76=1;
            }
            switch (alt76) {
                case 1 :
                    // BON.g:739:13: class_interface
                    {
                    pushFollow(FOLLOW_class_interface_in_classX10141);
                    class_interface131=class_interface();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_class_interface.add(class_interface131.getTree());

                    }
                    break;

            }

            if ( backtracking==0 ) {
               getContext().leaveClass(); 
            }

            // AST REWRITE
            // elements: COMMENT, formal_generics, class_interface, 219, 220, 216, 217, class_name, 221, 218
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 741:10: -> ^( CLASS[$c] ( 'root' )? ( 'deferred' )? ( 'effective' )? class_name ( formal_generics )? ( 'reused' )? ( 'persistent' )? ( 'interfaced' )? ( COMMENT )? ( class_interface )? )
            {
                // BON.g:742:10: ^( CLASS[$c] ( 'root' )? ( 'deferred' )? ( 'effective' )? class_name ( formal_generics )? ( 'reused' )? ( 'persistent' )? ( 'interfaced' )? ( COMMENT )? ( class_interface )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLASS, c), root_1);

                // BON.g:744:12: ( 'root' )?
                if ( stream_217.hasNext() ) {
                    adaptor.addChild(root_1, stream_217.next());

                }
                stream_217.reset();
                // BON.g:744:22: ( 'deferred' )?
                if ( stream_218.hasNext() ) {
                    adaptor.addChild(root_1, stream_218.next());

                }
                stream_218.reset();
                // BON.g:744:36: ( 'effective' )?
                if ( stream_219.hasNext() ) {
                    adaptor.addChild(root_1, stream_219.next());

                }
                stream_219.reset();
                adaptor.addChild(root_1, stream_class_name.next());
                // BON.g:745:23: ( formal_generics )?
                if ( stream_formal_generics.hasNext() ) {
                    adaptor.addChild(root_1, stream_formal_generics.next());

                }
                stream_formal_generics.reset();
                // BON.g:746:12: ( 'reused' )?
                if ( stream_216.hasNext() ) {
                    adaptor.addChild(root_1, stream_216.next());

                }
                stream_216.reset();
                // BON.g:746:24: ( 'persistent' )?
                if ( stream_220.hasNext() ) {
                    adaptor.addChild(root_1, stream_220.next());

                }
                stream_220.reset();
                // BON.g:746:41: ( 'interfaced' )?
                if ( stream_221.hasNext() ) {
                    adaptor.addChild(root_1, stream_221.next());

                }
                stream_221.reset();
                // BON.g:746:57: ( COMMENT )?
                if ( stream_COMMENT.hasNext() ) {
                    adaptor.addChild(root_1, stream_COMMENT.next());

                }
                stream_COMMENT.reset();
                // BON.g:747:12: ( class_interface )?
                if ( stream_class_interface.hasNext() ) {
                    adaptor.addChild(root_1, stream_class_interface.next());

                }
                stream_class_interface.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end classX

    public static class static_relation_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start static_relation
    // BON.g:751:1: static_relation : (ir= inheritance_relation -> ^( STATIC_RELATION[$ir.start] inheritance_relation ) | cr= client_relation -> ^( STATIC_RELATION[$cr.start] client_relation ) );
    public final static_relation_return static_relation() throws RecognitionException {
        static_relation_return retval = new static_relation_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        inheritance_relation_return ir = null;

        client_relation_return cr = null;


        RewriteRuleSubtreeStream stream_client_relation=new RewriteRuleSubtreeStream(adaptor,"rule client_relation");
        RewriteRuleSubtreeStream stream_inheritance_relation=new RewriteRuleSubtreeStream(adaptor,"rule inheritance_relation");
        try {
            // BON.g:751:18: (ir= inheritance_relation -> ^( STATIC_RELATION[$ir.start] inheritance_relation ) | cr= client_relation -> ^( STATIC_RELATION[$cr.start] client_relation ) )
            int alt77=2;
            alt77 = dfa77.predict(input);
            switch (alt77) {
                case 1 :
                    // BON.g:751:21: ir= inheritance_relation
                    {
                    pushFollow(FOLLOW_inheritance_relation_in_static_relation10332);
                    ir=inheritance_relation();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_inheritance_relation.add(ir.getTree());

                    // AST REWRITE
                    // elements: inheritance_relation
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 752:19: -> ^( STATIC_RELATION[$ir.start] inheritance_relation )
                    {
                        // BON.g:753:19: ^( STATIC_RELATION[$ir.start] inheritance_relation )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(STATIC_RELATION, ((Token)ir.start)), root_1);

                        adaptor.addChild(root_1, stream_inheritance_relation.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:756:21: cr= client_relation
                    {
                    pushFollow(FOLLOW_client_relation_in_static_relation10443);
                    cr=client_relation();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_client_relation.add(cr.getTree());

                    // AST REWRITE
                    // elements: client_relation
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 757:19: -> ^( STATIC_RELATION[$cr.start] client_relation )
                    {
                        // BON.g:758:19: ^( STATIC_RELATION[$cr.start] client_relation )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(STATIC_RELATION, ((Token)cr.start)), root_1);

                        adaptor.addChild(root_1, stream_client_relation.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end static_relation

    public static class inheritance_relation_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start inheritance_relation
    // BON.g:763:1: inheritance_relation : c= child 'inherit' ( '{' multiplicity '}' )? parent ( semantic_label )? -> ^( INHERITENCE_RELATION[$c.start] child ( multiplicity )? parent ( semantic_label )? ) ;
    public final inheritance_relation_return inheritance_relation() throws RecognitionException {
        inheritance_relation_return retval = new inheritance_relation_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal132=null;
        Token char_literal133=null;
        Token char_literal135=null;
        child_return c = null;

        multiplicity_return multiplicity134 = null;

        parent_return parent136 = null;

        semantic_label_return semantic_label137 = null;


        CommonTree string_literal132_tree=null;
        CommonTree char_literal133_tree=null;
        CommonTree char_literal135_tree=null;
        RewriteRuleTokenStream stream_222=new RewriteRuleTokenStream(adaptor,"token 222");
        RewriteRuleTokenStream stream_223=new RewriteRuleTokenStream(adaptor,"token 223");
        RewriteRuleTokenStream stream_200=new RewriteRuleTokenStream(adaptor,"token 200");
        RewriteRuleSubtreeStream stream_child=new RewriteRuleSubtreeStream(adaptor,"rule child");
        RewriteRuleSubtreeStream stream_semantic_label=new RewriteRuleSubtreeStream(adaptor,"rule semantic_label");
        RewriteRuleSubtreeStream stream_parent=new RewriteRuleSubtreeStream(adaptor,"rule parent");
        RewriteRuleSubtreeStream stream_multiplicity=new RewriteRuleSubtreeStream(adaptor,"rule multiplicity");
        try {
            // BON.g:765:23: (c= child 'inherit' ( '{' multiplicity '}' )? parent ( semantic_label )? -> ^( INHERITENCE_RELATION[$c.start] child ( multiplicity )? parent ( semantic_label )? ) )
            // BON.g:765:26: c= child 'inherit' ( '{' multiplicity '}' )? parent ( semantic_label )?
            {
            pushFollow(FOLLOW_child_in_inheritance_relation10582);
            c=child();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_child.add(c.getTree());
            string_literal132=(Token)input.LT(1);
            match(input,200,FOLLOW_200_in_inheritance_relation10584); if (failed) return retval;
            if ( backtracking==0 ) stream_200.add(string_literal132);

            // BON.g:765:44: ( '{' multiplicity '}' )?
            int alt78=2;
            int LA78_0 = input.LA(1);

            if ( (LA78_0==222) ) {
                alt78=1;
            }
            switch (alt78) {
                case 1 :
                    // BON.g:765:45: '{' multiplicity '}'
                    {
                    char_literal133=(Token)input.LT(1);
                    match(input,222,FOLLOW_222_in_inheritance_relation10587); if (failed) return retval;
                    if ( backtracking==0 ) stream_222.add(char_literal133);

                    pushFollow(FOLLOW_multiplicity_in_inheritance_relation10589);
                    multiplicity134=multiplicity();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_multiplicity.add(multiplicity134.getTree());
                    char_literal135=(Token)input.LT(1);
                    match(input,223,FOLLOW_223_in_inheritance_relation10591); if (failed) return retval;
                    if ( backtracking==0 ) stream_223.add(char_literal135);


                    }
                    break;

            }

            pushFollow(FOLLOW_parent_in_inheritance_relation10621);
            parent136=parent();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_parent.add(parent136.getTree());
            // BON.g:766:33: ( semantic_label )?
            int alt79=2;
            int LA79_0 = input.LA(1);

            if ( (LA79_0==MANIFEST_STRING) ) {
                alt79=1;
            }
            switch (alt79) {
                case 1 :
                    // BON.g:766:34: semantic_label
                    {
                    pushFollow(FOLLOW_semantic_label_in_inheritance_relation10624);
                    semantic_label137=semantic_label();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_semantic_label.add(semantic_label137.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: parent, semantic_label, child, multiplicity
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 767:24: -> ^( INHERITENCE_RELATION[$c.start] child ( multiplicity )? parent ( semantic_label )? )
            {
                // BON.g:768:24: ^( INHERITENCE_RELATION[$c.start] child ( multiplicity )? parent ( semantic_label )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INHERITENCE_RELATION, ((Token)c.start)), root_1);

                adaptor.addChild(root_1, stream_child.next());
                // BON.g:770:32: ( multiplicity )?
                if ( stream_multiplicity.hasNext() ) {
                    adaptor.addChild(root_1, stream_multiplicity.next());

                }
                stream_multiplicity.reset();
                adaptor.addChild(root_1, stream_parent.next());
                // BON.g:771:33: ( semantic_label )?
                if ( stream_semantic_label.hasNext() ) {
                    adaptor.addChild(root_1, stream_semantic_label.next());

                }
                stream_semantic_label.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end inheritance_relation

    public static class client_relation_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start client_relation
    // BON.g:775:1: client_relation : c= client 'client' ( client_entities )? ( type_mark )? supplier ( semantic_label )? -> ^( CLIENT_RELATION[$c.start] client ( client_entities )? ( type_mark )? supplier ( semantic_label )? ) ;
    public final client_relation_return client_relation() throws RecognitionException {
        client_relation_return retval = new client_relation_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal138=null;
        client_return c = null;

        client_entities_return client_entities139 = null;

        type_mark_return type_mark140 = null;

        supplier_return supplier141 = null;

        semantic_label_return semantic_label142 = null;


        CommonTree string_literal138_tree=null;
        RewriteRuleTokenStream stream_224=new RewriteRuleTokenStream(adaptor,"token 224");
        RewriteRuleSubtreeStream stream_client=new RewriteRuleSubtreeStream(adaptor,"rule client");
        RewriteRuleSubtreeStream stream_semantic_label=new RewriteRuleSubtreeStream(adaptor,"rule semantic_label");
        RewriteRuleSubtreeStream stream_type_mark=new RewriteRuleSubtreeStream(adaptor,"rule type_mark");
        RewriteRuleSubtreeStream stream_client_entities=new RewriteRuleSubtreeStream(adaptor,"rule client_entities");
        RewriteRuleSubtreeStream stream_supplier=new RewriteRuleSubtreeStream(adaptor,"rule supplier");
        try {
            // BON.g:775:18: (c= client 'client' ( client_entities )? ( type_mark )? supplier ( semantic_label )? -> ^( CLIENT_RELATION[$c.start] client ( client_entities )? ( type_mark )? supplier ( semantic_label )? ) )
            // BON.g:775:21: c= client 'client' ( client_entities )? ( type_mark )? supplier ( semantic_label )?
            {
            pushFollow(FOLLOW_client_in_client_relation10852);
            c=client();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_client.add(c.getTree());
            string_literal138=(Token)input.LT(1);
            match(input,224,FOLLOW_224_in_client_relation10854); if (failed) return retval;
            if ( backtracking==0 ) stream_224.add(string_literal138);

            // BON.g:775:39: ( client_entities )?
            int alt80=2;
            int LA80_0 = input.LA(1);

            if ( (LA80_0==222) ) {
                alt80=1;
            }
            switch (alt80) {
                case 1 :
                    // BON.g:775:40: client_entities
                    {
                    pushFollow(FOLLOW_client_entities_in_client_relation10857);
                    client_entities139=client_entities();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_client_entities.add(client_entities139.getTree());

                    }
                    break;

            }

            // BON.g:775:58: ( type_mark )?
            int alt81=2;
            int LA81_0 = input.LA(1);

            if ( (LA81_0==196||LA81_0==231) ) {
                alt81=1;
            }
            switch (alt81) {
                case 1 :
                    // BON.g:775:59: type_mark
                    {
                    pushFollow(FOLLOW_type_mark_in_client_relation10862);
                    type_mark140=type_mark();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_type_mark.add(type_mark140.getTree());

                    }
                    break;

            }

            pushFollow(FOLLOW_supplier_in_client_relation10887);
            supplier141=supplier();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_supplier.add(supplier141.getTree());
            // BON.g:776:30: ( semantic_label )?
            int alt82=2;
            int LA82_0 = input.LA(1);

            if ( (LA82_0==MANIFEST_STRING) ) {
                alt82=1;
            }
            switch (alt82) {
                case 1 :
                    // BON.g:776:31: semantic_label
                    {
                    pushFollow(FOLLOW_semantic_label_in_client_relation10890);
                    semantic_label142=semantic_label();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_semantic_label.add(semantic_label142.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: type_mark, semantic_label, supplier, client, client_entities
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 777:19: -> ^( CLIENT_RELATION[$c.start] client ( client_entities )? ( type_mark )? supplier ( semantic_label )? )
            {
                // BON.g:778:19: ^( CLIENT_RELATION[$c.start] client ( client_entities )? ( type_mark )? supplier ( semantic_label )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLIENT_RELATION, ((Token)c.start)), root_1);

                adaptor.addChild(root_1, stream_client.next());
                // BON.g:780:28: ( client_entities )?
                if ( stream_client_entities.hasNext() ) {
                    adaptor.addChild(root_1, stream_client_entities.next());

                }
                stream_client_entities.reset();
                // BON.g:780:47: ( type_mark )?
                if ( stream_type_mark.hasNext() ) {
                    adaptor.addChild(root_1, stream_type_mark.next());

                }
                stream_type_mark.reset();
                adaptor.addChild(root_1, stream_supplier.next());
                // BON.g:781:30: ( semantic_label )?
                if ( stream_semantic_label.hasNext() ) {
                    adaptor.addChild(root_1, stream_semantic_label.next());

                }
                stream_semantic_label.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end client_relation

    public static class client_entities_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start client_entities
    // BON.g:785:1: client_entities : a= '{' client_entity_expression '}' -> ^( CLIENT_ENTITIES[$a] client_entity_expression ) ;
    public final client_entities_return client_entities() throws RecognitionException {
        client_entities_return retval = new client_entities_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token a=null;
        Token char_literal144=null;
        client_entity_expression_return client_entity_expression143 = null;


        CommonTree a_tree=null;
        CommonTree char_literal144_tree=null;
        RewriteRuleTokenStream stream_222=new RewriteRuleTokenStream(adaptor,"token 222");
        RewriteRuleTokenStream stream_223=new RewriteRuleTokenStream(adaptor,"token 223");
        RewriteRuleSubtreeStream stream_client_entity_expression=new RewriteRuleSubtreeStream(adaptor,"rule client_entity_expression");
        try {
            // BON.g:785:18: (a= '{' client_entity_expression '}' -> ^( CLIENT_ENTITIES[$a] client_entity_expression ) )
            // BON.g:785:21: a= '{' client_entity_expression '}'
            {
            a=(Token)input.LT(1);
            match(input,222,FOLLOW_222_in_client_entities11085); if (failed) return retval;
            if ( backtracking==0 ) stream_222.add(a);

            pushFollow(FOLLOW_client_entity_expression_in_client_entities11087);
            client_entity_expression143=client_entity_expression();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_client_entity_expression.add(client_entity_expression143.getTree());
            char_literal144=(Token)input.LT(1);
            match(input,223,FOLLOW_223_in_client_entities11089); if (failed) return retval;
            if ( backtracking==0 ) stream_223.add(char_literal144);


            // AST REWRITE
            // elements: client_entity_expression
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 786:19: -> ^( CLIENT_ENTITIES[$a] client_entity_expression )
            {
                // BON.g:787:19: ^( CLIENT_ENTITIES[$a] client_entity_expression )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLIENT_ENTITIES, a), root_1);

                adaptor.addChild(root_1, stream_client_entity_expression.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end client_entities

    public static class client_entity_expression_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start client_entity_expression
    // BON.g:793:1: client_entity_expression : (cel= client_entity_list -> ^( CLIENT_ENTITY_EXPRESSION[$cel.start] client_entity_list ) | m= multiplicity -> ^( CLIENT_ENTITY_EXPRESSION[$m.start] multiplicity ) );
    public final client_entity_expression_return client_entity_expression() throws RecognitionException {
        client_entity_expression_return retval = new client_entity_expression_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        client_entity_list_return cel = null;

        multiplicity_return m = null;


        RewriteRuleSubtreeStream stream_client_entity_list=new RewriteRuleSubtreeStream(adaptor,"rule client_entity_list");
        RewriteRuleSubtreeStream stream_multiplicity=new RewriteRuleSubtreeStream(adaptor,"rule multiplicity");
        try {
            // BON.g:793:27: (cel= client_entity_list -> ^( CLIENT_ENTITY_EXPRESSION[$cel.start] client_entity_list ) | m= multiplicity -> ^( CLIENT_ENTITY_EXPRESSION[$m.start] multiplicity ) )
            int alt83=2;
            int LA83_0 = input.LA(1);

            if ( (LA83_0==IDENTIFIER||LA83_0==225||(LA83_0>=227 && LA83_0<=228)||LA83_0==230||LA83_0==239||LA83_0==241) ) {
                alt83=1;
            }
            else if ( (LA83_0==INTEGER) ) {
                alt83=2;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("793:1: client_entity_expression : (cel= client_entity_list -> ^( CLIENT_ENTITY_EXPRESSION[$cel.start] client_entity_list ) | m= multiplicity -> ^( CLIENT_ENTITY_EXPRESSION[$m.start] multiplicity ) );", 83, 0, input);

                throw nvae;
            }
            switch (alt83) {
                case 1 :
                    // BON.g:793:30: cel= client_entity_list
                    {
                    pushFollow(FOLLOW_client_entity_list_in_client_entity_expression11243);
                    cel=client_entity_list();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_client_entity_list.add(cel.getTree());

                    // AST REWRITE
                    // elements: client_entity_list
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 794:28: -> ^( CLIENT_ENTITY_EXPRESSION[$cel.start] client_entity_list )
                    {
                        // BON.g:795:28: ^( CLIENT_ENTITY_EXPRESSION[$cel.start] client_entity_list )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLIENT_ENTITY_EXPRESSION, ((Token)cel.start)), root_1);

                        adaptor.addChild(root_1, stream_client_entity_list.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:798:30: m= multiplicity
                    {
                    pushFollow(FOLLOW_multiplicity_in_client_entity_expression11399);
                    m=multiplicity();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_multiplicity.add(m.getTree());

                    // AST REWRITE
                    // elements: multiplicity
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 799:28: -> ^( CLIENT_ENTITY_EXPRESSION[$m.start] multiplicity )
                    {
                        // BON.g:800:28: ^( CLIENT_ENTITY_EXPRESSION[$m.start] multiplicity )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLIENT_ENTITY_EXPRESSION, ((Token)m.start)), root_1);

                        adaptor.addChild(root_1, stream_multiplicity.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end client_entity_expression

    public static class client_entity_list_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start client_entity_list
    // BON.g:805:1: client_entity_list : ce= client_entity ( ',' client_entity )* -> ^( CLIENT_ENTITY_LIST[$ce.start] ( client_entity )+ ) ;
    public final client_entity_list_return client_entity_list() throws RecognitionException {
        client_entity_list_return retval = new client_entity_list_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal145=null;
        client_entity_return ce = null;

        client_entity_return client_entity146 = null;


        CommonTree char_literal145_tree=null;
        RewriteRuleTokenStream stream_197=new RewriteRuleTokenStream(adaptor,"token 197");
        RewriteRuleSubtreeStream stream_client_entity=new RewriteRuleSubtreeStream(adaptor,"rule client_entity");
        try {
            // BON.g:805:21: (ce= client_entity ( ',' client_entity )* -> ^( CLIENT_ENTITY_LIST[$ce.start] ( client_entity )+ ) )
            // BON.g:805:24: ce= client_entity ( ',' client_entity )*
            {
            pushFollow(FOLLOW_client_entity_in_client_entity_list11587);
            ce=client_entity();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_client_entity.add(ce.getTree());
            // BON.g:805:41: ( ',' client_entity )*
            loop84:
            do {
                int alt84=2;
                int LA84_0 = input.LA(1);

                if ( (LA84_0==197) ) {
                    alt84=1;
                }


                switch (alt84) {
            	case 1 :
            	    // BON.g:805:42: ',' client_entity
            	    {
            	    char_literal145=(Token)input.LT(1);
            	    match(input,197,FOLLOW_197_in_client_entity_list11590); if (failed) return retval;
            	    if ( backtracking==0 ) stream_197.add(char_literal145);

            	    pushFollow(FOLLOW_client_entity_in_client_entity_list11592);
            	    client_entity146=client_entity();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_client_entity.add(client_entity146.getTree());

            	    }
            	    break;

            	default :
            	    break loop84;
                }
            } while (true);


            // AST REWRITE
            // elements: client_entity
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 806:22: -> ^( CLIENT_ENTITY_LIST[$ce.start] ( client_entity )+ )
            {
                // BON.g:807:22: ^( CLIENT_ENTITY_LIST[$ce.start] ( client_entity )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLIENT_ENTITY_LIST, ((Token)ce.start)), root_1);

                if ( !(stream_client_entity.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_client_entity.hasNext() ) {
                    adaptor.addChild(root_1, stream_client_entity.next());

                }
                stream_client_entity.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end client_entity_list

    public static class client_entity_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start client_entity
    // BON.g:816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );
    public final client_entity_return client_entity() throws RecognitionException {
        client_entity_return retval = new client_entity_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        prefix_return prefix147 = null;

        infix_return infix148 = null;

        supplier_indirection_return supplier_indirection149 = null;

        parent_indirection_return parent_indirection150 = null;


        RewriteRuleSubtreeStream stream_supplier_indirection=new RewriteRuleSubtreeStream(adaptor,"rule supplier_indirection");
        RewriteRuleSubtreeStream stream_infix=new RewriteRuleSubtreeStream(adaptor,"rule infix");
        RewriteRuleSubtreeStream stream_prefix=new RewriteRuleSubtreeStream(adaptor,"rule prefix");
        RewriteRuleSubtreeStream stream_parent_indirection=new RewriteRuleSubtreeStream(adaptor,"rule parent_indirection");
        try {
            // BON.g:816:16: ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) )
            int alt85=4;
            switch ( input.LA(1) ) {
            case 239:
                {
                int LA85_1 = input.LA(2);

                if ( (LA85_1==240) ) {
                    switch ( input.LA(3) ) {
                    case 268:
                        {
                        int LA85_7 = input.LA(4);

                        if ( (LA85_7==240) ) {
                            int LA85_26 = input.LA(5);

                            if ( (LA85_26==196) ) {
                                alt85=3;
                            }
                            else if ( (LA85_26==197||LA85_26==223) ) {
                                alt85=1;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 26, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 7, input);

                            throw nvae;
                        }
                        }
                        break;
                    case 269:
                        {
                        int LA85_8 = input.LA(4);

                        if ( (LA85_8==240) ) {
                            int LA85_26 = input.LA(5);

                            if ( (LA85_26==196) ) {
                                alt85=3;
                            }
                            else if ( (LA85_26==197||LA85_26==223) ) {
                                alt85=1;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 26, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 8, input);

                            throw nvae;
                        }
                        }
                        break;
                    case 270:
                        {
                        int LA85_9 = input.LA(4);

                        if ( (LA85_9==240) ) {
                            int LA85_26 = input.LA(5);

                            if ( (LA85_26==196) ) {
                                alt85=3;
                            }
                            else if ( (LA85_26==197||LA85_26==223) ) {
                                alt85=1;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 26, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 9, input);

                            throw nvae;
                        }
                        }
                        break;
                    case 263:
                    case 264:
                        {
                        int LA85_10 = input.LA(4);

                        if ( (LA85_10==240) ) {
                            int LA85_26 = input.LA(5);

                            if ( (LA85_26==196) ) {
                                alt85=3;
                            }
                            else if ( (LA85_26==197||LA85_26==223) ) {
                                alt85=1;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 26, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 10, input);

                            throw nvae;
                        }
                        }
                        break;
                    default:
                        if (backtracking>0) {failed=true; return retval;}
                        NoViableAltException nvae =
                            new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 5, input);

                        throw nvae;
                    }

                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 1, input);

                    throw nvae;
                }
                }
                break;
            case 241:
                {
                int LA85_2 = input.LA(2);

                if ( (LA85_2==240) ) {
                    switch ( input.LA(3) ) {
                    case 263:
                    case 264:
                        {
                        int LA85_11 = input.LA(4);

                        if ( (LA85_11==240) ) {
                            int LA85_27 = input.LA(5);

                            if ( (LA85_27==197||LA85_27==223) ) {
                                alt85=2;
                            }
                            else if ( (LA85_27==196) ) {
                                alt85=3;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 27, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 11, input);

                            throw nvae;
                        }
                        }
                        break;
                    case 277:
                    case 278:
                    case 279:
                        {
                        int LA85_12 = input.LA(4);

                        if ( (LA85_12==240) ) {
                            int LA85_27 = input.LA(5);

                            if ( (LA85_27==197||LA85_27==223) ) {
                                alt85=2;
                            }
                            else if ( (LA85_27==196) ) {
                                alt85=3;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 27, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 12, input);

                            throw nvae;
                        }
                        }
                        break;
                    case 271:
                        {
                        int LA85_13 = input.LA(4);

                        if ( (LA85_13==240) ) {
                            int LA85_27 = input.LA(5);

                            if ( (LA85_27==197||LA85_27==223) ) {
                                alt85=2;
                            }
                            else if ( (LA85_27==196) ) {
                                alt85=3;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 27, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 13, input);

                            throw nvae;
                        }
                        }
                        break;
                    case 272:
                        {
                        int LA85_14 = input.LA(4);

                        if ( (LA85_14==240) ) {
                            int LA85_27 = input.LA(5);

                            if ( (LA85_27==197||LA85_27==223) ) {
                                alt85=2;
                            }
                            else if ( (LA85_27==196) ) {
                                alt85=3;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 27, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 14, input);

                            throw nvae;
                        }
                        }
                        break;
                    case 273:
                        {
                        int LA85_15 = input.LA(4);

                        if ( (LA85_15==240) ) {
                            int LA85_27 = input.LA(5);

                            if ( (LA85_27==197||LA85_27==223) ) {
                                alt85=2;
                            }
                            else if ( (LA85_27==196) ) {
                                alt85=3;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 27, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 15, input);

                            throw nvae;
                        }
                        }
                        break;
                    case 274:
                        {
                        int LA85_16 = input.LA(4);

                        if ( (LA85_16==240) ) {
                            int LA85_27 = input.LA(5);

                            if ( (LA85_27==197||LA85_27==223) ) {
                                alt85=2;
                            }
                            else if ( (LA85_27==196) ) {
                                alt85=3;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 27, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 16, input);

                            throw nvae;
                        }
                        }
                        break;
                    case 275:
                        {
                        int LA85_17 = input.LA(4);

                        if ( (LA85_17==240) ) {
                            int LA85_27 = input.LA(5);

                            if ( (LA85_27==197||LA85_27==223) ) {
                                alt85=2;
                            }
                            else if ( (LA85_27==196) ) {
                                alt85=3;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 27, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 17, input);

                            throw nvae;
                        }
                        }
                        break;
                    case 276:
                        {
                        int LA85_18 = input.LA(4);

                        if ( (LA85_18==240) ) {
                            int LA85_27 = input.LA(5);

                            if ( (LA85_27==197||LA85_27==223) ) {
                                alt85=2;
                            }
                            else if ( (LA85_27==196) ) {
                                alt85=3;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 27, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 18, input);

                            throw nvae;
                        }
                        }
                        break;
                    case 246:
                        {
                        int LA85_19 = input.LA(4);

                        if ( (LA85_19==240) ) {
                            int LA85_27 = input.LA(5);

                            if ( (LA85_27==197||LA85_27==223) ) {
                                alt85=2;
                            }
                            else if ( (LA85_27==196) ) {
                                alt85=3;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 27, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 19, input);

                            throw nvae;
                        }
                        }
                        break;
                    case 270:
                        {
                        int LA85_20 = input.LA(4);

                        if ( (LA85_20==246) ) {
                            int LA85_28 = input.LA(5);

                            if ( (LA85_28==240) ) {
                                int LA85_27 = input.LA(6);

                                if ( (LA85_27==197||LA85_27==223) ) {
                                    alt85=2;
                                }
                                else if ( (LA85_27==196) ) {
                                    alt85=3;
                                }
                                else {
                                    if (backtracking>0) {failed=true; return retval;}
                                    NoViableAltException nvae =
                                        new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 27, input);

                                    throw nvae;
                                }
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 28, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 20, input);

                            throw nvae;
                        }
                        }
                        break;
                    case 196:
                        {
                        int LA85_21 = input.LA(4);

                        if ( (LA85_21==240) ) {
                            int LA85_27 = input.LA(5);

                            if ( (LA85_27==197||LA85_27==223) ) {
                                alt85=2;
                            }
                            else if ( (LA85_27==196) ) {
                                alt85=3;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 27, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 21, input);

                            throw nvae;
                        }
                        }
                        break;
                    case MOD_POW_OP:
                        {
                        int LA85_22 = input.LA(4);

                        if ( (LA85_22==240) ) {
                            int LA85_27 = input.LA(5);

                            if ( (LA85_27==197||LA85_27==223) ) {
                                alt85=2;
                            }
                            else if ( (LA85_27==196) ) {
                                alt85=3;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 27, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 22, input);

                            throw nvae;
                        }
                        }
                        break;
                    case 265:
                    case 266:
                    case 267:
                        {
                        int LA85_23 = input.LA(4);

                        if ( (LA85_23==240) ) {
                            int LA85_27 = input.LA(5);

                            if ( (LA85_27==197||LA85_27==223) ) {
                                alt85=2;
                            }
                            else if ( (LA85_27==196) ) {
                                alt85=3;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 27, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 23, input);

                            throw nvae;
                        }
                        }
                        break;
                    case 227:
                        {
                        int LA85_24 = input.LA(4);

                        if ( (LA85_24==240) ) {
                            int LA85_27 = input.LA(5);

                            if ( (LA85_27==197||LA85_27==223) ) {
                                alt85=2;
                            }
                            else if ( (LA85_27==196) ) {
                                alt85=3;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 27, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 24, input);

                            throw nvae;
                        }
                        }
                        break;
                    case 262:
                        {
                        int LA85_25 = input.LA(4);

                        if ( (LA85_25==240) ) {
                            int LA85_27 = input.LA(5);

                            if ( (LA85_27==197||LA85_27==223) ) {
                                alt85=2;
                            }
                            else if ( (LA85_27==196) ) {
                                alt85=3;
                            }
                            else {
                                if (backtracking>0) {failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 27, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (backtracking>0) {failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 25, input);

                            throw nvae;
                        }
                        }
                        break;
                    default:
                        if (backtracking>0) {failed=true; return retval;}
                        NoViableAltException nvae =
                            new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 6, input);

                        throw nvae;
                    }

                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 2, input);

                    throw nvae;
                }
                }
                break;
            case IDENTIFIER:
            case 225:
            case 228:
            case 230:
                {
                alt85=3;
                }
                break;
            case 227:
                {
                alt85=4;
                }
                break;
            default:
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("816:1: client_entity : ( prefix -> ^( CLIENT_ENTITY prefix ) | infix -> ^( CLIENT_ENTITY infix ) | supplier_indirection -> ^( CLIENT_ENTITY supplier_indirection ) | parent_indirection -> ^( CLIENT_ENTITY parent_indirection ) );", 85, 0, input);

                throw nvae;
            }

            switch (alt85) {
                case 1 :
                    // BON.g:816:21: prefix
                    {
                    pushFollow(FOLLOW_prefix_in_client_entity11754);
                    prefix147=prefix();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_prefix.add(prefix147.getTree());

                    // AST REWRITE
                    // elements: prefix
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 817:19: -> ^( CLIENT_ENTITY prefix )
                    {
                        // BON.g:818:19: ^( CLIENT_ENTITY prefix )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLIENT_ENTITY, "CLIENT_ENTITY"), root_1);

                        adaptor.addChild(root_1, stream_prefix.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:821:21: infix
                    {
                    pushFollow(FOLLOW_infix_in_client_entity11861);
                    infix148=infix();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_infix.add(infix148.getTree());

                    // AST REWRITE
                    // elements: infix
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 822:19: -> ^( CLIENT_ENTITY infix )
                    {
                        // BON.g:823:19: ^( CLIENT_ENTITY infix )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLIENT_ENTITY, "CLIENT_ENTITY"), root_1);

                        adaptor.addChild(root_1, stream_infix.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 3 :
                    // BON.g:826:21: supplier_indirection
                    {
                    pushFollow(FOLLOW_supplier_indirection_in_client_entity11968);
                    supplier_indirection149=supplier_indirection();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_supplier_indirection.add(supplier_indirection149.getTree());

                    // AST REWRITE
                    // elements: supplier_indirection
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 827:19: -> ^( CLIENT_ENTITY supplier_indirection )
                    {
                        // BON.g:828:19: ^( CLIENT_ENTITY supplier_indirection )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLIENT_ENTITY, "CLIENT_ENTITY"), root_1);

                        adaptor.addChild(root_1, stream_supplier_indirection.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 4 :
                    // BON.g:831:21: parent_indirection
                    {
                    pushFollow(FOLLOW_parent_indirection_in_client_entity12076);
                    parent_indirection150=parent_indirection();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_parent_indirection.add(parent_indirection150.getTree());

                    // AST REWRITE
                    // elements: parent_indirection
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 832:19: -> ^( CLIENT_ENTITY parent_indirection )
                    {
                        // BON.g:833:19: ^( CLIENT_ENTITY parent_indirection )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLIENT_ENTITY, "CLIENT_ENTITY"), root_1);

                        adaptor.addChild(root_1, stream_parent_indirection.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end client_entity

    public static class supplier_indirection_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start supplier_indirection
    // BON.g:838:1: supplier_indirection : ( indirection_feature_part ':' )? generic_indirection -> ^( SUPPLIER_INDIRECTION ( indirection_feature_part )? generic_indirection ) ;
    public final supplier_indirection_return supplier_indirection() throws RecognitionException {
        supplier_indirection_return retval = new supplier_indirection_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal152=null;
        indirection_feature_part_return indirection_feature_part151 = null;

        generic_indirection_return generic_indirection153 = null;


        CommonTree char_literal152_tree=null;
        RewriteRuleTokenStream stream_196=new RewriteRuleTokenStream(adaptor,"token 196");
        RewriteRuleSubtreeStream stream_indirection_feature_part=new RewriteRuleSubtreeStream(adaptor,"rule indirection_feature_part");
        RewriteRuleSubtreeStream stream_generic_indirection=new RewriteRuleSubtreeStream(adaptor,"rule generic_indirection");
        try {
            // BON.g:838:23: ( ( indirection_feature_part ':' )? generic_indirection -> ^( SUPPLIER_INDIRECTION ( indirection_feature_part )? generic_indirection ) )
            // BON.g:838:26: ( indirection_feature_part ':' )? generic_indirection
            {
            // BON.g:838:26: ( indirection_feature_part ':' )?
            int alt86=2;
            int LA86_0 = input.LA(1);

            if ( (LA86_0==IDENTIFIER) ) {
                int LA86_1 = input.LA(2);

                if ( (LA86_1==196) ) {
                    alt86=1;
                }
            }
            else if ( (LA86_0==225||LA86_0==239||LA86_0==241) ) {
                alt86=1;
            }
            switch (alt86) {
                case 1 :
                    // BON.g:838:27: indirection_feature_part ':'
                    {
                    pushFollow(FOLLOW_indirection_feature_part_in_supplier_indirection12204);
                    indirection_feature_part151=indirection_feature_part();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_indirection_feature_part.add(indirection_feature_part151.getTree());
                    char_literal152=(Token)input.LT(1);
                    match(input,196,FOLLOW_196_in_supplier_indirection12206); if (failed) return retval;
                    if ( backtracking==0 ) stream_196.add(char_literal152);


                    }
                    break;

            }

            pushFollow(FOLLOW_generic_indirection_in_supplier_indirection12210);
            generic_indirection153=generic_indirection();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_generic_indirection.add(generic_indirection153.getTree());

            // AST REWRITE
            // elements: indirection_feature_part, generic_indirection
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 839:24: -> ^( SUPPLIER_INDIRECTION ( indirection_feature_part )? generic_indirection )
            {
                // BON.g:840:24: ^( SUPPLIER_INDIRECTION ( indirection_feature_part )? generic_indirection )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(SUPPLIER_INDIRECTION, "SUPPLIER_INDIRECTION"), root_1);

                // BON.g:841:47: ( indirection_feature_part )?
                if ( stream_indirection_feature_part.hasNext() ) {
                    adaptor.addChild(root_1, stream_indirection_feature_part.next());

                }
                stream_indirection_feature_part.reset();
                adaptor.addChild(root_1, stream_generic_indirection.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end supplier_indirection

    public static class indirection_feature_part_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start indirection_feature_part
    // BON.g:845:1: indirection_feature_part : ( feature_name -> ^( INDIRECTION_FEATURE_PART feature_name ) | indirection_feature_list -> ^( INDIRECTION_FEATURE_PART indirection_feature_list ) );
    public final indirection_feature_part_return indirection_feature_part() throws RecognitionException {
        indirection_feature_part_return retval = new indirection_feature_part_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        feature_name_return feature_name154 = null;

        indirection_feature_list_return indirection_feature_list155 = null;


        RewriteRuleSubtreeStream stream_feature_name=new RewriteRuleSubtreeStream(adaptor,"rule feature_name");
        RewriteRuleSubtreeStream stream_indirection_feature_list=new RewriteRuleSubtreeStream(adaptor,"rule indirection_feature_list");
        try {
            // BON.g:845:27: ( feature_name -> ^( INDIRECTION_FEATURE_PART feature_name ) | indirection_feature_list -> ^( INDIRECTION_FEATURE_PART indirection_feature_list ) )
            int alt87=2;
            int LA87_0 = input.LA(1);

            if ( (LA87_0==IDENTIFIER||LA87_0==239||LA87_0==241) ) {
                alt87=1;
            }
            else if ( (LA87_0==225) ) {
                alt87=2;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("845:1: indirection_feature_part : ( feature_name -> ^( INDIRECTION_FEATURE_PART feature_name ) | indirection_feature_list -> ^( INDIRECTION_FEATURE_PART indirection_feature_list ) );", 87, 0, input);

                throw nvae;
            }
            switch (alt87) {
                case 1 :
                    // BON.g:845:30: feature_name
                    {
                    pushFollow(FOLLOW_feature_name_in_indirection_feature_part12377);
                    feature_name154=feature_name();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_feature_name.add(feature_name154.getTree());

                    // AST REWRITE
                    // elements: feature_name
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 846:28: -> ^( INDIRECTION_FEATURE_PART feature_name )
                    {
                        // BON.g:847:28: ^( INDIRECTION_FEATURE_PART feature_name )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INDIRECTION_FEATURE_PART, "INDIRECTION_FEATURE_PART"), root_1);

                        adaptor.addChild(root_1, stream_feature_name.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:850:30: indirection_feature_list
                    {
                    pushFollow(FOLLOW_indirection_feature_list_in_indirection_feature_part12530);
                    indirection_feature_list155=indirection_feature_list();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_indirection_feature_list.add(indirection_feature_list155.getTree());

                    // AST REWRITE
                    // elements: indirection_feature_list
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 851:28: -> ^( INDIRECTION_FEATURE_PART indirection_feature_list )
                    {
                        // BON.g:852:28: ^( INDIRECTION_FEATURE_PART indirection_feature_list )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INDIRECTION_FEATURE_PART, "INDIRECTION_FEATURE_PART"), root_1);

                        adaptor.addChild(root_1, stream_indirection_feature_list.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end indirection_feature_part

    public static class indirection_feature_list_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start indirection_feature_list
    // BON.g:857:1: indirection_feature_list : '(' feature_name_list ')' -> ^( INDIRECTION_FEATURE_LIST feature_name_list ) ;
    public final indirection_feature_list_return indirection_feature_list() throws RecognitionException {
        indirection_feature_list_return retval = new indirection_feature_list_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal156=null;
        Token char_literal158=null;
        feature_name_list_return feature_name_list157 = null;


        CommonTree char_literal156_tree=null;
        CommonTree char_literal158_tree=null;
        RewriteRuleTokenStream stream_225=new RewriteRuleTokenStream(adaptor,"token 225");
        RewriteRuleTokenStream stream_226=new RewriteRuleTokenStream(adaptor,"token 226");
        RewriteRuleSubtreeStream stream_feature_name_list=new RewriteRuleSubtreeStream(adaptor,"rule feature_name_list");
        try {
            // BON.g:857:27: ( '(' feature_name_list ')' -> ^( INDIRECTION_FEATURE_LIST feature_name_list ) )
            // BON.g:857:30: '(' feature_name_list ')'
            {
            char_literal156=(Token)input.LT(1);
            match(input,225,FOLLOW_225_in_indirection_feature_list12716); if (failed) return retval;
            if ( backtracking==0 ) stream_225.add(char_literal156);

            pushFollow(FOLLOW_feature_name_list_in_indirection_feature_list12718);
            feature_name_list157=feature_name_list();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_feature_name_list.add(feature_name_list157.getTree());
            char_literal158=(Token)input.LT(1);
            match(input,226,FOLLOW_226_in_indirection_feature_list12720); if (failed) return retval;
            if ( backtracking==0 ) stream_226.add(char_literal158);


            // AST REWRITE
            // elements: feature_name_list
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 858:28: -> ^( INDIRECTION_FEATURE_LIST feature_name_list )
            {
                // BON.g:859:28: ^( INDIRECTION_FEATURE_LIST feature_name_list )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INDIRECTION_FEATURE_LIST, "INDIRECTION_FEATURE_LIST"), root_1);

                adaptor.addChild(root_1, stream_feature_name_list.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end indirection_feature_list

    public static class parent_indirection_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start parent_indirection
    // BON.g:864:1: parent_indirection : '->' generic_indirection -> ^( PARENT_INDIRECTION generic_indirection ) ;
    public final parent_indirection_return parent_indirection() throws RecognitionException {
        parent_indirection_return retval = new parent_indirection_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal159=null;
        generic_indirection_return generic_indirection160 = null;


        CommonTree string_literal159_tree=null;
        RewriteRuleTokenStream stream_227=new RewriteRuleTokenStream(adaptor,"token 227");
        RewriteRuleSubtreeStream stream_generic_indirection=new RewriteRuleSubtreeStream(adaptor,"rule generic_indirection");
        try {
            // BON.g:864:21: ( '->' generic_indirection -> ^( PARENT_INDIRECTION generic_indirection ) )
            // BON.g:864:24: '->' generic_indirection
            {
            string_literal159=(Token)input.LT(1);
            match(input,227,FOLLOW_227_in_parent_indirection12905); if (failed) return retval;
            if ( backtracking==0 ) stream_227.add(string_literal159);

            pushFollow(FOLLOW_generic_indirection_in_parent_indirection12907);
            generic_indirection160=generic_indirection();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_generic_indirection.add(generic_indirection160.getTree());

            // AST REWRITE
            // elements: generic_indirection
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 865:22: -> ^( PARENT_INDIRECTION generic_indirection )
            {
                // BON.g:866:22: ^( PARENT_INDIRECTION generic_indirection )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(PARENT_INDIRECTION, "PARENT_INDIRECTION"), root_1);

                adaptor.addChild(root_1, stream_generic_indirection.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end parent_indirection

    public static class generic_indirection_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start generic_indirection
    // BON.g:871:1: generic_indirection : indirection_element -> ^( GENERIC_INDIRECTION indirection_element ) ;
    public final generic_indirection_return generic_indirection() throws RecognitionException {
        generic_indirection_return retval = new generic_indirection_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        indirection_element_return indirection_element161 = null;


        RewriteRuleSubtreeStream stream_indirection_element=new RewriteRuleSubtreeStream(adaptor,"rule indirection_element");
        try {
            // BON.g:873:22: ( indirection_element -> ^( GENERIC_INDIRECTION indirection_element ) )
            // BON.g:881:23: indirection_element
            {
            pushFollow(FOLLOW_indirection_element_in_generic_indirection13089);
            indirection_element161=indirection_element();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_indirection_element.add(indirection_element161.getTree());

            // AST REWRITE
            // elements: indirection_element
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 882:23: -> ^( GENERIC_INDIRECTION indirection_element )
            {
                // BON.g:883:23: ^( GENERIC_INDIRECTION indirection_element )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(GENERIC_INDIRECTION, "GENERIC_INDIRECTION"), root_1);

                adaptor.addChild(root_1, stream_indirection_element.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end generic_indirection

    public static class named_indirection_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start named_indirection
    // BON.g:888:1: named_indirection : ( class_name '[' indirection_list ']' -> ^( NAMED_INDIRECTION class_name indirection_list ) | s= '[' indirection_list ']' -> ^( NAMED_INDIRECTION PARSE_ERROR ) );
    public final named_indirection_return named_indirection() throws RecognitionException {
        named_indirection_return retval = new named_indirection_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token s=null;
        Token char_literal163=null;
        Token char_literal165=null;
        Token char_literal167=null;
        class_name_return class_name162 = null;

        indirection_list_return indirection_list164 = null;

        indirection_list_return indirection_list166 = null;


        CommonTree s_tree=null;
        CommonTree char_literal163_tree=null;
        CommonTree char_literal165_tree=null;
        CommonTree char_literal167_tree=null;
        RewriteRuleTokenStream stream_228=new RewriteRuleTokenStream(adaptor,"token 228");
        RewriteRuleTokenStream stream_229=new RewriteRuleTokenStream(adaptor,"token 229");
        RewriteRuleSubtreeStream stream_indirection_list=new RewriteRuleSubtreeStream(adaptor,"rule indirection_list");
        RewriteRuleSubtreeStream stream_class_name=new RewriteRuleSubtreeStream(adaptor,"rule class_name");
        try {
            // BON.g:888:19: ( class_name '[' indirection_list ']' -> ^( NAMED_INDIRECTION class_name indirection_list ) | s= '[' indirection_list ']' -> ^( NAMED_INDIRECTION PARSE_ERROR ) )
            int alt88=2;
            int LA88_0 = input.LA(1);

            if ( (LA88_0==IDENTIFIER) ) {
                alt88=1;
            }
            else if ( (LA88_0==228) ) {
                alt88=2;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("888:1: named_indirection : ( class_name '[' indirection_list ']' -> ^( NAMED_INDIRECTION class_name indirection_list ) | s= '[' indirection_list ']' -> ^( NAMED_INDIRECTION PARSE_ERROR ) );", 88, 0, input);

                throw nvae;
            }
            switch (alt88) {
                case 1 :
                    // BON.g:888:22: class_name '[' indirection_list ']'
                    {
                    pushFollow(FOLLOW_class_name_in_named_indirection13242);
                    class_name162=class_name();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_class_name.add(class_name162.getTree());
                    char_literal163=(Token)input.LT(1);
                    match(input,228,FOLLOW_228_in_named_indirection13244); if (failed) return retval;
                    if ( backtracking==0 ) stream_228.add(char_literal163);

                    pushFollow(FOLLOW_indirection_list_in_named_indirection13246);
                    indirection_list164=indirection_list();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_indirection_list.add(indirection_list164.getTree());
                    char_literal165=(Token)input.LT(1);
                    match(input,229,FOLLOW_229_in_named_indirection13248); if (failed) return retval;
                    if ( backtracking==0 ) stream_229.add(char_literal165);


                    // AST REWRITE
                    // elements: indirection_list, class_name
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 889:21: -> ^( NAMED_INDIRECTION class_name indirection_list )
                    {
                        // BON.g:890:21: ^( NAMED_INDIRECTION class_name indirection_list )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(NAMED_INDIRECTION, "NAMED_INDIRECTION"), root_1);

                        adaptor.addChild(root_1, stream_class_name.next());
                        adaptor.addChild(root_1, stream_indirection_list.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:894:22: s= '[' indirection_list ']'
                    {
                    s=(Token)input.LT(1);
                    match(input,228,FOLLOW_228_in_named_indirection13390); if (failed) return retval;
                    if ( backtracking==0 ) stream_228.add(s);

                    pushFollow(FOLLOW_indirection_list_in_named_indirection13392);
                    indirection_list166=indirection_list();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_indirection_list.add(indirection_list166.getTree());
                    char_literal167=(Token)input.LT(1);
                    match(input,229,FOLLOW_229_in_named_indirection13394); if (failed) return retval;
                    if ( backtracking==0 ) stream_229.add(char_literal167);

                    if ( backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSLoc(s), "class name", "before indirection list", true)); 
                    }

                    // AST REWRITE
                    // elements: 
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 895:21: -> ^( NAMED_INDIRECTION PARSE_ERROR )
                    {
                        // BON.g:896:23: ^( NAMED_INDIRECTION PARSE_ERROR )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(NAMED_INDIRECTION, "NAMED_INDIRECTION"), root_1);

                        adaptor.addChild(root_1, adaptor.create(PARSE_ERROR, "PARSE_ERROR"));

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end named_indirection

    public static class indirection_list_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start indirection_list
    // BON.g:899:1: indirection_list : indirection_element ( ',' indirection_element )* -> ^( INDIRECTION_LIST ( indirection_element )+ ) ;
    public final indirection_list_return indirection_list() throws RecognitionException {
        indirection_list_return retval = new indirection_list_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal169=null;
        indirection_element_return indirection_element168 = null;

        indirection_element_return indirection_element170 = null;


        CommonTree char_literal169_tree=null;
        RewriteRuleTokenStream stream_197=new RewriteRuleTokenStream(adaptor,"token 197");
        RewriteRuleSubtreeStream stream_indirection_element=new RewriteRuleSubtreeStream(adaptor,"rule indirection_element");
        try {
            // BON.g:899:19: ( indirection_element ( ',' indirection_element )* -> ^( INDIRECTION_LIST ( indirection_element )+ ) )
            // BON.g:899:22: indirection_element ( ',' indirection_element )*
            {
            pushFollow(FOLLOW_indirection_element_in_indirection_list13497);
            indirection_element168=indirection_element();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_indirection_element.add(indirection_element168.getTree());
            // BON.g:899:42: ( ',' indirection_element )*
            loop89:
            do {
                int alt89=2;
                int LA89_0 = input.LA(1);

                if ( (LA89_0==197) ) {
                    alt89=1;
                }


                switch (alt89) {
            	case 1 :
            	    // BON.g:899:43: ',' indirection_element
            	    {
            	    char_literal169=(Token)input.LT(1);
            	    match(input,197,FOLLOW_197_in_indirection_list13500); if (failed) return retval;
            	    if ( backtracking==0 ) stream_197.add(char_literal169);

            	    pushFollow(FOLLOW_indirection_element_in_indirection_list13502);
            	    indirection_element170=indirection_element();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_indirection_element.add(indirection_element170.getTree());

            	    }
            	    break;

            	default :
            	    break loop89;
                }
            } while (true);


            // AST REWRITE
            // elements: indirection_element
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 900:20: -> ^( INDIRECTION_LIST ( indirection_element )+ )
            {
                // BON.g:901:20: ^( INDIRECTION_LIST ( indirection_element )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INDIRECTION_LIST, "INDIRECTION_LIST"), root_1);

                if ( !(stream_indirection_element.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_indirection_element.hasNext() ) {
                    adaptor.addChild(root_1, stream_indirection_element.next());

                }
                stream_indirection_element.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end indirection_list

    public static class indirection_element_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start indirection_element
    // BON.g:906:1: indirection_element : ( '...' -> ^( INDIRECTION_ELEMENT '...' ) | named_indirection -> ^( INDIRECTION_ELEMENT named_indirection ) | class_name -> ^( INDIRECTION_ELEMENT class_name ) );
    public final indirection_element_return indirection_element() throws RecognitionException {
        indirection_element_return retval = new indirection_element_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal171=null;
        named_indirection_return named_indirection172 = null;

        class_name_return class_name173 = null;


        CommonTree string_literal171_tree=null;
        RewriteRuleTokenStream stream_230=new RewriteRuleTokenStream(adaptor,"token 230");
        RewriteRuleSubtreeStream stream_named_indirection=new RewriteRuleSubtreeStream(adaptor,"rule named_indirection");
        RewriteRuleSubtreeStream stream_class_name=new RewriteRuleSubtreeStream(adaptor,"rule class_name");
        try {
            // BON.g:906:22: ( '...' -> ^( INDIRECTION_ELEMENT '...' ) | named_indirection -> ^( INDIRECTION_ELEMENT named_indirection ) | class_name -> ^( INDIRECTION_ELEMENT class_name ) )
            int alt90=3;
            switch ( input.LA(1) ) {
            case 230:
                {
                alt90=1;
                }
                break;
            case IDENTIFIER:
                {
                int LA90_2 = input.LA(2);

                if ( (LA90_2==197||LA90_2==223||LA90_2==229) ) {
                    alt90=3;
                }
                else if ( (LA90_2==228) ) {
                    alt90=2;
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("906:1: indirection_element : ( '...' -> ^( INDIRECTION_ELEMENT '...' ) | named_indirection -> ^( INDIRECTION_ELEMENT named_indirection ) | class_name -> ^( INDIRECTION_ELEMENT class_name ) );", 90, 2, input);

                    throw nvae;
                }
                }
                break;
            case 228:
                {
                alt90=2;
                }
                break;
            default:
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("906:1: indirection_element : ( '...' -> ^( INDIRECTION_ELEMENT '...' ) | named_indirection -> ^( INDIRECTION_ELEMENT named_indirection ) | class_name -> ^( INDIRECTION_ELEMENT class_name ) );", 90, 0, input);

                throw nvae;
            }

            switch (alt90) {
                case 1 :
                    // BON.g:906:26: '...'
                    {
                    string_literal171=(Token)input.LT(1);
                    match(input,230,FOLLOW_230_in_indirection_element13644); if (failed) return retval;
                    if ( backtracking==0 ) stream_230.add(string_literal171);


                    // AST REWRITE
                    // elements: 230
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 907:24: -> ^( INDIRECTION_ELEMENT '...' )
                    {
                        // BON.g:908:24: ^( INDIRECTION_ELEMENT '...' )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INDIRECTION_ELEMENT, "INDIRECTION_ELEMENT"), root_1);

                        adaptor.addChild(root_1, stream_230.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:911:25: named_indirection
                    {
                    pushFollow(FOLLOW_named_indirection_in_indirection_element13775);
                    named_indirection172=named_indirection();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_named_indirection.add(named_indirection172.getTree());

                    // AST REWRITE
                    // elements: named_indirection
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 912:24: -> ^( INDIRECTION_ELEMENT named_indirection )
                    {
                        // BON.g:913:24: ^( INDIRECTION_ELEMENT named_indirection )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INDIRECTION_ELEMENT, "INDIRECTION_ELEMENT"), root_1);

                        adaptor.addChild(root_1, stream_named_indirection.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 3 :
                    // BON.g:916:25: class_name
                    {
                    pushFollow(FOLLOW_class_name_in_indirection_element13907);
                    class_name173=class_name();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_class_name.add(class_name173.getTree());

                    // AST REWRITE
                    // elements: class_name
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 917:24: -> ^( INDIRECTION_ELEMENT class_name )
                    {
                        // BON.g:918:24: ^( INDIRECTION_ELEMENT class_name )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INDIRECTION_ELEMENT, "INDIRECTION_ELEMENT"), root_1);

                        adaptor.addChild(root_1, stream_class_name.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end indirection_element

    public static class type_mark_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start type_mark
    // BON.g:924:1: type_mark : ( ':' -> ^( TYPE_MARK ':' ) | ':{' -> ^( TYPE_MARK ':{' ) | shared_mark -> ^( TYPE_MARK shared_mark ) );
    public final type_mark_return type_mark() throws RecognitionException {
        type_mark_return retval = new type_mark_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal174=null;
        Token string_literal175=null;
        shared_mark_return shared_mark176 = null;


        CommonTree char_literal174_tree=null;
        CommonTree string_literal175_tree=null;
        RewriteRuleTokenStream stream_231=new RewriteRuleTokenStream(adaptor,"token 231");
        RewriteRuleTokenStream stream_196=new RewriteRuleTokenStream(adaptor,"token 196");
        RewriteRuleSubtreeStream stream_shared_mark=new RewriteRuleSubtreeStream(adaptor,"rule shared_mark");
        try {
            // BON.g:924:12: ( ':' -> ^( TYPE_MARK ':' ) | ':{' -> ^( TYPE_MARK ':{' ) | shared_mark -> ^( TYPE_MARK shared_mark ) )
            int alt91=3;
            int LA91_0 = input.LA(1);

            if ( (LA91_0==196) ) {
                int LA91_1 = input.LA(2);

                if ( (LA91_1==225) ) {
                    alt91=3;
                }
                else if ( (LA91_1==IDENTIFIER) ) {
                    alt91=1;
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("924:1: type_mark : ( ':' -> ^( TYPE_MARK ':' ) | ':{' -> ^( TYPE_MARK ':{' ) | shared_mark -> ^( TYPE_MARK shared_mark ) );", 91, 1, input);

                    throw nvae;
                }
            }
            else if ( (LA91_0==231) ) {
                alt91=2;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("924:1: type_mark : ( ':' -> ^( TYPE_MARK ':' ) | ':{' -> ^( TYPE_MARK ':{' ) | shared_mark -> ^( TYPE_MARK shared_mark ) );", 91, 0, input);

                throw nvae;
            }
            switch (alt91) {
                case 1 :
                    // BON.g:924:15: ':'
                    {
                    char_literal174=(Token)input.LT(1);
                    match(input,196,FOLLOW_196_in_type_mark14066); if (failed) return retval;
                    if ( backtracking==0 ) stream_196.add(char_literal174);


                    // AST REWRITE
                    // elements: 196
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 925:13: -> ^( TYPE_MARK ':' )
                    {
                        // BON.g:926:13: ^( TYPE_MARK ':' )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(TYPE_MARK, "TYPE_MARK"), root_1);

                        adaptor.addChild(root_1, stream_196.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:929:15: ':{'
                    {
                    string_literal175=(Token)input.LT(1);
                    match(input,231,FOLLOW_231_in_type_mark14144); if (failed) return retval;
                    if ( backtracking==0 ) stream_231.add(string_literal175);


                    // AST REWRITE
                    // elements: 231
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 930:13: -> ^( TYPE_MARK ':{' )
                    {
                        // BON.g:931:13: ^( TYPE_MARK ':{' )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(TYPE_MARK, "TYPE_MARK"), root_1);

                        adaptor.addChild(root_1, stream_231.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 3 :
                    // BON.g:934:15: shared_mark
                    {
                    pushFollow(FOLLOW_shared_mark_in_type_mark14222);
                    shared_mark176=shared_mark();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_shared_mark.add(shared_mark176.getTree());

                    // AST REWRITE
                    // elements: shared_mark
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 935:13: -> ^( TYPE_MARK shared_mark )
                    {
                        // BON.g:936:13: ^( TYPE_MARK shared_mark )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(TYPE_MARK, "TYPE_MARK"), root_1);

                        adaptor.addChild(root_1, stream_shared_mark.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end type_mark

    public static class shared_mark_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start shared_mark
    // BON.g:941:1: shared_mark : ':' '(' multiplicity ')' -> ^( SHARED_MARK multiplicity ) ;
    public final shared_mark_return shared_mark() throws RecognitionException {
        shared_mark_return retval = new shared_mark_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal177=null;
        Token char_literal178=null;
        Token char_literal180=null;
        multiplicity_return multiplicity179 = null;


        CommonTree char_literal177_tree=null;
        CommonTree char_literal178_tree=null;
        CommonTree char_literal180_tree=null;
        RewriteRuleTokenStream stream_225=new RewriteRuleTokenStream(adaptor,"token 225");
        RewriteRuleTokenStream stream_226=new RewriteRuleTokenStream(adaptor,"token 226");
        RewriteRuleTokenStream stream_196=new RewriteRuleTokenStream(adaptor,"token 196");
        RewriteRuleSubtreeStream stream_multiplicity=new RewriteRuleSubtreeStream(adaptor,"rule multiplicity");
        try {
            // BON.g:941:14: ( ':' '(' multiplicity ')' -> ^( SHARED_MARK multiplicity ) )
            // BON.g:941:17: ':' '(' multiplicity ')'
            {
            char_literal177=(Token)input.LT(1);
            match(input,196,FOLLOW_196_in_shared_mark14329); if (failed) return retval;
            if ( backtracking==0 ) stream_196.add(char_literal177);

            char_literal178=(Token)input.LT(1);
            match(input,225,FOLLOW_225_in_shared_mark14331); if (failed) return retval;
            if ( backtracking==0 ) stream_225.add(char_literal178);

            pushFollow(FOLLOW_multiplicity_in_shared_mark14333);
            multiplicity179=multiplicity();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_multiplicity.add(multiplicity179.getTree());
            char_literal180=(Token)input.LT(1);
            match(input,226,FOLLOW_226_in_shared_mark14335); if (failed) return retval;
            if ( backtracking==0 ) stream_226.add(char_literal180);


            // AST REWRITE
            // elements: multiplicity
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 942:15: -> ^( SHARED_MARK multiplicity )
            {
                // BON.g:943:15: ^( SHARED_MARK multiplicity )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(SHARED_MARK, "SHARED_MARK"), root_1);

                adaptor.addChild(root_1, stream_multiplicity.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end shared_mark

    public static class child_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start child
    // BON.g:948:1: child : static_ref -> ^( CHILD static_ref ) ;
    public final child_return child() throws RecognitionException {
        child_return retval = new child_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        static_ref_return static_ref181 = null;


        RewriteRuleSubtreeStream stream_static_ref=new RewriteRuleSubtreeStream(adaptor,"rule static_ref");
        try {
            // BON.g:950:8: ( static_ref -> ^( CHILD static_ref ) )
            // BON.g:950:11: static_ref
            {
            pushFollow(FOLLOW_static_ref_in_child14431);
            static_ref181=static_ref();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_static_ref.add(static_ref181.getTree());

            // AST REWRITE
            // elements: static_ref
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 951:9: -> ^( CHILD static_ref )
            {
                // BON.g:952:9: ^( CHILD static_ref )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CHILD, "CHILD"), root_1);

                adaptor.addChild(root_1, stream_static_ref.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end child

    public static class parent_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start parent
    // BON.g:957:1: parent : static_ref -> ^( PARENT static_ref ) ;
    public final parent_return parent() throws RecognitionException {
        parent_return retval = new parent_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        static_ref_return static_ref182 = null;


        RewriteRuleSubtreeStream stream_static_ref=new RewriteRuleSubtreeStream(adaptor,"rule static_ref");
        try {
            // BON.g:957:9: ( static_ref -> ^( PARENT static_ref ) )
            // BON.g:957:12: static_ref
            {
            pushFollow(FOLLOW_static_ref_in_parent14502);
            static_ref182=static_ref();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_static_ref.add(static_ref182.getTree());

            // AST REWRITE
            // elements: static_ref
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 958:10: -> ^( PARENT static_ref )
            {
                // BON.g:959:10: ^( PARENT static_ref )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(PARENT, "PARENT"), root_1);

                adaptor.addChild(root_1, stream_static_ref.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end parent

    public static class client_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start client
    // BON.g:964:1: client : static_ref -> ^( CLIENT static_ref ) ;
    public final client_return client() throws RecognitionException {
        client_return retval = new client_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        static_ref_return static_ref183 = null;


        RewriteRuleSubtreeStream stream_static_ref=new RewriteRuleSubtreeStream(adaptor,"rule static_ref");
        try {
            // BON.g:964:9: ( static_ref -> ^( CLIENT static_ref ) )
            // BON.g:964:12: static_ref
            {
            pushFollow(FOLLOW_static_ref_in_client14587);
            static_ref183=static_ref();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_static_ref.add(static_ref183.getTree());

            // AST REWRITE
            // elements: static_ref
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 965:10: -> ^( CLIENT static_ref )
            {
                // BON.g:966:10: ^( CLIENT static_ref )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLIENT, "CLIENT"), root_1);

                adaptor.addChild(root_1, stream_static_ref.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end client

    public static class supplier_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start supplier
    // BON.g:971:1: supplier : static_ref -> ^( SUPPLIER static_ref ) ;
    public final supplier_return supplier() throws RecognitionException {
        supplier_return retval = new supplier_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        static_ref_return static_ref184 = null;


        RewriteRuleSubtreeStream stream_static_ref=new RewriteRuleSubtreeStream(adaptor,"rule static_ref");
        try {
            // BON.g:971:11: ( static_ref -> ^( SUPPLIER static_ref ) )
            // BON.g:971:14: static_ref
            {
            pushFollow(FOLLOW_static_ref_in_supplier14664);
            static_ref184=static_ref();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_static_ref.add(static_ref184.getTree());

            // AST REWRITE
            // elements: static_ref
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 972:12: -> ^( SUPPLIER static_ref )
            {
                // BON.g:973:12: ^( SUPPLIER static_ref )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(SUPPLIER, "SUPPLIER"), root_1);

                adaptor.addChild(root_1, stream_static_ref.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end supplier

    public static class static_ref_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start static_ref
    // BON.g:978:1: static_ref : (s= static_component_name -> ^( STATIC_REF[$s.start] static_component_name ) | c= cluster_prefix static_component_name -> ^( STATIC_REF[$c.start] cluster_prefix static_component_name ) );
    public final static_ref_return static_ref() throws RecognitionException {
        static_ref_return retval = new static_ref_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        static_component_name_return s = null;

        cluster_prefix_return c = null;

        static_component_name_return static_component_name185 = null;


        RewriteRuleSubtreeStream stream_cluster_prefix=new RewriteRuleSubtreeStream(adaptor,"rule cluster_prefix");
        RewriteRuleSubtreeStream stream_static_component_name=new RewriteRuleSubtreeStream(adaptor,"rule static_component_name");
        try {
            // BON.g:978:13: (s= static_component_name -> ^( STATIC_REF[$s.start] static_component_name ) | c= cluster_prefix static_component_name -> ^( STATIC_REF[$c.start] cluster_prefix static_component_name ) )
            int alt92=2;
            int LA92_0 = input.LA(1);

            if ( (LA92_0==IDENTIFIER) ) {
                int LA92_1 = input.LA(2);

                if ( ((LA92_1>=MANIFEST_STRING && LA92_1<=IDENTIFIER)||(LA92_1>=187 && LA92_1<=189)||LA92_1==200||(LA92_1>=217 && LA92_1<=219)||LA92_1==224) ) {
                    alt92=1;
                }
                else if ( (LA92_1==232) ) {
                    alt92=2;
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("978:1: static_ref : (s= static_component_name -> ^( STATIC_REF[$s.start] static_component_name ) | c= cluster_prefix static_component_name -> ^( STATIC_REF[$c.start] cluster_prefix static_component_name ) );", 92, 1, input);

                    throw nvae;
                }
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("978:1: static_ref : (s= static_component_name -> ^( STATIC_REF[$s.start] static_component_name ) | c= cluster_prefix static_component_name -> ^( STATIC_REF[$c.start] cluster_prefix static_component_name ) );", 92, 0, input);

                throw nvae;
            }
            switch (alt92) {
                case 1 :
                    // BON.g:979:16: s= static_component_name
                    {
                    pushFollow(FOLLOW_static_component_name_in_static_ref14770);
                    s=static_component_name();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_static_component_name.add(s.getTree());

                    // AST REWRITE
                    // elements: static_component_name
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 980:14: -> ^( STATIC_REF[$s.start] static_component_name )
                    {
                        // BON.g:981:14: ^( STATIC_REF[$s.start] static_component_name )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(STATIC_REF, ((Token)s.start)), root_1);

                        adaptor.addChild(root_1, stream_static_component_name.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:985:16: c= cluster_prefix static_component_name
                    {
                    pushFollow(FOLLOW_cluster_prefix_in_static_ref14871);
                    c=cluster_prefix();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_cluster_prefix.add(c.getTree());
                    pushFollow(FOLLOW_static_component_name_in_static_ref14873);
                    static_component_name185=static_component_name();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_static_component_name.add(static_component_name185.getTree());

                    // AST REWRITE
                    // elements: cluster_prefix, static_component_name
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 986:14: -> ^( STATIC_REF[$c.start] cluster_prefix static_component_name )
                    {
                        // BON.g:987:14: ^( STATIC_REF[$c.start] cluster_prefix static_component_name )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(STATIC_REF, ((Token)c.start)), root_1);

                        adaptor.addChild(root_1, stream_cluster_prefix.next());
                        adaptor.addChild(root_1, stream_static_component_name.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end static_ref

    public static class cluster_prefix_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start cluster_prefix
    // BON.g:992:1: cluster_prefix : c1= cluster_name '.' ( cluster_name '.' )* -> ^( CLUSTER_PREFIX[$c1.start] ( cluster_name )+ ) ;
    public final cluster_prefix_return cluster_prefix() throws RecognitionException {
        cluster_prefix_return retval = new cluster_prefix_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal186=null;
        Token char_literal188=null;
        cluster_name_return c1 = null;

        cluster_name_return cluster_name187 = null;


        CommonTree char_literal186_tree=null;
        CommonTree char_literal188_tree=null;
        RewriteRuleTokenStream stream_232=new RewriteRuleTokenStream(adaptor,"token 232");
        RewriteRuleSubtreeStream stream_cluster_name=new RewriteRuleSubtreeStream(adaptor,"rule cluster_name");
        try {
            // BON.g:992:17: (c1= cluster_name '.' ( cluster_name '.' )* -> ^( CLUSTER_PREFIX[$c1.start] ( cluster_name )+ ) )
            // BON.g:992:20: c1= cluster_name '.' ( cluster_name '.' )*
            {
            pushFollow(FOLLOW_cluster_name_in_cluster_prefix14979);
            c1=cluster_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_cluster_name.add(c1.getTree());
            char_literal186=(Token)input.LT(1);
            match(input,232,FOLLOW_232_in_cluster_prefix14981); if (failed) return retval;
            if ( backtracking==0 ) stream_232.add(char_literal186);

            // BON.g:992:40: ( cluster_name '.' )*
            loop93:
            do {
                int alt93=2;
                int LA93_0 = input.LA(1);

                if ( (LA93_0==IDENTIFIER) ) {
                    int LA93_1 = input.LA(2);

                    if ( (LA93_1==232) ) {
                        alt93=1;
                    }


                }


                switch (alt93) {
            	case 1 :
            	    // BON.g:992:41: cluster_name '.'
            	    {
            	    pushFollow(FOLLOW_cluster_name_in_cluster_prefix14984);
            	    cluster_name187=cluster_name();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_cluster_name.add(cluster_name187.getTree());
            	    char_literal188=(Token)input.LT(1);
            	    match(input,232,FOLLOW_232_in_cluster_prefix14986); if (failed) return retval;
            	    if ( backtracking==0 ) stream_232.add(char_literal188);


            	    }
            	    break;

            	default :
            	    break loop93;
                }
            } while (true);


            // AST REWRITE
            // elements: cluster_name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 993:18: -> ^( CLUSTER_PREFIX[$c1.start] ( cluster_name )+ )
            {
                // BON.g:994:18: ^( CLUSTER_PREFIX[$c1.start] ( cluster_name )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLUSTER_PREFIX, ((Token)c1.start)), root_1);

                if ( !(stream_cluster_name.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_cluster_name.hasNext() ) {
                    adaptor.addChild(root_1, stream_cluster_name.next());

                }
                stream_cluster_name.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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

    public static class static_component_name_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start static_component_name
    // BON.g:1001:1: static_component_name : i= IDENTIFIER -> ^( STATIC_COMPONENT_NAME[$i] IDENTIFIER ) ;
    public final static_component_name_return static_component_name() throws RecognitionException {
        static_component_name_return retval = new static_component_name_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token i=null;

        CommonTree i_tree=null;
        RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");

        try {
            // BON.g:1001:24: (i= IDENTIFIER -> ^( STATIC_COMPONENT_NAME[$i] IDENTIFIER ) )
            // BON.g:1001:27: i= IDENTIFIER
            {
            i=(Token)input.LT(1);
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_static_component_name15106); if (failed) return retval;
            if ( backtracking==0 ) stream_IDENTIFIER.add(i);


            // AST REWRITE
            // elements: IDENTIFIER
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1002:25: -> ^( STATIC_COMPONENT_NAME[$i] IDENTIFIER )
            {
                // BON.g:1003:25: ^( STATIC_COMPONENT_NAME[$i] IDENTIFIER )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(STATIC_COMPONENT_NAME, i), root_1);

                adaptor.addChild(root_1, stream_IDENTIFIER.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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

    public static class multiplicity_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start multiplicity
    // BON.g:1008:1: multiplicity : i= INTEGER -> ^( MULTIPLICITY[$i] INTEGER ) ;
    public final multiplicity_return multiplicity() throws RecognitionException {
        multiplicity_return retval = new multiplicity_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token i=null;

        CommonTree i_tree=null;
        RewriteRuleTokenStream stream_INTEGER=new RewriteRuleTokenStream(adaptor,"token INTEGER");

        try {
            // BON.g:1008:15: (i= INTEGER -> ^( MULTIPLICITY[$i] INTEGER ) )
            // BON.g:1008:18: i= INTEGER
            {
            i=(Token)input.LT(1);
            match(input,INTEGER,FOLLOW_INTEGER_in_multiplicity15275); if (failed) return retval;
            if ( backtracking==0 ) stream_INTEGER.add(i);


            // AST REWRITE
            // elements: INTEGER
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1009:16: -> ^( MULTIPLICITY[$i] INTEGER )
            {
                // BON.g:1010:16: ^( MULTIPLICITY[$i] INTEGER )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(MULTIPLICITY, i), root_1);

                adaptor.addChild(root_1, stream_INTEGER.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end multiplicity

    public static class semantic_label_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start semantic_label
    // BON.g:1015:1: semantic_label : m= MANIFEST_STRING -> ^( SEMANTIC_LABEL[$m] MANIFEST_STRING ) ;
    public final semantic_label_return semantic_label() throws RecognitionException {
        semantic_label_return retval = new semantic_label_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token m=null;

        CommonTree m_tree=null;
        RewriteRuleTokenStream stream_MANIFEST_STRING=new RewriteRuleTokenStream(adaptor,"token MANIFEST_STRING");

        try {
            // BON.g:1015:17: (m= MANIFEST_STRING -> ^( SEMANTIC_LABEL[$m] MANIFEST_STRING ) )
            // BON.g:1015:20: m= MANIFEST_STRING
            {
            m=(Token)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_semantic_label15391); if (failed) return retval;
            if ( backtracking==0 ) stream_MANIFEST_STRING.add(m);


            // AST REWRITE
            // elements: MANIFEST_STRING
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1016:18: -> ^( SEMANTIC_LABEL[$m] MANIFEST_STRING )
            {
                // BON.g:1017:18: ^( SEMANTIC_LABEL[$m] MANIFEST_STRING )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(SEMANTIC_LABEL, m), root_1);

                adaptor.addChild(root_1, stream_MANIFEST_STRING.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end semantic_label

    public static class class_interface_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start class_interface
    // BON.g:1022:1: class_interface : ( indexing )? ( parent_class_list )? features ( class_invariant )? 'end' -> ^( CLASS_INTERFACE ( indexing )? ( parent_class_list )? features ( class_invariant )? ) ;
    public final class_interface_return class_interface() throws RecognitionException {
        class_interface_return retval = new class_interface_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal193=null;
        indexing_return indexing189 = null;

        parent_class_list_return parent_class_list190 = null;

        features_return features191 = null;

        class_invariant_return class_invariant192 = null;


        CommonTree string_literal193_tree=null;
        RewriteRuleTokenStream stream_187=new RewriteRuleTokenStream(adaptor,"token 187");
        RewriteRuleSubtreeStream stream_class_invariant=new RewriteRuleSubtreeStream(adaptor,"rule class_invariant");
        RewriteRuleSubtreeStream stream_indexing=new RewriteRuleSubtreeStream(adaptor,"rule indexing");
        RewriteRuleSubtreeStream stream_features=new RewriteRuleSubtreeStream(adaptor,"rule features");
        RewriteRuleSubtreeStream stream_parent_class_list=new RewriteRuleSubtreeStream(adaptor,"rule parent_class_list");
        try {
            // BON.g:1026:18: ( ( indexing )? ( parent_class_list )? features ( class_invariant )? 'end' -> ^( CLASS_INTERFACE ( indexing )? ( parent_class_list )? features ( class_invariant )? ) )
            // BON.g:1026:21: ( indexing )? ( parent_class_list )? features ( class_invariant )? 'end'
            {
            // BON.g:1026:21: ( indexing )?
            int alt94=2;
            int LA94_0 = input.LA(1);

            if ( (LA94_0==192) ) {
                alt94=1;
            }
            switch (alt94) {
                case 1 :
                    // BON.g:1026:22: indexing
                    {
                    pushFollow(FOLLOW_indexing_in_class_interface15504);
                    indexing189=indexing();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_indexing.add(indexing189.getTree());

                    }
                    break;

            }

            // BON.g:1027:21: ( parent_class_list )?
            int alt95=2;
            int LA95_0 = input.LA(1);

            if ( (LA95_0==200) ) {
                alt95=1;
            }
            switch (alt95) {
                case 1 :
                    // BON.g:1027:22: parent_class_list
                    {
                    pushFollow(FOLLOW_parent_class_list_in_class_interface15529);
                    parent_class_list190=parent_class_list();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_parent_class_list.add(parent_class_list190.getTree());

                    }
                    break;

            }

            pushFollow(FOLLOW_features_in_class_interface15553);
            features191=features();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_features.add(features191.getTree());
            // BON.g:1029:21: ( class_invariant )?
            int alt96=2;
            int LA96_0 = input.LA(1);

            if ( (LA96_0==233) ) {
                alt96=1;
            }
            switch (alt96) {
                case 1 :
                    // BON.g:1029:22: class_invariant
                    {
                    pushFollow(FOLLOW_class_invariant_in_class_interface15576);
                    class_invariant192=class_invariant();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_class_invariant.add(class_invariant192.getTree());

                    }
                    break;

            }

            string_literal193=(Token)input.LT(1);
            match(input,187,FOLLOW_187_in_class_interface15600); if (failed) return retval;
            if ( backtracking==0 ) stream_187.add(string_literal193);


            // AST REWRITE
            // elements: class_invariant, parent_class_list, features, indexing
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1031:19: -> ^( CLASS_INTERFACE ( indexing )? ( parent_class_list )? features ( class_invariant )? )
            {
                // BON.g:1032:19: ^( CLASS_INTERFACE ( indexing )? ( parent_class_list )? features ( class_invariant )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLASS_INTERFACE, "CLASS_INTERFACE"), root_1);

                // BON.g:1034:21: ( indexing )?
                if ( stream_indexing.hasNext() ) {
                    adaptor.addChild(root_1, stream_indexing.next());

                }
                stream_indexing.reset();
                // BON.g:1035:21: ( parent_class_list )?
                if ( stream_parent_class_list.hasNext() ) {
                    adaptor.addChild(root_1, stream_parent_class_list.next());

                }
                stream_parent_class_list.reset();
                adaptor.addChild(root_1, stream_features.next());
                // BON.g:1037:21: ( class_invariant )?
                if ( stream_class_invariant.hasNext() ) {
                    adaptor.addChild(root_1, stream_class_invariant.next());

                }
                stream_class_invariant.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end class_interface

    public static class class_invariant_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start class_invariant
    // BON.g:1041:1: class_invariant : 'invariant' assertion -> ^( CLASS_INVARIANT assertion ) ;
    public final class_invariant_return class_invariant() throws RecognitionException {
        class_invariant_return retval = new class_invariant_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal194=null;
        assertion_return assertion195 = null;


        CommonTree string_literal194_tree=null;
        RewriteRuleTokenStream stream_233=new RewriteRuleTokenStream(adaptor,"token 233");
        RewriteRuleSubtreeStream stream_assertion=new RewriteRuleSubtreeStream(adaptor,"rule assertion");
        try {
            // BON.g:1041:18: ( 'invariant' assertion -> ^( CLASS_INVARIANT assertion ) )
            // BON.g:1041:21: 'invariant' assertion
            {
            string_literal194=(Token)input.LT(1);
            match(input,233,FOLLOW_233_in_class_invariant15828); if (failed) return retval;
            if ( backtracking==0 ) stream_233.add(string_literal194);

            pushFollow(FOLLOW_assertion_in_class_invariant15830);
            assertion195=assertion();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_assertion.add(assertion195.getTree());

            // AST REWRITE
            // elements: assertion
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1042:19: -> ^( CLASS_INVARIANT assertion )
            {
                // BON.g:1043:19: ^( CLASS_INVARIANT assertion )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLASS_INVARIANT, "CLASS_INVARIANT"), root_1);

                adaptor.addChild(root_1, stream_assertion.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end class_invariant

    public static class parent_class_list_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start parent_class_list
    // BON.g:1048:1: parent_class_list : ( 'inherit' c1= class_type ( ';' c= class_type )* ( ';' )? -> ^( PARENT_CLASS_LIST ( class_type )+ ) | i= 'inherit' -> ^( PARENT_CLASS_LIST PARSE_ERROR ) );
    public final parent_class_list_return parent_class_list() throws RecognitionException {
        parent_class_list_return retval = new parent_class_list_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token i=null;
        Token string_literal196=null;
        Token char_literal197=null;
        Token char_literal198=null;
        class_type_return c1 = null;

        class_type_return c = null;


        CommonTree i_tree=null;
        CommonTree string_literal196_tree=null;
        CommonTree char_literal197_tree=null;
        CommonTree char_literal198_tree=null;
        RewriteRuleTokenStream stream_200=new RewriteRuleTokenStream(adaptor,"token 200");
        RewriteRuleTokenStream stream_195=new RewriteRuleTokenStream(adaptor,"token 195");
        RewriteRuleSubtreeStream stream_class_type=new RewriteRuleSubtreeStream(adaptor,"rule class_type");
        try {
            // BON.g:1048:20: ( 'inherit' c1= class_type ( ';' c= class_type )* ( ';' )? -> ^( PARENT_CLASS_LIST ( class_type )+ ) | i= 'inherit' -> ^( PARENT_CLASS_LIST PARSE_ERROR ) )
            int alt99=2;
            int LA99_0 = input.LA(1);

            if ( (LA99_0==200) ) {
                int LA99_1 = input.LA(2);

                if ( (LA99_1==234) ) {
                    alt99=2;
                }
                else if ( (LA99_1==IDENTIFIER) ) {
                    alt99=1;
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("1048:1: parent_class_list : ( 'inherit' c1= class_type ( ';' c= class_type )* ( ';' )? -> ^( PARENT_CLASS_LIST ( class_type )+ ) | i= 'inherit' -> ^( PARENT_CLASS_LIST PARSE_ERROR ) );", 99, 1, input);

                    throw nvae;
                }
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1048:1: parent_class_list : ( 'inherit' c1= class_type ( ';' c= class_type )* ( ';' )? -> ^( PARENT_CLASS_LIST ( class_type )+ ) | i= 'inherit' -> ^( PARENT_CLASS_LIST PARSE_ERROR ) );", 99, 0, input);

                throw nvae;
            }
            switch (alt99) {
                case 1 :
                    // BON.g:1048:23: 'inherit' c1= class_type ( ';' c= class_type )* ( ';' )?
                    {
                    string_literal196=(Token)input.LT(1);
                    match(input,200,FOLLOW_200_in_parent_class_list15977); if (failed) return retval;
                    if ( backtracking==0 ) stream_200.add(string_literal196);

                    pushFollow(FOLLOW_class_type_in_parent_class_list15981);
                    c1=class_type();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_class_type.add(c1.getTree());
                    if ( backtracking==0 ) {
                       getTI().addParentClass(input.toString(c1.start,c1.stop),getSLoc(((Token)c1.start))); 
                    }
                    // BON.g:1048:104: ( ';' c= class_type )*
                    loop97:
                    do {
                        int alt97=2;
                        int LA97_0 = input.LA(1);

                        if ( (LA97_0==195) ) {
                            int LA97_1 = input.LA(2);

                            if ( (LA97_1==IDENTIFIER) ) {
                                alt97=1;
                            }


                        }


                        switch (alt97) {
                    	case 1 :
                    	    // BON.g:1048:105: ';' c= class_type
                    	    {
                    	    char_literal197=(Token)input.LT(1);
                    	    match(input,195,FOLLOW_195_in_parent_class_list15986); if (failed) return retval;
                    	    if ( backtracking==0 ) stream_195.add(char_literal197);

                    	    pushFollow(FOLLOW_class_type_in_parent_class_list15990);
                    	    c=class_type();
                    	    _fsp--;
                    	    if (failed) return retval;
                    	    if ( backtracking==0 ) stream_class_type.add(c.getTree());
                    	    if ( backtracking==0 ) {
                    	       getTI().addParentClass(input.toString(c.start,c.stop),getSLoc(((Token)c.start))); 
                    	    }

                    	    }
                    	    break;

                    	default :
                    	    break loop97;
                        }
                    } while (true);

                    // BON.g:1048:180: ( ';' )?
                    int alt98=2;
                    int LA98_0 = input.LA(1);

                    if ( (LA98_0==195) ) {
                        alt98=1;
                    }
                    switch (alt98) {
                        case 1 :
                            // BON.g:1048:180: ';'
                            {
                            char_literal198=(Token)input.LT(1);
                            match(input,195,FOLLOW_195_in_parent_class_list15997); if (failed) return retval;
                            if ( backtracking==0 ) stream_195.add(char_literal198);


                            }
                            break;

                    }


                    // AST REWRITE
                    // elements: class_type
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1049:21: -> ^( PARENT_CLASS_LIST ( class_type )+ )
                    {
                        // BON.g:1050:21: ^( PARENT_CLASS_LIST ( class_type )+ )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(PARENT_CLASS_LIST, "PARENT_CLASS_LIST"), root_1);

                        if ( !(stream_class_type.hasNext()) ) {
                            throw new RewriteEarlyExitException();
                        }
                        while ( stream_class_type.hasNext() ) {
                            adaptor.addChild(root_1, stream_class_type.next());

                        }
                        stream_class_type.reset();

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:1054:24: i= 'inherit'
                    {
                    i=(Token)input.LT(1);
                    match(input,200,FOLLOW_200_in_parent_class_list16145); if (failed) return retval;
                    if ( backtracking==0 ) stream_200.add(i);

                    if ( backtracking==0 ) {
                       addParseProblem(new MissingElementParseError(getSourceLocation(i), "class name(s)", "in inherits clause", true)); 
                    }

                    // AST REWRITE
                    // elements: 
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1055:21: -> ^( PARENT_CLASS_LIST PARSE_ERROR )
                    {
                        // BON.g:1056:21: ^( PARENT_CLASS_LIST PARSE_ERROR )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(PARENT_CLASS_LIST, "PARENT_CLASS_LIST"), root_1);

                        adaptor.addChild(root_1, adaptor.create(PARSE_ERROR, "PARSE_ERROR"));

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end parent_class_list

    public static class features_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start features
    // BON.g:1059:1: features : ( feature_clause )+ -> ^( FEATURES ( feature_clause )+ ) ;
    public final features_return features() throws RecognitionException {
        features_return retval = new features_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        feature_clause_return feature_clause199 = null;


        RewriteRuleSubtreeStream stream_feature_clause=new RewriteRuleSubtreeStream(adaptor,"rule feature_clause");
        try {
            // BON.g:1059:11: ( ( feature_clause )+ -> ^( FEATURES ( feature_clause )+ ) )
            // BON.g:1059:14: ( feature_clause )+
            {
            // BON.g:1059:14: ( feature_clause )+
            int cnt100=0;
            loop100:
            do {
                int alt100=2;
                int LA100_0 = input.LA(1);

                if ( (LA100_0==234) ) {
                    alt100=1;
                }


                switch (alt100) {
            	case 1 :
            	    // BON.g:1059:15: feature_clause
            	    {
            	    pushFollow(FOLLOW_feature_clause_in_features16246);
            	    feature_clause199=feature_clause();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_feature_clause.add(feature_clause199.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt100 >= 1 ) break loop100;
            	    if (backtracking>0) {failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(100, input);
                        throw eee;
                }
                cnt100++;
            } while (true);


            // AST REWRITE
            // elements: feature_clause
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1060:12: -> ^( FEATURES ( feature_clause )+ )
            {
                // BON.g:1061:12: ^( FEATURES ( feature_clause )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(FEATURES, "FEATURES"), root_1);

                if ( !(stream_feature_clause.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_feature_clause.hasNext() ) {
                    adaptor.addChild(root_1, stream_feature_clause.next());

                }
                stream_feature_clause.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end features

    public static class feature_clause_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start feature_clause
    // BON.g:1066:1: feature_clause : f= 'feature' ( selective_export )? ( COMMENT )? feature_specifications -> ^( FEATURE_CLAUSE ( selective_export )? ( COMMENT )? feature_specifications ) ;
    public final feature_clause_return feature_clause() throws RecognitionException {
        feature_clause_return retval = new feature_clause_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token f=null;
        Token COMMENT201=null;
        selective_export_return selective_export200 = null;

        feature_specifications_return feature_specifications202 = null;


        CommonTree f_tree=null;
        CommonTree COMMENT201_tree=null;
        RewriteRuleTokenStream stream_COMMENT=new RewriteRuleTokenStream(adaptor,"token COMMENT");
        RewriteRuleTokenStream stream_234=new RewriteRuleTokenStream(adaptor,"token 234");
        RewriteRuleSubtreeStream stream_feature_specifications=new RewriteRuleSubtreeStream(adaptor,"rule feature_specifications");
        RewriteRuleSubtreeStream stream_selective_export=new RewriteRuleSubtreeStream(adaptor,"rule selective_export");
        try {
            // BON.g:1068:17: (f= 'feature' ( selective_export )? ( COMMENT )? feature_specifications -> ^( FEATURE_CLAUSE ( selective_export )? ( COMMENT )? feature_specifications ) )
            // BON.g:1068:20: f= 'feature' ( selective_export )? ( COMMENT )? feature_specifications
            {
            f=(Token)input.LT(1);
            match(input,234,FOLLOW_234_in_feature_clause16345); if (failed) return retval;
            if ( backtracking==0 ) stream_234.add(f);

            if ( backtracking==0 ) {
               getContext().enterFeatureClause(getSLoc(f)); 
            }
            // BON.g:1070:20: ( selective_export )?
            int alt101=2;
            int LA101_0 = input.LA(1);

            if ( (LA101_0==222) ) {
                alt101=1;
            }
            switch (alt101) {
                case 1 :
                    // BON.g:1070:21: selective_export
                    {
                    pushFollow(FOLLOW_selective_export_in_feature_clause16389);
                    selective_export200=selective_export();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_selective_export.add(selective_export200.getTree());

                    }
                    break;

            }

            // BON.g:1071:20: ( COMMENT )?
            int alt102=2;
            int LA102_0 = input.LA(1);

            if ( (LA102_0==COMMENT) ) {
                alt102=1;
            }
            switch (alt102) {
                case 1 :
                    // BON.g:1071:21: COMMENT
                    {
                    COMMENT201=(Token)input.LT(1);
                    match(input,COMMENT,FOLLOW_COMMENT_in_feature_clause16414); if (failed) return retval;
                    if ( backtracking==0 ) stream_COMMENT.add(COMMENT201);


                    }
                    break;

            }

            pushFollow(FOLLOW_feature_specifications_in_feature_clause16438);
            feature_specifications202=feature_specifications();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_feature_specifications.add(feature_specifications202.getTree());
            if ( backtracking==0 ) {
               getContext().leaveFeatureClause(); 
            }

            // AST REWRITE
            // elements: selective_export, feature_specifications, COMMENT
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1074:18: -> ^( FEATURE_CLAUSE ( selective_export )? ( COMMENT )? feature_specifications )
            {
                // BON.g:1075:18: ^( FEATURE_CLAUSE ( selective_export )? ( COMMENT )? feature_specifications )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(FEATURE_CLAUSE, "FEATURE_CLAUSE"), root_1);

                // BON.g:1077:20: ( selective_export )?
                if ( stream_selective_export.hasNext() ) {
                    adaptor.addChild(root_1, stream_selective_export.next());

                }
                stream_selective_export.reset();
                // BON.g:1078:20: ( COMMENT )?
                if ( stream_COMMENT.hasNext() ) {
                    adaptor.addChild(root_1, stream_COMMENT.next());

                }
                stream_COMMENT.reset();
                adaptor.addChild(root_1, stream_feature_specifications.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end feature_clause

    public static class feature_specifications_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start feature_specifications
    // BON.g:1083:1: feature_specifications : ( feature_specification )+ -> ^( FEATURE_SPECIFICATIONS ( feature_specification )+ ) ;
    public final feature_specifications_return feature_specifications() throws RecognitionException {
        feature_specifications_return retval = new feature_specifications_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        feature_specification_return feature_specification203 = null;


        RewriteRuleSubtreeStream stream_feature_specification=new RewriteRuleSubtreeStream(adaptor,"rule feature_specification");
        try {
            // BON.g:1083:25: ( ( feature_specification )+ -> ^( FEATURE_SPECIFICATIONS ( feature_specification )+ ) )
            // BON.g:1083:28: ( feature_specification )+
            {
            // BON.g:1083:28: ( feature_specification )+
            int cnt103=0;
            loop103:
            do {
                int alt103=2;
                int LA103_0 = input.LA(1);

                if ( (LA103_0==IDENTIFIER||(LA103_0>=218 && LA103_0<=219)||LA103_0==235||LA103_0==239||LA103_0==241) ) {
                    alt103=1;
                }


                switch (alt103) {
            	case 1 :
            	    // BON.g:1083:29: feature_specification
            	    {
            	    pushFollow(FOLLOW_feature_specification_in_feature_specifications16655);
            	    feature_specification203=feature_specification();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_feature_specification.add(feature_specification203.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt103 >= 1 ) break loop103;
            	    if (backtracking>0) {failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(103, input);
                        throw eee;
                }
                cnt103++;
            } while (true);


            // AST REWRITE
            // elements: feature_specification
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1084:26: -> ^( FEATURE_SPECIFICATIONS ( feature_specification )+ )
            {
                // BON.g:1085:26: ^( FEATURE_SPECIFICATIONS ( feature_specification )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(FEATURE_SPECIFICATIONS, "FEATURE_SPECIFICATIONS"), root_1);

                if ( !(stream_feature_specification.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_feature_specification.hasNext() ) {
                    adaptor.addChild(root_1, stream_feature_specification.next());

                }
                stream_feature_specification.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end feature_specifications

    public static class feature_specification_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start feature_specification
    // BON.g:1091:1: feature_specification : ( ( 'deferred' feature_name_list ) | ( 'effective' feature_name_list ) | ( 'redefined' feature_name_list ) | ( feature_name_list ) ) ( has_type )? ( rename_clause )? ( COMMENT )? ( feature_arguments )? ( contract_clause )? -> ^( FEATURE_SPECIFICATION ( 'deferred' )? ( 'effective' )? ( 'redefined' )? feature_name_list ( has_type )? ( rename_clause )? ( COMMENT )? ( feature_arguments )? ( contract_clause )? ) ;
    public final feature_specification_return feature_specification() throws RecognitionException {
        feature_specification_return retval = new feature_specification_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal204=null;
        Token string_literal206=null;
        Token string_literal208=null;
        Token COMMENT213=null;
        feature_name_list_return feature_name_list205 = null;

        feature_name_list_return feature_name_list207 = null;

        feature_name_list_return feature_name_list209 = null;

        feature_name_list_return feature_name_list210 = null;

        has_type_return has_type211 = null;

        rename_clause_return rename_clause212 = null;

        feature_arguments_return feature_arguments214 = null;

        contract_clause_return contract_clause215 = null;


        CommonTree string_literal204_tree=null;
        CommonTree string_literal206_tree=null;
        CommonTree string_literal208_tree=null;
        CommonTree COMMENT213_tree=null;
        RewriteRuleTokenStream stream_COMMENT=new RewriteRuleTokenStream(adaptor,"token COMMENT");
        RewriteRuleTokenStream stream_219=new RewriteRuleTokenStream(adaptor,"token 219");
        RewriteRuleTokenStream stream_218=new RewriteRuleTokenStream(adaptor,"token 218");
        RewriteRuleTokenStream stream_235=new RewriteRuleTokenStream(adaptor,"token 235");
        RewriteRuleSubtreeStream stream_feature_arguments=new RewriteRuleSubtreeStream(adaptor,"rule feature_arguments");
        RewriteRuleSubtreeStream stream_feature_name_list=new RewriteRuleSubtreeStream(adaptor,"rule feature_name_list");
        RewriteRuleSubtreeStream stream_has_type=new RewriteRuleSubtreeStream(adaptor,"rule has_type");
        RewriteRuleSubtreeStream stream_contract_clause=new RewriteRuleSubtreeStream(adaptor,"rule contract_clause");
        RewriteRuleSubtreeStream stream_rename_clause=new RewriteRuleSubtreeStream(adaptor,"rule rename_clause");
        try {
            // BON.g:1091:24: ( ( ( 'deferred' feature_name_list ) | ( 'effective' feature_name_list ) | ( 'redefined' feature_name_list ) | ( feature_name_list ) ) ( has_type )? ( rename_clause )? ( COMMENT )? ( feature_arguments )? ( contract_clause )? -> ^( FEATURE_SPECIFICATION ( 'deferred' )? ( 'effective' )? ( 'redefined' )? feature_name_list ( has_type )? ( rename_clause )? ( COMMENT )? ( feature_arguments )? ( contract_clause )? ) )
            // BON.g:1091:27: ( ( 'deferred' feature_name_list ) | ( 'effective' feature_name_list ) | ( 'redefined' feature_name_list ) | ( feature_name_list ) ) ( has_type )? ( rename_clause )? ( COMMENT )? ( feature_arguments )? ( contract_clause )?
            {
            // BON.g:1091:27: ( ( 'deferred' feature_name_list ) | ( 'effective' feature_name_list ) | ( 'redefined' feature_name_list ) | ( feature_name_list ) )
            int alt104=4;
            switch ( input.LA(1) ) {
            case 218:
                {
                alt104=1;
                }
                break;
            case 219:
                {
                alt104=2;
                }
                break;
            case 235:
                {
                alt104=3;
                }
                break;
            case IDENTIFIER:
            case 239:
            case 241:
                {
                alt104=4;
                }
                break;
            default:
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1091:27: ( ( 'deferred' feature_name_list ) | ( 'effective' feature_name_list ) | ( 'redefined' feature_name_list ) | ( feature_name_list ) )", 104, 0, input);

                throw nvae;
            }

            switch (alt104) {
                case 1 :
                    // BON.g:1091:29: ( 'deferred' feature_name_list )
                    {
                    // BON.g:1091:29: ( 'deferred' feature_name_list )
                    // BON.g:1091:31: 'deferred' feature_name_list
                    {
                    string_literal204=(Token)input.LT(1);
                    match(input,218,FOLLOW_218_in_feature_specification16864); if (failed) return retval;
                    if ( backtracking==0 ) stream_218.add(string_literal204);

                    if ( backtracking==0 ) {
                       getContext().enterFeatureSpecification(); 
                    }
                    pushFollow(FOLLOW_feature_name_list_in_feature_specification16869);
                    feature_name_list205=feature_name_list();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_feature_name_list.add(feature_name_list205.getTree());
                    if ( backtracking==0 ) {
                       getTI().featureSpecDeferred(); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // BON.g:1092:29: ( 'effective' feature_name_list )
                    {
                    // BON.g:1092:29: ( 'effective' feature_name_list )
                    // BON.g:1092:31: 'effective' feature_name_list
                    {
                    string_literal206=(Token)input.LT(1);
                    match(input,219,FOLLOW_219_in_feature_specification16907); if (failed) return retval;
                    if ( backtracking==0 ) stream_219.add(string_literal206);

                    if ( backtracking==0 ) {
                       getContext().enterFeatureSpecification(); 
                    }
                    pushFollow(FOLLOW_feature_name_list_in_feature_specification16911);
                    feature_name_list207=feature_name_list();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_feature_name_list.add(feature_name_list207.getTree());
                    if ( backtracking==0 ) {
                       getTI().featureSpecEffective(); 
                    }

                    }


                    }
                    break;
                case 3 :
                    // BON.g:1093:29: ( 'redefined' feature_name_list )
                    {
                    // BON.g:1093:29: ( 'redefined' feature_name_list )
                    // BON.g:1093:31: 'redefined' feature_name_list
                    {
                    string_literal208=(Token)input.LT(1);
                    match(input,235,FOLLOW_235_in_feature_specification16947); if (failed) return retval;
                    if ( backtracking==0 ) stream_235.add(string_literal208);

                    if ( backtracking==0 ) {
                       getContext().enterFeatureSpecification(); 
                    }
                    pushFollow(FOLLOW_feature_name_list_in_feature_specification16951);
                    feature_name_list209=feature_name_list();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_feature_name_list.add(feature_name_list209.getTree());
                    if ( backtracking==0 ) {
                       getTI().featureSpecRedefined(); 
                    }

                    }


                    }
                    break;
                case 4 :
                    // BON.g:1094:29: ( feature_name_list )
                    {
                    // BON.g:1094:29: ( feature_name_list )
                    // BON.g:1094:31: feature_name_list
                    {
                    if ( backtracking==0 ) {
                       getContext().enterFeatureSpecification(); 
                    }
                    pushFollow(FOLLOW_feature_name_list_in_feature_specification16989);
                    feature_name_list210=feature_name_list();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_feature_name_list.add(feature_name_list210.getTree());

                    }


                    }
                    break;

            }

            // BON.g:1096:27: ( has_type )?
            int alt105=2;
            int LA105_0 = input.LA(1);

            if ( (LA105_0==196||LA105_0==231) ) {
                alt105=1;
            }
            switch (alt105) {
                case 1 :
                    // BON.g:1096:28: has_type
                    {
                    pushFollow(FOLLOW_has_type_in_feature_specification17096);
                    has_type211=has_type();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_has_type.add(has_type211.getTree());

                    }
                    break;

            }

            // BON.g:1097:27: ( rename_clause )?
            int alt106=2;
            int LA106_0 = input.LA(1);

            if ( (LA106_0==222) ) {
                alt106=1;
            }
            switch (alt106) {
                case 1 :
                    // BON.g:1097:28: rename_clause
                    {
                    pushFollow(FOLLOW_rename_clause_in_feature_specification17127);
                    rename_clause212=rename_clause();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_rename_clause.add(rename_clause212.getTree());
                    if ( backtracking==0 ) {
                        
                    }

                    }
                    break;

            }

            // BON.g:1098:27: ( COMMENT )?
            int alt107=2;
            int LA107_0 = input.LA(1);

            if ( (LA107_0==COMMENT) ) {
                alt107=1;
            }
            switch (alt107) {
                case 1 :
                    // BON.g:1098:28: COMMENT
                    {
                    COMMENT213=(Token)input.LT(1);
                    match(input,COMMENT,FOLLOW_COMMENT_in_feature_specification17161); if (failed) return retval;
                    if ( backtracking==0 ) stream_COMMENT.add(COMMENT213);


                    }
                    break;

            }

            // BON.g:1099:27: ( feature_arguments )?
            int alt108=2;
            int LA108_0 = input.LA(1);

            if ( (LA108_0==227) ) {
                alt108=1;
            }
            switch (alt108) {
                case 1 :
                    // BON.g:1099:28: feature_arguments
                    {
                    pushFollow(FOLLOW_feature_arguments_in_feature_specification17192);
                    feature_arguments214=feature_arguments();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_feature_arguments.add(feature_arguments214.getTree());

                    }
                    break;

            }

            // BON.g:1100:27: ( contract_clause )?
            int alt109=2;
            int LA109_0 = input.LA(1);

            if ( ((LA109_0>=236 && LA109_0<=237)) ) {
                alt109=1;
            }
            switch (alt109) {
                case 1 :
                    // BON.g:1100:28: contract_clause
                    {
                    pushFollow(FOLLOW_contract_clause_in_feature_specification17223);
                    contract_clause215=contract_clause();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_contract_clause.add(contract_clause215.getTree());

                    }
                    break;

            }

            if ( backtracking==0 ) {
               getContext().leaveFeatureSpecification(); 
            }

            // AST REWRITE
            // elements: 235, 218, contract_clause, 219, has_type, COMMENT, rename_clause, feature_arguments, feature_name_list
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1102:25: -> ^( FEATURE_SPECIFICATION ( 'deferred' )? ( 'effective' )? ( 'redefined' )? feature_name_list ( has_type )? ( rename_clause )? ( COMMENT )? ( feature_arguments )? ( contract_clause )? )
            {
                // BON.g:1103:25: ^( FEATURE_SPECIFICATION ( 'deferred' )? ( 'effective' )? ( 'redefined' )? feature_name_list ( has_type )? ( rename_clause )? ( COMMENT )? ( feature_arguments )? ( contract_clause )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(FEATURE_SPECIFICATION, "FEATURE_SPECIFICATION"), root_1);

                // BON.g:1105:27: ( 'deferred' )?
                if ( stream_218.hasNext() ) {
                    adaptor.addChild(root_1, stream_218.next());

                }
                stream_218.reset();
                // BON.g:1105:41: ( 'effective' )?
                if ( stream_219.hasNext() ) {
                    adaptor.addChild(root_1, stream_219.next());

                }
                stream_219.reset();
                // BON.g:1105:56: ( 'redefined' )?
                if ( stream_235.hasNext() ) {
                    adaptor.addChild(root_1, stream_235.next());

                }
                stream_235.reset();
                adaptor.addChild(root_1, stream_feature_name_list.next());
                // BON.g:1106:45: ( has_type )?
                if ( stream_has_type.hasNext() ) {
                    adaptor.addChild(root_1, stream_has_type.next());

                }
                stream_has_type.reset();
                // BON.g:1107:27: ( rename_clause )?
                if ( stream_rename_clause.hasNext() ) {
                    adaptor.addChild(root_1, stream_rename_clause.next());

                }
                stream_rename_clause.reset();
                // BON.g:1108:27: ( COMMENT )?
                if ( stream_COMMENT.hasNext() ) {
                    adaptor.addChild(root_1, stream_COMMENT.next());

                }
                stream_COMMENT.reset();
                // BON.g:1109:27: ( feature_arguments )?
                if ( stream_feature_arguments.hasNext() ) {
                    adaptor.addChild(root_1, stream_feature_arguments.next());

                }
                stream_feature_arguments.reset();
                // BON.g:1110:27: ( contract_clause )?
                if ( stream_contract_clause.hasNext() ) {
                    adaptor.addChild(root_1, stream_contract_clause.next());

                }
                stream_contract_clause.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end feature_specification

    public static class has_type_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start has_type
    // BON.g:1114:1: has_type : type_mark type -> ^( HAS_TYPE type_mark type ) ;
    public final has_type_return has_type() throws RecognitionException {
        has_type_return retval = new has_type_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        type_mark_return type_mark216 = null;

        type_return type217 = null;


        RewriteRuleSubtreeStream stream_type_mark=new RewriteRuleSubtreeStream(adaptor,"rule type_mark");
        RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type");
        try {
            // BON.g:1114:11: ( type_mark type -> ^( HAS_TYPE type_mark type ) )
            // BON.g:1114:14: type_mark type
            {
            pushFollow(FOLLOW_type_mark_in_has_type17617);
            type_mark216=type_mark();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_type_mark.add(type_mark216.getTree());
            pushFollow(FOLLOW_type_in_has_type17619);
            type217=type();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_type.add(type217.getTree());
            if ( backtracking==0 ) {
               getTI().hasType(input.toString(type217.start,type217.stop)); 
            }

            // AST REWRITE
            // elements: type_mark, type
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1115:12: -> ^( HAS_TYPE type_mark type )
            {
                // BON.g:1116:12: ^( HAS_TYPE type_mark type )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(HAS_TYPE, "HAS_TYPE"), root_1);

                adaptor.addChild(root_1, stream_type_mark.next());
                adaptor.addChild(root_1, stream_type.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end has_type

    public static class contract_clause_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start contract_clause
    // BON.g:1119:1: contract_clause : contracting_conditions 'end' -> ^( CONTRACT_CLAUSE contracting_conditions ) ;
    public final contract_clause_return contract_clause() throws RecognitionException {
        contract_clause_return retval = new contract_clause_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal219=null;
        contracting_conditions_return contracting_conditions218 = null;


        CommonTree string_literal219_tree=null;
        RewriteRuleTokenStream stream_187=new RewriteRuleTokenStream(adaptor,"token 187");
        RewriteRuleSubtreeStream stream_contracting_conditions=new RewriteRuleSubtreeStream(adaptor,"rule contracting_conditions");
        try {
            // BON.g:1121:18: ( contracting_conditions 'end' -> ^( CONTRACT_CLAUSE contracting_conditions ) )
            // BON.g:1121:21: contracting_conditions 'end'
            {
            pushFollow(FOLLOW_contracting_conditions_in_contract_clause17677);
            contracting_conditions218=contracting_conditions();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_contracting_conditions.add(contracting_conditions218.getTree());
            string_literal219=(Token)input.LT(1);
            match(input,187,FOLLOW_187_in_contract_clause17679); if (failed) return retval;
            if ( backtracking==0 ) stream_187.add(string_literal219);


            // AST REWRITE
            // elements: contracting_conditions
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1122:19: -> ^( CONTRACT_CLAUSE contracting_conditions )
            {
                // BON.g:1123:19: ^( CONTRACT_CLAUSE contracting_conditions )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CONTRACT_CLAUSE, "CONTRACT_CLAUSE"), root_1);

                adaptor.addChild(root_1, stream_contracting_conditions.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end contract_clause

    public static class contracting_conditions_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start contracting_conditions
    // BON.g:1129:1: contracting_conditions : ( ( precondition ( postcondition )? ) | postcondition ) -> ^( CONTRACTING_CONDITIONS ( precondition )? ( postcondition )? ) ;
    public final contracting_conditions_return contracting_conditions() throws RecognitionException {
        contracting_conditions_return retval = new contracting_conditions_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        precondition_return precondition220 = null;

        postcondition_return postcondition221 = null;

        postcondition_return postcondition222 = null;


        RewriteRuleSubtreeStream stream_postcondition=new RewriteRuleSubtreeStream(adaptor,"rule postcondition");
        RewriteRuleSubtreeStream stream_precondition=new RewriteRuleSubtreeStream(adaptor,"rule precondition");
        try {
            // BON.g:1129:25: ( ( ( precondition ( postcondition )? ) | postcondition ) -> ^( CONTRACTING_CONDITIONS ( precondition )? ( postcondition )? ) )
            // BON.g:1129:28: ( ( precondition ( postcondition )? ) | postcondition )
            {
            // BON.g:1129:28: ( ( precondition ( postcondition )? ) | postcondition )
            int alt111=2;
            int LA111_0 = input.LA(1);

            if ( (LA111_0==236) ) {
                alt111=1;
            }
            else if ( (LA111_0==237) ) {
                alt111=2;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1129:28: ( ( precondition ( postcondition )? ) | postcondition )", 111, 0, input);

                throw nvae;
            }
            switch (alt111) {
                case 1 :
                    // BON.g:1129:29: ( precondition ( postcondition )? )
                    {
                    // BON.g:1129:29: ( precondition ( postcondition )? )
                    // BON.g:1129:30: precondition ( postcondition )?
                    {
                    pushFollow(FOLLOW_precondition_in_contracting_conditions17796);
                    precondition220=precondition();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_precondition.add(precondition220.getTree());
                    // BON.g:1129:43: ( postcondition )?
                    int alt110=2;
                    int LA110_0 = input.LA(1);

                    if ( (LA110_0==237) ) {
                        alt110=1;
                    }
                    switch (alt110) {
                        case 1 :
                            // BON.g:1129:44: postcondition
                            {
                            pushFollow(FOLLOW_postcondition_in_contracting_conditions17799);
                            postcondition221=postcondition();
                            _fsp--;
                            if (failed) return retval;
                            if ( backtracking==0 ) stream_postcondition.add(postcondition221.getTree());

                            }
                            break;

                    }


                    }


                    }
                    break;
                case 2 :
                    // BON.g:1129:63: postcondition
                    {
                    pushFollow(FOLLOW_postcondition_in_contracting_conditions17806);
                    postcondition222=postcondition();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_postcondition.add(postcondition222.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: postcondition, precondition
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1130:26: -> ^( CONTRACTING_CONDITIONS ( precondition )? ( postcondition )? )
            {
                // BON.g:1131:26: ^( CONTRACTING_CONDITIONS ( precondition )? ( postcondition )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CONTRACTING_CONDITIONS, "CONTRACTING_CONDITIONS"), root_1);

                // BON.g:1132:51: ( precondition )?
                if ( stream_precondition.hasNext() ) {
                    adaptor.addChild(root_1, stream_precondition.next());

                }
                stream_precondition.reset();
                // BON.g:1132:67: ( postcondition )?
                if ( stream_postcondition.hasNext() ) {
                    adaptor.addChild(root_1, stream_postcondition.next());

                }
                stream_postcondition.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end contracting_conditions

    public static class precondition_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start precondition
    // BON.g:1139:1: precondition : 'require' assertion -> ^( PRECONDITION assertion ) ;
    public final precondition_return precondition() throws RecognitionException {
        precondition_return retval = new precondition_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal223=null;
        assertion_return assertion224 = null;


        CommonTree string_literal223_tree=null;
        RewriteRuleTokenStream stream_236=new RewriteRuleTokenStream(adaptor,"token 236");
        RewriteRuleSubtreeStream stream_assertion=new RewriteRuleSubtreeStream(adaptor,"rule assertion");
        try {
            // BON.g:1139:15: ( 'require' assertion -> ^( PRECONDITION assertion ) )
            // BON.g:1139:18: 'require' assertion
            {
            string_literal223=(Token)input.LT(1);
            match(input,236,FOLLOW_236_in_precondition17991); if (failed) return retval;
            if ( backtracking==0 ) stream_236.add(string_literal223);

            pushFollow(FOLLOW_assertion_in_precondition17993);
            assertion224=assertion();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_assertion.add(assertion224.getTree());

            // AST REWRITE
            // elements: assertion
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1140:16: -> ^( PRECONDITION assertion )
            {
                // BON.g:1141:16: ^( PRECONDITION assertion )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(PRECONDITION, "PRECONDITION"), root_1);

                adaptor.addChild(root_1, stream_assertion.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end precondition

    public static class postcondition_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start postcondition
    // BON.g:1146:1: postcondition : 'ensure' assertion -> ^( POSTCONDITION assertion ) ;
    public final postcondition_return postcondition() throws RecognitionException {
        postcondition_return retval = new postcondition_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal225=null;
        assertion_return assertion226 = null;


        CommonTree string_literal225_tree=null;
        RewriteRuleTokenStream stream_237=new RewriteRuleTokenStream(adaptor,"token 237");
        RewriteRuleSubtreeStream stream_assertion=new RewriteRuleSubtreeStream(adaptor,"rule assertion");
        try {
            // BON.g:1146:16: ( 'ensure' assertion -> ^( POSTCONDITION assertion ) )
            // BON.g:1146:19: 'ensure' assertion
            {
            string_literal225=(Token)input.LT(1);
            match(input,237,FOLLOW_237_in_postcondition18106); if (failed) return retval;
            if ( backtracking==0 ) stream_237.add(string_literal225);

            pushFollow(FOLLOW_assertion_in_postcondition18108);
            assertion226=assertion();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_assertion.add(assertion226.getTree());

            // AST REWRITE
            // elements: assertion
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1147:17: -> ^( POSTCONDITION assertion )
            {
                // BON.g:1148:17: ^( POSTCONDITION assertion )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(POSTCONDITION, "POSTCONDITION"), root_1);

                adaptor.addChild(root_1, stream_assertion.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end postcondition

    public static class selective_export_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start selective_export
    // BON.g:1153:1: selective_export : '{' class_name_list '}' -> ^( SELECTIVE_EXPORT class_name_list ) ;
    public final selective_export_return selective_export() throws RecognitionException {
        selective_export_return retval = new selective_export_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal227=null;
        Token char_literal229=null;
        class_name_list_return class_name_list228 = null;


        CommonTree char_literal227_tree=null;
        CommonTree char_literal229_tree=null;
        RewriteRuleTokenStream stream_222=new RewriteRuleTokenStream(adaptor,"token 222");
        RewriteRuleTokenStream stream_223=new RewriteRuleTokenStream(adaptor,"token 223");
        RewriteRuleSubtreeStream stream_class_name_list=new RewriteRuleSubtreeStream(adaptor,"rule class_name_list");
        try {
            // BON.g:1155:19: ( '{' class_name_list '}' -> ^( SELECTIVE_EXPORT class_name_list ) )
            // BON.g:1155:22: '{' class_name_list '}'
            {
            char_literal227=(Token)input.LT(1);
            match(input,222,FOLLOW_222_in_selective_export18215); if (failed) return retval;
            if ( backtracking==0 ) stream_222.add(char_literal227);

            if ( backtracking==0 ) {
               getContext().enterSelectiveExport(); 
            }
            pushFollow(FOLLOW_class_name_list_in_selective_export18263);
            class_name_list228=class_name_list();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_class_name_list.add(class_name_list228.getTree());
            if ( backtracking==0 ) {
               getContext().leaveSelectiveExport(); 
            }
            char_literal229=(Token)input.LT(1);
            match(input,223,FOLLOW_223_in_selective_export18313); if (failed) return retval;
            if ( backtracking==0 ) stream_223.add(char_literal229);


            // AST REWRITE
            // elements: class_name_list
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1160:20: -> ^( SELECTIVE_EXPORT class_name_list )
            {
                // BON.g:1161:20: ^( SELECTIVE_EXPORT class_name_list )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(SELECTIVE_EXPORT, "SELECTIVE_EXPORT"), root_1);

                adaptor.addChild(root_1, stream_class_name_list.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end selective_export

    public static class feature_name_list_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start feature_name_list
    // BON.g:1166:1: feature_name_list : f1= feature_name ( ',' f= feature_name )* -> ^( FEATURE_NAME_LIST ( feature_name )+ ) ;
    public final feature_name_list_return feature_name_list() throws RecognitionException {
        feature_name_list_return retval = new feature_name_list_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal230=null;
        feature_name_return f1 = null;

        feature_name_return f = null;


        CommonTree char_literal230_tree=null;
        RewriteRuleTokenStream stream_197=new RewriteRuleTokenStream(adaptor,"token 197");
        RewriteRuleSubtreeStream stream_feature_name=new RewriteRuleSubtreeStream(adaptor,"rule feature_name");
        try {
            // BON.g:1166:20: (f1= feature_name ( ',' f= feature_name )* -> ^( FEATURE_NAME_LIST ( feature_name )+ ) )
            // BON.g:1166:23: f1= feature_name ( ',' f= feature_name )*
            {
            pushFollow(FOLLOW_feature_name_in_feature_name_list18452);
            f1=feature_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_feature_name.add(f1.getTree());
            if ( backtracking==0 ) {
               getTI().featureNameListEntry(input.toString(f1.start,f1.stop),getSLoc(((Token)f1.start))); 
            }
            // BON.g:1167:23: ( ',' f= feature_name )*
            loop112:
            do {
                int alt112=2;
                int LA112_0 = input.LA(1);

                if ( (LA112_0==197) ) {
                    alt112=1;
                }


                switch (alt112) {
            	case 1 :
            	    // BON.g:1167:24: ',' f= feature_name
            	    {
            	    char_literal230=(Token)input.LT(1);
            	    match(input,197,FOLLOW_197_in_feature_name_list18480); if (failed) return retval;
            	    if ( backtracking==0 ) stream_197.add(char_literal230);

            	    pushFollow(FOLLOW_feature_name_in_feature_name_list18484);
            	    f=feature_name();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_feature_name.add(f.getTree());
            	    if ( backtracking==0 ) {
            	       getTI().featureNameListEntry(input.toString(f.start,f.stop),getSLoc(((Token)f.start))); 
            	    }

            	    }
            	    break;

            	default :
            	    break loop112;
                }
            } while (true);


            // AST REWRITE
            // elements: feature_name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1168:21: -> ^( FEATURE_NAME_LIST ( feature_name )+ )
            {
                // BON.g:1169:21: ^( FEATURE_NAME_LIST ( feature_name )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(FEATURE_NAME_LIST, "FEATURE_NAME_LIST"), root_1);

                if ( !(stream_feature_name.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_feature_name.hasNext() ) {
                    adaptor.addChild(root_1, stream_feature_name.next());

                }
                stream_feature_name.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end feature_name_list

    public static class feature_name_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start feature_name
    // BON.g:1174:1: feature_name : ( IDENTIFIER -> ^( FEATURE_NAME IDENTIFIER ) | prefix -> ^( FEATURE_NAME prefix ) | infix -> ^( FEATURE_NAME infix ) );
    public final feature_name_return feature_name() throws RecognitionException {
        feature_name_return retval = new feature_name_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token IDENTIFIER231=null;
        prefix_return prefix232 = null;

        infix_return infix233 = null;


        CommonTree IDENTIFIER231_tree=null;
        RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
        RewriteRuleSubtreeStream stream_infix=new RewriteRuleSubtreeStream(adaptor,"rule infix");
        RewriteRuleSubtreeStream stream_prefix=new RewriteRuleSubtreeStream(adaptor,"rule prefix");
        try {
            // BON.g:1174:15: ( IDENTIFIER -> ^( FEATURE_NAME IDENTIFIER ) | prefix -> ^( FEATURE_NAME prefix ) | infix -> ^( FEATURE_NAME infix ) )
            int alt113=3;
            switch ( input.LA(1) ) {
            case IDENTIFIER:
                {
                alt113=1;
                }
                break;
            case 239:
                {
                alt113=2;
                }
                break;
            case 241:
                {
                alt113=3;
                }
                break;
            default:
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1174:1: feature_name : ( IDENTIFIER -> ^( FEATURE_NAME IDENTIFIER ) | prefix -> ^( FEATURE_NAME prefix ) | infix -> ^( FEATURE_NAME infix ) );", 113, 0, input);

                throw nvae;
            }

            switch (alt113) {
                case 1 :
                    // BON.g:1174:18: IDENTIFIER
                    {
                    IDENTIFIER231=(Token)input.LT(1);
                    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_feature_name18635); if (failed) return retval;
                    if ( backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER231);


                    // AST REWRITE
                    // elements: IDENTIFIER
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1175:16: -> ^( FEATURE_NAME IDENTIFIER )
                    {
                        // BON.g:1176:16: ^( FEATURE_NAME IDENTIFIER )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(FEATURE_NAME, "FEATURE_NAME"), root_1);

                        adaptor.addChild(root_1, stream_IDENTIFIER.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:1179:18: prefix
                    {
                    pushFollow(FOLLOW_prefix_in_feature_name18728);
                    prefix232=prefix();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_prefix.add(prefix232.getTree());

                    // AST REWRITE
                    // elements: prefix
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1180:16: -> ^( FEATURE_NAME prefix )
                    {
                        // BON.g:1181:16: ^( FEATURE_NAME prefix )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(FEATURE_NAME, "FEATURE_NAME"), root_1);

                        adaptor.addChild(root_1, stream_prefix.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 3 :
                    // BON.g:1184:18: infix
                    {
                    pushFollow(FOLLOW_infix_in_feature_name18821);
                    infix233=infix();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_infix.add(infix233.getTree());

                    // AST REWRITE
                    // elements: infix
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1185:16: -> ^( FEATURE_NAME infix )
                    {
                        // BON.g:1186:16: ^( FEATURE_NAME infix )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(FEATURE_NAME, "FEATURE_NAME"), root_1);

                        adaptor.addChild(root_1, stream_infix.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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

    public static class rename_clause_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start rename_clause
    // BON.g:1191:1: rename_clause : '{' renaming '}' -> ^( RENAME_CLAUSE renaming ) ;
    public final rename_clause_return rename_clause() throws RecognitionException {
        rename_clause_return retval = new rename_clause_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal234=null;
        Token char_literal236=null;
        renaming_return renaming235 = null;


        CommonTree char_literal234_tree=null;
        CommonTree char_literal236_tree=null;
        RewriteRuleTokenStream stream_222=new RewriteRuleTokenStream(adaptor,"token 222");
        RewriteRuleTokenStream stream_223=new RewriteRuleTokenStream(adaptor,"token 223");
        RewriteRuleSubtreeStream stream_renaming=new RewriteRuleSubtreeStream(adaptor,"rule renaming");
        try {
            // BON.g:1191:16: ( '{' renaming '}' -> ^( RENAME_CLAUSE renaming ) )
            // BON.g:1191:19: '{' renaming '}'
            {
            char_literal234=(Token)input.LT(1);
            match(input,222,FOLLOW_222_in_rename_clause18934); if (failed) return retval;
            if ( backtracking==0 ) stream_222.add(char_literal234);

            pushFollow(FOLLOW_renaming_in_rename_clause18936);
            renaming235=renaming();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_renaming.add(renaming235.getTree());
            char_literal236=(Token)input.LT(1);
            match(input,223,FOLLOW_223_in_rename_clause18938); if (failed) return retval;
            if ( backtracking==0 ) stream_223.add(char_literal236);


            // AST REWRITE
            // elements: renaming
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1192:17: -> ^( RENAME_CLAUSE renaming )
            {
                // BON.g:1193:17: ^( RENAME_CLAUSE renaming )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(RENAME_CLAUSE, "RENAME_CLAUSE"), root_1);

                adaptor.addChild(root_1, stream_renaming.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end rename_clause

    public static class renaming_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start renaming
    // BON.g:1198:1: renaming : s= '^' class_name '.' feature_name -> ^( RENAMING class_name feature_name ) ;
    public final renaming_return renaming() throws RecognitionException {
        renaming_return retval = new renaming_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token s=null;
        Token char_literal238=null;
        class_name_return class_name237 = null;

        feature_name_return feature_name239 = null;


        CommonTree s_tree=null;
        CommonTree char_literal238_tree=null;
        RewriteRuleTokenStream stream_232=new RewriteRuleTokenStream(adaptor,"token 232");
        RewriteRuleTokenStream stream_238=new RewriteRuleTokenStream(adaptor,"token 238");
        RewriteRuleSubtreeStream stream_feature_name=new RewriteRuleSubtreeStream(adaptor,"rule feature_name");
        RewriteRuleSubtreeStream stream_class_name=new RewriteRuleSubtreeStream(adaptor,"rule class_name");
        try {
            // BON.g:1198:11: (s= '^' class_name '.' feature_name -> ^( RENAMING class_name feature_name ) )
            // BON.g:1198:14: s= '^' class_name '.' feature_name
            {
            s=(Token)input.LT(1);
            match(input,238,FOLLOW_238_in_renaming19058); if (failed) return retval;
            if ( backtracking==0 ) stream_238.add(s);

            pushFollow(FOLLOW_class_name_in_renaming19060);
            class_name237=class_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_class_name.add(class_name237.getTree());
            char_literal238=(Token)input.LT(1);
            match(input,232,FOLLOW_232_in_renaming19062); if (failed) return retval;
            if ( backtracking==0 ) stream_232.add(char_literal238);

            pushFollow(FOLLOW_feature_name_in_renaming19064);
            feature_name239=feature_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_feature_name.add(feature_name239.getTree());
            if ( backtracking==0 ) {
               getTI().renaming(input.toString(class_name237.start,class_name237.stop),input.toString(feature_name239.start,feature_name239.stop),getSLoc(s)); 
            }

            // AST REWRITE
            // elements: class_name, feature_name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1200:12: -> ^( RENAMING class_name feature_name )
            {
                // BON.g:1201:12: ^( RENAMING class_name feature_name )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(RENAMING, "RENAMING"), root_1);

                adaptor.addChild(root_1, stream_class_name.next());
                adaptor.addChild(root_1, stream_feature_name.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end renaming

    public static class feature_arguments_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start feature_arguments
    // BON.g:1206:1: feature_arguments : ( feature_argument )+ -> ^( FEATURE_ARGUMENTS ( feature_argument )+ ) ;
    public final feature_arguments_return feature_arguments() throws RecognitionException {
        feature_arguments_return retval = new feature_arguments_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        feature_argument_return feature_argument240 = null;


        RewriteRuleSubtreeStream stream_feature_argument=new RewriteRuleSubtreeStream(adaptor,"rule feature_argument");
        try {
            // BON.g:1206:20: ( ( feature_argument )+ -> ^( FEATURE_ARGUMENTS ( feature_argument )+ ) )
            // BON.g:1206:23: ( feature_argument )+
            {
            // BON.g:1206:23: ( feature_argument )+
            int cnt114=0;
            loop114:
            do {
                int alt114=2;
                int LA114_0 = input.LA(1);

                if ( (LA114_0==227) ) {
                    alt114=1;
                }


                switch (alt114) {
            	case 1 :
            	    // BON.g:1206:24: feature_argument
            	    {
            	    pushFollow(FOLLOW_feature_argument_in_feature_arguments19171);
            	    feature_argument240=feature_argument();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_feature_argument.add(feature_argument240.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt114 >= 1 ) break loop114;
            	    if (backtracking>0) {failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(114, input);
                        throw eee;
                }
                cnt114++;
            } while (true);


            // AST REWRITE
            // elements: feature_argument
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1207:21: -> ^( FEATURE_ARGUMENTS ( feature_argument )+ )
            {
                // BON.g:1208:21: ^( FEATURE_ARGUMENTS ( feature_argument )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(FEATURE_ARGUMENTS, "FEATURE_ARGUMENTS"), root_1);

                if ( !(stream_feature_argument.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_feature_argument.hasNext() ) {
                    adaptor.addChild(root_1, stream_feature_argument.next());

                }
                stream_feature_argument.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end feature_arguments

    public static class feature_argument_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start feature_argument
    // BON.g:1213:1: feature_argument : '->' ( ( identifier_list ':' t1= type ) | (t2= type ) ) -> ^( FEATURE_ARGUMENT ( identifier_list )? type ) ;
    public final feature_argument_return feature_argument() throws RecognitionException {
        feature_argument_return retval = new feature_argument_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal241=null;
        Token char_literal243=null;
        type_return t1 = null;

        type_return t2 = null;

        identifier_list_return identifier_list242 = null;


        CommonTree string_literal241_tree=null;
        CommonTree char_literal243_tree=null;
        RewriteRuleTokenStream stream_227=new RewriteRuleTokenStream(adaptor,"token 227");
        RewriteRuleTokenStream stream_196=new RewriteRuleTokenStream(adaptor,"token 196");
        RewriteRuleSubtreeStream stream_identifier_list=new RewriteRuleSubtreeStream(adaptor,"rule identifier_list");
        RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type");
        try {
            // BON.g:1213:19: ( '->' ( ( identifier_list ':' t1= type ) | (t2= type ) ) -> ^( FEATURE_ARGUMENT ( identifier_list )? type ) )
            // BON.g:1213:22: '->' ( ( identifier_list ':' t1= type ) | (t2= type ) )
            {
            string_literal241=(Token)input.LT(1);
            match(input,227,FOLLOW_227_in_feature_argument19320); if (failed) return retval;
            if ( backtracking==0 ) stream_227.add(string_literal241);

            // BON.g:1214:22: ( ( identifier_list ':' t1= type ) | (t2= type ) )
            int alt115=2;
            int LA115_0 = input.LA(1);

            if ( (LA115_0==IDENTIFIER) ) {
                int LA115_1 = input.LA(2);

                if ( (LA115_1==IDENTIFIER||LA115_1==187||(LA115_1>=218 && LA115_1<=219)||(LA115_1>=227 && LA115_1<=228)||(LA115_1>=233 && LA115_1<=237)||LA115_1==239||LA115_1==241) ) {
                    alt115=2;
                }
                else if ( ((LA115_1>=196 && LA115_1<=197)) ) {
                    alt115=1;
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("1214:22: ( ( identifier_list ':' t1= type ) | (t2= type ) )", 115, 1, input);

                    throw nvae;
                }
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1214:22: ( ( identifier_list ':' t1= type ) | (t2= type ) )", 115, 0, input);

                throw nvae;
            }
            switch (alt115) {
                case 1 :
                    // BON.g:1215:25: ( identifier_list ':' t1= type )
                    {
                    // BON.g:1215:25: ( identifier_list ':' t1= type )
                    // BON.g:1215:27: identifier_list ':' t1= type
                    {
                    pushFollow(FOLLOW_identifier_list_in_feature_argument19374);
                    identifier_list242=identifier_list();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_identifier_list.add(identifier_list242.getTree());
                    char_literal243=(Token)input.LT(1);
                    match(input,196,FOLLOW_196_in_feature_argument19376); if (failed) return retval;
                    if ( backtracking==0 ) stream_196.add(char_literal243);

                    pushFollow(FOLLOW_type_in_feature_argument19380);
                    t1=type();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_type.add(t1.getTree());
                    if ( backtracking==0 ) {
                       getTI().featureArg(input.toString(identifier_list242.start,identifier_list242.stop),input.toString(t1.start,t1.stop)); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // BON.g:1216:25: (t2= type )
                    {
                    // BON.g:1216:25: (t2= type )
                    // BON.g:1216:27: t2= type
                    {
                    pushFollow(FOLLOW_type_in_feature_argument19415);
                    t2=type();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_type.add(t2.getTree());
                    if ( backtracking==0 ) {
                       getTI().featureArg(null,input.toString(t2.start,t2.stop)); 
                    }

                    }


                    }
                    break;

            }


            // AST REWRITE
            // elements: type, identifier_list
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1218:20: -> ^( FEATURE_ARGUMENT ( identifier_list )? type )
            {
                // BON.g:1219:20: ^( FEATURE_ARGUMENT ( identifier_list )? type )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(FEATURE_ARGUMENT, "FEATURE_ARGUMENT"), root_1);

                // BON.g:1220:39: ( identifier_list )?
                if ( stream_identifier_list.hasNext() ) {
                    adaptor.addChild(root_1, stream_identifier_list.next());

                }
                stream_identifier_list.reset();
                adaptor.addChild(root_1, stream_type.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end feature_argument

    public static class identifier_list_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start identifier_list
    // BON.g:1224:1: identifier_list : IDENTIFIER ( ',' IDENTIFIER )* -> ^( IDENTIFIER_LIST ( IDENTIFIER )+ ) ;
    public final identifier_list_return identifier_list() throws RecognitionException {
        identifier_list_return retval = new identifier_list_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token IDENTIFIER244=null;
        Token char_literal245=null;
        Token IDENTIFIER246=null;

        CommonTree IDENTIFIER244_tree=null;
        CommonTree char_literal245_tree=null;
        CommonTree IDENTIFIER246_tree=null;
        RewriteRuleTokenStream stream_197=new RewriteRuleTokenStream(adaptor,"token 197");
        RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");

        try {
            // BON.g:1224:18: ( IDENTIFIER ( ',' IDENTIFIER )* -> ^( IDENTIFIER_LIST ( IDENTIFIER )+ ) )
            // BON.g:1224:21: IDENTIFIER ( ',' IDENTIFIER )*
            {
            IDENTIFIER244=(Token)input.LT(1);
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_identifier_list19621); if (failed) return retval;
            if ( backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER244);

            // BON.g:1224:32: ( ',' IDENTIFIER )*
            loop116:
            do {
                int alt116=2;
                int LA116_0 = input.LA(1);

                if ( (LA116_0==197) ) {
                    alt116=1;
                }


                switch (alt116) {
            	case 1 :
            	    // BON.g:1224:33: ',' IDENTIFIER
            	    {
            	    char_literal245=(Token)input.LT(1);
            	    match(input,197,FOLLOW_197_in_identifier_list19624); if (failed) return retval;
            	    if ( backtracking==0 ) stream_197.add(char_literal245);

            	    IDENTIFIER246=(Token)input.LT(1);
            	    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_identifier_list19626); if (failed) return retval;
            	    if ( backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER246);


            	    }
            	    break;

            	default :
            	    break loop116;
                }
            } while (true);


            // AST REWRITE
            // elements: IDENTIFIER
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1225:19: -> ^( IDENTIFIER_LIST ( IDENTIFIER )+ )
            {
                // BON.g:1226:19: ^( IDENTIFIER_LIST ( IDENTIFIER )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(IDENTIFIER_LIST, "IDENTIFIER_LIST"), root_1);

                if ( !(stream_IDENTIFIER.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_IDENTIFIER.hasNext() ) {
                    adaptor.addChild(root_1, stream_IDENTIFIER.next());

                }
                stream_IDENTIFIER.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end identifier_list

    public static class prefix_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start prefix
    // BON.g:1232:1: prefix : 'prefix' '\"' prefix_operator '\"' -> ^( PREFIX prefix_operator ) ;
    public final prefix_return prefix() throws RecognitionException {
        prefix_return retval = new prefix_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal247=null;
        Token char_literal248=null;
        Token char_literal250=null;
        prefix_operator_return prefix_operator249 = null;


        CommonTree string_literal247_tree=null;
        CommonTree char_literal248_tree=null;
        CommonTree char_literal250_tree=null;
        RewriteRuleTokenStream stream_239=new RewriteRuleTokenStream(adaptor,"token 239");
        RewriteRuleTokenStream stream_240=new RewriteRuleTokenStream(adaptor,"token 240");
        RewriteRuleSubtreeStream stream_prefix_operator=new RewriteRuleSubtreeStream(adaptor,"rule prefix_operator");
        try {
            // BON.g:1232:9: ( 'prefix' '\"' prefix_operator '\"' -> ^( PREFIX prefix_operator ) )
            // BON.g:1232:12: 'prefix' '\"' prefix_operator '\"'
            {
            string_literal247=(Token)input.LT(1);
            match(input,239,FOLLOW_239_in_prefix19745); if (failed) return retval;
            if ( backtracking==0 ) stream_239.add(string_literal247);

            char_literal248=(Token)input.LT(1);
            match(input,240,FOLLOW_240_in_prefix19747); if (failed) return retval;
            if ( backtracking==0 ) stream_240.add(char_literal248);

            pushFollow(FOLLOW_prefix_operator_in_prefix19749);
            prefix_operator249=prefix_operator();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_prefix_operator.add(prefix_operator249.getTree());
            char_literal250=(Token)input.LT(1);
            match(input,240,FOLLOW_240_in_prefix19751); if (failed) return retval;
            if ( backtracking==0 ) stream_240.add(char_literal250);


            // AST REWRITE
            // elements: prefix_operator
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1233:10: -> ^( PREFIX prefix_operator )
            {
                // BON.g:1234:10: ^( PREFIX prefix_operator )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(PREFIX, "PREFIX"), root_1);

                adaptor.addChild(root_1, stream_prefix_operator.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end prefix

    public static class infix_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start infix
    // BON.g:1239:1: infix : 'infix' '\"' infix_operator '\"' -> ^( INFIX infix_operator ) ;
    public final infix_return infix() throws RecognitionException {
        infix_return retval = new infix_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal251=null;
        Token char_literal252=null;
        Token char_literal254=null;
        infix_operator_return infix_operator253 = null;


        CommonTree string_literal251_tree=null;
        CommonTree char_literal252_tree=null;
        CommonTree char_literal254_tree=null;
        RewriteRuleTokenStream stream_240=new RewriteRuleTokenStream(adaptor,"token 240");
        RewriteRuleTokenStream stream_241=new RewriteRuleTokenStream(adaptor,"token 241");
        RewriteRuleSubtreeStream stream_infix_operator=new RewriteRuleSubtreeStream(adaptor,"rule infix_operator");
        try {
            // BON.g:1239:8: ( 'infix' '\"' infix_operator '\"' -> ^( INFIX infix_operator ) )
            // BON.g:1239:11: 'infix' '\"' infix_operator '\"'
            {
            string_literal251=(Token)input.LT(1);
            match(input,241,FOLLOW_241_in_infix19828); if (failed) return retval;
            if ( backtracking==0 ) stream_241.add(string_literal251);

            char_literal252=(Token)input.LT(1);
            match(input,240,FOLLOW_240_in_infix19830); if (failed) return retval;
            if ( backtracking==0 ) stream_240.add(char_literal252);

            pushFollow(FOLLOW_infix_operator_in_infix19832);
            infix_operator253=infix_operator();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_infix_operator.add(infix_operator253.getTree());
            char_literal254=(Token)input.LT(1);
            match(input,240,FOLLOW_240_in_infix19834); if (failed) return retval;
            if ( backtracking==0 ) stream_240.add(char_literal254);


            // AST REWRITE
            // elements: infix_operator
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1240:9: -> ^( INFIX infix_operator )
            {
                // BON.g:1241:9: ^( INFIX infix_operator )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INFIX, "INFIX"), root_1);

                adaptor.addChild(root_1, stream_infix_operator.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end infix

    public static class prefix_operator_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start prefix_operator
    // BON.g:1247:1: prefix_operator : unary -> ^( PREFIX_OPERATOR unary ) ;
    public final prefix_operator_return prefix_operator() throws RecognitionException {
        prefix_operator_return retval = new prefix_operator_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        unary_return unary255 = null;


        RewriteRuleSubtreeStream stream_unary=new RewriteRuleSubtreeStream(adaptor,"rule unary");
        try {
            // BON.g:1247:18: ( unary -> ^( PREFIX_OPERATOR unary ) )
            // BON.g:1247:21: unary
            {
            pushFollow(FOLLOW_unary_in_prefix_operator19906);
            unary255=unary();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_unary.add(unary255.getTree());

            // AST REWRITE
            // elements: unary
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1248:19: -> ^( PREFIX_OPERATOR unary )
            {
                // BON.g:1249:19: ^( PREFIX_OPERATOR unary )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(PREFIX_OPERATOR, "PREFIX_OPERATOR"), root_1);

                adaptor.addChild(root_1, stream_unary.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end prefix_operator

    public static class infix_operator_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start infix_operator
    // BON.g:1255:1: infix_operator : binary -> ^( INFIX_OPERATOR binary ) ;
    public final infix_operator_return infix_operator() throws RecognitionException {
        infix_operator_return retval = new infix_operator_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        binary_return binary256 = null;


        RewriteRuleSubtreeStream stream_binary=new RewriteRuleSubtreeStream(adaptor,"rule binary");
        try {
            // BON.g:1255:17: ( binary -> ^( INFIX_OPERATOR binary ) )
            // BON.g:1255:20: binary
            {
            pushFollow(FOLLOW_binary_in_infix_operator20020);
            binary256=binary();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_binary.add(binary256.getTree());

            // AST REWRITE
            // elements: binary
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1256:18: -> ^( INFIX_OPERATOR binary )
            {
                // BON.g:1257:18: ^( INFIX_OPERATOR binary )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INFIX_OPERATOR, "INFIX_OPERATOR"), root_1);

                adaptor.addChild(root_1, stream_binary.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end infix_operator

    public static class formal_generics_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start formal_generics
    // BON.g:1263:1: formal_generics : '[' formal_generic_list ']' -> ^( FORMAL_GENERICS formal_generic_list ) ;
    public final formal_generics_return formal_generics() throws RecognitionException {
        formal_generics_return retval = new formal_generics_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal257=null;
        Token char_literal259=null;
        formal_generic_list_return formal_generic_list258 = null;


        CommonTree char_literal257_tree=null;
        CommonTree char_literal259_tree=null;
        RewriteRuleTokenStream stream_228=new RewriteRuleTokenStream(adaptor,"token 228");
        RewriteRuleTokenStream stream_229=new RewriteRuleTokenStream(adaptor,"token 229");
        RewriteRuleSubtreeStream stream_formal_generic_list=new RewriteRuleSubtreeStream(adaptor,"rule formal_generic_list");
        try {
            // BON.g:1265:18: ( '[' formal_generic_list ']' -> ^( FORMAL_GENERICS formal_generic_list ) )
            // BON.g:1265:21: '[' formal_generic_list ']'
            {
            char_literal257=(Token)input.LT(1);
            match(input,228,FOLLOW_228_in_formal_generics20132); if (failed) return retval;
            if ( backtracking==0 ) stream_228.add(char_literal257);

            pushFollow(FOLLOW_formal_generic_list_in_formal_generics20134);
            formal_generic_list258=formal_generic_list();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_formal_generic_list.add(formal_generic_list258.getTree());
            char_literal259=(Token)input.LT(1);
            match(input,229,FOLLOW_229_in_formal_generics20136); if (failed) return retval;
            if ( backtracking==0 ) stream_229.add(char_literal259);


            // AST REWRITE
            // elements: formal_generic_list
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1266:19: -> ^( FORMAL_GENERICS formal_generic_list )
            {
                // BON.g:1267:19: ^( FORMAL_GENERICS formal_generic_list )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(FORMAL_GENERICS, "FORMAL_GENERICS"), root_1);

                adaptor.addChild(root_1, stream_formal_generic_list.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end formal_generics

    public static class formal_generic_list_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start formal_generic_list
    // BON.g:1272:1: formal_generic_list : formal_generic ( ',' formal_generic )* -> ^( FORMAL_GENERIC_LIST ( formal_generic )+ ) ;
    public final formal_generic_list_return formal_generic_list() throws RecognitionException {
        formal_generic_list_return retval = new formal_generic_list_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal261=null;
        formal_generic_return formal_generic260 = null;

        formal_generic_return formal_generic262 = null;


        CommonTree char_literal261_tree=null;
        RewriteRuleTokenStream stream_197=new RewriteRuleTokenStream(adaptor,"token 197");
        RewriteRuleSubtreeStream stream_formal_generic=new RewriteRuleSubtreeStream(adaptor,"rule formal_generic");
        try {
            // BON.g:1272:22: ( formal_generic ( ',' formal_generic )* -> ^( FORMAL_GENERIC_LIST ( formal_generic )+ ) )
            // BON.g:1272:25: formal_generic ( ',' formal_generic )*
            {
            pushFollow(FOLLOW_formal_generic_in_formal_generic_list20266);
            formal_generic260=formal_generic();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_formal_generic.add(formal_generic260.getTree());
            // BON.g:1272:40: ( ',' formal_generic )*
            loop117:
            do {
                int alt117=2;
                int LA117_0 = input.LA(1);

                if ( (LA117_0==197) ) {
                    alt117=1;
                }


                switch (alt117) {
            	case 1 :
            	    // BON.g:1272:41: ',' formal_generic
            	    {
            	    char_literal261=(Token)input.LT(1);
            	    match(input,197,FOLLOW_197_in_formal_generic_list20269); if (failed) return retval;
            	    if ( backtracking==0 ) stream_197.add(char_literal261);

            	    pushFollow(FOLLOW_formal_generic_in_formal_generic_list20271);
            	    formal_generic262=formal_generic();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_formal_generic.add(formal_generic262.getTree());

            	    }
            	    break;

            	default :
            	    break loop117;
                }
            } while (true);


            // AST REWRITE
            // elements: formal_generic
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1273:23: -> ^( FORMAL_GENERIC_LIST ( formal_generic )+ )
            {
                // BON.g:1274:23: ^( FORMAL_GENERIC_LIST ( formal_generic )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(FORMAL_GENERIC_LIST, "FORMAL_GENERIC_LIST"), root_1);

                if ( !(stream_formal_generic.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_formal_generic.hasNext() ) {
                    adaptor.addChild(root_1, stream_formal_generic.next());

                }
                stream_formal_generic.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end formal_generic_list

    public static class formal_generic_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start formal_generic
    // BON.g:1279:1: formal_generic : (f= formal_generic_name -> ^( FORMAL_GENERIC formal_generic_name ) | f= formal_generic_name '->' ct= class_type -> ^( FORMAL_GENERIC formal_generic_name class_type ) );
    public final formal_generic_return formal_generic() throws RecognitionException {
        formal_generic_return retval = new formal_generic_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal263=null;
        formal_generic_name_return f = null;

        class_type_return ct = null;


        CommonTree string_literal263_tree=null;
        RewriteRuleTokenStream stream_227=new RewriteRuleTokenStream(adaptor,"token 227");
        RewriteRuleSubtreeStream stream_formal_generic_name=new RewriteRuleSubtreeStream(adaptor,"rule formal_generic_name");
        RewriteRuleSubtreeStream stream_class_type=new RewriteRuleSubtreeStream(adaptor,"rule class_type");
        try {
            // BON.g:1279:17: (f= formal_generic_name -> ^( FORMAL_GENERIC formal_generic_name ) | f= formal_generic_name '->' ct= class_type -> ^( FORMAL_GENERIC formal_generic_name class_type ) )
            int alt118=2;
            int LA118_0 = input.LA(1);

            if ( (LA118_0==IDENTIFIER) ) {
                int LA118_1 = input.LA(2);

                if ( (LA118_1==227) ) {
                    alt118=2;
                }
                else if ( (LA118_1==197||LA118_1==229) ) {
                    alt118=1;
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("1279:1: formal_generic : (f= formal_generic_name -> ^( FORMAL_GENERIC formal_generic_name ) | f= formal_generic_name '->' ct= class_type -> ^( FORMAL_GENERIC formal_generic_name class_type ) );", 118, 1, input);

                    throw nvae;
                }
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1279:1: formal_generic : (f= formal_generic_name -> ^( FORMAL_GENERIC formal_generic_name ) | f= formal_generic_name '->' ct= class_type -> ^( FORMAL_GENERIC formal_generic_name class_type ) );", 118, 0, input);

                throw nvae;
            }
            switch (alt118) {
                case 1 :
                    // BON.g:1279:21: f= formal_generic_name
                    {
                    pushFollow(FOLLOW_formal_generic_name_in_formal_generic20435);
                    f=formal_generic_name();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_formal_generic_name.add(f.getTree());
                    if ( backtracking==0 ) {
                       getTI().formalGeneric(input.toString(f.start,f.stop), null, getSLoc(((Token)f.start))); 
                    }

                    // AST REWRITE
                    // elements: formal_generic_name
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1280:10: -> ^( FORMAL_GENERIC formal_generic_name )
                    {
                        // BON.g:1281:10: ^( FORMAL_GENERIC formal_generic_name )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(FORMAL_GENERIC, "FORMAL_GENERIC"), root_1);

                        adaptor.addChild(root_1, stream_formal_generic_name.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:1284:12: f= formal_generic_name '->' ct= class_type
                    {
                    pushFollow(FOLLOW_formal_generic_name_in_formal_generic20512);
                    f=formal_generic_name();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_formal_generic_name.add(f.getTree());
                    string_literal263=(Token)input.LT(1);
                    match(input,227,FOLLOW_227_in_formal_generic20514); if (failed) return retval;
                    if ( backtracking==0 ) stream_227.add(string_literal263);

                    pushFollow(FOLLOW_class_type_in_formal_generic20518);
                    ct=class_type();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_class_type.add(ct.getTree());
                    if ( backtracking==0 ) {
                       getTI().formalGeneric(input.toString(f.start,f.stop), input.toString(ct.start,ct.stop), getSLoc(((Token)f.start))); 
                    }

                    // AST REWRITE
                    // elements: class_type, formal_generic_name
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1285:18: -> ^( FORMAL_GENERIC formal_generic_name class_type )
                    {
                        // BON.g:1286:18: ^( FORMAL_GENERIC formal_generic_name class_type )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(FORMAL_GENERIC, "FORMAL_GENERIC"), root_1);

                        adaptor.addChild(root_1, stream_formal_generic_name.next());
                        adaptor.addChild(root_1, stream_class_type.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end formal_generic

    public static class formal_generic_name_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start formal_generic_name
    // BON.g:1291:1: formal_generic_name : i= IDENTIFIER -> ^( FORMAL_GENERIC_NAME[$i] IDENTIFIER ) ;
    public final formal_generic_name_return formal_generic_name() throws RecognitionException {
        formal_generic_name_return retval = new formal_generic_name_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token i=null;

        CommonTree i_tree=null;
        RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");

        try {
            // BON.g:1291:22: (i= IDENTIFIER -> ^( FORMAL_GENERIC_NAME[$i] IDENTIFIER ) )
            // BON.g:1291:25: i= IDENTIFIER
            {
            i=(Token)input.LT(1);
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_formal_generic_name20649); if (failed) return retval;
            if ( backtracking==0 ) stream_IDENTIFIER.add(i);


            // AST REWRITE
            // elements: IDENTIFIER
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1292:23: -> ^( FORMAL_GENERIC_NAME[$i] IDENTIFIER )
            {
                // BON.g:1293:23: ^( FORMAL_GENERIC_NAME[$i] IDENTIFIER )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(FORMAL_GENERIC_NAME, i), root_1);

                adaptor.addChild(root_1, stream_IDENTIFIER.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end formal_generic_name

    public static class class_type_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start class_type
    // BON.g:1298:1: class_type : c= class_name ( actual_generics )? -> ^( CLASS_TYPE[$c.start] class_name ( actual_generics )? ) ;
    public final class_type_return class_type() throws RecognitionException {
        class_type_return retval = new class_type_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        class_name_return c = null;

        actual_generics_return actual_generics264 = null;


        RewriteRuleSubtreeStream stream_class_name=new RewriteRuleSubtreeStream(adaptor,"rule class_name");
        RewriteRuleSubtreeStream stream_actual_generics=new RewriteRuleSubtreeStream(adaptor,"rule actual_generics");
        try {
            // BON.g:1298:13: (c= class_name ( actual_generics )? -> ^( CLASS_TYPE[$c.start] class_name ( actual_generics )? ) )
            // BON.g:1298:16: c= class_name ( actual_generics )?
            {
            pushFollow(FOLLOW_class_name_in_class_type20808);
            c=class_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_class_name.add(c.getTree());
            // BON.g:1298:29: ( actual_generics )?
            int alt119=2;
            int LA119_0 = input.LA(1);

            if ( (LA119_0==228) ) {
                alt119=1;
            }
            switch (alt119) {
                case 1 :
                    // BON.g:1298:30: actual_generics
                    {
                    pushFollow(FOLLOW_actual_generics_in_class_type20811);
                    actual_generics264=actual_generics();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_actual_generics.add(actual_generics264.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: actual_generics, class_name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1299:14: -> ^( CLASS_TYPE[$c.start] class_name ( actual_generics )? )
            {
                // BON.g:1300:14: ^( CLASS_TYPE[$c.start] class_name ( actual_generics )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CLASS_TYPE, ((Token)c.start)), root_1);

                adaptor.addChild(root_1, stream_class_name.next());
                // BON.g:1301:48: ( actual_generics )?
                if ( stream_actual_generics.hasNext() ) {
                    adaptor.addChild(root_1, stream_actual_generics.next());

                }
                stream_actual_generics.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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

    public static class actual_generics_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start actual_generics
    // BON.g:1305:1: actual_generics : '[' type_list ']' -> ^( ACTUAL_GENERICS type_list ) ;
    public final actual_generics_return actual_generics() throws RecognitionException {
        actual_generics_return retval = new actual_generics_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal265=null;
        Token char_literal267=null;
        type_list_return type_list266 = null;


        CommonTree char_literal265_tree=null;
        CommonTree char_literal267_tree=null;
        RewriteRuleTokenStream stream_228=new RewriteRuleTokenStream(adaptor,"token 228");
        RewriteRuleTokenStream stream_229=new RewriteRuleTokenStream(adaptor,"token 229");
        RewriteRuleSubtreeStream stream_type_list=new RewriteRuleSubtreeStream(adaptor,"rule type_list");
        try {
            // BON.g:1305:18: ( '[' type_list ']' -> ^( ACTUAL_GENERICS type_list ) )
            // BON.g:1305:21: '[' type_list ']'
            {
            char_literal265=(Token)input.LT(1);
            match(input,228,FOLLOW_228_in_actual_generics20921); if (failed) return retval;
            if ( backtracking==0 ) stream_228.add(char_literal265);

            pushFollow(FOLLOW_type_list_in_actual_generics20923);
            type_list266=type_list();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_type_list.add(type_list266.getTree());
            char_literal267=(Token)input.LT(1);
            match(input,229,FOLLOW_229_in_actual_generics20925); if (failed) return retval;
            if ( backtracking==0 ) stream_229.add(char_literal267);


            // AST REWRITE
            // elements: type_list
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1306:19: -> ^( ACTUAL_GENERICS type_list )
            {
                // BON.g:1307:19: ^( ACTUAL_GENERICS type_list )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(ACTUAL_GENERICS, "ACTUAL_GENERICS"), root_1);

                adaptor.addChild(root_1, stream_type_list.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end actual_generics

    public static class type_list_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start type_list
    // BON.g:1312:1: type_list : type ( ',' type )* -> ^( TYPE_LIST ( type )+ ) ;
    public final type_list_return type_list() throws RecognitionException {
        type_list_return retval = new type_list_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal269=null;
        type_return type268 = null;

        type_return type270 = null;


        CommonTree char_literal269_tree=null;
        RewriteRuleTokenStream stream_197=new RewriteRuleTokenStream(adaptor,"token 197");
        RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type");
        try {
            // BON.g:1312:12: ( type ( ',' type )* -> ^( TYPE_LIST ( type )+ ) )
            // BON.g:1312:15: type ( ',' type )*
            {
            pushFollow(FOLLOW_type_in_type_list21056);
            type268=type();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_type.add(type268.getTree());
            // BON.g:1312:20: ( ',' type )*
            loop120:
            do {
                int alt120=2;
                int LA120_0 = input.LA(1);

                if ( (LA120_0==197) ) {
                    alt120=1;
                }


                switch (alt120) {
            	case 1 :
            	    // BON.g:1312:21: ',' type
            	    {
            	    char_literal269=(Token)input.LT(1);
            	    match(input,197,FOLLOW_197_in_type_list21059); if (failed) return retval;
            	    if ( backtracking==0 ) stream_197.add(char_literal269);

            	    pushFollow(FOLLOW_type_in_type_list21061);
            	    type270=type();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_type.add(type270.getTree());

            	    }
            	    break;

            	default :
            	    break loop120;
                }
            } while (true);


            // AST REWRITE
            // elements: type
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1313:13: -> ^( TYPE_LIST ( type )+ )
            {
                // BON.g:1314:13: ^( TYPE_LIST ( type )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(TYPE_LIST, "TYPE_LIST"), root_1);

                if ( !(stream_type.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_type.hasNext() ) {
                    adaptor.addChild(root_1, stream_type.next());

                }
                stream_type.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end type_list

    public static class type_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start type
    // BON.g:1322:1: type : IDENTIFIER ( actual_generics )? -> ^( TYPE IDENTIFIER ( actual_generics )? ) ;
    public final type_return type() throws RecognitionException {
        type_return retval = new type_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token IDENTIFIER271=null;
        actual_generics_return actual_generics272 = null;


        CommonTree IDENTIFIER271_tree=null;
        RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
        RewriteRuleSubtreeStream stream_actual_generics=new RewriteRuleSubtreeStream(adaptor,"rule actual_generics");
        try {
            // BON.g:1322:7: ( IDENTIFIER ( actual_generics )? -> ^( TYPE IDENTIFIER ( actual_generics )? ) )
            // BON.g:1322:10: IDENTIFIER ( actual_generics )?
            {
            IDENTIFIER271=(Token)input.LT(1);
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_type21153); if (failed) return retval;
            if ( backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER271);

            // BON.g:1322:21: ( actual_generics )?
            int alt121=2;
            int LA121_0 = input.LA(1);

            if ( (LA121_0==228) ) {
                alt121=1;
            }
            switch (alt121) {
                case 1 :
                    // BON.g:1322:22: actual_generics
                    {
                    pushFollow(FOLLOW_actual_generics_in_type21156);
                    actual_generics272=actual_generics();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_actual_generics.add(actual_generics272.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: IDENTIFIER, actual_generics
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1323:8: -> ^( TYPE IDENTIFIER ( actual_generics )? )
            {
                // BON.g:1324:8: ^( TYPE IDENTIFIER ( actual_generics )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(TYPE, "TYPE"), root_1);

                adaptor.addChild(root_1, stream_IDENTIFIER.next());
                // BON.g:1325:26: ( actual_generics )?
                if ( stream_actual_generics.hasNext() ) {
                    adaptor.addChild(root_1, stream_actual_generics.next());

                }
                stream_actual_generics.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end type

    public static class assertion_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start assertion
    // BON.g:1329:1: assertion : assertion_clause ( ';' assertion_clause )* ( ';' )? -> ^( ASSERTION ( assertion_clause )+ ) ;
    public final assertion_return assertion() throws RecognitionException {
        assertion_return retval = new assertion_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal274=null;
        Token char_literal276=null;
        assertion_clause_return assertion_clause273 = null;

        assertion_clause_return assertion_clause275 = null;


        CommonTree char_literal274_tree=null;
        CommonTree char_literal276_tree=null;
        RewriteRuleTokenStream stream_195=new RewriteRuleTokenStream(adaptor,"token 195");
        RewriteRuleSubtreeStream stream_assertion_clause=new RewriteRuleSubtreeStream(adaptor,"rule assertion_clause");
        try {
            // BON.g:1334:12: ( assertion_clause ( ';' assertion_clause )* ( ';' )? -> ^( ASSERTION ( assertion_clause )+ ) )
            // BON.g:1334:15: assertion_clause ( ';' assertion_clause )* ( ';' )?
            {
            pushFollow(FOLLOW_assertion_clause_in_assertion21220);
            assertion_clause273=assertion_clause();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_assertion_clause.add(assertion_clause273.getTree());
            // BON.g:1334:32: ( ';' assertion_clause )*
            loop122:
            do {
                int alt122=2;
                int LA122_0 = input.LA(1);

                if ( (LA122_0==195) ) {
                    int LA122_1 = input.LA(2);

                    if ( ((LA122_1>=MANIFEST_STRING && LA122_1<=IDENTIFIER)||(LA122_1>=INTEGER && LA122_1<=REAL)||LA122_1==222||LA122_1==225||(LA122_1>=242 && LA122_1<=243)||(LA122_1>=248 && LA122_1<=251)||(LA122_1>=263 && LA122_1<=264)||(LA122_1>=268 && LA122_1<=270)) ) {
                        alt122=1;
                    }


                }


                switch (alt122) {
            	case 1 :
            	    // BON.g:1334:33: ';' assertion_clause
            	    {
            	    char_literal274=(Token)input.LT(1);
            	    match(input,195,FOLLOW_195_in_assertion21223); if (failed) return retval;
            	    if ( backtracking==0 ) stream_195.add(char_literal274);

            	    pushFollow(FOLLOW_assertion_clause_in_assertion21225);
            	    assertion_clause275=assertion_clause();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_assertion_clause.add(assertion_clause275.getTree());

            	    }
            	    break;

            	default :
            	    break loop122;
                }
            } while (true);

            // BON.g:1334:56: ( ';' )?
            int alt123=2;
            int LA123_0 = input.LA(1);

            if ( (LA123_0==195) ) {
                alt123=1;
            }
            switch (alt123) {
                case 1 :
                    // BON.g:1334:56: ';'
                    {
                    char_literal276=(Token)input.LT(1);
                    match(input,195,FOLLOW_195_in_assertion21229); if (failed) return retval;
                    if ( backtracking==0 ) stream_195.add(char_literal276);


                    }
                    break;

            }


            // AST REWRITE
            // elements: assertion_clause
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1335:13: -> ^( ASSERTION ( assertion_clause )+ )
            {
                // BON.g:1336:13: ^( ASSERTION ( assertion_clause )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(ASSERTION, "ASSERTION"), root_1);

                if ( !(stream_assertion_clause.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_assertion_clause.hasNext() ) {
                    adaptor.addChild(root_1, stream_assertion_clause.next());

                }
                stream_assertion_clause.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end assertion

    public static class assertion_clause_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start assertion_clause
    // BON.g:1341:1: assertion_clause : boolean_expression -> ^( ASSERTION_CLAUSE boolean_expression ) ;
    public final assertion_clause_return assertion_clause() throws RecognitionException {
        assertion_clause_return retval = new assertion_clause_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        boolean_expression_return boolean_expression277 = null;


        RewriteRuleSubtreeStream stream_boolean_expression=new RewriteRuleSubtreeStream(adaptor,"rule boolean_expression");
        try {
            // BON.g:1341:19: ( boolean_expression -> ^( ASSERTION_CLAUSE boolean_expression ) )
            // BON.g:1341:22: boolean_expression
            {
            pushFollow(FOLLOW_boolean_expression_in_assertion_clause21329);
            boolean_expression277=boolean_expression();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_boolean_expression.add(boolean_expression277.getTree());

            // AST REWRITE
            // elements: boolean_expression
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1342:20: -> ^( ASSERTION_CLAUSE boolean_expression )
            {
                // BON.g:1343:20: ^( ASSERTION_CLAUSE boolean_expression )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(ASSERTION_CLAUSE, "ASSERTION_CLAUSE"), root_1);

                adaptor.addChild(root_1, stream_boolean_expression.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end assertion_clause

    public static class boolean_expression_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start boolean_expression
    // BON.g:1355:1: boolean_expression : expression -> ^( BOOLEAN_EXPRESSION expression ) ;
    public final boolean_expression_return boolean_expression() throws RecognitionException {
        boolean_expression_return retval = new boolean_expression_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        expression_return expression278 = null;


        RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
        try {
            // BON.g:1355:21: ( expression -> ^( BOOLEAN_EXPRESSION expression ) )
            // BON.g:1355:24: expression
            {
            pushFollow(FOLLOW_expression_in_boolean_expression21455);
            expression278=expression();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_expression.add(expression278.getTree());

            // AST REWRITE
            // elements: expression
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1356:22: -> ^( BOOLEAN_EXPRESSION expression )
            {
                // BON.g:1357:22: ^( BOOLEAN_EXPRESSION expression )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(BOOLEAN_EXPRESSION, "BOOLEAN_EXPRESSION"), root_1);

                adaptor.addChild(root_1, stream_expression.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end boolean_expression

    public static class quantification_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start quantification
    // BON.g:1362:1: quantification : q= quantifier range_expression ( restriction )? proposition -> ^( QUANTIFICATION[$q.start] quantifier range_expression ( restriction )? proposition ) ;
    public final quantification_return quantification() throws RecognitionException {
        quantification_return retval = new quantification_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        quantifier_return q = null;

        range_expression_return range_expression279 = null;

        restriction_return restriction280 = null;

        proposition_return proposition281 = null;


        RewriteRuleSubtreeStream stream_quantifier=new RewriteRuleSubtreeStream(adaptor,"rule quantifier");
        RewriteRuleSubtreeStream stream_restriction=new RewriteRuleSubtreeStream(adaptor,"rule restriction");
        RewriteRuleSubtreeStream stream_proposition=new RewriteRuleSubtreeStream(adaptor,"rule proposition");
        RewriteRuleSubtreeStream stream_range_expression=new RewriteRuleSubtreeStream(adaptor,"rule range_expression");
        try {
            // BON.g:1362:17: (q= quantifier range_expression ( restriction )? proposition -> ^( QUANTIFICATION[$q.start] quantifier range_expression ( restriction )? proposition ) )
            // BON.g:1362:20: q= quantifier range_expression ( restriction )? proposition
            {
            pushFollow(FOLLOW_quantifier_in_quantification21598);
            q=quantifier();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_quantifier.add(q.getTree());
            pushFollow(FOLLOW_range_expression_in_quantification21620);
            range_expression279=range_expression();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_range_expression.add(range_expression279.getTree());
            // BON.g:1364:20: ( restriction )?
            int alt124=2;
            int LA124_0 = input.LA(1);

            if ( (LA124_0==244) ) {
                alt124=1;
            }
            switch (alt124) {
                case 1 :
                    // BON.g:1364:21: restriction
                    {
                    pushFollow(FOLLOW_restriction_in_quantification21643);
                    restriction280=restriction();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_restriction.add(restriction280.getTree());

                    }
                    break;

            }

            pushFollow(FOLLOW_proposition_in_quantification21667);
            proposition281=proposition();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_proposition.add(proposition281.getTree());

            // AST REWRITE
            // elements: range_expression, quantifier, proposition, restriction
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1366:18: -> ^( QUANTIFICATION[$q.start] quantifier range_expression ( restriction )? proposition )
            {
                // BON.g:1367:18: ^( QUANTIFICATION[$q.start] quantifier range_expression ( restriction )? proposition )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(QUANTIFICATION, ((Token)q.start)), root_1);

                adaptor.addChild(root_1, stream_quantifier.next());
                adaptor.addChild(root_1, stream_range_expression.next());
                // BON.g:1371:20: ( restriction )?
                if ( stream_restriction.hasNext() ) {
                    adaptor.addChild(root_1, stream_restriction.next());

                }
                stream_restriction.reset();
                adaptor.addChild(root_1, stream_proposition.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end quantification

    public static class quantifier_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start quantifier
    // BON.g:1376:1: quantifier : (f= 'for_all' -> ^( QUANTIFIER[$f] 'for_all' ) | e= 'exists' -> ^( QUANTIFIER[$e] 'exists' ) );
    public final quantifier_return quantifier() throws RecognitionException {
        quantifier_return retval = new quantifier_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token f=null;
        Token e=null;

        CommonTree f_tree=null;
        CommonTree e_tree=null;
        RewriteRuleTokenStream stream_243=new RewriteRuleTokenStream(adaptor,"token 243");
        RewriteRuleTokenStream stream_242=new RewriteRuleTokenStream(adaptor,"token 242");

        try {
            // BON.g:1376:13: (f= 'for_all' -> ^( QUANTIFIER[$f] 'for_all' ) | e= 'exists' -> ^( QUANTIFIER[$e] 'exists' ) )
            int alt125=2;
            int LA125_0 = input.LA(1);

            if ( (LA125_0==242) ) {
                alt125=1;
            }
            else if ( (LA125_0==243) ) {
                alt125=2;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1376:1: quantifier : (f= 'for_all' -> ^( QUANTIFIER[$f] 'for_all' ) | e= 'exists' -> ^( QUANTIFIER[$e] 'exists' ) );", 125, 0, input);

                throw nvae;
            }
            switch (alt125) {
                case 1 :
                    // BON.g:1376:16: f= 'for_all'
                    {
                    f=(Token)input.LT(1);
                    match(input,242,FOLLOW_242_in_quantifier21885); if (failed) return retval;
                    if ( backtracking==0 ) stream_242.add(f);


                    // AST REWRITE
                    // elements: 242
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1377:14: -> ^( QUANTIFIER[$f] 'for_all' )
                    {
                        // BON.g:1378:14: ^( QUANTIFIER[$f] 'for_all' )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(QUANTIFIER, f), root_1);

                        adaptor.addChild(root_1, stream_242.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:1381:16: e= 'exists'
                    {
                    e=(Token)input.LT(1);
                    match(input,243,FOLLOW_243_in_quantifier21971); if (failed) return retval;
                    if ( backtracking==0 ) stream_243.add(e);


                    // AST REWRITE
                    // elements: 243
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1382:14: -> ^( QUANTIFIER[$e] 'exists' )
                    {
                        // BON.g:1383:14: ^( QUANTIFIER[$e] 'exists' )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(QUANTIFIER, e), root_1);

                        adaptor.addChild(root_1, stream_243.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end quantifier

    public static class range_expression_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start range_expression
    // BON.g:1388:1: range_expression : vr= variable_range ( ';' variable_range )* ( ';' )? -> ^( RANGE_EXPRESSION[$vr.start] ( variable_range )+ ) ;
    public final range_expression_return range_expression() throws RecognitionException {
        range_expression_return retval = new range_expression_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal282=null;
        Token char_literal284=null;
        variable_range_return vr = null;

        variable_range_return variable_range283 = null;


        CommonTree char_literal282_tree=null;
        CommonTree char_literal284_tree=null;
        RewriteRuleTokenStream stream_195=new RewriteRuleTokenStream(adaptor,"token 195");
        RewriteRuleSubtreeStream stream_variable_range=new RewriteRuleSubtreeStream(adaptor,"rule variable_range");
        try {
            // BON.g:1388:19: (vr= variable_range ( ';' variable_range )* ( ';' )? -> ^( RANGE_EXPRESSION[$vr.start] ( variable_range )+ ) )
            // BON.g:1388:22: vr= variable_range ( ';' variable_range )* ( ';' )?
            {
            pushFollow(FOLLOW_variable_range_in_range_expression22074);
            vr=variable_range();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_variable_range.add(vr.getTree());
            // BON.g:1388:40: ( ';' variable_range )*
            loop126:
            do {
                int alt126=2;
                int LA126_0 = input.LA(1);

                if ( (LA126_0==195) ) {
                    int LA126_1 = input.LA(2);

                    if ( (LA126_1==IDENTIFIER) ) {
                        alt126=1;
                    }


                }


                switch (alt126) {
            	case 1 :
            	    // BON.g:1388:41: ';' variable_range
            	    {
            	    char_literal282=(Token)input.LT(1);
            	    match(input,195,FOLLOW_195_in_range_expression22077); if (failed) return retval;
            	    if ( backtracking==0 ) stream_195.add(char_literal282);

            	    pushFollow(FOLLOW_variable_range_in_range_expression22079);
            	    variable_range283=variable_range();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_variable_range.add(variable_range283.getTree());

            	    }
            	    break;

            	default :
            	    break loop126;
                }
            } while (true);

            // BON.g:1388:62: ( ';' )?
            int alt127=2;
            int LA127_0 = input.LA(1);

            if ( (LA127_0==195) ) {
                alt127=1;
            }
            switch (alt127) {
                case 1 :
                    // BON.g:1388:62: ';'
                    {
                    char_literal284=(Token)input.LT(1);
                    match(input,195,FOLLOW_195_in_range_expression22083); if (failed) return retval;
                    if ( backtracking==0 ) stream_195.add(char_literal284);


                    }
                    break;

            }


            // AST REWRITE
            // elements: variable_range
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1389:20: -> ^( RANGE_EXPRESSION[$vr.start] ( variable_range )+ )
            {
                // BON.g:1390:20: ^( RANGE_EXPRESSION[$vr.start] ( variable_range )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(RANGE_EXPRESSION, ((Token)vr.start)), root_1);

                if ( !(stream_variable_range.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_variable_range.hasNext() ) {
                    adaptor.addChild(root_1, stream_variable_range.next());

                }
                stream_variable_range.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end range_expression

    public static class restriction_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start restriction
    // BON.g:1395:1: restriction : st= 'such_that' boolean_expression -> ^( RESTRICTION[$st] boolean_expression ) ;
    public final restriction_return restriction() throws RecognitionException {
        restriction_return retval = new restriction_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token st=null;
        boolean_expression_return boolean_expression285 = null;


        CommonTree st_tree=null;
        RewriteRuleTokenStream stream_244=new RewriteRuleTokenStream(adaptor,"token 244");
        RewriteRuleSubtreeStream stream_boolean_expression=new RewriteRuleSubtreeStream(adaptor,"rule boolean_expression");
        try {
            // BON.g:1395:14: (st= 'such_that' boolean_expression -> ^( RESTRICTION[$st] boolean_expression ) )
            // BON.g:1395:17: st= 'such_that' boolean_expression
            {
            st=(Token)input.LT(1);
            match(input,244,FOLLOW_244_in_restriction22227); if (failed) return retval;
            if ( backtracking==0 ) stream_244.add(st);

            pushFollow(FOLLOW_boolean_expression_in_restriction22229);
            boolean_expression285=boolean_expression();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_boolean_expression.add(boolean_expression285.getTree());

            // AST REWRITE
            // elements: boolean_expression
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1396:15: -> ^( RESTRICTION[$st] boolean_expression )
            {
                // BON.g:1397:15: ^( RESTRICTION[$st] boolean_expression )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(RESTRICTION, st), root_1);

                adaptor.addChild(root_1, stream_boolean_expression.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end restriction

    public static class proposition_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start proposition
    // BON.g:1402:1: proposition : ih= 'it_holds' boolean_expression -> ^( PROPOSITION[$ih] boolean_expression ) ;
    public final proposition_return proposition() throws RecognitionException {
        proposition_return retval = new proposition_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token ih=null;
        boolean_expression_return boolean_expression286 = null;


        CommonTree ih_tree=null;
        RewriteRuleTokenStream stream_245=new RewriteRuleTokenStream(adaptor,"token 245");
        RewriteRuleSubtreeStream stream_boolean_expression=new RewriteRuleSubtreeStream(adaptor,"rule boolean_expression");
        try {
            // BON.g:1402:14: (ih= 'it_holds' boolean_expression -> ^( PROPOSITION[$ih] boolean_expression ) )
            // BON.g:1402:17: ih= 'it_holds' boolean_expression
            {
            ih=(Token)input.LT(1);
            match(input,245,FOLLOW_245_in_proposition22339); if (failed) return retval;
            if ( backtracking==0 ) stream_245.add(ih);

            pushFollow(FOLLOW_boolean_expression_in_proposition22341);
            boolean_expression286=boolean_expression();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_boolean_expression.add(boolean_expression286.getTree());

            // AST REWRITE
            // elements: boolean_expression
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1403:15: -> ^( PROPOSITION[$ih] boolean_expression )
            {
                // BON.g:1404:15: ^( PROPOSITION[$ih] boolean_expression )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(PROPOSITION, ih), root_1);

                adaptor.addChild(root_1, stream_boolean_expression.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end proposition

    public static class variable_range_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start variable_range
    // BON.g:1409:1: variable_range : ( member_range -> ^( VARIABLE_RANGE member_range ) | type_range -> ^( VARIABLE_RANGE type_range ) );
    public final variable_range_return variable_range() throws RecognitionException {
        variable_range_return retval = new variable_range_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        member_range_return member_range287 = null;

        type_range_return type_range288 = null;


        RewriteRuleSubtreeStream stream_member_range=new RewriteRuleSubtreeStream(adaptor,"rule member_range");
        RewriteRuleSubtreeStream stream_type_range=new RewriteRuleSubtreeStream(adaptor,"rule type_range");
        try {
            // BON.g:1409:17: ( member_range -> ^( VARIABLE_RANGE member_range ) | type_range -> ^( VARIABLE_RANGE type_range ) )
            int alt128=2;
            alt128 = dfa128.predict(input);
            switch (alt128) {
                case 1 :
                    // BON.g:1409:20: member_range
                    {
                    pushFollow(FOLLOW_member_range_in_variable_range22449);
                    member_range287=member_range();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_member_range.add(member_range287.getTree());

                    // AST REWRITE
                    // elements: member_range
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1410:18: -> ^( VARIABLE_RANGE member_range )
                    {
                        // BON.g:1411:18: ^( VARIABLE_RANGE member_range )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(VARIABLE_RANGE, "VARIABLE_RANGE"), root_1);

                        adaptor.addChild(root_1, stream_member_range.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:1414:20: type_range
                    {
                    pushFollow(FOLLOW_type_range_in_variable_range22552);
                    type_range288=type_range();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_type_range.add(type_range288.getTree());

                    // AST REWRITE
                    // elements: type_range
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1415:18: -> ^( VARIABLE_RANGE type_range )
                    {
                        // BON.g:1416:18: ^( VARIABLE_RANGE type_range )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(VARIABLE_RANGE, "VARIABLE_RANGE"), root_1);

                        adaptor.addChild(root_1, stream_type_range.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end variable_range

    public static class member_range_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start member_range
    // BON.g:1421:1: member_range : identifier_list 'member_of' expression -> ^( MEMBER_RANGE identifier_list expression ) ;
    public final member_range_return member_range() throws RecognitionException {
        member_range_return retval = new member_range_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal290=null;
        identifier_list_return identifier_list289 = null;

        expression_return expression291 = null;


        CommonTree string_literal290_tree=null;
        RewriteRuleTokenStream stream_246=new RewriteRuleTokenStream(adaptor,"token 246");
        RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
        RewriteRuleSubtreeStream stream_identifier_list=new RewriteRuleSubtreeStream(adaptor,"rule identifier_list");
        try {
            // BON.g:1421:15: ( identifier_list 'member_of' expression -> ^( MEMBER_RANGE identifier_list expression ) )
            // BON.g:1421:18: identifier_list 'member_of' expression
            {
            pushFollow(FOLLOW_identifier_list_in_member_range22677);
            identifier_list289=identifier_list();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_identifier_list.add(identifier_list289.getTree());
            string_literal290=(Token)input.LT(1);
            match(input,246,FOLLOW_246_in_member_range22679); if (failed) return retval;
            if ( backtracking==0 ) stream_246.add(string_literal290);

            pushFollow(FOLLOW_expression_in_member_range22681);
            expression291=expression();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_expression.add(expression291.getTree());

            // AST REWRITE
            // elements: expression, identifier_list
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1422:16: -> ^( MEMBER_RANGE identifier_list expression )
            {
                // BON.g:1423:16: ^( MEMBER_RANGE identifier_list expression )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(MEMBER_RANGE, "MEMBER_RANGE"), root_1);

                adaptor.addChild(root_1, stream_identifier_list.next());
                adaptor.addChild(root_1, stream_expression.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end member_range

    public static class type_range_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start type_range
    // BON.g:1428:1: type_range : identifier_list ':' type -> ^( TYPE_RANGE identifier_list type ) ;
    public final type_range_return type_range() throws RecognitionException {
        type_range_return retval = new type_range_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal293=null;
        identifier_list_return identifier_list292 = null;

        type_return type294 = null;


        CommonTree char_literal293_tree=null;
        RewriteRuleTokenStream stream_196=new RewriteRuleTokenStream(adaptor,"token 196");
        RewriteRuleSubtreeStream stream_identifier_list=new RewriteRuleSubtreeStream(adaptor,"rule identifier_list");
        RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type");
        try {
            // BON.g:1428:13: ( identifier_list ':' type -> ^( TYPE_RANGE identifier_list type ) )
            // BON.g:1428:16: identifier_list ':' type
            {
            pushFollow(FOLLOW_identifier_list_in_type_range22797);
            identifier_list292=identifier_list();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_identifier_list.add(identifier_list292.getTree());
            char_literal293=(Token)input.LT(1);
            match(input,196,FOLLOW_196_in_type_range22799); if (failed) return retval;
            if ( backtracking==0 ) stream_196.add(char_literal293);

            pushFollow(FOLLOW_type_in_type_range22801);
            type294=type();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_type.add(type294.getTree());

            // AST REWRITE
            // elements: type, identifier_list
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1429:14: -> ^( TYPE_RANGE identifier_list type )
            {
                // BON.g:1430:14: ^( TYPE_RANGE identifier_list type )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(TYPE_RANGE, "TYPE_RANGE"), root_1);

                adaptor.addChild(root_1, stream_identifier_list.next());
                adaptor.addChild(root_1, stream_type.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end type_range

    public static class call_chain_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start call_chain
    // BON.g:1435:1: call_chain : unqualified_call ( '.' unqualified_call )* -> ^( CALL_CHAIN ( unqualified_call )+ ) ;
    public final call_chain_return call_chain() throws RecognitionException {
        call_chain_return retval = new call_chain_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal296=null;
        unqualified_call_return unqualified_call295 = null;

        unqualified_call_return unqualified_call297 = null;


        CommonTree char_literal296_tree=null;
        RewriteRuleTokenStream stream_232=new RewriteRuleTokenStream(adaptor,"token 232");
        RewriteRuleSubtreeStream stream_unqualified_call=new RewriteRuleSubtreeStream(adaptor,"rule unqualified_call");
        try {
            // BON.g:1446:13: ( unqualified_call ( '.' unqualified_call )* -> ^( CALL_CHAIN ( unqualified_call )+ ) )
            // BON.g:1446:16: unqualified_call ( '.' unqualified_call )*
            {
            pushFollow(FOLLOW_unqualified_call_in_call_chain22935);
            unqualified_call295=unqualified_call();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_unqualified_call.add(unqualified_call295.getTree());
            // BON.g:1446:33: ( '.' unqualified_call )*
            loop129:
            do {
                int alt129=2;
                int LA129_0 = input.LA(1);

                if ( (LA129_0==232) ) {
                    alt129=1;
                }


                switch (alt129) {
            	case 1 :
            	    // BON.g:1446:34: '.' unqualified_call
            	    {
            	    char_literal296=(Token)input.LT(1);
            	    match(input,232,FOLLOW_232_in_call_chain22938); if (failed) return retval;
            	    if ( backtracking==0 ) stream_232.add(char_literal296);

            	    pushFollow(FOLLOW_unqualified_call_in_call_chain22940);
            	    unqualified_call297=unqualified_call();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_unqualified_call.add(unqualified_call297.getTree());

            	    }
            	    break;

            	default :
            	    break loop129;
                }
            } while (true);


            // AST REWRITE
            // elements: unqualified_call
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1447:14: -> ^( CALL_CHAIN ( unqualified_call )+ )
            {
                // BON.g:1448:14: ^( CALL_CHAIN ( unqualified_call )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CALL_CHAIN, "CALL_CHAIN"), root_1);

                if ( !(stream_unqualified_call.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_unqualified_call.hasNext() ) {
                    adaptor.addChild(root_1, stream_unqualified_call.next());

                }
                stream_unqualified_call.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end call_chain

    public static class unqualified_call_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start unqualified_call
    // BON.g:1453:1: unqualified_call : IDENTIFIER ( actual_arguments )? -> ^( UNQUALIFIED_CALL IDENTIFIER ( actual_arguments )? ) ;
    public final unqualified_call_return unqualified_call() throws RecognitionException {
        unqualified_call_return retval = new unqualified_call_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token IDENTIFIER298=null;
        actual_arguments_return actual_arguments299 = null;


        CommonTree IDENTIFIER298_tree=null;
        RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
        RewriteRuleSubtreeStream stream_actual_arguments=new RewriteRuleSubtreeStream(adaptor,"rule actual_arguments");
        try {
            // BON.g:1453:19: ( IDENTIFIER ( actual_arguments )? -> ^( UNQUALIFIED_CALL IDENTIFIER ( actual_arguments )? ) )
            // BON.g:1453:22: IDENTIFIER ( actual_arguments )?
            {
            IDENTIFIER298=(Token)input.LT(1);
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_unqualified_call23047); if (failed) return retval;
            if ( backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER298);

            // BON.g:1453:33: ( actual_arguments )?
            int alt130=2;
            int LA130_0 = input.LA(1);

            if ( (LA130_0==225) ) {
                alt130=1;
            }
            switch (alt130) {
                case 1 :
                    // BON.g:1453:34: actual_arguments
                    {
                    pushFollow(FOLLOW_actual_arguments_in_unqualified_call23050);
                    actual_arguments299=actual_arguments();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_actual_arguments.add(actual_arguments299.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: actual_arguments, IDENTIFIER
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1454:20: -> ^( UNQUALIFIED_CALL IDENTIFIER ( actual_arguments )? )
            {
                // BON.g:1455:20: ^( UNQUALIFIED_CALL IDENTIFIER ( actual_arguments )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(UNQUALIFIED_CALL, "UNQUALIFIED_CALL"), root_1);

                adaptor.addChild(root_1, stream_IDENTIFIER.next());
                // BON.g:1456:50: ( actual_arguments )?
                if ( stream_actual_arguments.hasNext() ) {
                    adaptor.addChild(root_1, stream_actual_arguments.next());

                }
                stream_actual_arguments.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end unqualified_call

    public static class actual_arguments_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start actual_arguments
    // BON.g:1460:1: actual_arguments : '(' ( expression_list )? ')' -> ^( ACTUAL_ARGUMENTS ( expression_list )? ) ;
    public final actual_arguments_return actual_arguments() throws RecognitionException {
        actual_arguments_return retval = new actual_arguments_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal300=null;
        Token char_literal302=null;
        expression_list_return expression_list301 = null;


        CommonTree char_literal300_tree=null;
        CommonTree char_literal302_tree=null;
        RewriteRuleTokenStream stream_225=new RewriteRuleTokenStream(adaptor,"token 225");
        RewriteRuleTokenStream stream_226=new RewriteRuleTokenStream(adaptor,"token 226");
        RewriteRuleSubtreeStream stream_expression_list=new RewriteRuleSubtreeStream(adaptor,"rule expression_list");
        try {
            // BON.g:1460:19: ( '(' ( expression_list )? ')' -> ^( ACTUAL_ARGUMENTS ( expression_list )? ) )
            // BON.g:1460:22: '(' ( expression_list )? ')'
            {
            char_literal300=(Token)input.LT(1);
            match(input,225,FOLLOW_225_in_actual_arguments23194); if (failed) return retval;
            if ( backtracking==0 ) stream_225.add(char_literal300);

            // BON.g:1460:26: ( expression_list )?
            int alt131=2;
            int LA131_0 = input.LA(1);

            if ( ((LA131_0>=MANIFEST_STRING && LA131_0<=IDENTIFIER)||(LA131_0>=INTEGER && LA131_0<=REAL)||LA131_0==222||LA131_0==225||(LA131_0>=242 && LA131_0<=243)||(LA131_0>=248 && LA131_0<=251)||(LA131_0>=263 && LA131_0<=264)||(LA131_0>=268 && LA131_0<=270)) ) {
                alt131=1;
            }
            switch (alt131) {
                case 1 :
                    // BON.g:1460:26: expression_list
                    {
                    pushFollow(FOLLOW_expression_list_in_actual_arguments23196);
                    expression_list301=expression_list();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_expression_list.add(expression_list301.getTree());

                    }
                    break;

            }

            char_literal302=(Token)input.LT(1);
            match(input,226,FOLLOW_226_in_actual_arguments23199); if (failed) return retval;
            if ( backtracking==0 ) stream_226.add(char_literal302);


            // AST REWRITE
            // elements: expression_list
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1461:20: -> ^( ACTUAL_ARGUMENTS ( expression_list )? )
            {
                // BON.g:1462:20: ^( ACTUAL_ARGUMENTS ( expression_list )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(ACTUAL_ARGUMENTS, "ACTUAL_ARGUMENTS"), root_1);

                // BON.g:1463:39: ( expression_list )?
                if ( stream_expression_list.hasNext() ) {
                    adaptor.addChild(root_1, stream_expression_list.next());

                }
                stream_expression_list.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end actual_arguments

    public static class expression_list_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start expression_list
    // BON.g:1467:1: expression_list : expression ( ',' expression )* -> ^( EXPRESSION_LIST ( expression )+ ) ;
    public final expression_list_return expression_list() throws RecognitionException {
        expression_list_return retval = new expression_list_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal304=null;
        expression_return expression303 = null;

        expression_return expression305 = null;


        CommonTree char_literal304_tree=null;
        RewriteRuleTokenStream stream_197=new RewriteRuleTokenStream(adaptor,"token 197");
        RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
        try {
            // BON.g:1467:18: ( expression ( ',' expression )* -> ^( EXPRESSION_LIST ( expression )+ ) )
            // BON.g:1467:21: expression ( ',' expression )*
            {
            pushFollow(FOLLOW_expression_in_expression_list23333);
            expression303=expression();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_expression.add(expression303.getTree());
            // BON.g:1467:32: ( ',' expression )*
            loop132:
            do {
                int alt132=2;
                int LA132_0 = input.LA(1);

                if ( (LA132_0==197) ) {
                    alt132=1;
                }


                switch (alt132) {
            	case 1 :
            	    // BON.g:1467:33: ',' expression
            	    {
            	    char_literal304=(Token)input.LT(1);
            	    match(input,197,FOLLOW_197_in_expression_list23336); if (failed) return retval;
            	    if ( backtracking==0 ) stream_197.add(char_literal304);

            	    pushFollow(FOLLOW_expression_in_expression_list23338);
            	    expression305=expression();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_expression.add(expression305.getTree());

            	    }
            	    break;

            	default :
            	    break loop132;
                }
            } while (true);


            // AST REWRITE
            // elements: expression
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1468:19: -> ^( EXPRESSION_LIST ( expression )+ )
            {
                // BON.g:1469:19: ^( EXPRESSION_LIST ( expression )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(EXPRESSION_LIST, "EXPRESSION_LIST"), root_1);

                if ( !(stream_expression.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_expression.hasNext() ) {
                    adaptor.addChild(root_1, stream_expression.next());

                }
                stream_expression.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end expression_list

    public static class enumerated_set_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start enumerated_set
    // BON.g:1484:1: enumerated_set : '{' enumeration_list '}' -> ^( ENUMERATED_SET enumeration_list ) ;
    public final enumerated_set_return enumerated_set() throws RecognitionException {
        enumerated_set_return retval = new enumerated_set_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal306=null;
        Token char_literal308=null;
        enumeration_list_return enumeration_list307 = null;


        CommonTree char_literal306_tree=null;
        CommonTree char_literal308_tree=null;
        RewriteRuleTokenStream stream_222=new RewriteRuleTokenStream(adaptor,"token 222");
        RewriteRuleTokenStream stream_223=new RewriteRuleTokenStream(adaptor,"token 223");
        RewriteRuleSubtreeStream stream_enumeration_list=new RewriteRuleSubtreeStream(adaptor,"rule enumeration_list");
        try {
            // BON.g:1499:17: ( '{' enumeration_list '}' -> ^( ENUMERATED_SET enumeration_list ) )
            // BON.g:1499:20: '{' enumeration_list '}'
            {
            char_literal306=(Token)input.LT(1);
            match(input,222,FOLLOW_222_in_enumerated_set23542); if (failed) return retval;
            if ( backtracking==0 ) stream_222.add(char_literal306);

            pushFollow(FOLLOW_enumeration_list_in_enumerated_set23544);
            enumeration_list307=enumeration_list();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_enumeration_list.add(enumeration_list307.getTree());
            char_literal308=(Token)input.LT(1);
            match(input,223,FOLLOW_223_in_enumerated_set23546); if (failed) return retval;
            if ( backtracking==0 ) stream_223.add(char_literal308);


            // AST REWRITE
            // elements: enumeration_list
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1500:18: -> ^( ENUMERATED_SET enumeration_list )
            {
                // BON.g:1501:18: ^( ENUMERATED_SET enumeration_list )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(ENUMERATED_SET, "ENUMERATED_SET"), root_1);

                adaptor.addChild(root_1, stream_enumeration_list.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end enumerated_set

    public static class enumeration_list_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start enumeration_list
    // BON.g:1506:1: enumeration_list : enumeration_element ( ',' enumeration_element )* -> ^( ENUMERATION_LIST ( enumeration_element )+ ) ;
    public final enumeration_list_return enumeration_list() throws RecognitionException {
        enumeration_list_return retval = new enumeration_list_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal310=null;
        enumeration_element_return enumeration_element309 = null;

        enumeration_element_return enumeration_element311 = null;


        CommonTree char_literal310_tree=null;
        RewriteRuleTokenStream stream_197=new RewriteRuleTokenStream(adaptor,"token 197");
        RewriteRuleSubtreeStream stream_enumeration_element=new RewriteRuleSubtreeStream(adaptor,"rule enumeration_element");
        try {
            // BON.g:1506:19: ( enumeration_element ( ',' enumeration_element )* -> ^( ENUMERATION_LIST ( enumeration_element )+ ) )
            // BON.g:1506:22: enumeration_element ( ',' enumeration_element )*
            {
            pushFollow(FOLLOW_enumeration_element_in_enumeration_list23670);
            enumeration_element309=enumeration_element();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_enumeration_element.add(enumeration_element309.getTree());
            // BON.g:1506:42: ( ',' enumeration_element )*
            loop133:
            do {
                int alt133=2;
                int LA133_0 = input.LA(1);

                if ( (LA133_0==197) ) {
                    alt133=1;
                }


                switch (alt133) {
            	case 1 :
            	    // BON.g:1506:43: ',' enumeration_element
            	    {
            	    char_literal310=(Token)input.LT(1);
            	    match(input,197,FOLLOW_197_in_enumeration_list23673); if (failed) return retval;
            	    if ( backtracking==0 ) stream_197.add(char_literal310);

            	    pushFollow(FOLLOW_enumeration_element_in_enumeration_list23675);
            	    enumeration_element311=enumeration_element();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_enumeration_element.add(enumeration_element311.getTree());

            	    }
            	    break;

            	default :
            	    break loop133;
                }
            } while (true);


            // AST REWRITE
            // elements: enumeration_element
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1507:20: -> ^( ENUMERATION_LIST ( enumeration_element )+ )
            {
                // BON.g:1508:20: ^( ENUMERATION_LIST ( enumeration_element )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(ENUMERATION_LIST, "ENUMERATION_LIST"), root_1);

                if ( !(stream_enumeration_element.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_enumeration_element.hasNext() ) {
                    adaptor.addChild(root_1, stream_enumeration_element.next());

                }
                stream_enumeration_element.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end enumeration_list

    public static class enumeration_element_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start enumeration_element
    // BON.g:1513:1: enumeration_element : ( expression -> ^( ENUMERATION_ELEMENT expression ) | interval -> ^( ENUMERATION_ELEMENT interval ) );
    public final enumeration_element_return enumeration_element() throws RecognitionException {
        enumeration_element_return retval = new enumeration_element_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        expression_return expression312 = null;

        interval_return interval313 = null;


        RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
        RewriteRuleSubtreeStream stream_interval=new RewriteRuleSubtreeStream(adaptor,"rule interval");
        try {
            // BON.g:1513:22: ( expression -> ^( ENUMERATION_ELEMENT expression ) | interval -> ^( ENUMERATION_ELEMENT interval ) )
            int alt134=2;
            switch ( input.LA(1) ) {
            case MANIFEST_STRING:
            case IDENTIFIER:
            case REAL:
            case 222:
            case 225:
            case 242:
            case 243:
            case 248:
            case 249:
            case 250:
            case 251:
            case 268:
            case 269:
            case 270:
                {
                alt134=1;
                }
                break;
            case CHARACTER_CONSTANT:
                {
                int LA134_2 = input.LA(2);

                if ( (LA134_2==247) ) {
                    alt134=2;
                }
                else if ( (LA134_2==MOD_POW_OP||(LA134_2>=196 && LA134_2<=197)||LA134_2==223||LA134_2==227||LA134_2==246||(LA134_2>=262 && LA134_2<=267)||(LA134_2>=270 && LA134_2<=279)) ) {
                    alt134=1;
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("1513:1: enumeration_element : ( expression -> ^( ENUMERATION_ELEMENT expression ) | interval -> ^( ENUMERATION_ELEMENT interval ) );", 134, 2, input);

                    throw nvae;
                }
                }
                break;
            case 263:
            case 264:
                {
                int LA134_3 = input.LA(2);

                if ( ((LA134_3>=MANIFEST_STRING && LA134_3<=IDENTIFIER)||(LA134_3>=CHARACTER_CONSTANT && LA134_3<=REAL)||LA134_3==222||LA134_3==225||(LA134_3>=248 && LA134_3<=251)||(LA134_3>=263 && LA134_3<=264)||(LA134_3>=268 && LA134_3<=270)) ) {
                    alt134=1;
                }
                else if ( (LA134_3==INTEGER) ) {
                    int LA134_6 = input.LA(3);

                    if ( (LA134_6==247) ) {
                        alt134=2;
                    }
                    else if ( (LA134_6==MOD_POW_OP||(LA134_6>=196 && LA134_6<=197)||LA134_6==223||LA134_6==227||LA134_6==246||(LA134_6>=262 && LA134_6<=267)||(LA134_6>=270 && LA134_6<=279)) ) {
                        alt134=1;
                    }
                    else {
                        if (backtracking>0) {failed=true; return retval;}
                        NoViableAltException nvae =
                            new NoViableAltException("1513:1: enumeration_element : ( expression -> ^( ENUMERATION_ELEMENT expression ) | interval -> ^( ENUMERATION_ELEMENT interval ) );", 134, 6, input);

                        throw nvae;
                    }
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("1513:1: enumeration_element : ( expression -> ^( ENUMERATION_ELEMENT expression ) | interval -> ^( ENUMERATION_ELEMENT interval ) );", 134, 3, input);

                    throw nvae;
                }
                }
                break;
            case INTEGER:
                {
                int LA134_4 = input.LA(2);

                if ( (LA134_4==247) ) {
                    alt134=2;
                }
                else if ( (LA134_4==MOD_POW_OP||(LA134_4>=196 && LA134_4<=197)||LA134_4==223||LA134_4==227||LA134_4==246||(LA134_4>=262 && LA134_4<=267)||(LA134_4>=270 && LA134_4<=279)) ) {
                    alt134=1;
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("1513:1: enumeration_element : ( expression -> ^( ENUMERATION_ELEMENT expression ) | interval -> ^( ENUMERATION_ELEMENT interval ) );", 134, 4, input);

                    throw nvae;
                }
                }
                break;
            default:
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1513:1: enumeration_element : ( expression -> ^( ENUMERATION_ELEMENT expression ) | interval -> ^( ENUMERATION_ELEMENT interval ) );", 134, 0, input);

                throw nvae;
            }

            switch (alt134) {
                case 1 :
                    // BON.g:1513:25: expression
                    {
                    pushFollow(FOLLOW_expression_in_enumeration_element23809);
                    expression312=expression();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_expression.add(expression312.getTree());

                    // AST REWRITE
                    // elements: expression
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1514:23: -> ^( ENUMERATION_ELEMENT expression )
                    {
                        // BON.g:1515:23: ^( ENUMERATION_ELEMENT expression )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(ENUMERATION_ELEMENT, "ENUMERATION_ELEMENT"), root_1);

                        adaptor.addChild(root_1, stream_expression.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:1518:25: interval
                    {
                    pushFollow(FOLLOW_interval_in_enumeration_element23937);
                    interval313=interval();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_interval.add(interval313.getTree());

                    // AST REWRITE
                    // elements: interval
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1519:23: -> ^( ENUMERATION_ELEMENT interval )
                    {
                        // BON.g:1520:23: ^( ENUMERATION_ELEMENT interval )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(ENUMERATION_ELEMENT, "ENUMERATION_ELEMENT"), root_1);

                        adaptor.addChild(root_1, stream_interval.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end enumeration_element

    public static class interval_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start interval
    // BON.g:1525:1: interval : ( integer_interval -> ^( INTERVAL integer_interval ) | character_interval -> ^( INTERVAL character_interval ) );
    public final interval_return interval() throws RecognitionException {
        interval_return retval = new interval_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        integer_interval_return integer_interval314 = null;

        character_interval_return character_interval315 = null;


        RewriteRuleSubtreeStream stream_character_interval=new RewriteRuleSubtreeStream(adaptor,"rule character_interval");
        RewriteRuleSubtreeStream stream_integer_interval=new RewriteRuleSubtreeStream(adaptor,"rule integer_interval");
        try {
            // BON.g:1525:11: ( integer_interval -> ^( INTERVAL integer_interval ) | character_interval -> ^( INTERVAL character_interval ) )
            int alt135=2;
            int LA135_0 = input.LA(1);

            if ( (LA135_0==INTEGER||(LA135_0>=263 && LA135_0<=264)) ) {
                alt135=1;
            }
            else if ( (LA135_0==CHARACTER_CONSTANT) ) {
                alt135=2;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1525:1: interval : ( integer_interval -> ^( INTERVAL integer_interval ) | character_interval -> ^( INTERVAL character_interval ) );", 135, 0, input);

                throw nvae;
            }
            switch (alt135) {
                case 1 :
                    // BON.g:1525:14: integer_interval
                    {
                    pushFollow(FOLLOW_integer_interval_in_interval24092);
                    integer_interval314=integer_interval();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_integer_interval.add(integer_interval314.getTree());

                    // AST REWRITE
                    // elements: integer_interval
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1526:12: -> ^( INTERVAL integer_interval )
                    {
                        // BON.g:1527:12: ^( INTERVAL integer_interval )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INTERVAL, "INTERVAL"), root_1);

                        adaptor.addChild(root_1, stream_integer_interval.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:1530:14: character_interval
                    {
                    pushFollow(FOLLOW_character_interval_in_interval24165);
                    character_interval315=character_interval();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_character_interval.add(character_interval315.getTree());

                    // AST REWRITE
                    // elements: character_interval
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1531:12: -> ^( INTERVAL character_interval )
                    {
                        // BON.g:1532:12: ^( INTERVAL character_interval )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INTERVAL, "INTERVAL"), root_1);

                        adaptor.addChild(root_1, stream_character_interval.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end interval

    public static class integer_interval_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start integer_interval
    // BON.g:1537:1: integer_interval : integer_constant '..' integer_constant -> ^( INTEGER_INTERVAL integer_constant integer_constant ) ;
    public final integer_interval_return integer_interval() throws RecognitionException {
        integer_interval_return retval = new integer_interval_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal317=null;
        integer_constant_return integer_constant316 = null;

        integer_constant_return integer_constant318 = null;


        CommonTree string_literal317_tree=null;
        RewriteRuleTokenStream stream_247=new RewriteRuleTokenStream(adaptor,"token 247");
        RewriteRuleSubtreeStream stream_integer_constant=new RewriteRuleSubtreeStream(adaptor,"rule integer_constant");
        try {
            // BON.g:1537:19: ( integer_constant '..' integer_constant -> ^( INTEGER_INTERVAL integer_constant integer_constant ) )
            // BON.g:1537:22: integer_constant '..' integer_constant
            {
            pushFollow(FOLLOW_integer_constant_in_integer_interval24255);
            integer_constant316=integer_constant();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_integer_constant.add(integer_constant316.getTree());
            string_literal317=(Token)input.LT(1);
            match(input,247,FOLLOW_247_in_integer_interval24257); if (failed) return retval;
            if ( backtracking==0 ) stream_247.add(string_literal317);

            pushFollow(FOLLOW_integer_constant_in_integer_interval24259);
            integer_constant318=integer_constant();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_integer_constant.add(integer_constant318.getTree());

            // AST REWRITE
            // elements: integer_constant, integer_constant
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1538:20: -> ^( INTEGER_INTERVAL integer_constant integer_constant )
            {
                // BON.g:1539:20: ^( INTEGER_INTERVAL integer_constant integer_constant )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INTEGER_INTERVAL, "INTEGER_INTERVAL"), root_1);

                adaptor.addChild(root_1, stream_integer_constant.next());
                adaptor.addChild(root_1, stream_integer_constant.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end integer_interval

    public static class character_interval_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start character_interval
    // BON.g:1544:1: character_interval : CHARACTER_CONSTANT '..' CHARACTER_CONSTANT -> ^( CHARACTER_INTERVAL CHARACTER_CONSTANT CHARACTER_CONSTANT ) ;
    public final character_interval_return character_interval() throws RecognitionException {
        character_interval_return retval = new character_interval_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token CHARACTER_CONSTANT319=null;
        Token string_literal320=null;
        Token CHARACTER_CONSTANT321=null;

        CommonTree CHARACTER_CONSTANT319_tree=null;
        CommonTree string_literal320_tree=null;
        CommonTree CHARACTER_CONSTANT321_tree=null;
        RewriteRuleTokenStream stream_CHARACTER_CONSTANT=new RewriteRuleTokenStream(adaptor,"token CHARACTER_CONSTANT");
        RewriteRuleTokenStream stream_247=new RewriteRuleTokenStream(adaptor,"token 247");

        try {
            // BON.g:1544:21: ( CHARACTER_CONSTANT '..' CHARACTER_CONSTANT -> ^( CHARACTER_INTERVAL CHARACTER_CONSTANT CHARACTER_CONSTANT ) )
            // BON.g:1544:24: CHARACTER_CONSTANT '..' CHARACTER_CONSTANT
            {
            CHARACTER_CONSTANT319=(Token)input.LT(1);
            match(input,CHARACTER_CONSTANT,FOLLOW_CHARACTER_CONSTANT_in_character_interval24398); if (failed) return retval;
            if ( backtracking==0 ) stream_CHARACTER_CONSTANT.add(CHARACTER_CONSTANT319);

            string_literal320=(Token)input.LT(1);
            match(input,247,FOLLOW_247_in_character_interval24400); if (failed) return retval;
            if ( backtracking==0 ) stream_247.add(string_literal320);

            CHARACTER_CONSTANT321=(Token)input.LT(1);
            match(input,CHARACTER_CONSTANT,FOLLOW_CHARACTER_CONSTANT_in_character_interval24402); if (failed) return retval;
            if ( backtracking==0 ) stream_CHARACTER_CONSTANT.add(CHARACTER_CONSTANT321);


            // AST REWRITE
            // elements: CHARACTER_CONSTANT, CHARACTER_CONSTANT
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1545:22: -> ^( CHARACTER_INTERVAL CHARACTER_CONSTANT CHARACTER_CONSTANT )
            {
                // BON.g:1546:22: ^( CHARACTER_INTERVAL CHARACTER_CONSTANT CHARACTER_CONSTANT )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CHARACTER_INTERVAL, "CHARACTER_INTERVAL"), root_1);

                adaptor.addChild(root_1, stream_CHARACTER_CONSTANT.next());
                adaptor.addChild(root_1, stream_CHARACTER_CONSTANT.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end character_interval

    public static class constant_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start constant
    // BON.g:1550:1: constant : (mc= manifest_constant -> ^( CONSTANT[$mc.start] manifest_constant ) | c= 'Current' -> ^( CONSTANT[$c] 'Current' ) | v= 'Void' -> ^( CONSTANT[$v] 'Void' ) );
    public final constant_return constant() throws RecognitionException {
        constant_return retval = new constant_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token c=null;
        Token v=null;
        manifest_constant_return mc = null;


        CommonTree c_tree=null;
        CommonTree v_tree=null;
        RewriteRuleTokenStream stream_249=new RewriteRuleTokenStream(adaptor,"token 249");
        RewriteRuleTokenStream stream_248=new RewriteRuleTokenStream(adaptor,"token 248");
        RewriteRuleSubtreeStream stream_manifest_constant=new RewriteRuleSubtreeStream(adaptor,"rule manifest_constant");
        try {
            // BON.g:1552:11: (mc= manifest_constant -> ^( CONSTANT[$mc.start] manifest_constant ) | c= 'Current' -> ^( CONSTANT[$c] 'Current' ) | v= 'Void' -> ^( CONSTANT[$v] 'Void' ) )
            int alt136=3;
            switch ( input.LA(1) ) {
            case MANIFEST_STRING:
            case INTEGER:
            case CHARACTER_CONSTANT:
            case REAL:
            case 222:
            case 250:
            case 251:
            case 263:
            case 264:
                {
                alt136=1;
                }
                break;
            case 248:
                {
                alt136=2;
                }
                break;
            case 249:
                {
                alt136=3;
                }
                break;
            default:
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1550:1: constant : (mc= manifest_constant -> ^( CONSTANT[$mc.start] manifest_constant ) | c= 'Current' -> ^( CONSTANT[$c] 'Current' ) | v= 'Void' -> ^( CONSTANT[$v] 'Void' ) );", 136, 0, input);

                throw nvae;
            }

            switch (alt136) {
                case 1 :
                    // BON.g:1552:14: mc= manifest_constant
                    {
                    pushFollow(FOLLOW_manifest_constant_in_constant24537);
                    mc=manifest_constant();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_manifest_constant.add(mc.getTree());

                    // AST REWRITE
                    // elements: manifest_constant
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1553:12: -> ^( CONSTANT[$mc.start] manifest_constant )
                    {
                        // BON.g:1554:12: ^( CONSTANT[$mc.start] manifest_constant )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CONSTANT, ((Token)mc.start)), root_1);

                        adaptor.addChild(root_1, stream_manifest_constant.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:1557:14: c= 'Current'
                    {
                    c=(Token)input.LT(1);
                    match(input,248,FOLLOW_248_in_constant24613); if (failed) return retval;
                    if ( backtracking==0 ) stream_248.add(c);


                    // AST REWRITE
                    // elements: 248
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1558:12: -> ^( CONSTANT[$c] 'Current' )
                    {
                        // BON.g:1559:12: ^( CONSTANT[$c] 'Current' )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CONSTANT, c), root_1);

                        adaptor.addChild(root_1, stream_248.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 3 :
                    // BON.g:1562:14: v= 'Void'
                    {
                    v=(Token)input.LT(1);
                    match(input,249,FOLLOW_249_in_constant24689); if (failed) return retval;
                    if ( backtracking==0 ) stream_249.add(v);


                    // AST REWRITE
                    // elements: 249
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1563:12: -> ^( CONSTANT[$v] 'Void' )
                    {
                        // BON.g:1564:12: ^( CONSTANT[$v] 'Void' )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CONSTANT, v), root_1);

                        adaptor.addChild(root_1, stream_249.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end constant

    public static class manifest_constant_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start manifest_constant
    // BON.g:1569:1: manifest_constant : (bc= boolean_constant -> ^( MANIFEST_CONSTANT[$bc.start] boolean_constant ) | cc= CHARACTER_CONSTANT -> ^( MANIFEST_CONSTANT[$cc] CHARACTER_CONSTANT ) | ic= integer_constant -> ^( MANIFEST_CONSTANT[$ic.start] integer_constant ) | rc= real_constant -> ^( MANIFEST_CONSTANT[$rc.start] real_constant ) | ms= MANIFEST_STRING -> ^( MANIFEST_CONSTANT[$ms] MANIFEST_STRING ) | es= enumerated_set -> ^( MANIFEST_CONSTANT[$es.start] enumerated_set ) );
    public final manifest_constant_return manifest_constant() throws RecognitionException {
        manifest_constant_return retval = new manifest_constant_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token cc=null;
        Token ms=null;
        boolean_constant_return bc = null;

        integer_constant_return ic = null;

        real_constant_return rc = null;

        enumerated_set_return es = null;


        CommonTree cc_tree=null;
        CommonTree ms_tree=null;
        RewriteRuleTokenStream stream_MANIFEST_STRING=new RewriteRuleTokenStream(adaptor,"token MANIFEST_STRING");
        RewriteRuleTokenStream stream_CHARACTER_CONSTANT=new RewriteRuleTokenStream(adaptor,"token CHARACTER_CONSTANT");
        RewriteRuleSubtreeStream stream_boolean_constant=new RewriteRuleSubtreeStream(adaptor,"rule boolean_constant");
        RewriteRuleSubtreeStream stream_integer_constant=new RewriteRuleSubtreeStream(adaptor,"rule integer_constant");
        RewriteRuleSubtreeStream stream_enumerated_set=new RewriteRuleSubtreeStream(adaptor,"rule enumerated_set");
        RewriteRuleSubtreeStream stream_real_constant=new RewriteRuleSubtreeStream(adaptor,"rule real_constant");
        try {
            // BON.g:1569:20: (bc= boolean_constant -> ^( MANIFEST_CONSTANT[$bc.start] boolean_constant ) | cc= CHARACTER_CONSTANT -> ^( MANIFEST_CONSTANT[$cc] CHARACTER_CONSTANT ) | ic= integer_constant -> ^( MANIFEST_CONSTANT[$ic.start] integer_constant ) | rc= real_constant -> ^( MANIFEST_CONSTANT[$rc.start] real_constant ) | ms= MANIFEST_STRING -> ^( MANIFEST_CONSTANT[$ms] MANIFEST_STRING ) | es= enumerated_set -> ^( MANIFEST_CONSTANT[$es.start] enumerated_set ) )
            int alt137=6;
            switch ( input.LA(1) ) {
            case 250:
            case 251:
                {
                alt137=1;
                }
                break;
            case CHARACTER_CONSTANT:
                {
                alt137=2;
                }
                break;
            case 263:
            case 264:
                {
                int LA137_3 = input.LA(2);

                if ( (LA137_3==REAL) ) {
                    alt137=4;
                }
                else if ( (LA137_3==INTEGER) ) {
                    alt137=3;
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("1569:1: manifest_constant : (bc= boolean_constant -> ^( MANIFEST_CONSTANT[$bc.start] boolean_constant ) | cc= CHARACTER_CONSTANT -> ^( MANIFEST_CONSTANT[$cc] CHARACTER_CONSTANT ) | ic= integer_constant -> ^( MANIFEST_CONSTANT[$ic.start] integer_constant ) | rc= real_constant -> ^( MANIFEST_CONSTANT[$rc.start] real_constant ) | ms= MANIFEST_STRING -> ^( MANIFEST_CONSTANT[$ms] MANIFEST_STRING ) | es= enumerated_set -> ^( MANIFEST_CONSTANT[$es.start] enumerated_set ) );", 137, 3, input);

                    throw nvae;
                }
                }
                break;
            case INTEGER:
                {
                alt137=3;
                }
                break;
            case REAL:
                {
                alt137=4;
                }
                break;
            case MANIFEST_STRING:
                {
                alt137=5;
                }
                break;
            case 222:
                {
                alt137=6;
                }
                break;
            default:
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1569:1: manifest_constant : (bc= boolean_constant -> ^( MANIFEST_CONSTANT[$bc.start] boolean_constant ) | cc= CHARACTER_CONSTANT -> ^( MANIFEST_CONSTANT[$cc] CHARACTER_CONSTANT ) | ic= integer_constant -> ^( MANIFEST_CONSTANT[$ic.start] integer_constant ) | rc= real_constant -> ^( MANIFEST_CONSTANT[$rc.start] real_constant ) | ms= MANIFEST_STRING -> ^( MANIFEST_CONSTANT[$ms] MANIFEST_STRING ) | es= enumerated_set -> ^( MANIFEST_CONSTANT[$es.start] enumerated_set ) );", 137, 0, input);

                throw nvae;
            }

            switch (alt137) {
                case 1 :
                    // BON.g:1569:24: bc= boolean_constant
                    {
                    pushFollow(FOLLOW_boolean_constant_in_manifest_constant24783);
                    bc=boolean_constant();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_boolean_constant.add(bc.getTree());

                    // AST REWRITE
                    // elements: boolean_constant
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1570:22: -> ^( MANIFEST_CONSTANT[$bc.start] boolean_constant )
                    {
                        // BON.g:1571:22: ^( MANIFEST_CONSTANT[$bc.start] boolean_constant )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(MANIFEST_CONSTANT, ((Token)bc.start)), root_1);

                        adaptor.addChild(root_1, stream_boolean_constant.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:1574:24: cc= CHARACTER_CONSTANT
                    {
                    cc=(Token)input.LT(1);
                    match(input,CHARACTER_CONSTANT,FOLLOW_CHARACTER_CONSTANT_in_manifest_constant24909); if (failed) return retval;
                    if ( backtracking==0 ) stream_CHARACTER_CONSTANT.add(cc);


                    // AST REWRITE
                    // elements: CHARACTER_CONSTANT
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1575:22: -> ^( MANIFEST_CONSTANT[$cc] CHARACTER_CONSTANT )
                    {
                        // BON.g:1576:22: ^( MANIFEST_CONSTANT[$cc] CHARACTER_CONSTANT )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(MANIFEST_CONSTANT, cc), root_1);

                        adaptor.addChild(root_1, stream_CHARACTER_CONSTANT.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 3 :
                    // BON.g:1579:24: ic= integer_constant
                    {
                    pushFollow(FOLLOW_integer_constant_in_manifest_constant25035);
                    ic=integer_constant();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_integer_constant.add(ic.getTree());

                    // AST REWRITE
                    // elements: integer_constant
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1580:22: -> ^( MANIFEST_CONSTANT[$ic.start] integer_constant )
                    {
                        // BON.g:1581:22: ^( MANIFEST_CONSTANT[$ic.start] integer_constant )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(MANIFEST_CONSTANT, ((Token)ic.start)), root_1);

                        adaptor.addChild(root_1, stream_integer_constant.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 4 :
                    // BON.g:1584:24: rc= real_constant
                    {
                    pushFollow(FOLLOW_real_constant_in_manifest_constant25161);
                    rc=real_constant();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_real_constant.add(rc.getTree());

                    // AST REWRITE
                    // elements: real_constant
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1585:22: -> ^( MANIFEST_CONSTANT[$rc.start] real_constant )
                    {
                        // BON.g:1586:22: ^( MANIFEST_CONSTANT[$rc.start] real_constant )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(MANIFEST_CONSTANT, ((Token)rc.start)), root_1);

                        adaptor.addChild(root_1, stream_real_constant.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 5 :
                    // BON.g:1589:24: ms= MANIFEST_STRING
                    {
                    ms=(Token)input.LT(1);
                    match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_manifest_constant25287); if (failed) return retval;
                    if ( backtracking==0 ) stream_MANIFEST_STRING.add(ms);


                    // AST REWRITE
                    // elements: MANIFEST_STRING
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1590:22: -> ^( MANIFEST_CONSTANT[$ms] MANIFEST_STRING )
                    {
                        // BON.g:1591:22: ^( MANIFEST_CONSTANT[$ms] MANIFEST_STRING )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(MANIFEST_CONSTANT, ms), root_1);

                        adaptor.addChild(root_1, stream_MANIFEST_STRING.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 6 :
                    // BON.g:1594:24: es= enumerated_set
                    {
                    pushFollow(FOLLOW_enumerated_set_in_manifest_constant25413);
                    es=enumerated_set();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_enumerated_set.add(es.getTree());

                    // AST REWRITE
                    // elements: enumerated_set
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1595:22: -> ^( MANIFEST_CONSTANT[$es.start] enumerated_set )
                    {
                        // BON.g:1596:22: ^( MANIFEST_CONSTANT[$es.start] enumerated_set )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(MANIFEST_CONSTANT, ((Token)es.start)), root_1);

                        adaptor.addChild(root_1, stream_enumerated_set.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end manifest_constant

    public static class sign_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start sign
    // BON.g:1601:1: sign : add_sub_op -> ^( SIGN add_sub_op ) ;
    public final sign_return sign() throws RecognitionException {
        sign_return retval = new sign_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        add_sub_op_return add_sub_op322 = null;


        RewriteRuleSubtreeStream stream_add_sub_op=new RewriteRuleSubtreeStream(adaptor,"rule add_sub_op");
        try {
            // BON.g:1601:7: ( add_sub_op -> ^( SIGN add_sub_op ) )
            // BON.g:1601:10: add_sub_op
            {
            pushFollow(FOLLOW_add_sub_op_in_sign25560);
            add_sub_op322=add_sub_op();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_add_sub_op.add(add_sub_op322.getTree());

            // AST REWRITE
            // elements: add_sub_op
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1602:8: -> ^( SIGN add_sub_op )
            {
                // BON.g:1603:8: ^( SIGN add_sub_op )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(SIGN, "SIGN"), root_1);

                adaptor.addChild(root_1, stream_add_sub_op.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end sign

    public static class boolean_constant_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start boolean_constant
    // BON.g:1608:1: boolean_constant : ( 'true' -> ^( BOOLEAN_CONSTANT 'true' ) | 'false' -> ^( BOOLEAN_CONSTANT 'false' ) );
    public final boolean_constant_return boolean_constant() throws RecognitionException {
        boolean_constant_return retval = new boolean_constant_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal323=null;
        Token string_literal324=null;

        CommonTree string_literal323_tree=null;
        CommonTree string_literal324_tree=null;
        RewriteRuleTokenStream stream_250=new RewriteRuleTokenStream(adaptor,"token 250");
        RewriteRuleTokenStream stream_251=new RewriteRuleTokenStream(adaptor,"token 251");

        try {
            // BON.g:1608:19: ( 'true' -> ^( BOOLEAN_CONSTANT 'true' ) | 'false' -> ^( BOOLEAN_CONSTANT 'false' ) )
            int alt138=2;
            int LA138_0 = input.LA(1);

            if ( (LA138_0==250) ) {
                alt138=1;
            }
            else if ( (LA138_0==251) ) {
                alt138=2;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1608:1: boolean_constant : ( 'true' -> ^( BOOLEAN_CONSTANT 'true' ) | 'false' -> ^( BOOLEAN_CONSTANT 'false' ) );", 138, 0, input);

                throw nvae;
            }
            switch (alt138) {
                case 1 :
                    // BON.g:1608:22: 'true'
                    {
                    string_literal323=(Token)input.LT(1);
                    match(input,250,FOLLOW_250_in_boolean_constant25624); if (failed) return retval;
                    if ( backtracking==0 ) stream_250.add(string_literal323);


                    // AST REWRITE
                    // elements: 250
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1609:20: -> ^( BOOLEAN_CONSTANT 'true' )
                    {
                        // BON.g:1610:20: ^( BOOLEAN_CONSTANT 'true' )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(BOOLEAN_CONSTANT, "BOOLEAN_CONSTANT"), root_1);

                        adaptor.addChild(root_1, stream_250.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:1613:22: 'false'
                    {
                    string_literal324=(Token)input.LT(1);
                    match(input,251,FOLLOW_251_in_boolean_constant25737); if (failed) return retval;
                    if ( backtracking==0 ) stream_251.add(string_literal324);


                    // AST REWRITE
                    // elements: 251
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1614:20: -> ^( BOOLEAN_CONSTANT 'false' )
                    {
                        // BON.g:1615:20: ^( BOOLEAN_CONSTANT 'false' )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(BOOLEAN_CONSTANT, "BOOLEAN_CONSTANT"), root_1);

                        adaptor.addChild(root_1, stream_251.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end boolean_constant

    public static class integer_constant_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start integer_constant
    // BON.g:1627:1: integer_constant : ( sign )? i= INTEGER -> ^( INTEGER_CONSTANT[$i] ( sign )? INTEGER ) ;
    public final integer_constant_return integer_constant() throws RecognitionException {
        integer_constant_return retval = new integer_constant_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token i=null;
        sign_return sign325 = null;


        CommonTree i_tree=null;
        RewriteRuleTokenStream stream_INTEGER=new RewriteRuleTokenStream(adaptor,"token INTEGER");
        RewriteRuleSubtreeStream stream_sign=new RewriteRuleSubtreeStream(adaptor,"rule sign");
        try {
            // BON.g:1627:19: ( ( sign )? i= INTEGER -> ^( INTEGER_CONSTANT[$i] ( sign )? INTEGER ) )
            // BON.g:1627:22: ( sign )? i= INTEGER
            {
            // BON.g:1627:22: ( sign )?
            int alt139=2;
            int LA139_0 = input.LA(1);

            if ( ((LA139_0>=263 && LA139_0<=264)) ) {
                alt139=1;
            }
            switch (alt139) {
                case 1 :
                    // BON.g:1627:23: sign
                    {
                    pushFollow(FOLLOW_sign_in_integer_constant25917);
                    sign325=sign();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_sign.add(sign325.getTree());

                    }
                    break;

            }

            i=(Token)input.LT(1);
            match(input,INTEGER,FOLLOW_INTEGER_in_integer_constant25923); if (failed) return retval;
            if ( backtracking==0 ) stream_INTEGER.add(i);


            // AST REWRITE
            // elements: sign, INTEGER
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1628:20: -> ^( INTEGER_CONSTANT[$i] ( sign )? INTEGER )
            {
                // BON.g:1629:20: ^( INTEGER_CONSTANT[$i] ( sign )? INTEGER )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(INTEGER_CONSTANT, i), root_1);

                // BON.g:1631:22: ( sign )?
                if ( stream_sign.hasNext() ) {
                    adaptor.addChild(root_1, stream_sign.next());

                }
                stream_sign.reset();
                adaptor.addChild(root_1, stream_INTEGER.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end integer_constant

    public static class real_constant_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start real_constant
    // BON.g:1635:1: real_constant : ( sign )? r= REAL -> ^( REAL_CONSTANT[$r] ( sign )? REAL ) ;
    public final real_constant_return real_constant() throws RecognitionException {
        real_constant_return retval = new real_constant_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token r=null;
        sign_return sign326 = null;


        CommonTree r_tree=null;
        RewriteRuleTokenStream stream_REAL=new RewriteRuleTokenStream(adaptor,"token REAL");
        RewriteRuleSubtreeStream stream_sign=new RewriteRuleSubtreeStream(adaptor,"rule sign");
        try {
            // BON.g:1635:16: ( ( sign )? r= REAL -> ^( REAL_CONSTANT[$r] ( sign )? REAL ) )
            // BON.g:1635:19: ( sign )? r= REAL
            {
            // BON.g:1635:19: ( sign )?
            int alt140=2;
            int LA140_0 = input.LA(1);

            if ( ((LA140_0>=263 && LA140_0<=264)) ) {
                alt140=1;
            }
            switch (alt140) {
                case 1 :
                    // BON.g:1635:20: sign
                    {
                    pushFollow(FOLLOW_sign_in_real_constant26088);
                    sign326=sign();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_sign.add(sign326.getTree());

                    }
                    break;

            }

            r=(Token)input.LT(1);
            match(input,REAL,FOLLOW_REAL_in_real_constant26094); if (failed) return retval;
            if ( backtracking==0 ) stream_REAL.add(r);


            // AST REWRITE
            // elements: sign, REAL
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1636:17: -> ^( REAL_CONSTANT[$r] ( sign )? REAL )
            {
                // BON.g:1637:17: ^( REAL_CONSTANT[$r] ( sign )? REAL )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(REAL_CONSTANT, r), root_1);

                // BON.g:1639:19: ( sign )?
                if ( stream_sign.hasNext() ) {
                    adaptor.addChild(root_1, stream_sign.next());

                }
                stream_sign.reset();
                adaptor.addChild(root_1, stream_REAL.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end real_constant

    public static class dynamic_diagram_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start dynamic_diagram
    // BON.g:1643:1: dynamic_diagram : 'dynamic_diagram' ( extended_id )? ( COMMENT )? 'component' ( dynamic_block )? 'end' -> ^( DYNAMIC_DIAGRAM ( extended_id )? ( COMMENT )? ( dynamic_block )? ) ;
    public final dynamic_diagram_return dynamic_diagram() throws RecognitionException {
        dynamic_diagram_return retval = new dynamic_diagram_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal327=null;
        Token COMMENT329=null;
        Token string_literal330=null;
        Token string_literal332=null;
        extended_id_return extended_id328 = null;

        dynamic_block_return dynamic_block331 = null;


        CommonTree string_literal327_tree=null;
        CommonTree COMMENT329_tree=null;
        CommonTree string_literal330_tree=null;
        CommonTree string_literal332_tree=null;
        RewriteRuleTokenStream stream_252=new RewriteRuleTokenStream(adaptor,"token 252");
        RewriteRuleTokenStream stream_215=new RewriteRuleTokenStream(adaptor,"token 215");
        RewriteRuleTokenStream stream_COMMENT=new RewriteRuleTokenStream(adaptor,"token COMMENT");
        RewriteRuleTokenStream stream_187=new RewriteRuleTokenStream(adaptor,"token 187");
        RewriteRuleSubtreeStream stream_extended_id=new RewriteRuleSubtreeStream(adaptor,"rule extended_id");
        RewriteRuleSubtreeStream stream_dynamic_block=new RewriteRuleSubtreeStream(adaptor,"rule dynamic_block");
        try {
            // BON.g:1647:18: ( 'dynamic_diagram' ( extended_id )? ( COMMENT )? 'component' ( dynamic_block )? 'end' -> ^( DYNAMIC_DIAGRAM ( extended_id )? ( COMMENT )? ( dynamic_block )? ) )
            // BON.g:1647:21: 'dynamic_diagram' ( extended_id )? ( COMMENT )? 'component' ( dynamic_block )? 'end'
            {
            string_literal327=(Token)input.LT(1);
            match(input,252,FOLLOW_252_in_dynamic_diagram26225); if (failed) return retval;
            if ( backtracking==0 ) stream_252.add(string_literal327);

            // BON.g:1647:39: ( extended_id )?
            int alt141=2;
            int LA141_0 = input.LA(1);

            if ( (LA141_0==IDENTIFIER||LA141_0==INTEGER) ) {
                alt141=1;
            }
            switch (alt141) {
                case 1 :
                    // BON.g:1647:40: extended_id
                    {
                    pushFollow(FOLLOW_extended_id_in_dynamic_diagram26228);
                    extended_id328=extended_id();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_extended_id.add(extended_id328.getTree());

                    }
                    break;

            }

            // BON.g:1647:54: ( COMMENT )?
            int alt142=2;
            int LA142_0 = input.LA(1);

            if ( (LA142_0==COMMENT) ) {
                alt142=1;
            }
            switch (alt142) {
                case 1 :
                    // BON.g:1647:55: COMMENT
                    {
                    COMMENT329=(Token)input.LT(1);
                    match(input,COMMENT,FOLLOW_COMMENT_in_dynamic_diagram26233); if (failed) return retval;
                    if ( backtracking==0 ) stream_COMMENT.add(COMMENT329);


                    }
                    break;

            }

            string_literal330=(Token)input.LT(1);
            match(input,215,FOLLOW_215_in_dynamic_diagram26257); if (failed) return retval;
            if ( backtracking==0 ) stream_215.add(string_literal330);

            // BON.g:1648:33: ( dynamic_block )?
            int alt143=2;
            int LA143_0 = input.LA(1);

            if ( (LA143_0==IDENTIFIER||LA143_0==INTEGER||LA143_0==210||(LA143_0>=254 && LA143_0<=257)) ) {
                alt143=1;
            }
            switch (alt143) {
                case 1 :
                    // BON.g:1648:34: dynamic_block
                    {
                    pushFollow(FOLLOW_dynamic_block_in_dynamic_diagram26260);
                    dynamic_block331=dynamic_block();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_dynamic_block.add(dynamic_block331.getTree());

                    }
                    break;

            }

            string_literal332=(Token)input.LT(1);
            match(input,187,FOLLOW_187_in_dynamic_diagram26264); if (failed) return retval;
            if ( backtracking==0 ) stream_187.add(string_literal332);


            // AST REWRITE
            // elements: extended_id, COMMENT, dynamic_block
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1649:19: -> ^( DYNAMIC_DIAGRAM ( extended_id )? ( COMMENT )? ( dynamic_block )? )
            {
                // BON.g:1650:19: ^( DYNAMIC_DIAGRAM ( extended_id )? ( COMMENT )? ( dynamic_block )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(DYNAMIC_DIAGRAM, "DYNAMIC_DIAGRAM"), root_1);

                // BON.g:1652:21: ( extended_id )?
                if ( stream_extended_id.hasNext() ) {
                    adaptor.addChild(root_1, stream_extended_id.next());

                }
                stream_extended_id.reset();
                // BON.g:1652:36: ( COMMENT )?
                if ( stream_COMMENT.hasNext() ) {
                    adaptor.addChild(root_1, stream_COMMENT.next());

                }
                stream_COMMENT.reset();
                // BON.g:1653:21: ( dynamic_block )?
                if ( stream_dynamic_block.hasNext() ) {
                    adaptor.addChild(root_1, stream_dynamic_block.next());

                }
                stream_dynamic_block.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end dynamic_diagram

    public static class dynamic_block_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start dynamic_block
    // BON.g:1657:1: dynamic_block : ( dynamic_component )+ -> ^( DYNAMIC_BLOCK ( dynamic_component )+ ) ;
    public final dynamic_block_return dynamic_block() throws RecognitionException {
        dynamic_block_return retval = new dynamic_block_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        dynamic_component_return dynamic_component333 = null;


        RewriteRuleSubtreeStream stream_dynamic_component=new RewriteRuleSubtreeStream(adaptor,"rule dynamic_component");
        try {
            // BON.g:1657:16: ( ( dynamic_component )+ -> ^( DYNAMIC_BLOCK ( dynamic_component )+ ) )
            // BON.g:1657:19: ( dynamic_component )+
            {
            // BON.g:1657:19: ( dynamic_component )+
            int cnt144=0;
            loop144:
            do {
                int alt144=2;
                int LA144_0 = input.LA(1);

                if ( (LA144_0==IDENTIFIER||LA144_0==INTEGER||LA144_0==210||(LA144_0>=254 && LA144_0<=257)) ) {
                    alt144=1;
                }


                switch (alt144) {
            	case 1 :
            	    // BON.g:1657:20: dynamic_component
            	    {
            	    pushFollow(FOLLOW_dynamic_component_in_dynamic_block26448);
            	    dynamic_component333=dynamic_component();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_dynamic_component.add(dynamic_component333.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt144 >= 1 ) break loop144;
            	    if (backtracking>0) {failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(144, input);
                        throw eee;
                }
                cnt144++;
            } while (true);


            // AST REWRITE
            // elements: dynamic_component
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1658:17: -> ^( DYNAMIC_BLOCK ( dynamic_component )+ )
            {
                // BON.g:1659:17: ^( DYNAMIC_BLOCK ( dynamic_component )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(DYNAMIC_BLOCK, "DYNAMIC_BLOCK"), root_1);

                if ( !(stream_dynamic_component.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_dynamic_component.hasNext() ) {
                    adaptor.addChild(root_1, stream_dynamic_component.next());

                }
                stream_dynamic_component.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end dynamic_block

    public static class dynamic_component_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start dynamic_component
    // BON.g:1665:1: dynamic_component : ( scenario_description -> ^( DYNAMIC_COMPONENT scenario_description ) | object_group -> ^( DYNAMIC_COMPONENT object_group ) | object_stack -> ^( DYNAMIC_COMPONENT object_stack ) | object -> ^( DYNAMIC_COMPONENT object ) | message_relation -> ^( DYNAMIC_COMPONENT message_relation ) );
    public final dynamic_component_return dynamic_component() throws RecognitionException {
        dynamic_component_return retval = new dynamic_component_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        scenario_description_return scenario_description334 = null;

        object_group_return object_group335 = null;

        object_stack_return object_stack336 = null;

        object_return object337 = null;

        message_relation_return message_relation338 = null;


        RewriteRuleSubtreeStream stream_object_stack=new RewriteRuleSubtreeStream(adaptor,"rule object_stack");
        RewriteRuleSubtreeStream stream_message_relation=new RewriteRuleSubtreeStream(adaptor,"rule message_relation");
        RewriteRuleSubtreeStream stream_object_group=new RewriteRuleSubtreeStream(adaptor,"rule object_group");
        RewriteRuleSubtreeStream stream_object=new RewriteRuleSubtreeStream(adaptor,"rule object");
        RewriteRuleSubtreeStream stream_scenario_description=new RewriteRuleSubtreeStream(adaptor,"rule scenario_description");
        try {
            // BON.g:1665:20: ( scenario_description -> ^( DYNAMIC_COMPONENT scenario_description ) | object_group -> ^( DYNAMIC_COMPONENT object_group ) | object_stack -> ^( DYNAMIC_COMPONENT object_stack ) | object -> ^( DYNAMIC_COMPONENT object ) | message_relation -> ^( DYNAMIC_COMPONENT message_relation ) )
            int alt145=5;
            switch ( input.LA(1) ) {
            case 210:
                {
                alt145=1;
                }
                break;
            case 254:
            case 255:
                {
                alt145=2;
                }
                break;
            case 256:
                {
                alt145=3;
                }
                break;
            case 257:
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
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1665:1: dynamic_component : ( scenario_description -> ^( DYNAMIC_COMPONENT scenario_description ) | object_group -> ^( DYNAMIC_COMPONENT object_group ) | object_stack -> ^( DYNAMIC_COMPONENT object_stack ) | object -> ^( DYNAMIC_COMPONENT object ) | message_relation -> ^( DYNAMIC_COMPONENT message_relation ) );", 145, 0, input);

                throw nvae;
            }

            switch (alt145) {
                case 1 :
                    // BON.g:1665:24: scenario_description
                    {
                    pushFollow(FOLLOW_scenario_description_in_dynamic_component26591);
                    scenario_description334=scenario_description();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_scenario_description.add(scenario_description334.getTree());

                    // AST REWRITE
                    // elements: scenario_description
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1666:22: -> ^( DYNAMIC_COMPONENT scenario_description )
                    {
                        // BON.g:1667:22: ^( DYNAMIC_COMPONENT scenario_description )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(DYNAMIC_COMPONENT, "DYNAMIC_COMPONENT"), root_1);

                        adaptor.addChild(root_1, stream_scenario_description.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:1670:24: object_group
                    {
                    pushFollow(FOLLOW_object_group_in_dynamic_component26714);
                    object_group335=object_group();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_object_group.add(object_group335.getTree());

                    // AST REWRITE
                    // elements: object_group
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1671:22: -> ^( DYNAMIC_COMPONENT object_group )
                    {
                        // BON.g:1672:22: ^( DYNAMIC_COMPONENT object_group )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(DYNAMIC_COMPONENT, "DYNAMIC_COMPONENT"), root_1);

                        adaptor.addChild(root_1, stream_object_group.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 3 :
                    // BON.g:1675:24: object_stack
                    {
                    pushFollow(FOLLOW_object_stack_in_dynamic_component26838);
                    object_stack336=object_stack();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_object_stack.add(object_stack336.getTree());

                    // AST REWRITE
                    // elements: object_stack
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1676:22: -> ^( DYNAMIC_COMPONENT object_stack )
                    {
                        // BON.g:1677:22: ^( DYNAMIC_COMPONENT object_stack )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(DYNAMIC_COMPONENT, "DYNAMIC_COMPONENT"), root_1);

                        adaptor.addChild(root_1, stream_object_stack.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 4 :
                    // BON.g:1680:24: object
                    {
                    pushFollow(FOLLOW_object_in_dynamic_component26961);
                    object337=object();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_object.add(object337.getTree());

                    // AST REWRITE
                    // elements: object
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1681:22: -> ^( DYNAMIC_COMPONENT object )
                    {
                        // BON.g:1682:22: ^( DYNAMIC_COMPONENT object )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(DYNAMIC_COMPONENT, "DYNAMIC_COMPONENT"), root_1);

                        adaptor.addChild(root_1, stream_object.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 5 :
                    // BON.g:1685:24: message_relation
                    {
                    pushFollow(FOLLOW_message_relation_in_dynamic_component27084);
                    message_relation338=message_relation();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_message_relation.add(message_relation338.getTree());

                    // AST REWRITE
                    // elements: message_relation
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1686:22: -> ^( DYNAMIC_COMPONENT message_relation )
                    {
                        // BON.g:1687:22: ^( DYNAMIC_COMPONENT message_relation )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(DYNAMIC_COMPONENT, "DYNAMIC_COMPONENT"), root_1);

                        adaptor.addChild(root_1, stream_message_relation.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end dynamic_component

    public static class scenario_description_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start scenario_description
    // BON.g:1692:1: scenario_description : 'scenario' scenario_name ( COMMENT )? 'action' labelled_actions 'end' -> ^( SCENARIO_DESCRIPTION scenario_name ( COMMENT )? labelled_actions ) ;
    public final scenario_description_return scenario_description() throws RecognitionException {
        scenario_description_return retval = new scenario_description_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal339=null;
        Token COMMENT341=null;
        Token string_literal342=null;
        Token string_literal344=null;
        scenario_name_return scenario_name340 = null;

        labelled_actions_return labelled_actions343 = null;


        CommonTree string_literal339_tree=null;
        CommonTree COMMENT341_tree=null;
        CommonTree string_literal342_tree=null;
        CommonTree string_literal344_tree=null;
        RewriteRuleTokenStream stream_210=new RewriteRuleTokenStream(adaptor,"token 210");
        RewriteRuleTokenStream stream_COMMENT=new RewriteRuleTokenStream(adaptor,"token COMMENT");
        RewriteRuleTokenStream stream_187=new RewriteRuleTokenStream(adaptor,"token 187");
        RewriteRuleTokenStream stream_253=new RewriteRuleTokenStream(adaptor,"token 253");
        RewriteRuleSubtreeStream stream_scenario_name=new RewriteRuleSubtreeStream(adaptor,"rule scenario_name");
        RewriteRuleSubtreeStream stream_labelled_actions=new RewriteRuleSubtreeStream(adaptor,"rule labelled_actions");
        try {
            // BON.g:1694:23: ( 'scenario' scenario_name ( COMMENT )? 'action' labelled_actions 'end' -> ^( SCENARIO_DESCRIPTION scenario_name ( COMMENT )? labelled_actions ) )
            // BON.g:1694:26: 'scenario' scenario_name ( COMMENT )? 'action' labelled_actions 'end'
            {
            string_literal339=(Token)input.LT(1);
            match(input,210,FOLLOW_210_in_scenario_description27217); if (failed) return retval;
            if ( backtracking==0 ) stream_210.add(string_literal339);

            pushFollow(FOLLOW_scenario_name_in_scenario_description27219);
            scenario_name340=scenario_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_scenario_name.add(scenario_name340.getTree());
            // BON.g:1694:51: ( COMMENT )?
            int alt146=2;
            int LA146_0 = input.LA(1);

            if ( (LA146_0==COMMENT) ) {
                alt146=1;
            }
            switch (alt146) {
                case 1 :
                    // BON.g:1694:52: COMMENT
                    {
                    COMMENT341=(Token)input.LT(1);
                    match(input,COMMENT,FOLLOW_COMMENT_in_scenario_description27222); if (failed) return retval;
                    if ( backtracking==0 ) stream_COMMENT.add(COMMENT341);


                    }
                    break;

            }

            string_literal342=(Token)input.LT(1);
            match(input,253,FOLLOW_253_in_scenario_description27251); if (failed) return retval;
            if ( backtracking==0 ) stream_253.add(string_literal342);

            pushFollow(FOLLOW_labelled_actions_in_scenario_description27253);
            labelled_actions343=labelled_actions();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_labelled_actions.add(labelled_actions343.getTree());
            string_literal344=(Token)input.LT(1);
            match(input,187,FOLLOW_187_in_scenario_description27255); if (failed) return retval;
            if ( backtracking==0 ) stream_187.add(string_literal344);


            // AST REWRITE
            // elements: COMMENT, labelled_actions, scenario_name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1696:24: -> ^( SCENARIO_DESCRIPTION scenario_name ( COMMENT )? labelled_actions )
            {
                // BON.g:1697:24: ^( SCENARIO_DESCRIPTION scenario_name ( COMMENT )? labelled_actions )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(SCENARIO_DESCRIPTION, "SCENARIO_DESCRIPTION"), root_1);

                adaptor.addChild(root_1, stream_scenario_name.next());
                // BON.g:1699:40: ( COMMENT )?
                if ( stream_COMMENT.hasNext() ) {
                    adaptor.addChild(root_1, stream_COMMENT.next());

                }
                stream_COMMENT.reset();
                adaptor.addChild(root_1, stream_labelled_actions.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end scenario_description

    public static class labelled_actions_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start labelled_actions
    // BON.g:1704:1: labelled_actions : ( labelled_action )+ -> ^( LABELLED_ACTIONS ( labelled_action )+ ) ;
    public final labelled_actions_return labelled_actions() throws RecognitionException {
        labelled_actions_return retval = new labelled_actions_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        labelled_action_return labelled_action345 = null;


        RewriteRuleSubtreeStream stream_labelled_action=new RewriteRuleSubtreeStream(adaptor,"rule labelled_action");
        try {
            // BON.g:1704:19: ( ( labelled_action )+ -> ^( LABELLED_ACTIONS ( labelled_action )+ ) )
            // BON.g:1704:22: ( labelled_action )+
            {
            // BON.g:1704:22: ( labelled_action )+
            int cnt147=0;
            loop147:
            do {
                int alt147=2;
                int LA147_0 = input.LA(1);

                if ( (LA147_0==MANIFEST_STRING) ) {
                    alt147=1;
                }


                switch (alt147) {
            	case 1 :
            	    // BON.g:1704:23: labelled_action
            	    {
            	    pushFollow(FOLLOW_labelled_action_in_labelled_actions27475);
            	    labelled_action345=labelled_action();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_labelled_action.add(labelled_action345.getTree());

            	    }
            	    break;

            	default :
            	    if ( cnt147 >= 1 ) break loop147;
            	    if (backtracking>0) {failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(147, input);
                        throw eee;
                }
                cnt147++;
            } while (true);


            // AST REWRITE
            // elements: labelled_action
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1705:20: -> ^( LABELLED_ACTIONS ( labelled_action )+ )
            {
                // BON.g:1706:20: ^( LABELLED_ACTIONS ( labelled_action )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(LABELLED_ACTIONS, "LABELLED_ACTIONS"), root_1);

                if ( !(stream_labelled_action.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_labelled_action.hasNext() ) {
                    adaptor.addChild(root_1, stream_labelled_action.next());

                }
                stream_labelled_action.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end labelled_actions

    public static class labelled_action_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start labelled_action
    // BON.g:1711:1: labelled_action : action_label action_description -> ^( LABELLED_ACTION action_label action_description ) ;
    public final labelled_action_return labelled_action() throws RecognitionException {
        labelled_action_return retval = new labelled_action_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        action_label_return action_label346 = null;

        action_description_return action_description347 = null;


        RewriteRuleSubtreeStream stream_action_description=new RewriteRuleSubtreeStream(adaptor,"rule action_description");
        RewriteRuleSubtreeStream stream_action_label=new RewriteRuleSubtreeStream(adaptor,"rule action_label");
        try {
            // BON.g:1711:18: ( action_label action_description -> ^( LABELLED_ACTION action_label action_description ) )
            // BON.g:1711:21: action_label action_description
            {
            pushFollow(FOLLOW_action_label_in_labelled_action27617);
            action_label346=action_label();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_action_label.add(action_label346.getTree());
            pushFollow(FOLLOW_action_description_in_labelled_action27619);
            action_description347=action_description();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_action_description.add(action_description347.getTree());

            // AST REWRITE
            // elements: action_label, action_description
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1712:19: -> ^( LABELLED_ACTION action_label action_description )
            {
                // BON.g:1713:19: ^( LABELLED_ACTION action_label action_description )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(LABELLED_ACTION, "LABELLED_ACTION"), root_1);

                adaptor.addChild(root_1, stream_action_label.next());
                adaptor.addChild(root_1, stream_action_description.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end labelled_action

    public static class action_label_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start action_label
    // BON.g:1718:1: action_label : MANIFEST_STRING -> ^( ACTION_LABEL MANIFEST_STRING ) ;
    public final action_label_return action_label() throws RecognitionException {
        action_label_return retval = new action_label_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token MANIFEST_STRING348=null;

        CommonTree MANIFEST_STRING348_tree=null;
        RewriteRuleTokenStream stream_MANIFEST_STRING=new RewriteRuleTokenStream(adaptor,"token MANIFEST_STRING");

        try {
            // BON.g:1718:15: ( MANIFEST_STRING -> ^( ACTION_LABEL MANIFEST_STRING ) )
            // BON.g:1718:18: MANIFEST_STRING
            {
            MANIFEST_STRING348=(Token)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_action_label27752); if (failed) return retval;
            if ( backtracking==0 ) stream_MANIFEST_STRING.add(MANIFEST_STRING348);


            // AST REWRITE
            // elements: MANIFEST_STRING
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1719:16: -> ^( ACTION_LABEL MANIFEST_STRING )
            {
                // BON.g:1720:16: ^( ACTION_LABEL MANIFEST_STRING )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(ACTION_LABEL, "ACTION_LABEL"), root_1);

                adaptor.addChild(root_1, stream_MANIFEST_STRING.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end action_label

    public static class action_description_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start action_description
    // BON.g:1725:1: action_description : manifest_textblock -> ^( ACTION_DESCRIPTION manifest_textblock ) ;
    public final action_description_return action_description() throws RecognitionException {
        action_description_return retval = new action_description_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        manifest_textblock_return manifest_textblock349 = null;


        RewriteRuleSubtreeStream stream_manifest_textblock=new RewriteRuleSubtreeStream(adaptor,"rule manifest_textblock");
        try {
            // BON.g:1725:21: ( manifest_textblock -> ^( ACTION_DESCRIPTION manifest_textblock ) )
            // BON.g:1725:24: manifest_textblock
            {
            pushFollow(FOLLOW_manifest_textblock_in_action_description27865);
            manifest_textblock349=manifest_textblock();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_manifest_textblock.add(manifest_textblock349.getTree());

            // AST REWRITE
            // elements: manifest_textblock
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1726:22: -> ^( ACTION_DESCRIPTION manifest_textblock )
            {
                // BON.g:1727:22: ^( ACTION_DESCRIPTION manifest_textblock )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(ACTION_DESCRIPTION, "ACTION_DESCRIPTION"), root_1);

                adaptor.addChild(root_1, stream_manifest_textblock.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end action_description

    public static class scenario_name_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start scenario_name
    // BON.g:1732:1: scenario_name : manifest_textblock -> ^( SCENARIO_NAME MANIFEST_STRING ) ;
    public final scenario_name_return scenario_name() throws RecognitionException {
        scenario_name_return retval = new scenario_name_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        manifest_textblock_return manifest_textblock350 = null;


        RewriteRuleSubtreeStream stream_manifest_textblock=new RewriteRuleSubtreeStream(adaptor,"rule manifest_textblock");
        try {
            // BON.g:1732:16: ( manifest_textblock -> ^( SCENARIO_NAME MANIFEST_STRING ) )
            // BON.g:1732:19: manifest_textblock
            {
            pushFollow(FOLLOW_manifest_textblock_in_scenario_name28014);
            manifest_textblock350=manifest_textblock();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_manifest_textblock.add(manifest_textblock350.getTree());

            // AST REWRITE
            // elements: 
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1733:17: -> ^( SCENARIO_NAME MANIFEST_STRING )
            {
                // BON.g:1734:17: ^( SCENARIO_NAME MANIFEST_STRING )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(SCENARIO_NAME, "SCENARIO_NAME"), root_1);

                adaptor.addChild(root_1, adaptor.create(MANIFEST_STRING, "MANIFEST_STRING"));

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end scenario_name

    public static class object_group_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start object_group
    // BON.g:1739:1: object_group : ( 'nameless' )? 'object_group' group_name ( COMMENT )? ( group_components )? -> ^( OBJECT_GROUP ( 'nameless' )? group_name ( COMMENT )? ( group_components )? ) ;
    public final object_group_return object_group() throws RecognitionException {
        object_group_return retval = new object_group_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal351=null;
        Token string_literal352=null;
        Token COMMENT354=null;
        group_name_return group_name353 = null;

        group_components_return group_components355 = null;


        CommonTree string_literal351_tree=null;
        CommonTree string_literal352_tree=null;
        CommonTree COMMENT354_tree=null;
        RewriteRuleTokenStream stream_COMMENT=new RewriteRuleTokenStream(adaptor,"token COMMENT");
        RewriteRuleTokenStream stream_254=new RewriteRuleTokenStream(adaptor,"token 254");
        RewriteRuleTokenStream stream_255=new RewriteRuleTokenStream(adaptor,"token 255");
        RewriteRuleSubtreeStream stream_group_name=new RewriteRuleSubtreeStream(adaptor,"rule group_name");
        RewriteRuleSubtreeStream stream_group_components=new RewriteRuleSubtreeStream(adaptor,"rule group_components");
        try {
            // BON.g:1741:15: ( ( 'nameless' )? 'object_group' group_name ( COMMENT )? ( group_components )? -> ^( OBJECT_GROUP ( 'nameless' )? group_name ( COMMENT )? ( group_components )? ) )
            // BON.g:1741:18: ( 'nameless' )? 'object_group' group_name ( COMMENT )? ( group_components )?
            {
            // BON.g:1741:18: ( 'nameless' )?
            int alt148=2;
            int LA148_0 = input.LA(1);

            if ( (LA148_0==254) ) {
                alt148=1;
            }
            switch (alt148) {
                case 1 :
                    // BON.g:1741:19: 'nameless'
                    {
                    string_literal351=(Token)input.LT(1);
                    match(input,254,FOLLOW_254_in_object_group28122); if (failed) return retval;
                    if ( backtracking==0 ) stream_254.add(string_literal351);


                    }
                    break;

            }

            string_literal352=(Token)input.LT(1);
            match(input,255,FOLLOW_255_in_object_group28126); if (failed) return retval;
            if ( backtracking==0 ) stream_255.add(string_literal352);

            pushFollow(FOLLOW_group_name_in_object_group28128);
            group_name353=group_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_group_name.add(group_name353.getTree());
            // BON.g:1741:58: ( COMMENT )?
            int alt149=2;
            int LA149_0 = input.LA(1);

            if ( (LA149_0==COMMENT) ) {
                alt149=1;
            }
            switch (alt149) {
                case 1 :
                    // BON.g:1741:59: COMMENT
                    {
                    COMMENT354=(Token)input.LT(1);
                    match(input,COMMENT,FOLLOW_COMMENT_in_object_group28131); if (failed) return retval;
                    if ( backtracking==0 ) stream_COMMENT.add(COMMENT354);


                    }
                    break;

            }

            // BON.g:1742:18: ( group_components )?
            int alt150=2;
            int LA150_0 = input.LA(1);

            if ( (LA150_0==215) ) {
                alt150=1;
            }
            switch (alt150) {
                case 1 :
                    // BON.g:1742:19: group_components
                    {
                    pushFollow(FOLLOW_group_components_in_object_group28154);
                    group_components355=group_components();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_group_components.add(group_components355.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: group_components, group_name, 254, COMMENT
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1743:16: -> ^( OBJECT_GROUP ( 'nameless' )? group_name ( COMMENT )? ( group_components )? )
            {
                // BON.g:1744:16: ^( OBJECT_GROUP ( 'nameless' )? group_name ( COMMENT )? ( group_components )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(OBJECT_GROUP, "OBJECT_GROUP"), root_1);

                // BON.g:1745:31: ( 'nameless' )?
                if ( stream_254.hasNext() ) {
                    adaptor.addChild(root_1, stream_254.next());

                }
                stream_254.reset();
                adaptor.addChild(root_1, stream_group_name.next());
                // BON.g:1745:56: ( COMMENT )?
                if ( stream_COMMENT.hasNext() ) {
                    adaptor.addChild(root_1, stream_COMMENT.next());

                }
                stream_COMMENT.reset();
                // BON.g:1745:67: ( group_components )?
                if ( stream_group_components.hasNext() ) {
                    adaptor.addChild(root_1, stream_group_components.next());

                }
                stream_group_components.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end object_group

    public static class group_components_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start group_components
    // BON.g:1749:1: group_components : 'component' dynamic_block 'end' -> ^( GROUP_COMPONENTS dynamic_block ) ;
    public final group_components_return group_components() throws RecognitionException {
        group_components_return retval = new group_components_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal356=null;
        Token string_literal358=null;
        dynamic_block_return dynamic_block357 = null;


        CommonTree string_literal356_tree=null;
        CommonTree string_literal358_tree=null;
        RewriteRuleTokenStream stream_215=new RewriteRuleTokenStream(adaptor,"token 215");
        RewriteRuleTokenStream stream_187=new RewriteRuleTokenStream(adaptor,"token 187");
        RewriteRuleSubtreeStream stream_dynamic_block=new RewriteRuleSubtreeStream(adaptor,"rule dynamic_block");
        try {
            // BON.g:1749:19: ( 'component' dynamic_block 'end' -> ^( GROUP_COMPONENTS dynamic_block ) )
            // BON.g:1749:22: 'component' dynamic_block 'end'
            {
            string_literal356=(Token)input.LT(1);
            match(input,215,FOLLOW_215_in_group_components28285); if (failed) return retval;
            if ( backtracking==0 ) stream_215.add(string_literal356);

            pushFollow(FOLLOW_dynamic_block_in_group_components28287);
            dynamic_block357=dynamic_block();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_dynamic_block.add(dynamic_block357.getTree());
            string_literal358=(Token)input.LT(1);
            match(input,187,FOLLOW_187_in_group_components28289); if (failed) return retval;
            if ( backtracking==0 ) stream_187.add(string_literal358);


            // AST REWRITE
            // elements: dynamic_block
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1750:20: -> ^( GROUP_COMPONENTS dynamic_block )
            {
                // BON.g:1751:20: ^( GROUP_COMPONENTS dynamic_block )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(GROUP_COMPONENTS, "GROUP_COMPONENTS"), root_1);

                adaptor.addChild(root_1, stream_dynamic_block.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end group_components

    public static class object_stack_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start object_stack
    // BON.g:1756:1: object_stack : 'object_stack' object_name ( COMMENT )? -> ^( OBJECT_STACK object_name ( COMMENT )? ) ;
    public final object_stack_return object_stack() throws RecognitionException {
        object_stack_return retval = new object_stack_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal359=null;
        Token COMMENT361=null;
        object_name_return object_name360 = null;


        CommonTree string_literal359_tree=null;
        CommonTree COMMENT361_tree=null;
        RewriteRuleTokenStream stream_COMMENT=new RewriteRuleTokenStream(adaptor,"token COMMENT");
        RewriteRuleTokenStream stream_256=new RewriteRuleTokenStream(adaptor,"token 256");
        RewriteRuleSubtreeStream stream_object_name=new RewriteRuleSubtreeStream(adaptor,"rule object_name");
        try {
            // BON.g:1756:15: ( 'object_stack' object_name ( COMMENT )? -> ^( OBJECT_STACK object_name ( COMMENT )? ) )
            // BON.g:1756:18: 'object_stack' object_name ( COMMENT )?
            {
            string_literal359=(Token)input.LT(1);
            match(input,256,FOLLOW_256_in_object_stack28426); if (failed) return retval;
            if ( backtracking==0 ) stream_256.add(string_literal359);

            pushFollow(FOLLOW_object_name_in_object_stack28428);
            object_name360=object_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_object_name.add(object_name360.getTree());
            // BON.g:1756:45: ( COMMENT )?
            int alt151=2;
            int LA151_0 = input.LA(1);

            if ( (LA151_0==COMMENT) ) {
                alt151=1;
            }
            switch (alt151) {
                case 1 :
                    // BON.g:1756:46: COMMENT
                    {
                    COMMENT361=(Token)input.LT(1);
                    match(input,COMMENT,FOLLOW_COMMENT_in_object_stack28431); if (failed) return retval;
                    if ( backtracking==0 ) stream_COMMENT.add(COMMENT361);


                    }
                    break;

            }


            // AST REWRITE
            // elements: COMMENT, object_name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1757:16: -> ^( OBJECT_STACK object_name ( COMMENT )? )
            {
                // BON.g:1758:16: ^( OBJECT_STACK object_name ( COMMENT )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(OBJECT_STACK, "OBJECT_STACK"), root_1);

                adaptor.addChild(root_1, stream_object_name.next());
                // BON.g:1759:43: ( COMMENT )?
                if ( stream_COMMENT.hasNext() ) {
                    adaptor.addChild(root_1, stream_COMMENT.next());

                }
                stream_COMMENT.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end object_stack

    public static class object_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start object
    // BON.g:1763:1: object : 'object' object_name ( COMMENT )? -> ^( OBJECT object_name ( COMMENT )? ) ;
    public final object_return object() throws RecognitionException {
        object_return retval = new object_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal362=null;
        Token COMMENT364=null;
        object_name_return object_name363 = null;


        CommonTree string_literal362_tree=null;
        CommonTree COMMENT364_tree=null;
        RewriteRuleTokenStream stream_COMMENT=new RewriteRuleTokenStream(adaptor,"token COMMENT");
        RewriteRuleTokenStream stream_257=new RewriteRuleTokenStream(adaptor,"token 257");
        RewriteRuleSubtreeStream stream_object_name=new RewriteRuleSubtreeStream(adaptor,"rule object_name");
        try {
            // BON.g:1763:9: ( 'object' object_name ( COMMENT )? -> ^( OBJECT object_name ( COMMENT )? ) )
            // BON.g:1763:12: 'object' object_name ( COMMENT )?
            {
            string_literal362=(Token)input.LT(1);
            match(input,257,FOLLOW_257_in_object28550); if (failed) return retval;
            if ( backtracking==0 ) stream_257.add(string_literal362);

            pushFollow(FOLLOW_object_name_in_object28552);
            object_name363=object_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_object_name.add(object_name363.getTree());
            // BON.g:1763:33: ( COMMENT )?
            int alt152=2;
            int LA152_0 = input.LA(1);

            if ( (LA152_0==COMMENT) ) {
                alt152=1;
            }
            switch (alt152) {
                case 1 :
                    // BON.g:1763:34: COMMENT
                    {
                    COMMENT364=(Token)input.LT(1);
                    match(input,COMMENT,FOLLOW_COMMENT_in_object28555); if (failed) return retval;
                    if ( backtracking==0 ) stream_COMMENT.add(COMMENT364);


                    }
                    break;

            }


            // AST REWRITE
            // elements: COMMENT, object_name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1764:10: -> ^( OBJECT object_name ( COMMENT )? )
            {
                // BON.g:1765:10: ^( OBJECT object_name ( COMMENT )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(OBJECT, "OBJECT"), root_1);

                adaptor.addChild(root_1, stream_object_name.next());
                // BON.g:1766:31: ( COMMENT )?
                if ( stream_COMMENT.hasNext() ) {
                    adaptor.addChild(root_1, stream_COMMENT.next());

                }
                stream_COMMENT.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end object

    public static class message_relation_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start message_relation
    // BON.g:1770:1: message_relation : caller 'calls' receiver ( message_label )? -> ^( MESSAGE_RELATION caller receiver ( message_label )? ) ;
    public final message_relation_return message_relation() throws RecognitionException {
        message_relation_return retval = new message_relation_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal366=null;
        caller_return caller365 = null;

        receiver_return receiver367 = null;

        message_label_return message_label368 = null;


        CommonTree string_literal366_tree=null;
        RewriteRuleTokenStream stream_258=new RewriteRuleTokenStream(adaptor,"token 258");
        RewriteRuleSubtreeStream stream_caller=new RewriteRuleSubtreeStream(adaptor,"rule caller");
        RewriteRuleSubtreeStream stream_receiver=new RewriteRuleSubtreeStream(adaptor,"rule receiver");
        RewriteRuleSubtreeStream stream_message_label=new RewriteRuleSubtreeStream(adaptor,"rule message_label");
        try {
            // BON.g:1772:19: ( caller 'calls' receiver ( message_label )? -> ^( MESSAGE_RELATION caller receiver ( message_label )? ) )
            // BON.g:1772:22: caller 'calls' receiver ( message_label )?
            {
            pushFollow(FOLLOW_caller_in_message_relation28634);
            caller365=caller();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_caller.add(caller365.getTree());
            string_literal366=(Token)input.LT(1);
            match(input,258,FOLLOW_258_in_message_relation28636); if (failed) return retval;
            if ( backtracking==0 ) stream_258.add(string_literal366);

            pushFollow(FOLLOW_receiver_in_message_relation28638);
            receiver367=receiver();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_receiver.add(receiver367.getTree());
            // BON.g:1772:46: ( message_label )?
            int alt153=2;
            int LA153_0 = input.LA(1);

            if ( (LA153_0==MANIFEST_STRING) ) {
                alt153=1;
            }
            switch (alt153) {
                case 1 :
                    // BON.g:1772:47: message_label
                    {
                    pushFollow(FOLLOW_message_label_in_message_relation28641);
                    message_label368=message_label();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_message_label.add(message_label368.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: message_label, caller, receiver
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1773:20: -> ^( MESSAGE_RELATION caller receiver ( message_label )? )
            {
                // BON.g:1774:20: ^( MESSAGE_RELATION caller receiver ( message_label )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(MESSAGE_RELATION, "MESSAGE_RELATION"), root_1);

                adaptor.addChild(root_1, stream_caller.next());
                adaptor.addChild(root_1, stream_receiver.next());
                // BON.g:1775:55: ( message_label )?
                if ( stream_message_label.hasNext() ) {
                    adaptor.addChild(root_1, stream_message_label.next());

                }
                stream_message_label.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end message_relation

    public static class caller_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start caller
    // BON.g:1779:1: caller : dynamic_ref -> ^( RECEIVER dynamic_ref ) ;
    public final caller_return caller() throws RecognitionException {
        caller_return retval = new caller_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        dynamic_ref_return dynamic_ref369 = null;


        RewriteRuleSubtreeStream stream_dynamic_ref=new RewriteRuleSubtreeStream(adaptor,"rule dynamic_ref");
        try {
            // BON.g:1779:9: ( dynamic_ref -> ^( RECEIVER dynamic_ref ) )
            // BON.g:1779:12: dynamic_ref
            {
            pushFollow(FOLLOW_dynamic_ref_in_caller28787);
            dynamic_ref369=dynamic_ref();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_dynamic_ref.add(dynamic_ref369.getTree());

            // AST REWRITE
            // elements: dynamic_ref
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1780:10: -> ^( RECEIVER dynamic_ref )
            {
                // BON.g:1781:10: ^( RECEIVER dynamic_ref )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(RECEIVER, "RECEIVER"), root_1);

                adaptor.addChild(root_1, stream_dynamic_ref.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end caller

    public static class receiver_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start receiver
    // BON.g:1786:1: receiver : dynamic_ref -> ^( RECEIVER dynamic_ref ) ;
    public final receiver_return receiver() throws RecognitionException {
        receiver_return retval = new receiver_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        dynamic_ref_return dynamic_ref370 = null;


        RewriteRuleSubtreeStream stream_dynamic_ref=new RewriteRuleSubtreeStream(adaptor,"rule dynamic_ref");
        try {
            // BON.g:1786:11: ( dynamic_ref -> ^( RECEIVER dynamic_ref ) )
            // BON.g:1786:14: dynamic_ref
            {
            pushFollow(FOLLOW_dynamic_ref_in_receiver28864);
            dynamic_ref370=dynamic_ref();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_dynamic_ref.add(dynamic_ref370.getTree());

            // AST REWRITE
            // elements: dynamic_ref
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1787:12: -> ^( RECEIVER dynamic_ref )
            {
                // BON.g:1788:12: ^( RECEIVER dynamic_ref )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(RECEIVER, "RECEIVER"), root_1);

                adaptor.addChild(root_1, stream_dynamic_ref.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end receiver

    public static class dynamic_ref_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start dynamic_ref
    // BON.g:1797:1: dynamic_ref : extended_id ( '.' extended_id )* -> ^( DYNAMIC_REF ( extended_id )+ ) ;
    public final dynamic_ref_return dynamic_ref() throws RecognitionException {
        dynamic_ref_return retval = new dynamic_ref_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal372=null;
        extended_id_return extended_id371 = null;

        extended_id_return extended_id373 = null;


        CommonTree char_literal372_tree=null;
        RewriteRuleTokenStream stream_232=new RewriteRuleTokenStream(adaptor,"token 232");
        RewriteRuleSubtreeStream stream_extended_id=new RewriteRuleSubtreeStream(adaptor,"rule extended_id");
        try {
            // BON.g:1797:14: ( extended_id ( '.' extended_id )* -> ^( DYNAMIC_REF ( extended_id )+ ) )
            // BON.g:1797:17: extended_id ( '.' extended_id )*
            {
            pushFollow(FOLLOW_extended_id_in_dynamic_ref28957);
            extended_id371=extended_id();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_extended_id.add(extended_id371.getTree());
            // BON.g:1797:29: ( '.' extended_id )*
            loop154:
            do {
                int alt154=2;
                int LA154_0 = input.LA(1);

                if ( (LA154_0==232) ) {
                    alt154=1;
                }


                switch (alt154) {
            	case 1 :
            	    // BON.g:1797:30: '.' extended_id
            	    {
            	    char_literal372=(Token)input.LT(1);
            	    match(input,232,FOLLOW_232_in_dynamic_ref28960); if (failed) return retval;
            	    if ( backtracking==0 ) stream_232.add(char_literal372);

            	    pushFollow(FOLLOW_extended_id_in_dynamic_ref28962);
            	    extended_id373=extended_id();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) stream_extended_id.add(extended_id373.getTree());

            	    }
            	    break;

            	default :
            	    break loop154;
                }
            } while (true);


            // AST REWRITE
            // elements: extended_id
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1798:15: -> ^( DYNAMIC_REF ( extended_id )+ )
            {
                // BON.g:1799:15: ^( DYNAMIC_REF ( extended_id )+ )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(DYNAMIC_REF, "DYNAMIC_REF"), root_1);

                if ( !(stream_extended_id.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_extended_id.hasNext() ) {
                    adaptor.addChild(root_1, stream_extended_id.next());

                }
                stream_extended_id.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end dynamic_ref

    public static class dynamic_component_name_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start dynamic_component_name
    // BON.g:1810:1: dynamic_component_name : ( ( IDENTIFIER ( '.' extended_id )? ) -> ^( DYNAMIC_COMPONENT_NAME IDENTIFIER ( extended_id )? ) | INTEGER -> ^( DYNAMIC_COMPONENT_NAME INTEGER ) );
    public final dynamic_component_name_return dynamic_component_name() throws RecognitionException {
        dynamic_component_name_return retval = new dynamic_component_name_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token IDENTIFIER374=null;
        Token char_literal375=null;
        Token INTEGER377=null;
        extended_id_return extended_id376 = null;


        CommonTree IDENTIFIER374_tree=null;
        CommonTree char_literal375_tree=null;
        CommonTree INTEGER377_tree=null;
        RewriteRuleTokenStream stream_INTEGER=new RewriteRuleTokenStream(adaptor,"token INTEGER");
        RewriteRuleTokenStream stream_232=new RewriteRuleTokenStream(adaptor,"token 232");
        RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
        RewriteRuleSubtreeStream stream_extended_id=new RewriteRuleSubtreeStream(adaptor,"rule extended_id");
        try {
            // BON.g:1810:25: ( ( IDENTIFIER ( '.' extended_id )? ) -> ^( DYNAMIC_COMPONENT_NAME IDENTIFIER ( extended_id )? ) | INTEGER -> ^( DYNAMIC_COMPONENT_NAME INTEGER ) )
            int alt156=2;
            int LA156_0 = input.LA(1);

            if ( (LA156_0==IDENTIFIER) ) {
                alt156=1;
            }
            else if ( (LA156_0==INTEGER) ) {
                alt156=2;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1810:1: dynamic_component_name : ( ( IDENTIFIER ( '.' extended_id )? ) -> ^( DYNAMIC_COMPONENT_NAME IDENTIFIER ( extended_id )? ) | INTEGER -> ^( DYNAMIC_COMPONENT_NAME INTEGER ) );", 156, 0, input);

                throw nvae;
            }
            switch (alt156) {
                case 1 :
                    // BON.g:1810:28: ( IDENTIFIER ( '.' extended_id )? )
                    {
                    // BON.g:1810:28: ( IDENTIFIER ( '.' extended_id )? )
                    // BON.g:1810:29: IDENTIFIER ( '.' extended_id )?
                    {
                    IDENTIFIER374=(Token)input.LT(1);
                    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_dynamic_component_name29074); if (failed) return retval;
                    if ( backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER374);

                    // BON.g:1810:40: ( '.' extended_id )?
                    int alt155=2;
                    int LA155_0 = input.LA(1);

                    if ( (LA155_0==232) ) {
                        alt155=1;
                    }
                    switch (alt155) {
                        case 1 :
                            // BON.g:1810:41: '.' extended_id
                            {
                            char_literal375=(Token)input.LT(1);
                            match(input,232,FOLLOW_232_in_dynamic_component_name29077); if (failed) return retval;
                            if ( backtracking==0 ) stream_232.add(char_literal375);

                            pushFollow(FOLLOW_extended_id_in_dynamic_component_name29079);
                            extended_id376=extended_id();
                            _fsp--;
                            if (failed) return retval;
                            if ( backtracking==0 ) stream_extended_id.add(extended_id376.getTree());

                            }
                            break;

                    }


                    }


                    // AST REWRITE
                    // elements: extended_id, IDENTIFIER
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1811:26: -> ^( DYNAMIC_COMPONENT_NAME IDENTIFIER ( extended_id )? )
                    {
                        // BON.g:1812:26: ^( DYNAMIC_COMPONENT_NAME IDENTIFIER ( extended_id )? )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(DYNAMIC_COMPONENT_NAME, "DYNAMIC_COMPONENT_NAME"), root_1);

                        adaptor.addChild(root_1, stream_IDENTIFIER.next());
                        // BON.g:1813:62: ( extended_id )?
                        if ( stream_extended_id.hasNext() ) {
                            adaptor.addChild(root_1, stream_extended_id.next());

                        }
                        stream_extended_id.reset();

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:1815:28: INTEGER
                    {
                    INTEGER377=(Token)input.LT(1);
                    match(input,INTEGER,FOLLOW_INTEGER_in_dynamic_component_name29230); if (failed) return retval;
                    if ( backtracking==0 ) stream_INTEGER.add(INTEGER377);


                    // AST REWRITE
                    // elements: INTEGER
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1816:26: -> ^( DYNAMIC_COMPONENT_NAME INTEGER )
                    {
                        // BON.g:1817:26: ^( DYNAMIC_COMPONENT_NAME INTEGER )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(DYNAMIC_COMPONENT_NAME, "DYNAMIC_COMPONENT_NAME"), root_1);

                        adaptor.addChild(root_1, stream_INTEGER.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end dynamic_component_name

    public static class object_name_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start object_name
    // BON.g:1822:1: object_name : class_name ( '.' extended_id )? -> ^( OBJECT_NAME class_name ( extended_id )? ) ;
    public final object_name_return object_name() throws RecognitionException {
        object_name_return retval = new object_name_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal379=null;
        class_name_return class_name378 = null;

        extended_id_return extended_id380 = null;


        CommonTree char_literal379_tree=null;
        RewriteRuleTokenStream stream_232=new RewriteRuleTokenStream(adaptor,"token 232");
        RewriteRuleSubtreeStream stream_extended_id=new RewriteRuleSubtreeStream(adaptor,"rule extended_id");
        RewriteRuleSubtreeStream stream_class_name=new RewriteRuleSubtreeStream(adaptor,"rule class_name");
        try {
            // BON.g:1822:14: ( class_name ( '.' extended_id )? -> ^( OBJECT_NAME class_name ( extended_id )? ) )
            // BON.g:1822:17: class_name ( '.' extended_id )?
            {
            pushFollow(FOLLOW_class_name_in_object_name29378);
            class_name378=class_name();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_class_name.add(class_name378.getTree());
            // BON.g:1822:28: ( '.' extended_id )?
            int alt157=2;
            int LA157_0 = input.LA(1);

            if ( (LA157_0==232) ) {
                alt157=1;
            }
            switch (alt157) {
                case 1 :
                    // BON.g:1822:29: '.' extended_id
                    {
                    char_literal379=(Token)input.LT(1);
                    match(input,232,FOLLOW_232_in_object_name29381); if (failed) return retval;
                    if ( backtracking==0 ) stream_232.add(char_literal379);

                    pushFollow(FOLLOW_extended_id_in_object_name29383);
                    extended_id380=extended_id();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_extended_id.add(extended_id380.getTree());

                    }
                    break;

            }


            // AST REWRITE
            // elements: extended_id, class_name
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1823:15: -> ^( OBJECT_NAME class_name ( extended_id )? )
            {
                // BON.g:1824:15: ^( OBJECT_NAME class_name ( extended_id )? )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(OBJECT_NAME, "OBJECT_NAME"), root_1);

                adaptor.addChild(root_1, stream_class_name.next());
                // BON.g:1825:40: ( extended_id )?
                if ( stream_extended_id.hasNext() ) {
                    adaptor.addChild(root_1, stream_extended_id.next());

                }
                stream_extended_id.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end object_name

    public static class group_name_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start group_name
    // BON.g:1829:1: group_name : extended_id -> ^( GROUP_NAME extended_id ) ;
    public final group_name_return group_name() throws RecognitionException {
        group_name_return retval = new group_name_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        extended_id_return extended_id381 = null;


        RewriteRuleSubtreeStream stream_extended_id=new RewriteRuleSubtreeStream(adaptor,"rule extended_id");
        try {
            // BON.g:1829:13: ( extended_id -> ^( GROUP_NAME extended_id ) )
            // BON.g:1829:16: extended_id
            {
            pushFollow(FOLLOW_extended_id_in_group_name29497);
            extended_id381=extended_id();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) stream_extended_id.add(extended_id381.getTree());

            // AST REWRITE
            // elements: extended_id
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1830:14: -> ^( GROUP_NAME extended_id )
            {
                // BON.g:1831:14: ^( GROUP_NAME extended_id )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(GROUP_NAME, "GROUP_NAME"), root_1);

                adaptor.addChild(root_1, stream_extended_id.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end group_name

    public static class message_label_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start message_label
    // BON.g:1836:1: message_label : MANIFEST_STRING -> ^( MESSAGE_LABEL MANIFEST_STRING ) ;
    public final message_label_return message_label() throws RecognitionException {
        message_label_return retval = new message_label_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token MANIFEST_STRING382=null;

        CommonTree MANIFEST_STRING382_tree=null;
        RewriteRuleTokenStream stream_MANIFEST_STRING=new RewriteRuleTokenStream(adaptor,"token MANIFEST_STRING");

        try {
            // BON.g:1836:16: ( MANIFEST_STRING -> ^( MESSAGE_LABEL MANIFEST_STRING ) )
            // BON.g:1836:19: MANIFEST_STRING
            {
            MANIFEST_STRING382=(Token)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_message_label29598); if (failed) return retval;
            if ( backtracking==0 ) stream_MANIFEST_STRING.add(MANIFEST_STRING382);


            // AST REWRITE
            // elements: MANIFEST_STRING
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1837:17: -> ^( MESSAGE_LABEL MANIFEST_STRING )
            {
                // BON.g:1838:17: ^( MESSAGE_LABEL MANIFEST_STRING )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(MESSAGE_LABEL, "MESSAGE_LABEL"), root_1);

                adaptor.addChild(root_1, stream_MANIFEST_STRING.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end message_label

    public static class notational_tuning_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start notational_tuning
    // BON.g:1843:1: notational_tuning : ( change_string_marks -> ^( NOTATIONAL_TUNING change_string_marks ) | change_concatenator -> ^( NOTATIONAL_TUNING change_concatenator ) | change_prefix -> ^( NOTATIONAL_TUNING change_prefix ) );
    public final notational_tuning_return notational_tuning() throws RecognitionException {
        notational_tuning_return retval = new notational_tuning_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        change_string_marks_return change_string_marks383 = null;

        change_concatenator_return change_concatenator384 = null;

        change_prefix_return change_prefix385 = null;


        RewriteRuleSubtreeStream stream_change_prefix=new RewriteRuleSubtreeStream(adaptor,"rule change_prefix");
        RewriteRuleSubtreeStream stream_change_string_marks=new RewriteRuleSubtreeStream(adaptor,"rule change_string_marks");
        RewriteRuleSubtreeStream stream_change_concatenator=new RewriteRuleSubtreeStream(adaptor,"rule change_concatenator");
        try {
            // BON.g:1847:20: ( change_string_marks -> ^( NOTATIONAL_TUNING change_string_marks ) | change_concatenator -> ^( NOTATIONAL_TUNING change_concatenator ) | change_prefix -> ^( NOTATIONAL_TUNING change_prefix ) )
            int alt158=3;
            switch ( input.LA(1) ) {
            case 259:
                {
                alt158=1;
                }
                break;
            case 260:
                {
                alt158=2;
                }
                break;
            case 261:
                {
                alt158=3;
                }
                break;
            default:
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1843:1: notational_tuning : ( change_string_marks -> ^( NOTATIONAL_TUNING change_string_marks ) | change_concatenator -> ^( NOTATIONAL_TUNING change_concatenator ) | change_prefix -> ^( NOTATIONAL_TUNING change_prefix ) );", 158, 0, input);

                throw nvae;
            }

            switch (alt158) {
                case 1 :
                    // BON.g:1847:23: change_string_marks
                    {
                    pushFollow(FOLLOW_change_string_marks_in_notational_tuning29705);
                    change_string_marks383=change_string_marks();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_change_string_marks.add(change_string_marks383.getTree());

                    // AST REWRITE
                    // elements: change_string_marks
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1848:21: -> ^( NOTATIONAL_TUNING change_string_marks )
                    {
                        // BON.g:1849:21: ^( NOTATIONAL_TUNING change_string_marks )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(NOTATIONAL_TUNING, "NOTATIONAL_TUNING"), root_1);

                        adaptor.addChild(root_1, stream_change_string_marks.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:1852:23: change_concatenator
                    {
                    pushFollow(FOLLOW_change_concatenator_in_notational_tuning29823);
                    change_concatenator384=change_concatenator();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_change_concatenator.add(change_concatenator384.getTree());

                    // AST REWRITE
                    // elements: change_concatenator
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1853:21: -> ^( NOTATIONAL_TUNING change_concatenator )
                    {
                        // BON.g:1854:21: ^( NOTATIONAL_TUNING change_concatenator )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(NOTATIONAL_TUNING, "NOTATIONAL_TUNING"), root_1);

                        adaptor.addChild(root_1, stream_change_concatenator.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 3 :
                    // BON.g:1857:23: change_prefix
                    {
                    pushFollow(FOLLOW_change_prefix_in_notational_tuning29940);
                    change_prefix385=change_prefix();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_change_prefix.add(change_prefix385.getTree());

                    // AST REWRITE
                    // elements: change_prefix
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1858:21: -> ^( NOTATIONAL_TUNING change_prefix )
                    {
                        // BON.g:1859:21: ^( NOTATIONAL_TUNING change_prefix )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(NOTATIONAL_TUNING, "NOTATIONAL_TUNING"), root_1);

                        adaptor.addChild(root_1, stream_change_prefix.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end notational_tuning

    public static class change_string_marks_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start change_string_marks
    // BON.g:1864:1: change_string_marks : 'string_marks' MANIFEST_STRING MANIFEST_STRING -> ^( CHANGE_STRING_MARKS MANIFEST_STRING MANIFEST_STRING ) ;
    public final change_string_marks_return change_string_marks() throws RecognitionException {
        change_string_marks_return retval = new change_string_marks_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal386=null;
        Token MANIFEST_STRING387=null;
        Token MANIFEST_STRING388=null;

        CommonTree string_literal386_tree=null;
        CommonTree MANIFEST_STRING387_tree=null;
        CommonTree MANIFEST_STRING388_tree=null;
        RewriteRuleTokenStream stream_MANIFEST_STRING=new RewriteRuleTokenStream(adaptor,"token MANIFEST_STRING");
        RewriteRuleTokenStream stream_259=new RewriteRuleTokenStream(adaptor,"token 259");

        try {
            // BON.g:1864:22: ( 'string_marks' MANIFEST_STRING MANIFEST_STRING -> ^( CHANGE_STRING_MARKS MANIFEST_STRING MANIFEST_STRING ) )
            // BON.g:1864:25: 'string_marks' MANIFEST_STRING MANIFEST_STRING
            {
            string_literal386=(Token)input.LT(1);
            match(input,259,FOLLOW_259_in_change_string_marks30064); if (failed) return retval;
            if ( backtracking==0 ) stream_259.add(string_literal386);

            MANIFEST_STRING387=(Token)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_string_marks30066); if (failed) return retval;
            if ( backtracking==0 ) stream_MANIFEST_STRING.add(MANIFEST_STRING387);

            MANIFEST_STRING388=(Token)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_string_marks30068); if (failed) return retval;
            if ( backtracking==0 ) stream_MANIFEST_STRING.add(MANIFEST_STRING388);


            // AST REWRITE
            // elements: MANIFEST_STRING, MANIFEST_STRING
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1865:23: -> ^( CHANGE_STRING_MARKS MANIFEST_STRING MANIFEST_STRING )
            {
                // BON.g:1866:23: ^( CHANGE_STRING_MARKS MANIFEST_STRING MANIFEST_STRING )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CHANGE_STRING_MARKS, "CHANGE_STRING_MARKS"), root_1);

                adaptor.addChild(root_1, stream_MANIFEST_STRING.next());
                adaptor.addChild(root_1, stream_MANIFEST_STRING.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end change_string_marks

    public static class change_concatenator_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start change_concatenator
    // BON.g:1871:1: change_concatenator : 'concatenator' MANIFEST_STRING -> ^( CHANGE_CONCATENATOR MANIFEST_STRING ) ;
    public final change_concatenator_return change_concatenator() throws RecognitionException {
        change_concatenator_return retval = new change_concatenator_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal389=null;
        Token MANIFEST_STRING390=null;

        CommonTree string_literal389_tree=null;
        CommonTree MANIFEST_STRING390_tree=null;
        RewriteRuleTokenStream stream_MANIFEST_STRING=new RewriteRuleTokenStream(adaptor,"token MANIFEST_STRING");
        RewriteRuleTokenStream stream_260=new RewriteRuleTokenStream(adaptor,"token 260");

        try {
            // BON.g:1871:22: ( 'concatenator' MANIFEST_STRING -> ^( CHANGE_CONCATENATOR MANIFEST_STRING ) )
            // BON.g:1871:25: 'concatenator' MANIFEST_STRING
            {
            string_literal389=(Token)input.LT(1);
            match(input,260,FOLLOW_260_in_change_concatenator30225); if (failed) return retval;
            if ( backtracking==0 ) stream_260.add(string_literal389);

            MANIFEST_STRING390=(Token)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_concatenator30227); if (failed) return retval;
            if ( backtracking==0 ) stream_MANIFEST_STRING.add(MANIFEST_STRING390);


            // AST REWRITE
            // elements: MANIFEST_STRING
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1872:23: -> ^( CHANGE_CONCATENATOR MANIFEST_STRING )
            {
                // BON.g:1873:23: ^( CHANGE_CONCATENATOR MANIFEST_STRING )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CHANGE_CONCATENATOR, "CHANGE_CONCATENATOR"), root_1);

                adaptor.addChild(root_1, stream_MANIFEST_STRING.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end change_concatenator

    public static class change_prefix_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start change_prefix
    // BON.g:1878:1: change_prefix : 'keyword_prefix' MANIFEST_STRING -> ^( CHANGE_PREFIX MANIFEST_STRING ) ;
    public final change_prefix_return change_prefix() throws RecognitionException {
        change_prefix_return retval = new change_prefix_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal391=null;
        Token MANIFEST_STRING392=null;

        CommonTree string_literal391_tree=null;
        CommonTree MANIFEST_STRING392_tree=null;
        RewriteRuleTokenStream stream_MANIFEST_STRING=new RewriteRuleTokenStream(adaptor,"token MANIFEST_STRING");
        RewriteRuleTokenStream stream_261=new RewriteRuleTokenStream(adaptor,"token 261");

        try {
            // BON.g:1878:16: ( 'keyword_prefix' MANIFEST_STRING -> ^( CHANGE_PREFIX MANIFEST_STRING ) )
            // BON.g:1878:19: 'keyword_prefix' MANIFEST_STRING
            {
            string_literal391=(Token)input.LT(1);
            match(input,261,FOLLOW_261_in_change_prefix30382); if (failed) return retval;
            if ( backtracking==0 ) stream_261.add(string_literal391);

            MANIFEST_STRING392=(Token)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_prefix30384); if (failed) return retval;
            if ( backtracking==0 ) stream_MANIFEST_STRING.add(MANIFEST_STRING392);


            // AST REWRITE
            // elements: MANIFEST_STRING
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (CommonTree)adaptor.nil();
            // 1879:17: -> ^( CHANGE_PREFIX MANIFEST_STRING )
            {
                // BON.g:1880:17: ^( CHANGE_PREFIX MANIFEST_STRING )
                {
                CommonTree root_1 = (CommonTree)adaptor.nil();
                root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(CHANGE_PREFIX, "CHANGE_PREFIX"), root_1);

                adaptor.addChild(root_1, stream_MANIFEST_STRING.next());

                adaptor.addChild(root_0, root_1);
                }

            }

            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end change_prefix

    public static class expression_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start expression
    // BON.g:1885:1: expression : (e= equivalence_expression -> ^( EXPRESSION[$e.start] equivalence_expression ) | q= quantification -> ^( EXPRESSION[$q.start] quantification ) );
    public final expression_return expression() throws RecognitionException {
        expression_return retval = new expression_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        equivalence_expression_return e = null;

        quantification_return q = null;


        RewriteRuleSubtreeStream stream_equivalence_expression=new RewriteRuleSubtreeStream(adaptor,"rule equivalence_expression");
        RewriteRuleSubtreeStream stream_quantification=new RewriteRuleSubtreeStream(adaptor,"rule quantification");
        try {
            // BON.g:1889:13: (e= equivalence_expression -> ^( EXPRESSION[$e.start] equivalence_expression ) | q= quantification -> ^( EXPRESSION[$q.start] quantification ) )
            int alt159=2;
            int LA159_0 = input.LA(1);

            if ( ((LA159_0>=MANIFEST_STRING && LA159_0<=IDENTIFIER)||(LA159_0>=INTEGER && LA159_0<=REAL)||LA159_0==222||LA159_0==225||(LA159_0>=248 && LA159_0<=251)||(LA159_0>=263 && LA159_0<=264)||(LA159_0>=268 && LA159_0<=270)) ) {
                alt159=1;
            }
            else if ( ((LA159_0>=242 && LA159_0<=243)) ) {
                alt159=2;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1885:1: expression : (e= equivalence_expression -> ^( EXPRESSION[$e.start] equivalence_expression ) | q= quantification -> ^( EXPRESSION[$q.start] quantification ) );", 159, 0, input);

                throw nvae;
            }
            switch (alt159) {
                case 1 :
                    // BON.g:1889:16: e= equivalence_expression
                    {
                    pushFollow(FOLLOW_equivalence_expression_in_expression30497);
                    e=equivalence_expression();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_equivalence_expression.add(e.getTree());

                    // AST REWRITE
                    // elements: equivalence_expression
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1890:14: -> ^( EXPRESSION[$e.start] equivalence_expression )
                    {
                        // BON.g:1891:14: ^( EXPRESSION[$e.start] equivalence_expression )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(EXPRESSION, ((Token)e.start)), root_1);

                        adaptor.addChild(root_1, stream_equivalence_expression.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;
                case 2 :
                    // BON.g:1894:16: q= quantification
                    {
                    pushFollow(FOLLOW_quantification_in_expression30584);
                    q=quantification();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) stream_quantification.add(q.getTree());

                    // AST REWRITE
                    // elements: quantification
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 1895:14: -> ^( EXPRESSION[$q.start] quantification )
                    {
                        // BON.g:1896:14: ^( EXPRESSION[$q.start] quantification )
                        {
                        CommonTree root_1 = (CommonTree)adaptor.nil();
                        root_1 = (CommonTree)adaptor.becomeRoot(adaptor.create(EXPRESSION, ((Token)q.start)), root_1);

                        adaptor.addChild(root_1, stream_quantification.next());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end expression

    public static class equivalence_expression_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start equivalence_expression
    // BON.g:1901:1: equivalence_expression : implies_expression ( '<->' implies_expression )* ;
    public final equivalence_expression_return equivalence_expression() throws RecognitionException {
        equivalence_expression_return retval = new equivalence_expression_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal394=null;
        implies_expression_return implies_expression393 = null;

        implies_expression_return implies_expression395 = null;


        CommonTree string_literal394_tree=null;

        try {
            // BON.g:1901:24: ( implies_expression ( '<->' implies_expression )* )
            // BON.g:1901:27: implies_expression ( '<->' implies_expression )*
            {
            root_0 = (CommonTree)adaptor.nil();

            pushFollow(FOLLOW_implies_expression_in_equivalence_expression30674);
            implies_expression393=implies_expression();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) adaptor.addChild(root_0, implies_expression393.getTree());
            // BON.g:1901:46: ( '<->' implies_expression )*
            loop160:
            do {
                int alt160=2;
                int LA160_0 = input.LA(1);

                if ( (LA160_0==262) ) {
                    alt160=1;
                }


                switch (alt160) {
            	case 1 :
            	    // BON.g:1901:47: '<->' implies_expression
            	    {
            	    string_literal394=(Token)input.LT(1);
            	    match(input,262,FOLLOW_262_in_equivalence_expression30677); if (failed) return retval;
            	    if ( backtracking==0 ) {
            	    string_literal394_tree = (CommonTree)adaptor.create(string_literal394);
            	    root_0 = (CommonTree)adaptor.becomeRoot(string_literal394_tree, root_0);
            	    }
            	    pushFollow(FOLLOW_implies_expression_in_equivalence_expression30680);
            	    implies_expression395=implies_expression();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) adaptor.addChild(root_0, implies_expression395.getTree());

            	    }
            	    break;

            	default :
            	    break loop160;
                }
            } while (true);


            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end equivalence_expression

    public static class implies_expression_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start implies_expression
    // BON.g:1905:1: implies_expression : and_or_xor_expression ( '->' implies_expression )? ;
    public final implies_expression_return implies_expression() throws RecognitionException {
        implies_expression_return retval = new implies_expression_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal397=null;
        and_or_xor_expression_return and_or_xor_expression396 = null;

        implies_expression_return implies_expression398 = null;


        CommonTree string_literal397_tree=null;

        try {
            // BON.g:1905:21: ( and_or_xor_expression ( '->' implies_expression )? )
            // BON.g:1905:24: and_or_xor_expression ( '->' implies_expression )?
            {
            root_0 = (CommonTree)adaptor.nil();

            pushFollow(FOLLOW_and_or_xor_expression_in_implies_expression30719);
            and_or_xor_expression396=and_or_xor_expression();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) adaptor.addChild(root_0, and_or_xor_expression396.getTree());
            // BON.g:1905:46: ( '->' implies_expression )?
            int alt161=2;
            int LA161_0 = input.LA(1);

            if ( (LA161_0==227) ) {
                alt161=1;
            }
            switch (alt161) {
                case 1 :
                    // BON.g:1905:47: '->' implies_expression
                    {
                    string_literal397=(Token)input.LT(1);
                    match(input,227,FOLLOW_227_in_implies_expression30722); if (failed) return retval;
                    if ( backtracking==0 ) {
                    string_literal397_tree = (CommonTree)adaptor.create(string_literal397);
                    root_0 = (CommonTree)adaptor.becomeRoot(string_literal397_tree, root_0);
                    }
                    pushFollow(FOLLOW_implies_expression_in_implies_expression30725);
                    implies_expression398=implies_expression();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, implies_expression398.getTree());

                    }
                    break;

            }


            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end implies_expression

    public static class and_or_xor_expression_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start and_or_xor_expression
    // BON.g:1908:1: and_or_xor_expression : comparison_expression ( and_or_xor_op comparison_expression )* ;
    public final and_or_xor_expression_return and_or_xor_expression() throws RecognitionException {
        and_or_xor_expression_return retval = new and_or_xor_expression_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        comparison_expression_return comparison_expression399 = null;

        and_or_xor_op_return and_or_xor_op400 = null;

        comparison_expression_return comparison_expression401 = null;



        try {
            // BON.g:1908:24: ( comparison_expression ( and_or_xor_op comparison_expression )* )
            // BON.g:1908:27: comparison_expression ( and_or_xor_op comparison_expression )*
            {
            root_0 = (CommonTree)adaptor.nil();

            pushFollow(FOLLOW_comparison_expression_in_and_or_xor_expression30758);
            comparison_expression399=comparison_expression();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) adaptor.addChild(root_0, comparison_expression399.getTree());
            // BON.g:1908:49: ( and_or_xor_op comparison_expression )*
            loop162:
            do {
                int alt162=2;
                int LA162_0 = input.LA(1);

                if ( ((LA162_0>=265 && LA162_0<=267)) ) {
                    alt162=1;
                }


                switch (alt162) {
            	case 1 :
            	    // BON.g:1908:50: and_or_xor_op comparison_expression
            	    {
            	    pushFollow(FOLLOW_and_or_xor_op_in_and_or_xor_expression30761);
            	    and_or_xor_op400=and_or_xor_op();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) root_0 = (CommonTree)adaptor.becomeRoot(and_or_xor_op400.getTree(), root_0);
            	    pushFollow(FOLLOW_comparison_expression_in_and_or_xor_expression30764);
            	    comparison_expression401=comparison_expression();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) adaptor.addChild(root_0, comparison_expression401.getTree());

            	    }
            	    break;

            	default :
            	    break loop162;
                }
            } while (true);


            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end and_or_xor_expression

    public static class comparison_expression_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start comparison_expression
    // BON.g:1911:1: comparison_expression : add_sub_expression ( comparison_op add_sub_expression )* ;
    public final comparison_expression_return comparison_expression() throws RecognitionException {
        comparison_expression_return retval = new comparison_expression_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        add_sub_expression_return add_sub_expression402 = null;

        comparison_op_return comparison_op403 = null;

        add_sub_expression_return add_sub_expression404 = null;



        try {
            // BON.g:1911:24: ( add_sub_expression ( comparison_op add_sub_expression )* )
            // BON.g:1911:27: add_sub_expression ( comparison_op add_sub_expression )*
            {
            root_0 = (CommonTree)adaptor.nil();

            pushFollow(FOLLOW_add_sub_expression_in_comparison_expression30801);
            add_sub_expression402=add_sub_expression();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) adaptor.addChild(root_0, add_sub_expression402.getTree());
            // BON.g:1911:46: ( comparison_op add_sub_expression )*
            loop163:
            do {
                int alt163=2;
                int LA163_0 = input.LA(1);

                if ( (LA163_0==196||LA163_0==246||(LA163_0>=270 && LA163_0<=276)) ) {
                    alt163=1;
                }


                switch (alt163) {
            	case 1 :
            	    // BON.g:1911:47: comparison_op add_sub_expression
            	    {
            	    pushFollow(FOLLOW_comparison_op_in_comparison_expression30804);
            	    comparison_op403=comparison_op();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) root_0 = (CommonTree)adaptor.becomeRoot(comparison_op403.getTree(), root_0);
            	    pushFollow(FOLLOW_add_sub_expression_in_comparison_expression30808);
            	    add_sub_expression404=add_sub_expression();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) adaptor.addChild(root_0, add_sub_expression404.getTree());

            	    }
            	    break;

            	default :
            	    break loop163;
                }
            } while (true);


            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end comparison_expression

    public static class add_sub_expression_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start add_sub_expression
    // BON.g:1914:1: add_sub_expression : mul_div_expression ( add_sub_op mul_div_expression )* ;
    public final add_sub_expression_return add_sub_expression() throws RecognitionException {
        add_sub_expression_return retval = new add_sub_expression_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        mul_div_expression_return mul_div_expression405 = null;

        add_sub_op_return add_sub_op406 = null;

        mul_div_expression_return mul_div_expression407 = null;



        try {
            // BON.g:1914:21: ( mul_div_expression ( add_sub_op mul_div_expression )* )
            // BON.g:1914:24: mul_div_expression ( add_sub_op mul_div_expression )*
            {
            root_0 = (CommonTree)adaptor.nil();

            pushFollow(FOLLOW_mul_div_expression_in_add_sub_expression30845);
            mul_div_expression405=mul_div_expression();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) adaptor.addChild(root_0, mul_div_expression405.getTree());
            // BON.g:1914:43: ( add_sub_op mul_div_expression )*
            loop164:
            do {
                int alt164=2;
                int LA164_0 = input.LA(1);

                if ( ((LA164_0>=263 && LA164_0<=264)) ) {
                    alt164=1;
                }


                switch (alt164) {
            	case 1 :
            	    // BON.g:1914:44: add_sub_op mul_div_expression
            	    {
            	    pushFollow(FOLLOW_add_sub_op_in_add_sub_expression30848);
            	    add_sub_op406=add_sub_op();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) root_0 = (CommonTree)adaptor.becomeRoot(add_sub_op406.getTree(), root_0);
            	    pushFollow(FOLLOW_mul_div_expression_in_add_sub_expression30851);
            	    mul_div_expression407=mul_div_expression();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) adaptor.addChild(root_0, mul_div_expression407.getTree());

            	    }
            	    break;

            	default :
            	    break loop164;
                }
            } while (true);


            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end add_sub_expression

    public static class mul_div_expression_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start mul_div_expression
    // BON.g:1917:1: mul_div_expression : mod_pow_expression ( mul_div_op mod_pow_expression )* ;
    public final mul_div_expression_return mul_div_expression() throws RecognitionException {
        mul_div_expression_return retval = new mul_div_expression_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        mod_pow_expression_return mod_pow_expression408 = null;

        mul_div_op_return mul_div_op409 = null;

        mod_pow_expression_return mod_pow_expression410 = null;



        try {
            // BON.g:1917:21: ( mod_pow_expression ( mul_div_op mod_pow_expression )* )
            // BON.g:1917:24: mod_pow_expression ( mul_div_op mod_pow_expression )*
            {
            root_0 = (CommonTree)adaptor.nil();

            pushFollow(FOLLOW_mod_pow_expression_in_mul_div_expression30885);
            mod_pow_expression408=mod_pow_expression();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) adaptor.addChild(root_0, mod_pow_expression408.getTree());
            // BON.g:1917:43: ( mul_div_op mod_pow_expression )*
            loop165:
            do {
                int alt165=2;
                int LA165_0 = input.LA(1);

                if ( ((LA165_0>=277 && LA165_0<=279)) ) {
                    alt165=1;
                }


                switch (alt165) {
            	case 1 :
            	    // BON.g:1917:44: mul_div_op mod_pow_expression
            	    {
            	    pushFollow(FOLLOW_mul_div_op_in_mul_div_expression30888);
            	    mul_div_op409=mul_div_op();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) root_0 = (CommonTree)adaptor.becomeRoot(mul_div_op409.getTree(), root_0);
            	    pushFollow(FOLLOW_mod_pow_expression_in_mul_div_expression30891);
            	    mod_pow_expression410=mod_pow_expression();
            	    _fsp--;
            	    if (failed) return retval;
            	    if ( backtracking==0 ) adaptor.addChild(root_0, mod_pow_expression410.getTree());

            	    }
            	    break;

            	default :
            	    break loop165;
                }
            } while (true);


            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end mul_div_expression

    public static class mod_pow_expression_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start mod_pow_expression
    // BON.g:1921:1: mod_pow_expression : lowest_expression ( MOD_POW_OP mod_pow_expression )? ;
    public final mod_pow_expression_return mod_pow_expression() throws RecognitionException {
        mod_pow_expression_return retval = new mod_pow_expression_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token MOD_POW_OP412=null;
        lowest_expression_return lowest_expression411 = null;

        mod_pow_expression_return mod_pow_expression413 = null;


        CommonTree MOD_POW_OP412_tree=null;

        try {
            // BON.g:1921:21: ( lowest_expression ( MOD_POW_OP mod_pow_expression )? )
            // BON.g:1921:24: lowest_expression ( MOD_POW_OP mod_pow_expression )?
            {
            root_0 = (CommonTree)adaptor.nil();

            pushFollow(FOLLOW_lowest_expression_in_mod_pow_expression30926);
            lowest_expression411=lowest_expression();
            _fsp--;
            if (failed) return retval;
            if ( backtracking==0 ) adaptor.addChild(root_0, lowest_expression411.getTree());
            // BON.g:1921:42: ( MOD_POW_OP mod_pow_expression )?
            int alt166=2;
            int LA166_0 = input.LA(1);

            if ( (LA166_0==MOD_POW_OP) ) {
                alt166=1;
            }
            switch (alt166) {
                case 1 :
                    // BON.g:1921:43: MOD_POW_OP mod_pow_expression
                    {
                    MOD_POW_OP412=(Token)input.LT(1);
                    match(input,MOD_POW_OP,FOLLOW_MOD_POW_OP_in_mod_pow_expression30929); if (failed) return retval;
                    if ( backtracking==0 ) {
                    MOD_POW_OP412_tree = (CommonTree)adaptor.create(MOD_POW_OP412);
                    root_0 = (CommonTree)adaptor.becomeRoot(MOD_POW_OP412_tree, root_0);
                    }
                    pushFollow(FOLLOW_mod_pow_expression_in_mod_pow_expression30932);
                    mod_pow_expression413=mod_pow_expression();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, mod_pow_expression413.getTree());

                    }
                    break;

            }


            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end mod_pow_expression

    public static class lowest_expression_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start lowest_expression
    // BON.g:1924:1: lowest_expression : ( ( constant )=> constant | unary lowest_expression | '(' expression ')' ( '.' call_chain )? | call_chain );
    public final lowest_expression_return lowest_expression() throws RecognitionException {
        lowest_expression_return retval = new lowest_expression_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal417=null;
        Token char_literal419=null;
        Token char_literal420=null;
        constant_return constant414 = null;

        unary_return unary415 = null;

        lowest_expression_return lowest_expression416 = null;

        expression_return expression418 = null;

        call_chain_return call_chain421 = null;

        call_chain_return call_chain422 = null;


        CommonTree char_literal417_tree=null;
        CommonTree char_literal419_tree=null;
        CommonTree char_literal420_tree=null;

        try {
            // BON.g:1924:20: ( ( constant )=> constant | unary lowest_expression | '(' expression ')' ( '.' call_chain )? | call_chain )
            int alt168=4;
            int LA168_0 = input.LA(1);

            if ( (LA168_0==250) && (synpred1())) {
                alt168=1;
            }
            else if ( (LA168_0==251) && (synpred1())) {
                alt168=1;
            }
            else if ( (LA168_0==CHARACTER_CONSTANT) && (synpred1())) {
                alt168=1;
            }
            else if ( ((LA168_0>=263 && LA168_0<=264)) ) {
                int LA168_4 = input.LA(2);

                if ( (synpred1()) ) {
                    alt168=1;
                }
                else if ( (true) ) {
                    alt168=2;
                }
                else {
                    if (backtracking>0) {failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("1924:1: lowest_expression : ( ( constant )=> constant | unary lowest_expression | '(' expression ')' ( '.' call_chain )? | call_chain );", 168, 4, input);

                    throw nvae;
                }
            }
            else if ( (LA168_0==INTEGER) && (synpred1())) {
                alt168=1;
            }
            else if ( (LA168_0==REAL) && (synpred1())) {
                alt168=1;
            }
            else if ( (LA168_0==MANIFEST_STRING) && (synpred1())) {
                alt168=1;
            }
            else if ( (LA168_0==222) && (synpred1())) {
                alt168=1;
            }
            else if ( (LA168_0==248) && (synpred1())) {
                alt168=1;
            }
            else if ( (LA168_0==249) && (synpred1())) {
                alt168=1;
            }
            else if ( ((LA168_0>=268 && LA168_0<=270)) ) {
                alt168=2;
            }
            else if ( (LA168_0==225) ) {
                alt168=3;
            }
            else if ( (LA168_0==IDENTIFIER) ) {
                alt168=4;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1924:1: lowest_expression : ( ( constant )=> constant | unary lowest_expression | '(' expression ')' ( '.' call_chain )? | call_chain );", 168, 0, input);

                throw nvae;
            }
            switch (alt168) {
                case 1 :
                    // BON.g:1924:23: ( constant )=> constant
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_constant_in_lowest_expression30971);
                    constant414=constant();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, constant414.getTree());

                    }
                    break;
                case 2 :
                    // BON.g:1925:13: unary lowest_expression
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_unary_in_lowest_expression30985);
                    unary415=unary();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, unary415.getTree());
                    pushFollow(FOLLOW_lowest_expression_in_lowest_expression30987);
                    lowest_expression416=lowest_expression();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, lowest_expression416.getTree());

                    }
                    break;
                case 3 :
                    // BON.g:1926:18: '(' expression ')' ( '.' call_chain )?
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    char_literal417=(Token)input.LT(1);
                    match(input,225,FOLLOW_225_in_lowest_expression31006); if (failed) return retval;
                    if ( backtracking==0 ) {
                    char_literal417_tree = (CommonTree)adaptor.create(char_literal417);
                    adaptor.addChild(root_0, char_literal417_tree);
                    }
                    pushFollow(FOLLOW_expression_in_lowest_expression31008);
                    expression418=expression();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, expression418.getTree());
                    char_literal419=(Token)input.LT(1);
                    match(input,226,FOLLOW_226_in_lowest_expression31010); if (failed) return retval;
                    if ( backtracking==0 ) {
                    char_literal419_tree = (CommonTree)adaptor.create(char_literal419);
                    adaptor.addChild(root_0, char_literal419_tree);
                    }
                    // BON.g:1926:37: ( '.' call_chain )?
                    int alt167=2;
                    int LA167_0 = input.LA(1);

                    if ( (LA167_0==232) ) {
                        alt167=1;
                    }
                    switch (alt167) {
                        case 1 :
                            // BON.g:1926:38: '.' call_chain
                            {
                            char_literal420=(Token)input.LT(1);
                            match(input,232,FOLLOW_232_in_lowest_expression31013); if (failed) return retval;
                            if ( backtracking==0 ) {
                            char_literal420_tree = (CommonTree)adaptor.create(char_literal420);
                            adaptor.addChild(root_0, char_literal420_tree);
                            }
                            pushFollow(FOLLOW_call_chain_in_lowest_expression31015);
                            call_chain421=call_chain();
                            _fsp--;
                            if (failed) return retval;
                            if ( backtracking==0 ) adaptor.addChild(root_0, call_chain421.getTree());

                            }
                            break;

                    }


                    }
                    break;
                case 4 :
                    // BON.g:1927:18: call_chain
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_call_chain_in_lowest_expression31036);
                    call_chain422=call_chain();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, call_chain422.getTree());

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end lowest_expression

    public static class manifest_textblock_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start manifest_textblock
    // BON.g:1968:1: manifest_textblock : ( MANIFEST_STRING | MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END );
    public final manifest_textblock_return manifest_textblock() throws RecognitionException {
        manifest_textblock_return retval = new manifest_textblock_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token MANIFEST_STRING423=null;
        Token MANIFEST_TEXTBLOCK_START424=null;
        Token MANIFEST_TEXTBLOCK_MIDDLE425=null;
        Token MANIFEST_TEXTBLOCK_END426=null;

        CommonTree MANIFEST_STRING423_tree=null;
        CommonTree MANIFEST_TEXTBLOCK_START424_tree=null;
        CommonTree MANIFEST_TEXTBLOCK_MIDDLE425_tree=null;
        CommonTree MANIFEST_TEXTBLOCK_END426_tree=null;

        try {
            // BON.g:1968:21: ( MANIFEST_STRING | MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END )
            int alt170=2;
            int LA170_0 = input.LA(1);

            if ( (LA170_0==MANIFEST_STRING) ) {
                alt170=1;
            }
            else if ( (LA170_0==MANIFEST_TEXTBLOCK_START) ) {
                alt170=2;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("1968:1: manifest_textblock : ( MANIFEST_STRING | MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END );", 170, 0, input);

                throw nvae;
            }
            switch (alt170) {
                case 1 :
                    // BON.g:1968:25: MANIFEST_STRING
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    MANIFEST_STRING423=(Token)input.LT(1);
                    match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_manifest_textblock31347); if (failed) return retval;
                    if ( backtracking==0 ) {
                    MANIFEST_STRING423_tree = (CommonTree)adaptor.create(MANIFEST_STRING423);
                    adaptor.addChild(root_0, MANIFEST_STRING423_tree);
                    }

                    }
                    break;
                case 2 :
                    // BON.g:1969:14: MANIFEST_TEXTBLOCK_START ( MANIFEST_TEXTBLOCK_MIDDLE )* MANIFEST_TEXTBLOCK_END
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    MANIFEST_TEXTBLOCK_START424=(Token)input.LT(1);
                    match(input,MANIFEST_TEXTBLOCK_START,FOLLOW_MANIFEST_TEXTBLOCK_START_in_manifest_textblock31363); if (failed) return retval;
                    if ( backtracking==0 ) {
                    MANIFEST_TEXTBLOCK_START424_tree = (CommonTree)adaptor.create(MANIFEST_TEXTBLOCK_START424);
                    adaptor.addChild(root_0, MANIFEST_TEXTBLOCK_START424_tree);
                    }
                    // BON.g:1969:39: ( MANIFEST_TEXTBLOCK_MIDDLE )*
                    loop169:
                    do {
                        int alt169=2;
                        int LA169_0 = input.LA(1);

                        if ( (LA169_0==MANIFEST_TEXTBLOCK_MIDDLE) ) {
                            alt169=1;
                        }


                        switch (alt169) {
                    	case 1 :
                    	    // BON.g:1969:39: MANIFEST_TEXTBLOCK_MIDDLE
                    	    {
                    	    MANIFEST_TEXTBLOCK_MIDDLE425=(Token)input.LT(1);
                    	    match(input,MANIFEST_TEXTBLOCK_MIDDLE,FOLLOW_MANIFEST_TEXTBLOCK_MIDDLE_in_manifest_textblock31365); if (failed) return retval;
                    	    if ( backtracking==0 ) {
                    	    MANIFEST_TEXTBLOCK_MIDDLE425_tree = (CommonTree)adaptor.create(MANIFEST_TEXTBLOCK_MIDDLE425);
                    	    adaptor.addChild(root_0, MANIFEST_TEXTBLOCK_MIDDLE425_tree);
                    	    }

                    	    }
                    	    break;

                    	default :
                    	    break loop169;
                        }
                    } while (true);

                    MANIFEST_TEXTBLOCK_END426=(Token)input.LT(1);
                    match(input,MANIFEST_TEXTBLOCK_END,FOLLOW_MANIFEST_TEXTBLOCK_END_in_manifest_textblock31368); if (failed) return retval;
                    if ( backtracking==0 ) {
                    MANIFEST_TEXTBLOCK_END426_tree = (CommonTree)adaptor.create(MANIFEST_TEXTBLOCK_END426);
                    adaptor.addChild(root_0, MANIFEST_TEXTBLOCK_END426_tree);
                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end manifest_textblock

    public static class add_sub_op_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start add_sub_op
    // BON.g:2001:1: add_sub_op : ( '+' | '-' );
    public final add_sub_op_return add_sub_op() throws RecognitionException {
        add_sub_op_return retval = new add_sub_op_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token set427=null;

        CommonTree set427_tree=null;

        try {
            // BON.g:2005:13: ( '+' | '-' )
            // BON.g:
            {
            root_0 = (CommonTree)adaptor.nil();

            set427=(Token)input.LT(1);
            if ( (input.LA(1)>=263 && input.LA(1)<=264) ) {
                input.consume();
                if ( backtracking==0 ) adaptor.addChild(root_0, adaptor.create(set427));
                errorRecovery=false;failed=false;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                MismatchedSetException mse =
                    new MismatchedSetException(null,input);
                recoverFromMismatchedSet(input,mse,FOLLOW_set_in_add_sub_op0);    throw mse;
            }


            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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

    public static class and_or_xor_op_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start and_or_xor_op
    // BON.g:2009:1: and_or_xor_op : ( 'and' | 'or' | 'xor' );
    public final and_or_xor_op_return and_or_xor_op() throws RecognitionException {
        and_or_xor_op_return retval = new and_or_xor_op_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token set428=null;

        CommonTree set428_tree=null;

        try {
            // BON.g:2009:16: ( 'and' | 'or' | 'xor' )
            // BON.g:
            {
            root_0 = (CommonTree)adaptor.nil();

            set428=(Token)input.LT(1);
            if ( (input.LA(1)>=265 && input.LA(1)<=267) ) {
                input.consume();
                if ( backtracking==0 ) adaptor.addChild(root_0, adaptor.create(set428));
                errorRecovery=false;failed=false;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                MismatchedSetException mse =
                    new MismatchedSetException(null,input);
                recoverFromMismatchedSet(input,mse,FOLLOW_set_in_and_or_xor_op0);    throw mse;
            }


            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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

    public static class unary_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start unary
    // BON.g:2014:1: unary : ( other_unary | add_sub_op );
    public final unary_return unary() throws RecognitionException {
        unary_return retval = new unary_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        other_unary_return other_unary429 = null;

        add_sub_op_return add_sub_op430 = null;



        try {
            // BON.g:2014:9: ( other_unary | add_sub_op )
            int alt171=2;
            int LA171_0 = input.LA(1);

            if ( ((LA171_0>=268 && LA171_0<=270)) ) {
                alt171=1;
            }
            else if ( ((LA171_0>=263 && LA171_0<=264)) ) {
                alt171=2;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("2014:1: unary : ( other_unary | add_sub_op );", 171, 0, input);

                throw nvae;
            }
            switch (alt171) {
                case 1 :
                    // BON.g:2014:13: other_unary
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_other_unary_in_unary31723);
                    other_unary429=other_unary();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, other_unary429.getTree());

                    }
                    break;
                case 2 :
                    // BON.g:2015:13: add_sub_op
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_add_sub_op_in_unary31738);
                    add_sub_op430=add_sub_op();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, add_sub_op430.getTree());

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end unary

    public static class other_unary_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start other_unary
    // BON.g:2018:1: other_unary : ( delta | old | not );
    public final other_unary_return other_unary() throws RecognitionException {
        other_unary_return retval = new other_unary_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        delta_return delta431 = null;

        old_return old432 = null;

        not_return not433 = null;



        try {
            // BON.g:2018:14: ( delta | old | not )
            int alt172=3;
            switch ( input.LA(1) ) {
            case 268:
                {
                alt172=1;
                }
                break;
            case 269:
                {
                alt172=2;
                }
                break;
            case 270:
                {
                alt172=3;
                }
                break;
            default:
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("2018:1: other_unary : ( delta | old | not );", 172, 0, input);

                throw nvae;
            }

            switch (alt172) {
                case 1 :
                    // BON.g:2018:17: delta
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_delta_in_other_unary31758);
                    delta431=delta();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, delta431.getTree());

                    }
                    break;
                case 2 :
                    // BON.g:2019:16: old
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_old_in_other_unary31776);
                    old432=old();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, old432.getTree());

                    }
                    break;
                case 3 :
                    // BON.g:2020:17: not
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_not_in_other_unary31795);
                    not433=not();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, not433.getTree());

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end other_unary

    public static class delta_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start delta
    // BON.g:2023:1: delta : 'delta' ;
    public final delta_return delta() throws RecognitionException {
        delta_return retval = new delta_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal434=null;

        CommonTree string_literal434_tree=null;

        try {
            // BON.g:2023:7: ( 'delta' )
            // BON.g:2023:9: 'delta'
            {
            root_0 = (CommonTree)adaptor.nil();

            string_literal434=(Token)input.LT(1);
            match(input,268,FOLLOW_268_in_delta31830); if (failed) return retval;
            if ( backtracking==0 ) {
            string_literal434_tree = (CommonTree)adaptor.create(string_literal434);
            adaptor.addChild(root_0, string_literal434_tree);
            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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

    public static class old_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start old
    // BON.g:2026:1: old : 'old' ;
    public final old_return old() throws RecognitionException {
        old_return retval = new old_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal435=null;

        CommonTree string_literal435_tree=null;

        try {
            // BON.g:2026:5: ( 'old' )
            // BON.g:2026:7: 'old'
            {
            root_0 = (CommonTree)adaptor.nil();

            string_literal435=(Token)input.LT(1);
            match(input,269,FOLLOW_269_in_old31845); if (failed) return retval;
            if ( backtracking==0 ) {
            string_literal435_tree = (CommonTree)adaptor.create(string_literal435);
            adaptor.addChild(root_0, string_literal435_tree);
            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end old

    public static class not_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start not
    // BON.g:2029:1: not : 'not' ;
    public final not_return not() throws RecognitionException {
        not_return retval = new not_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token string_literal436=null;

        CommonTree string_literal436_tree=null;

        try {
            // BON.g:2029:5: ( 'not' )
            // BON.g:2029:7: 'not'
            {
            root_0 = (CommonTree)adaptor.nil();

            string_literal436=(Token)input.LT(1);
            match(input,270,FOLLOW_270_in_not31862); if (failed) return retval;
            if ( backtracking==0 ) {
            string_literal436_tree = (CommonTree)adaptor.create(string_literal436);
            adaptor.addChild(root_0, string_literal436_tree);
            }

            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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

    public static class binary_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start binary
    // BON.g:2032:1: binary : ( add_sub_op | mul_div_op | comparison_op | MOD_POW_OP | and_or_xor_op | '->' | '<->' );
    public final binary_return binary() throws RecognitionException {
        binary_return retval = new binary_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token MOD_POW_OP440=null;
        Token string_literal442=null;
        Token string_literal443=null;
        add_sub_op_return add_sub_op437 = null;

        mul_div_op_return mul_div_op438 = null;

        comparison_op_return comparison_op439 = null;

        and_or_xor_op_return and_or_xor_op441 = null;


        CommonTree MOD_POW_OP440_tree=null;
        CommonTree string_literal442_tree=null;
        CommonTree string_literal443_tree=null;

        try {
            // BON.g:2032:9: ( add_sub_op | mul_div_op | comparison_op | MOD_POW_OP | and_or_xor_op | '->' | '<->' )
            int alt173=7;
            switch ( input.LA(1) ) {
            case 263:
            case 264:
                {
                alt173=1;
                }
                break;
            case 277:
            case 278:
            case 279:
                {
                alt173=2;
                }
                break;
            case 196:
            case 246:
            case 270:
            case 271:
            case 272:
            case 273:
            case 274:
            case 275:
            case 276:
                {
                alt173=3;
                }
                break;
            case MOD_POW_OP:
                {
                alt173=4;
                }
                break;
            case 265:
            case 266:
            case 267:
                {
                alt173=5;
                }
                break;
            case 227:
                {
                alt173=6;
                }
                break;
            case 262:
                {
                alt173=7;
                }
                break;
            default:
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("2032:1: binary : ( add_sub_op | mul_div_op | comparison_op | MOD_POW_OP | and_or_xor_op | '->' | '<->' );", 173, 0, input);

                throw nvae;
            }

            switch (alt173) {
                case 1 :
                    // BON.g:2032:13: add_sub_op
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_add_sub_op_in_binary31893);
                    add_sub_op437=add_sub_op();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, add_sub_op437.getTree());

                    }
                    break;
                case 2 :
                    // BON.g:2032:26: mul_div_op
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_mul_div_op_in_binary31897);
                    mul_div_op438=mul_div_op();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, mul_div_op438.getTree());

                    }
                    break;
                case 3 :
                    // BON.g:2032:39: comparison_op
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_comparison_op_in_binary31901);
                    comparison_op439=comparison_op();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, comparison_op439.getTree());

                    }
                    break;
                case 4 :
                    // BON.g:2033:13: MOD_POW_OP
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    MOD_POW_OP440=(Token)input.LT(1);
                    match(input,MOD_POW_OP,FOLLOW_MOD_POW_OP_in_binary31916); if (failed) return retval;
                    if ( backtracking==0 ) {
                    MOD_POW_OP440_tree = (CommonTree)adaptor.create(MOD_POW_OP440);
                    adaptor.addChild(root_0, MOD_POW_OP440_tree);
                    }

                    }
                    break;
                case 5 :
                    // BON.g:2033:26: and_or_xor_op
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    pushFollow(FOLLOW_and_or_xor_op_in_binary31920);
                    and_or_xor_op441=and_or_xor_op();
                    _fsp--;
                    if (failed) return retval;
                    if ( backtracking==0 ) adaptor.addChild(root_0, and_or_xor_op441.getTree());

                    }
                    break;
                case 6 :
                    // BON.g:2034:13: '->'
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    string_literal442=(Token)input.LT(1);
                    match(input,227,FOLLOW_227_in_binary31935); if (failed) return retval;
                    if ( backtracking==0 ) {
                    string_literal442_tree = (CommonTree)adaptor.create(string_literal442);
                    adaptor.addChild(root_0, string_literal442_tree);
                    }

                    }
                    break;
                case 7 :
                    // BON.g:2034:20: '<->'
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    string_literal443=(Token)input.LT(1);
                    match(input,262,FOLLOW_262_in_binary31939); if (failed) return retval;
                    if ( backtracking==0 ) {
                    string_literal443_tree = (CommonTree)adaptor.create(string_literal443);
                    adaptor.addChild(root_0, string_literal443_tree);
                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end binary

    public static class comparison_op_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start comparison_op
    // BON.g:2036:1: comparison_op : ( '<' | '>' | '<=' | '>=' | '=' | '/=' | 'member_of' | 'not' 'member_of' -> NOT_MEMBER_OF | ':' );
    public final comparison_op_return comparison_op() throws RecognitionException {
        comparison_op_return retval = new comparison_op_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token char_literal444=null;
        Token char_literal445=null;
        Token string_literal446=null;
        Token string_literal447=null;
        Token char_literal448=null;
        Token string_literal449=null;
        Token string_literal450=null;
        Token string_literal451=null;
        Token string_literal452=null;
        Token char_literal453=null;

        CommonTree char_literal444_tree=null;
        CommonTree char_literal445_tree=null;
        CommonTree string_literal446_tree=null;
        CommonTree string_literal447_tree=null;
        CommonTree char_literal448_tree=null;
        CommonTree string_literal449_tree=null;
        CommonTree string_literal450_tree=null;
        CommonTree string_literal451_tree=null;
        CommonTree string_literal452_tree=null;
        CommonTree char_literal453_tree=null;
        RewriteRuleTokenStream stream_270=new RewriteRuleTokenStream(adaptor,"token 270");
        RewriteRuleTokenStream stream_246=new RewriteRuleTokenStream(adaptor,"token 246");

        try {
            // BON.g:2036:16: ( '<' | '>' | '<=' | '>=' | '=' | '/=' | 'member_of' | 'not' 'member_of' -> NOT_MEMBER_OF | ':' )
            int alt174=9;
            switch ( input.LA(1) ) {
            case 271:
                {
                alt174=1;
                }
                break;
            case 272:
                {
                alt174=2;
                }
                break;
            case 273:
                {
                alt174=3;
                }
                break;
            case 274:
                {
                alt174=4;
                }
                break;
            case 275:
                {
                alt174=5;
                }
                break;
            case 276:
                {
                alt174=6;
                }
                break;
            case 246:
                {
                alt174=7;
                }
                break;
            case 270:
                {
                alt174=8;
                }
                break;
            case 196:
                {
                alt174=9;
                }
                break;
            default:
                if (backtracking>0) {failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("2036:1: comparison_op : ( '<' | '>' | '<=' | '>=' | '=' | '/=' | 'member_of' | 'not' 'member_of' -> NOT_MEMBER_OF | ':' );", 174, 0, input);

                throw nvae;
            }

            switch (alt174) {
                case 1 :
                    // BON.g:2036:21: '<'
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    char_literal444=(Token)input.LT(1);
                    match(input,271,FOLLOW_271_in_comparison_op31952); if (failed) return retval;
                    if ( backtracking==0 ) {
                    char_literal444_tree = (CommonTree)adaptor.create(char_literal444);
                    adaptor.addChild(root_0, char_literal444_tree);
                    }

                    }
                    break;
                case 2 :
                    // BON.g:2037:21: '>'
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    char_literal445=(Token)input.LT(1);
                    match(input,272,FOLLOW_272_in_comparison_op31974); if (failed) return retval;
                    if ( backtracking==0 ) {
                    char_literal445_tree = (CommonTree)adaptor.create(char_literal445);
                    adaptor.addChild(root_0, char_literal445_tree);
                    }

                    }
                    break;
                case 3 :
                    // BON.g:2038:21: '<='
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    string_literal446=(Token)input.LT(1);
                    match(input,273,FOLLOW_273_in_comparison_op31996); if (failed) return retval;
                    if ( backtracking==0 ) {
                    string_literal446_tree = (CommonTree)adaptor.create(string_literal446);
                    adaptor.addChild(root_0, string_literal446_tree);
                    }

                    }
                    break;
                case 4 :
                    // BON.g:2039:21: '>='
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    string_literal447=(Token)input.LT(1);
                    match(input,274,FOLLOW_274_in_comparison_op32018); if (failed) return retval;
                    if ( backtracking==0 ) {
                    string_literal447_tree = (CommonTree)adaptor.create(string_literal447);
                    adaptor.addChild(root_0, string_literal447_tree);
                    }

                    }
                    break;
                case 5 :
                    // BON.g:2040:21: '='
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    char_literal448=(Token)input.LT(1);
                    match(input,275,FOLLOW_275_in_comparison_op32040); if (failed) return retval;
                    if ( backtracking==0 ) {
                    char_literal448_tree = (CommonTree)adaptor.create(char_literal448);
                    adaptor.addChild(root_0, char_literal448_tree);
                    }

                    }
                    break;
                case 6 :
                    // BON.g:2041:21: '/='
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    string_literal449=(Token)input.LT(1);
                    match(input,276,FOLLOW_276_in_comparison_op32062); if (failed) return retval;
                    if ( backtracking==0 ) {
                    string_literal449_tree = (CommonTree)adaptor.create(string_literal449);
                    adaptor.addChild(root_0, string_literal449_tree);
                    }

                    }
                    break;
                case 7 :
                    // BON.g:2042:21: 'member_of'
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    string_literal450=(Token)input.LT(1);
                    match(input,246,FOLLOW_246_in_comparison_op32084); if (failed) return retval;
                    if ( backtracking==0 ) {
                    string_literal450_tree = (CommonTree)adaptor.create(string_literal450);
                    adaptor.addChild(root_0, string_literal450_tree);
                    }

                    }
                    break;
                case 8 :
                    // BON.g:2043:21: 'not' 'member_of'
                    {
                    string_literal451=(Token)input.LT(1);
                    match(input,270,FOLLOW_270_in_comparison_op32106); if (failed) return retval;
                    if ( backtracking==0 ) stream_270.add(string_literal451);

                    string_literal452=(Token)input.LT(1);
                    match(input,246,FOLLOW_246_in_comparison_op32108); if (failed) return retval;
                    if ( backtracking==0 ) stream_246.add(string_literal452);


                    // AST REWRITE
                    // elements: 
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (CommonTree)adaptor.nil();
                    // 2044:19: -> NOT_MEMBER_OF
                    {
                        adaptor.addChild(root_0, adaptor.create(NOT_MEMBER_OF, "NOT_MEMBER_OF"));

                    }

                    }

                    }
                    break;
                case 9 :
                    // BON.g:2046:21: ':'
                    {
                    root_0 = (CommonTree)adaptor.nil();

                    char_literal453=(Token)input.LT(1);
                    match(input,196,FOLLOW_196_in_comparison_op32171); if (failed) return retval;
                    if ( backtracking==0 ) {
                    char_literal453_tree = (CommonTree)adaptor.create(char_literal453);
                    adaptor.addChild(root_0, char_literal453_tree);
                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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
    // $ANTLR end comparison_op

    public static class mul_div_op_return extends ParserRuleReturnScope {
        CommonTree tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start mul_div_op
    // BON.g:2050:1: mul_div_op : ( '*' | '/' | '\\\\' );
    public final mul_div_op_return mul_div_op() throws RecognitionException {
        mul_div_op_return retval = new mul_div_op_return();
        retval.start = input.LT(1);

        CommonTree root_0 = null;

        Token set454=null;

        CommonTree set454_tree=null;

        try {
            // BON.g:2050:13: ( '*' | '/' | '\\\\' )
            // BON.g:
            {
            root_0 = (CommonTree)adaptor.nil();

            set454=(Token)input.LT(1);
            if ( (input.LA(1)>=277 && input.LA(1)<=279) ) {
                input.consume();
                if ( backtracking==0 ) adaptor.addChild(root_0, adaptor.create(set454));
                errorRecovery=false;failed=false;
            }
            else {
                if (backtracking>0) {failed=true; return retval;}
                MismatchedSetException mse =
                    new MismatchedSetException(null,input);
                recoverFromMismatchedSet(input,mse,FOLLOW_set_in_mul_div_op0);    throw mse;
            }


            }

            retval.stop = input.LT(-1);

            if ( backtracking==0 ) {
                retval.tree = (CommonTree)adaptor.rulePostProcessing(root_0);
                adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
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

    // $ANTLR start synpred1
    public final void synpred1_fragment() throws RecognitionException {   
        // BON.g:1924:23: ( constant )
        // BON.g:1924:24: constant
        {
        pushFollow(FOLLOW_constant_in_synpred130967);
        constant();
        _fsp--;
        if (failed) return ;

        }
    }
    // $ANTLR end synpred1

    public final boolean synpred1() {
        backtracking++;
        int start = input.mark();
        try {
            synpred1_fragment(); // can never throw exception
        } catch (RecognitionException re) {
            System.err.println("impossible: "+re);
        }
        boolean success = !failed;
        input.rewind(start);
        backtracking--;
        failed=false;
        return success;
    }


    protected DFA3 dfa3 = new DFA3(this);
    protected DFA77 dfa77 = new DFA77(this);
    protected DFA128 dfa128 = new DFA128(this);
    static final String DFA3_eotS =
        "\24\uffff";
    static final String DFA3_eofS =
        "\2\3\3\uffff\2\3\1\uffff\1\3\1\uffff\1\3\1\uffff\4\3\2\uffff\2\3";
    static final String DFA3_minS =
        "\1\u00ba\1\u00a6\2\uffff\1\u00c4\1\u00a5\1\u00a6\1\u00c4\1\u00a6"+
        "\1\u00c4\3\u00a5\3\u00a6\2\u00a5\2\u00a6";
    static final String DFA3_maxS =
        "\2\u0105\2\uffff\1\u00c4\2\u0105\1\u00c4\1\u0105\1\u00c4\1\u0105"+
        "\1\u00a5\4\u0105\2\u00a5\2\u0105";
    static final String DFA3_acceptS =
        "\2\uffff\1\1\1\2\20\uffff";
    static final String DFA3_specialS =
        "\24\uffff}>";
    static final String[] DFA3_transitionS = {
            "\1\2\3\uffff\1\2\1\uffff\1\1\5\uffff\2\2\4\uffff\1\2\4\uffff"+
            "\1\2\1\uffff\1\2\2\uffff\1\2\45\uffff\1\2\6\uffff\3\2",
            "\1\4\23\uffff\1\2\3\uffff\1\2\7\uffff\2\2\4\uffff\1\2\4\uffff"+
            "\1\2\1\uffff\1\2\2\uffff\1\2\45\uffff\1\2\6\uffff\3\2",
            "",
            "",
            "\1\5",
            "\1\10\1\7\23\uffff\1\2\3\uffff\1\2\4\uffff\1\6\2\uffff\2\2\4"+
            "\uffff\1\2\4\uffff\1\2\1\uffff\1\2\2\uffff\1\2\45\uffff\1\2"+
            "\6\uffff\3\2",
            "\1\11\23\uffff\1\2\3\uffff\1\2\7\uffff\2\2\4\uffff\1\2\4\uffff"+
            "\1\2\1\uffff\1\2\2\uffff\1\2\45\uffff\1\2\6\uffff\3\2",
            "\1\12",
            "\1\7\23\uffff\1\2\3\uffff\1\2\4\uffff\1\6\1\uffff\1\13\2\2\4"+
            "\uffff\1\2\4\uffff\1\2\1\uffff\1\2\2\uffff\1\2\45\uffff\1\2"+
            "\6\uffff\3\2",
            "\1\14",
            "\1\15\1\7\23\uffff\1\2\3\uffff\1\2\4\uffff\1\6\2\uffff\2\2\4"+
            "\uffff\1\2\4\uffff\1\2\1\uffff\1\2\2\uffff\1\2\45\uffff\1\2"+
            "\6\uffff\3\2",
            "\1\16",
            "\1\17\1\7\23\uffff\1\2\3\uffff\1\2\4\uffff\1\6\2\uffff\2\2\4"+
            "\uffff\1\2\4\uffff\1\2\1\uffff\1\2\2\uffff\1\2\45\uffff\1\2"+
            "\6\uffff\3\2",
            "\1\7\23\uffff\1\2\3\uffff\1\2\4\uffff\1\6\1\uffff\1\20\2\2\4"+
            "\uffff\1\2\4\uffff\1\2\1\uffff\1\2\2\uffff\1\2\45\uffff\1\2"+
            "\6\uffff\3\2",
            "\1\7\23\uffff\1\2\3\uffff\1\2\4\uffff\1\6\1\uffff\1\13\2\2\4"+
            "\uffff\1\2\4\uffff\1\2\1\uffff\1\2\2\uffff\1\2\45\uffff\1\2"+
            "\6\uffff\3\2",
            "\1\7\23\uffff\1\2\3\uffff\1\2\4\uffff\1\6\1\uffff\1\21\2\2\4"+
            "\uffff\1\2\4\uffff\1\2\1\uffff\1\2\2\uffff\1\2\45\uffff\1\2"+
            "\6\uffff\3\2",
            "\1\22",
            "\1\23",
            "\1\7\23\uffff\1\2\3\uffff\1\2\4\uffff\1\6\1\uffff\1\20\2\2\4"+
            "\uffff\1\2\4\uffff\1\2\1\uffff\1\2\2\uffff\1\2\45\uffff\1\2"+
            "\6\uffff\3\2",
            "\1\7\23\uffff\1\2\3\uffff\1\2\4\uffff\1\6\1\uffff\1\21\2\2\4"+
            "\uffff\1\2\4\uffff\1\2\1\uffff\1\2\2\uffff\1\2\45\uffff\1\2"+
            "\6\uffff\3\2"
    };

    static final short[] DFA3_eot = DFA.unpackEncodedString(DFA3_eotS);
    static final short[] DFA3_eof = DFA.unpackEncodedString(DFA3_eofS);
    static final char[] DFA3_min = DFA.unpackEncodedStringToUnsignedChars(DFA3_minS);
    static final char[] DFA3_max = DFA.unpackEncodedStringToUnsignedChars(DFA3_maxS);
    static final short[] DFA3_accept = DFA.unpackEncodedString(DFA3_acceptS);
    static final short[] DFA3_special = DFA.unpackEncodedString(DFA3_specialS);
    static final short[][] DFA3_transition;

    static {
        int numStates = DFA3_transitionS.length;
        DFA3_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA3_transition[i] = DFA.unpackEncodedString(DFA3_transitionS[i]);
        }
    }

    class DFA3 extends DFA {

        public DFA3(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 3;
            this.eot = DFA3_eot;
            this.eof = DFA3_eof;
            this.min = DFA3_min;
            this.max = DFA3_max;
            this.accept = DFA3_accept;
            this.special = DFA3_special;
            this.transition = DFA3_transition;
        }
        public String getDescription() {
            return "199:1: prog : ( ( indexing )? bon_specification EOF -> ^( PROG ( indexing )? bon_specification ) | ( indexing )? e= EOF -> ^( PROG PARSE_ERROR ) );";
        }
    }
    static final String DFA77_eotS =
        "\7\uffff";
    static final String DFA77_eofS =
        "\7\uffff";
    static final String DFA77_minS =
        "\1\u00a6\1\u00c8\1\uffff\1\u00a6\1\uffff\1\u00c8\1\u00a6";
    static final String DFA77_maxS =
        "\1\u00a6\1\u00e8\1\uffff\1\u00a6\1\uffff\1\u00e8\1\u00a6";
    static final String DFA77_acceptS =
        "\2\uffff\1\2\1\uffff\1\1\2\uffff";
    static final String DFA77_specialS =
        "\7\uffff}>";
    static final String[] DFA77_transitionS = {
            "\1\1",
            "\1\4\27\uffff\1\2\7\uffff\1\3",
            "",
            "\1\5",
            "",
            "\1\4\27\uffff\1\2\7\uffff\1\6",
            "\1\5"
    };

    static final short[] DFA77_eot = DFA.unpackEncodedString(DFA77_eotS);
    static final short[] DFA77_eof = DFA.unpackEncodedString(DFA77_eofS);
    static final char[] DFA77_min = DFA.unpackEncodedStringToUnsignedChars(DFA77_minS);
    static final char[] DFA77_max = DFA.unpackEncodedStringToUnsignedChars(DFA77_maxS);
    static final short[] DFA77_accept = DFA.unpackEncodedString(DFA77_acceptS);
    static final short[] DFA77_special = DFA.unpackEncodedString(DFA77_specialS);
    static final short[][] DFA77_transition;

    static {
        int numStates = DFA77_transitionS.length;
        DFA77_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA77_transition[i] = DFA.unpackEncodedString(DFA77_transitionS[i]);
        }
    }

    class DFA77 extends DFA {

        public DFA77(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 77;
            this.eot = DFA77_eot;
            this.eof = DFA77_eof;
            this.min = DFA77_min;
            this.max = DFA77_max;
            this.accept = DFA77_accept;
            this.special = DFA77_special;
            this.transition = DFA77_transition;
        }
        public String getDescription() {
            return "751:1: static_relation : (ir= inheritance_relation -> ^( STATIC_RELATION[$ir.start] inheritance_relation ) | cr= client_relation -> ^( STATIC_RELATION[$cr.start] client_relation ) );";
        }
    }
    static final String DFA128_eotS =
        "\6\uffff";
    static final String DFA128_eofS =
        "\6\uffff";
    static final String DFA128_minS =
        "\1\u00a6\1\u00c4\1\u00a6\2\uffff\1\u00c4";
    static final String DFA128_maxS =
        "\1\u00a6\1\u00f6\1\u00a6\2\uffff\1\u00f6";
    static final String DFA128_acceptS =
        "\3\uffff\1\2\1\1\1\uffff";
    static final String DFA128_specialS =
        "\6\uffff}>";
    static final String[] DFA128_transitionS = {
            "\1\1",
            "\1\3\1\2\60\uffff\1\4",
            "\1\5",
            "",
            "",
            "\1\3\1\2\60\uffff\1\4"
    };

    static final short[] DFA128_eot = DFA.unpackEncodedString(DFA128_eotS);
    static final short[] DFA128_eof = DFA.unpackEncodedString(DFA128_eofS);
    static final char[] DFA128_min = DFA.unpackEncodedStringToUnsignedChars(DFA128_minS);
    static final char[] DFA128_max = DFA.unpackEncodedStringToUnsignedChars(DFA128_maxS);
    static final short[] DFA128_accept = DFA.unpackEncodedString(DFA128_acceptS);
    static final short[] DFA128_special = DFA.unpackEncodedString(DFA128_specialS);
    static final short[][] DFA128_transition;

    static {
        int numStates = DFA128_transitionS.length;
        DFA128_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA128_transition[i] = DFA.unpackEncodedString(DFA128_transitionS[i]);
        }
    }

    class DFA128 extends DFA {

        public DFA128(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 128;
            this.eot = DFA128_eot;
            this.eof = DFA128_eof;
            this.min = DFA128_min;
            this.max = DFA128_max;
            this.accept = DFA128_accept;
            this.special = DFA128_special;
            this.transition = DFA128_transition;
        }
        public String getDescription() {
            return "1409:1: variable_range : ( member_range -> ^( VARIABLE_RANGE member_range ) | type_range -> ^( VARIABLE_RANGE type_range ) );";
        }
    }
 

    public static final BitSet FOLLOW_indexing_in_prog882 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x4400000000000000L,0x10000000004A10C0L,0x0000000000000038L});
    public static final BitSet FOLLOW_bon_specification_in_prog885 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_prog887 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indexing_in_prog936 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_prog941 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_specification_element_in_bon_specification1010 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x4400000000000000L,0x10000000004A10C0L,0x0000000000000038L});
    public static final BitSet FOLLOW_informal_chart_in_specification_element1045 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_dictionary_in_specification_element1075 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_diagram_in_specification_element1105 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_dynamic_diagram_in_specification_element1135 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_notational_tuning_in_specification_element1165 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_system_chart_in_informal_chart1205 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cluster_chart_in_informal_chart1228 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_chart_in_informal_chart1251 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_event_chart_in_informal_chart1274 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_scenario_chart_in_informal_chart1297 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_creation_chart_in_informal_chart1320 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_186_in_class_dictionary1353 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_system_name_in_class_dictionary1355 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x1000000000000000L});
    public static final BitSet FOLLOW_dictionary_entry_in_class_dictionary1380 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x1800000000000000L});
    public static final BitSet FOLLOW_187_in_class_dictionary1406 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_186_in_class_dictionary1570 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_system_name_in_class_dictionary1572 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L});
    public static final BitSet FOLLOW_187_in_class_dictionary1574 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_188_in_dictionary_entry1681 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_name_in_dictionary_entry1683 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x2000000000000000L});
    public static final BitSet FOLLOW_189_in_dictionary_entry1707 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_cluster_name_in_dictionary_entry1709 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
    public static final BitSet FOLLOW_description_in_dictionary_entry1733 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_190_in_system_chart1884 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_system_name_in_system_chart1886 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0xA800000000000000L,0x0000000000000003L});
    public static final BitSet FOLLOW_indexing_in_system_chart1926 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0xA800000000000000L,0x0000000000000002L});
    public static final BitSet FOLLOW_explanation_in_system_chart1948 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x2800000000000000L,0x0000000000000002L});
    public static final BitSet FOLLOW_part_in_system_chart1971 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x2800000000000000L});
    public static final BitSet FOLLOW_cluster_entries_in_system_chart1994 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L});
    public static final BitSet FOLLOW_187_in_system_chart2016 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_191_in_explanation2227 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_manifest_textblock_in_explanation2229 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_191_in_explanation2334 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_192_in_indexing2401 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_index_list_in_indexing2403 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_192_in_indexing2492 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_193_in_part2550 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_part2552 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_193_in_part2616 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_194_in_description2664 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_manifest_textblock_in_description2666 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cluster_entry_in_cluster_entries2763 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x2000000000000000L});
    public static final BitSet FOLLOW_189_in_cluster_entry2902 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_entry2904 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
    public static final BitSet FOLLOW_description_in_cluster_entry2906 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_system_name3050 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_index_clause_in_index_list3150 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000004000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_195_in_index_list3172 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_index_clause_in_index_list3174 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000004000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_index_clause_in_index_list3197 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000004000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_195_in_index_list3235 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_index_clause3342 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000010L});
    public static final BitSet FOLLOW_196_in_index_clause3344 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_index_term_list_in_index_clause3346 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_index_clause3461 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000010L});
    public static final BitSet FOLLOW_196_in_index_clause3463 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_index_string_in_index_term_list3548 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_197_in_index_term_list3551 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_index_string_in_index_term_list3553 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_index_string3691 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_198_in_cluster_chart3799 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_chart3801 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0xB800000000000000L,0x0000000000000003L});
    public static final BitSet FOLLOW_indexing_in_cluster_chart3843 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0xB800000000000000L,0x0000000000000002L});
    public static final BitSet FOLLOW_explanation_in_cluster_chart3867 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x3800000000000000L,0x0000000000000002L});
    public static final BitSet FOLLOW_part_in_cluster_chart3891 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x3800000000000000L});
    public static final BitSet FOLLOW_class_entries_in_cluster_chart3915 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x2800000000000000L});
    public static final BitSet FOLLOW_cluster_entries_in_cluster_chart3939 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L});
    public static final BitSet FOLLOW_187_in_cluster_chart3962 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_entry_in_class_entries4223 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x1000000000000000L});
    public static final BitSet FOLLOW_188_in_class_entry4350 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_name_in_class_entry4352 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
    public static final BitSet FOLLOW_description_in_class_entry4354 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_cluster_name4483 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_199_in_class_chart4588 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_name_in_class_chart4590 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8800000000000000L,0x0000000000000F03L});
    public static final BitSet FOLLOW_indexing_in_class_chart4628 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8800000000000000L,0x0000000000000F02L});
    public static final BitSet FOLLOW_explanation_in_class_chart4650 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L,0x0000000000000F02L});
    public static final BitSet FOLLOW_part_in_class_chart4672 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L,0x0000000000000F00L});
    public static final BitSet FOLLOW_inherits_in_class_chart4694 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L,0x0000000000000E00L});
    public static final BitSet FOLLOW_queries_in_class_chart4715 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L,0x0000000000000C00L});
    public static final BitSet FOLLOW_commands_in_class_chart4737 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L,0x0000000000000800L});
    public static final BitSet FOLLOW_constraints_in_class_chart4759 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L});
    public static final BitSet FOLLOW_187_in_class_chart4780 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_200_in_inherits5060 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_name_list_in_inherits5078 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_200_in_inherits5131 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_201_in_queries5188 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_query_list_in_queries5190 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_202_in_commands5230 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_command_list_in_commands5232 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_203_in_constraints5264 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_constraint_list_in_constraints5266 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_query_list5303 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000202000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_197_in_query_list5325 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_manifest_textblock_in_query_list5327 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000202000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_manifest_textblock_in_query_list5351 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000202000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_197_in_query_list5390 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_command_list5509 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000202000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_197_in_command_list5533 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_manifest_textblock_in_command_list5535 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000202000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_manifest_textblock_in_command_list5560 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000202000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_197_in_command_list5602 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_constraint_list5719 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000202000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_197_in_constraint_list5746 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_manifest_textblock_in_constraint_list5748 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000202000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_manifest_textblock_in_constraint_list5776 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000202000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_197_in_constraint_list5823 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_class_name_list5942 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000004000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_197_in_class_name_list5961 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_name_in_class_name_list5965 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000004000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_class_name_in_class_name_list5988 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000004000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_IDENTIFIER_in_class_name6203 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_204_in_event_chart6298 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_system_name_in_event_chart6300 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8800000000000000L,0x000000000000E003L});
    public static final BitSet FOLLOW_205_in_event_chart6320 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8800000000000000L,0x0000000000008003L});
    public static final BitSet FOLLOW_206_in_event_chart6324 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8800000000000000L,0x0000000000008003L});
    public static final BitSet FOLLOW_indexing_in_event_chart6345 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8800000000000000L,0x0000000000008002L});
    public static final BitSet FOLLOW_explanation_in_event_chart6366 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L,0x0000000000008002L});
    public static final BitSet FOLLOW_part_in_event_chart6387 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L,0x0000000000008000L});
    public static final BitSet FOLLOW_event_entries_in_event_chart6408 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L});
    public static final BitSet FOLLOW_187_in_event_chart6428 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_event_entry_in_event_entries6663 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000008000L});
    public static final BitSet FOLLOW_207_in_event_entry6829 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_manifest_textblock_in_event_entry6831 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000010000L});
    public static final BitSet FOLLOW_207_in_event_entry6858 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000010000L});
    public static final BitSet FOLLOW_208_in_event_entry6900 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_name_list_in_event_entry6902 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_208_in_event_entry6929 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_209_in_scenario_chart7166 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_system_name_in_scenario_chart7168 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8800000000000000L,0x0000000000040003L});
    public static final BitSet FOLLOW_indexing_in_scenario_chart7190 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8800000000000000L,0x0000000000040002L});
    public static final BitSet FOLLOW_explanation_in_scenario_chart7214 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L,0x0000000000040002L});
    public static final BitSet FOLLOW_part_in_scenario_chart7238 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L,0x0000000000040000L});
    public static final BitSet FOLLOW_scenario_entries_in_scenario_chart7262 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L});
    public static final BitSet FOLLOW_187_in_scenario_chart7285 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_scenario_entry_in_scenario_entries7526 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000040000L});
    public static final BitSet FOLLOW_210_in_scenario_entry7713 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_scenario_entry7715 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
    public static final BitSet FOLLOW_description_in_scenario_entry7717 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_211_in_creation_chart7854 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_system_name_in_creation_chart7856 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8800000000000000L,0x0000000000100003L});
    public static final BitSet FOLLOW_indexing_in_creation_chart7878 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x8800000000000000L,0x0000000000100002L});
    public static final BitSet FOLLOW_explanation_in_creation_chart7902 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L,0x0000000000100002L});
    public static final BitSet FOLLOW_part_in_creation_chart7926 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L,0x0000000000100000L});
    public static final BitSet FOLLOW_creation_entries_in_creation_chart7950 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L});
    public static final BitSet FOLLOW_187_in_creation_chart7973 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_creation_entry_in_creation_entries8215 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000100000L});
    public static final BitSet FOLLOW_212_in_creation_entry8379 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_name_in_creation_entry8381 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
    public static final BitSet FOLLOW_213_in_creation_entry8403 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_name_list_in_creation_entry8405 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_214_in_static_diagram8563 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x000001C000000000L,0x0000000000800000L});
    public static final BitSet FOLLOW_extended_id_in_static_diagram8566 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000008000000000L,0x0000000000800000L});
    public static final BitSet FOLLOW_COMMENT_in_static_diagram8571 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000800000L});
    public static final BitSet FOLLOW_215_in_static_diagram8595 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x3800004000000000L,0x000000000E000000L});
    public static final BitSet FOLLOW_static_block_in_static_diagram8618 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L});
    public static final BitSet FOLLOW_187_in_static_diagram8642 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_extended_id8841 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_INTEGER_in_extended_id8932 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_component_in_static_block9041 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x3000004000000000L,0x000000000E000000L});
    public static final BitSet FOLLOW_cluster_in_static_component9148 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_classX_in_static_component9269 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_relation_in_static_component9390 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_189_in_cluster9519 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_cluster_name_in_cluster9521 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000000001800000L});
    public static final BitSet FOLLOW_216_in_cluster9537 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000000000800000L});
    public static final BitSet FOLLOW_COMMENT_in_cluster9542 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000800000L});
    public static final BitSet FOLLOW_cluster_components_in_cluster9594 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_215_in_cluster_components9751 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x3800004000000000L,0x000000000E000000L});
    public static final BitSet FOLLOW_static_block_in_cluster_components9754 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L});
    public static final BitSet FOLLOW_187_in_cluster_components9758 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_217_in_classX9917 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x1000000000000000L});
    public static final BitSet FOLLOW_188_in_classX9921 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_name_in_classX9925 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000041031000101L});
    public static final BitSet FOLLOW_218_in_classX9951 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x1000000000000000L});
    public static final BitSet FOLLOW_188_in_classX9955 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_name_in_classX9959 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000041031000101L});
    public static final BitSet FOLLOW_219_in_classX9978 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x1000000000000000L});
    public static final BitSet FOLLOW_188_in_classX9982 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_name_in_classX9986 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000041031000101L});
    public static final BitSet FOLLOW_188_in_classX10005 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_name_in_classX10009 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000041031000101L});
    public static final BitSet FOLLOW_formal_generics_in_classX10068 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000040031000101L});
    public static final BitSet FOLLOW_216_in_classX10084 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000040030000101L});
    public static final BitSet FOLLOW_220_in_classX10101 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000040020000101L});
    public static final BitSet FOLLOW_221_in_classX10120 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000040000000101L});
    public static final BitSet FOLLOW_COMMENT_in_classX10125 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000040000000101L});
    public static final BitSet FOLLOW_class_interface_in_classX10141 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_inheritance_relation_in_static_relation10332 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_client_relation_in_static_relation10443 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_child_in_inheritance_relation10582 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000100L});
    public static final BitSet FOLLOW_200_in_inheritance_relation10584 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L,0x0000000040000000L});
    public static final BitSet FOLLOW_222_in_inheritance_relation10587 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_multiplicity_in_inheritance_relation10589 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000080000000L});
    public static final BitSet FOLLOW_223_in_inheritance_relation10591 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_parent_in_inheritance_relation10621 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_semantic_label_in_inheritance_relation10624 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_client_in_client_relation10852 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
    public static final BitSet FOLLOW_224_in_client_relation10854 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L,0x0000008040000010L});
    public static final BitSet FOLLOW_client_entities_in_client_relation10857 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L,0x0000008000000010L});
    public static final BitSet FOLLOW_type_mark_in_client_relation10862 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_supplier_in_client_relation10887 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_semantic_label_in_client_relation10890 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_222_in_client_entities11085 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000014000000000L,0x0002805A00000000L});
    public static final BitSet FOLLOW_client_entity_expression_in_client_entities11087 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000080000000L});
    public static final BitSet FOLLOW_223_in_client_entities11089 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_client_entity_list_in_client_entity_expression11243 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_multiplicity_in_client_entity_expression11399 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_client_entity_in_client_entity_list11587 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_197_in_client_entity_list11590 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L,0x0002805A00000000L});
    public static final BitSet FOLLOW_client_entity_in_client_entity_list11592 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_prefix_in_client_entity11754 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_infix_in_client_entity11861 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_supplier_indirection_in_client_entity11968 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_parent_indirection_in_client_entity12076 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indirection_feature_part_in_supplier_indirection12204 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000010L});
    public static final BitSet FOLLOW_196_in_supplier_indirection12206 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L,0x0000005000000000L});
    public static final BitSet FOLLOW_generic_indirection_in_supplier_indirection12210 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_name_in_indirection_feature_part12377 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indirection_feature_list_in_indirection_feature_part12530 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_225_in_indirection_feature_list12716 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L,0x0002800000000000L});
    public static final BitSet FOLLOW_feature_name_list_in_indirection_feature_list12718 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000400000000L});
    public static final BitSet FOLLOW_226_in_indirection_feature_list12720 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_227_in_parent_indirection12905 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L,0x0000005000000000L});
    public static final BitSet FOLLOW_generic_indirection_in_parent_indirection12907 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indirection_element_in_generic_indirection13089 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_named_indirection13242 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000001000000000L});
    public static final BitSet FOLLOW_228_in_named_indirection13244 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L,0x0000005000000000L});
    public static final BitSet FOLLOW_indirection_list_in_named_indirection13246 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_229_in_named_indirection13248 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_228_in_named_indirection13390 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L,0x0000005000000000L});
    public static final BitSet FOLLOW_indirection_list_in_named_indirection13392 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_229_in_named_indirection13394 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indirection_element_in_indirection_list13497 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_197_in_indirection_list13500 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L,0x0000005000000000L});
    public static final BitSet FOLLOW_indirection_element_in_indirection_list13502 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_230_in_indirection_element13644 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_named_indirection_in_indirection_element13775 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_indirection_element13907 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_196_in_type_mark14066 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_231_in_type_mark14144 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_shared_mark_in_type_mark14222 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_196_in_shared_mark14329 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000200000000L});
    public static final BitSet FOLLOW_225_in_shared_mark14331 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_multiplicity_in_shared_mark14333 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000400000000L});
    public static final BitSet FOLLOW_226_in_shared_mark14335 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_ref_in_child14431 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_ref_in_parent14502 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_ref_in_client14587 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_ref_in_supplier14664 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_component_name_in_static_ref14770 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cluster_prefix_in_static_ref14871 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_static_component_name_in_static_ref14873 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_prefix14979 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_232_in_cluster_prefix14981 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_prefix14984 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_232_in_cluster_prefix14986 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_IDENTIFIER_in_static_component_name15106 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_INTEGER_in_multiplicity15275 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_semantic_label15391 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_indexing_in_class_interface15504 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000040000000100L});
    public static final BitSet FOLLOW_parent_class_list_in_class_interface15529 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000040000000000L});
    public static final BitSet FOLLOW_features_in_class_interface15553 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L,0x0000020000000000L});
    public static final BitSet FOLLOW_class_invariant_in_class_interface15576 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L});
    public static final BitSet FOLLOW_187_in_class_interface15600 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_233_in_class_invariant15828 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F0C000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_assertion_in_class_invariant15830 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_200_in_parent_class_list15977 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_type_in_parent_class_list15981 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_195_in_parent_class_list15986 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_type_in_parent_class_list15990 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_195_in_parent_class_list15997 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_200_in_parent_class_list16145 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_clause_in_features16246 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000040000000000L});
    public static final BitSet FOLLOW_234_in_feature_clause16345 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x000000C000000000L,0x000288004C000000L});
    public static final BitSet FOLLOW_selective_export_in_feature_clause16389 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x000000C000000000L,0x000288000C000000L});
    public static final BitSet FOLLOW_COMMENT_in_feature_clause16414 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L,0x000288000C000000L});
    public static final BitSet FOLLOW_feature_specifications_in_feature_clause16438 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_specification_in_feature_specifications16655 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000004000000000L,0x000288000C000000L});
    public static final BitSet FOLLOW_218_in_feature_specification16864 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L,0x0002800000000000L});
    public static final BitSet FOLLOW_feature_name_list_in_feature_specification16869 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000308840000010L});
    public static final BitSet FOLLOW_219_in_feature_specification16907 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L,0x0002800000000000L});
    public static final BitSet FOLLOW_feature_name_list_in_feature_specification16911 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000308840000010L});
    public static final BitSet FOLLOW_235_in_feature_specification16947 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L,0x0002800000000000L});
    public static final BitSet FOLLOW_feature_name_list_in_feature_specification16951 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000308840000010L});
    public static final BitSet FOLLOW_feature_name_list_in_feature_specification16989 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000308840000010L});
    public static final BitSet FOLLOW_has_type_in_feature_specification17096 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000300840000000L});
    public static final BitSet FOLLOW_rename_clause_in_feature_specification17127 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000300800000000L});
    public static final BitSet FOLLOW_COMMENT_in_feature_specification17161 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000300800000000L});
    public static final BitSet FOLLOW_feature_arguments_in_feature_specification17192 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000300000000000L});
    public static final BitSet FOLLOW_contract_clause_in_feature_specification17223 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_type_mark_in_has_type17617 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_type_in_has_type17619 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_contracting_conditions_in_contract_clause17677 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L});
    public static final BitSet FOLLOW_187_in_contract_clause17679 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_precondition_in_contracting_conditions17796 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000200000000000L});
    public static final BitSet FOLLOW_postcondition_in_contracting_conditions17799 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_postcondition_in_contracting_conditions17806 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_236_in_precondition17991 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F0C000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_assertion_in_precondition17993 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_237_in_postcondition18106 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F0C000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_assertion_in_postcondition18108 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_222_in_selective_export18215 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_name_list_in_selective_export18263 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000080000000L});
    public static final BitSet FOLLOW_223_in_selective_export18313 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_name_in_feature_name_list18452 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_197_in_feature_name_list18480 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L,0x0002800000000000L});
    public static final BitSet FOLLOW_feature_name_in_feature_name_list18484 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_IDENTIFIER_in_feature_name18635 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_prefix_in_feature_name18728 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_infix_in_feature_name18821 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_222_in_rename_clause18934 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000400000000000L});
    public static final BitSet FOLLOW_renaming_in_rename_clause18936 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000080000000L});
    public static final BitSet FOLLOW_223_in_rename_clause18938 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_238_in_renaming19058 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_name_in_renaming19060 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_232_in_renaming19062 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L,0x0002800000000000L});
    public static final BitSet FOLLOW_feature_name_in_renaming19064 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_feature_argument_in_feature_arguments19171 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000800000000L});
    public static final BitSet FOLLOW_227_in_feature_argument19320 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_identifier_list_in_feature_argument19374 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000010L});
    public static final BitSet FOLLOW_196_in_feature_argument19376 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_type_in_feature_argument19380 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_type_in_feature_argument19415 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_identifier_list19621 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_197_in_identifier_list19624 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_IDENTIFIER_in_identifier_list19626 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_239_in_prefix19745 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0001000000000000L});
    public static final BitSet FOLLOW_240_in_prefix19747 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_prefix_operator_in_prefix19749 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0001000000000000L});
    public static final BitSet FOLLOW_240_in_prefix19751 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_241_in_infix19828 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0001000000000000L});
    public static final BitSet FOLLOW_240_in_infix19830 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000080000000000L,0x0040000800000010L,0x0000000000FFCFC0L});
    public static final BitSet FOLLOW_infix_operator_in_infix19832 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0001000000000000L});
    public static final BitSet FOLLOW_240_in_infix19834 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unary_in_prefix_operator19906 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_binary_in_infix_operator20020 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_228_in_formal_generics20132 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_formal_generic_list_in_formal_generics20134 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_229_in_formal_generics20136 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_formal_generic_in_formal_generic_list20266 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_197_in_formal_generic_list20269 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_formal_generic_in_formal_generic_list20271 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_formal_generic_name_in_formal_generic20435 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_formal_generic_name_in_formal_generic20512 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000800000000L});
    public static final BitSet FOLLOW_227_in_formal_generic20514 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_class_type_in_formal_generic20518 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_IDENTIFIER_in_formal_generic_name20649 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_class_type20808 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000001000000000L});
    public static final BitSet FOLLOW_actual_generics_in_class_type20811 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_228_in_actual_generics20921 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_type_list_in_actual_generics20923 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_229_in_actual_generics20925 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_type_in_type_list21056 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_197_in_type_list21059 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_type_in_type_list21061 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_IDENTIFIER_in_type21153 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000001000000000L});
    public static final BitSet FOLLOW_actual_generics_in_type21156 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_assertion_clause_in_assertion21220 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_195_in_assertion21223 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F0C000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_assertion_clause_in_assertion21225 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_195_in_assertion21229 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_boolean_expression_in_assertion_clause21329 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_expression_in_boolean_expression21455 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_quantifier_in_quantification21598 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_range_expression_in_quantification21620 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0030000000000000L});
    public static final BitSet FOLLOW_restriction_in_quantification21643 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0020000000000000L});
    public static final BitSet FOLLOW_proposition_in_quantification21667 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_242_in_quantifier21885 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_243_in_quantifier21971 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_variable_range_in_range_expression22074 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_195_in_range_expression22077 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_variable_range_in_range_expression22079 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_195_in_range_expression22083 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_244_in_restriction22227 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F0C000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_boolean_expression_in_restriction22229 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_245_in_proposition22339 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F0C000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_boolean_expression_in_proposition22341 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_member_range_in_variable_range22449 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_type_range_in_variable_range22552 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_identifier_list_in_member_range22677 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0040000000000000L});
    public static final BitSet FOLLOW_246_in_member_range22679 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F0C000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_expression_in_member_range22681 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_identifier_list_in_type_range22797 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000010L});
    public static final BitSet FOLLOW_196_in_type_range22799 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_type_in_type_range22801 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unqualified_call_in_call_chain22935 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_232_in_call_chain22938 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_unqualified_call_in_call_chain22940 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_IDENTIFIER_in_unqualified_call23047 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000200000000L});
    public static final BitSet FOLLOW_actual_arguments_in_unqualified_call23050 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_225_in_actual_arguments23194 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F0C000640000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_expression_list_in_actual_arguments23196 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000400000000L});
    public static final BitSet FOLLOW_226_in_actual_arguments23199 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_expression_in_expression_list23333 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_197_in_expression_list23336 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F0C000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_expression_in_expression_list23338 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_222_in_enumerated_set23542 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F0C000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_enumeration_list_in_enumerated_set23544 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000080000000L});
    public static final BitSet FOLLOW_223_in_enumerated_set23546 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_enumeration_element_in_enumeration_list23670 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_197_in_enumeration_list23673 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F0C000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_enumeration_element_in_enumeration_list23675 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_expression_in_enumeration_element23809 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_interval_in_enumeration_element23937 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_integer_interval_in_interval24092 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_character_interval_in_interval24165 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_integer_constant_in_integer_interval24255 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0080000000000000L});
    public static final BitSet FOLLOW_247_in_integer_interval24257 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000010000000000L,0x0000000000000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_integer_constant_in_integer_interval24259 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CHARACTER_CONSTANT_in_character_interval24398 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0080000000000000L});
    public static final BitSet FOLLOW_247_in_character_interval24400 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000020000000000L});
    public static final BitSet FOLLOW_CHARACTER_CONSTANT_in_character_interval24402 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_constant_in_constant24537 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_248_in_constant24613 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_249_in_constant24689 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_boolean_constant_in_manifest_constant24783 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CHARACTER_CONSTANT_in_manifest_constant24909 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_integer_constant_in_manifest_constant25035 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_real_constant_in_manifest_constant25161 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_manifest_constant25287 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_enumerated_set_in_manifest_constant25413 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_in_sign25560 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_250_in_boolean_constant25624 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_251_in_boolean_constant25737 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_integer_constant25917 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_INTEGER_in_integer_constant25923 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_sign_in_real_constant26088 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000040000000000L});
    public static final BitSet FOLLOW_REAL_in_real_constant26094 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_252_in_dynamic_diagram26225 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x000001C000000000L,0x0000000000800000L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_diagram26228 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000008000000000L,0x0000000000800000L});
    public static final BitSet FOLLOW_COMMENT_in_dynamic_diagram26233 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000800000L});
    public static final BitSet FOLLOW_215_in_dynamic_diagram26257 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800014000000000L,0xC000000000040000L,0x0000000000000003L});
    public static final BitSet FOLLOW_dynamic_block_in_dynamic_diagram26260 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L});
    public static final BitSet FOLLOW_187_in_dynamic_diagram26264 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_dynamic_component_in_dynamic_block26448 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000014000000000L,0xC000000000040000L,0x0000000000000003L});
    public static final BitSet FOLLOW_scenario_description_in_dynamic_component26591 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_object_group_in_dynamic_component26714 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_object_stack_in_dynamic_component26838 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_object_in_dynamic_component26961 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_message_relation_in_dynamic_component27084 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_210_in_scenario_description27217 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_scenario_name_in_scenario_description27219 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000008000000000L,0x2000000000000000L});
    public static final BitSet FOLLOW_COMMENT_in_scenario_description27222 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x2000000000000000L});
    public static final BitSet FOLLOW_253_in_scenario_description27251 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_labelled_actions_in_scenario_description27253 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L});
    public static final BitSet FOLLOW_187_in_scenario_description27255 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_labelled_action_in_labelled_actions27475 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_action_label_in_labelled_action27617 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_action_description_in_labelled_action27619 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_action_label27752 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_action_description27865 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_manifest_textblock_in_scenario_name28014 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_254_in_object_group28122 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x8000000000000000L});
    public static final BitSet FOLLOW_255_in_object_group28126 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000014000000000L});
    public static final BitSet FOLLOW_group_name_in_object_group28128 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L,0x0000000000800000L});
    public static final BitSet FOLLOW_COMMENT_in_object_group28131 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000800000L});
    public static final BitSet FOLLOW_group_components_in_object_group28154 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_215_in_group_components28285 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000014000000000L,0xC000000000040000L,0x0000000000000003L});
    public static final BitSet FOLLOW_dynamic_block_in_group_components28287 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0800000000000000L});
    public static final BitSet FOLLOW_187_in_group_components28289 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_256_in_object_stack28426 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_object_name_in_object_stack28428 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L});
    public static final BitSet FOLLOW_COMMENT_in_object_stack28431 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_257_in_object28550 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_object_name_in_object28552 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000008000000000L});
    public static final BitSet FOLLOW_COMMENT_in_object28555 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_caller_in_message_relation28634 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000004L});
    public static final BitSet FOLLOW_258_in_message_relation28636 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000014000000000L});
    public static final BitSet FOLLOW_receiver_in_message_relation28638 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_message_label_in_message_relation28641 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_dynamic_ref_in_caller28787 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_dynamic_ref_in_receiver28864 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_ref28957 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_232_in_dynamic_ref28960 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000014000000000L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_ref28962 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_IDENTIFIER_in_dynamic_component_name29074 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_232_in_dynamic_component_name29077 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000014000000000L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_component_name29079 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_INTEGER_in_dynamic_component_name29230 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_name_in_object_name29378 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_232_in_object_name29381 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000014000000000L});
    public static final BitSet FOLLOW_extended_id_in_object_name29383 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_extended_id_in_group_name29497 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_message_label29598 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_change_string_marks_in_notational_tuning29705 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_change_concatenator_in_notational_tuning29823 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_change_prefix_in_notational_tuning29940 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_259_in_change_string_marks30064 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_string_marks30066 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_string_marks30068 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_260_in_change_concatenator30225 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_concatenator30227 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_261_in_change_prefix30382 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_prefix30384 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_equivalence_expression_in_expression30497 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_quantification_in_expression30584 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_implies_expression_in_equivalence_expression30674 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000040L});
    public static final BitSet FOLLOW_262_in_equivalence_expression30677 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F00000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_implies_expression_in_equivalence_expression30680 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000040L});
    public static final BitSet FOLLOW_and_or_xor_expression_in_implies_expression30719 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000800000000L});
    public static final BitSet FOLLOW_227_in_implies_expression30722 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F00000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_implies_expression_in_implies_expression30725 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_comparison_expression_in_and_or_xor_expression30758 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000E00L});
    public static final BitSet FOLLOW_and_or_xor_op_in_and_or_xor_expression30761 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F00000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_comparison_expression_in_and_or_xor_expression30764 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000E00L});
    public static final BitSet FOLLOW_add_sub_expression_in_comparison_expression30801 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0040000000000010L,0x00000000001FC000L});
    public static final BitSet FOLLOW_comparison_op_in_comparison_expression30804 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F00000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_add_sub_expression_in_comparison_expression30808 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0040000000000010L,0x00000000001FC000L});
    public static final BitSet FOLLOW_mul_div_expression_in_add_sub_expression30845 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_add_sub_op_in_add_sub_expression30848 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F00000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_mul_div_expression_in_add_sub_expression30851 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000180L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mul_div_expression30885 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000E00000L});
    public static final BitSet FOLLOW_mul_div_op_in_mul_div_expression30888 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F00000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mul_div_expression30891 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000E00000L});
    public static final BitSet FOLLOW_lowest_expression_in_mod_pow_expression30926 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000080000000000L});
    public static final BitSet FOLLOW_MOD_POW_OP_in_mod_pow_expression30929 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F00000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mod_pow_expression30932 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constant_in_lowest_expression30971 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unary_in_lowest_expression30985 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F00000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_lowest_expression_in_lowest_expression30987 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_225_in_lowest_expression31006 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000076000000000L,0x0F0C000240000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_expression_in_lowest_expression31008 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000400000000L});
    public static final BitSet FOLLOW_226_in_lowest_expression31010 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_232_in_lowest_expression31013 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_call_chain_in_lowest_expression31015 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_call_chain_in_lowest_expression31036 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_manifest_textblock31347 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_START_in_manifest_textblock31363 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000C00000000000L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_MIDDLE_in_manifest_textblock31365 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000C00000000000L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_END_in_manifest_textblock31368 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_set_in_add_sub_op0 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_set_in_and_or_xor_op0 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_other_unary_in_unary31723 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_in_unary31738 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_delta_in_other_unary31758 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_old_in_other_unary31776 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_not_in_other_unary31795 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_268_in_delta31830 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_269_in_old31845 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_270_in_not31862 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_in_binary31893 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_mul_div_op_in_binary31897 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_comparison_op_in_binary31901 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MOD_POW_OP_in_binary31916 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_and_or_xor_op_in_binary31920 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_227_in_binary31935 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_262_in_binary31939 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_271_in_comparison_op31952 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_272_in_comparison_op31974 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_273_in_comparison_op31996 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_274_in_comparison_op32018 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_275_in_comparison_op32040 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_276_in_comparison_op32062 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_246_in_comparison_op32084 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_270_in_comparison_op32106 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0040000000000000L});
    public static final BitSet FOLLOW_246_in_comparison_op32108 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_196_in_comparison_op32171 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_set_in_mul_div_op0 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constant_in_synpred130967 = new BitSet(new long[]{0x0000000000000002L});

}