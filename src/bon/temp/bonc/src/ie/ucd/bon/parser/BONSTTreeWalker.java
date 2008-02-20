// $ANTLR 3.0.1 BONSTTreeWalker.g 2008-02-20 14:22:03

  package ie.ucd.bon.parser; 
  
  import java.util.LinkedList;


import org.antlr.runtime.*;
import org.antlr.runtime.tree.*;import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

import org.antlr.stringtemplate.*;
import org.antlr.stringtemplate.language.*;
import java.util.HashMap;
/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
public class BONSTTreeWalker extends AbstractBONSTWalker {
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

        public BONSTTreeWalker(TreeNodeStream input) {
            super(input);
        }
        
    protected StringTemplateGroup templateLib =
      new StringTemplateGroup("BONSTTreeWalkerTemplates", AngleBracketTemplateLexer.class);

    public void setTemplateLib(StringTemplateGroup templateLib) {
      this.templateLib = templateLib;
    }
    public StringTemplateGroup getTemplateLib() {
      return templateLib;
    }
    /** allows convenient multi-value initialization:
     *  "new STAttrMap().put(...).put(...)"
     */
    public static class STAttrMap extends HashMap {
      public STAttrMap put(String attrName, Object value) {
        super.put(attrName, value);
        return this;
      }
      public STAttrMap put(String attrName, int value) {
        super.put(attrName, new Integer(value));
        return this;
      }
    }

    public String[] getTokenNames() { return tokenNames; }
    public String getGrammarFileName() { return "BONSTTreeWalker.g"; }


    public static class prog_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start prog
    // BONSTTreeWalker.g:21:1: prog : ( ^( PROG bon_specification ) -> prog(p=$bon_specification.st) | ^( PROG indexing bon_specification ) -> prog(p=$bon_specification.sti=$indexing.st) | ^( PROG PARSE_ERROR ) );
    public final prog_return prog() throws RecognitionException {
        prog_return retval = new prog_return();
        retval.start = input.LT(1);

        bon_specification_return bon_specification1 = null;

        bon_specification_return bon_specification2 = null;

        indexing_return indexing3 = null;


        try {
            // BONSTTreeWalker.g:27:7: ( ^( PROG bon_specification ) -> prog(p=$bon_specification.st) | ^( PROG indexing bon_specification ) -> prog(p=$bon_specification.sti=$indexing.st) | ^( PROG PARSE_ERROR ) )
            int alt1=3;
            int LA1_0 = input.LA(1);

            if ( (LA1_0==PROG) ) {
                int LA1_1 = input.LA(2);

                if ( (LA1_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case PARSE_ERROR:
                        {
                        alt1=3;
                        }
                        break;
                    case CLASS_CHART:
                    case CLASS_DICTIONARY:
                    case SYSTEM_CHART:
                    case CLUSTER_CHART:
                    case EVENT_CHART:
                    case SCENARIO_CHART:
                    case CREATION_CHART:
                    case STATIC_DIAGRAM:
                    case DYNAMIC_DIAGRAM:
                    case NOTATIONAL_TUNING:
                        {
                        alt1=1;
                        }
                        break;
                    case INDEXING:
                        {
                        alt1=2;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("21:1: prog : ( ^( PROG bon_specification ) -> prog(p=$bon_specification.st) | ^( PROG indexing bon_specification ) -> prog(p=$bon_specification.sti=$indexing.st) | ^( PROG PARSE_ERROR ) );", 1, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("21:1: prog : ( ^( PROG bon_specification ) -> prog(p=$bon_specification.st) | ^( PROG indexing bon_specification ) -> prog(p=$bon_specification.sti=$indexing.st) | ^( PROG PARSE_ERROR ) );", 1, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("21:1: prog : ( ^( PROG bon_specification ) -> prog(p=$bon_specification.st) | ^( PROG indexing bon_specification ) -> prog(p=$bon_specification.sti=$indexing.st) | ^( PROG PARSE_ERROR ) );", 1, 0, input);

                throw nvae;
            }
            switch (alt1) {
                case 1 :
                    // BONSTTreeWalker.g:27:10: ^( PROG bon_specification )
                    {
                    match(input,PROG,FOLLOW_PROG_in_prog63); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_bon_specification_in_prog65);
                    bon_specification1=bon_specification();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 27:38: -> prog(p=$bon_specification.st)
                    {
                        retval.st = templateLib.getInstanceOf("prog",
                      new STAttrMap().put("p", bon_specification1.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:29:10: ^( PROG indexing bon_specification )
                    {
                    match(input,PROG,FOLLOW_PROG_in_prog99); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_indexing_in_prog101);
                    indexing3=indexing();
                    _fsp--;

                    pushFollow(FOLLOW_bon_specification_in_prog103);
                    bon_specification2=bon_specification();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 29:47: -> prog(p=$bon_specification.sti=$indexing.st)
                    {
                        retval.st = templateLib.getInstanceOf("prog",
                      new STAttrMap().put("p", bon_specification2.st).put("i", indexing3.st));
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:31:10: ^( PROG PARSE_ERROR )
                    {
                    match(input,PROG,FOLLOW_PROG_in_prog141); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_prog143); 

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
    // $ANTLR end prog

    public static class bon_specification_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start bon_specification
    // BONSTTreeWalker.g:34:1: bon_specification : (b+= specification_element )+ -> bonSpecification(bs=$b);
    public final bon_specification_return bon_specification() throws RecognitionException {
        bon_specification_return retval = new bon_specification_return();
        retval.start = input.LT(1);

        List list_b=null;
        RuleReturnScope b = null;
        try {
            // BONSTTreeWalker.g:38:20: ( (b+= specification_element )+ -> bonSpecification(bs=$b))
            // BONSTTreeWalker.g:38:23: (b+= specification_element )+
            {
            // BONSTTreeWalker.g:38:23: (b+= specification_element )+
            int cnt2=0;
            loop2:
            do {
                int alt2=2;
                int LA2_0 = input.LA(1);

                if ( ((LA2_0>=CLASS_CHART && LA2_0<=CLASS_DICTIONARY)||LA2_0==SYSTEM_CHART||LA2_0==CLUSTER_CHART||LA2_0==EVENT_CHART||LA2_0==SCENARIO_CHART||LA2_0==CREATION_CHART||LA2_0==STATIC_DIAGRAM||LA2_0==DYNAMIC_DIAGRAM||LA2_0==NOTATIONAL_TUNING) ) {
                    alt2=1;
                }


                switch (alt2) {
            	case 1 :
            	    // BONSTTreeWalker.g:38:24: b+= specification_element
            	    {
            	    pushFollow(FOLLOW_specification_element_in_bon_specification168);
            	    b=specification_element();
            	    _fsp--;

            	    if (list_b==null) list_b=new ArrayList();
            	    list_b.add(b.getTemplate());


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


            // TEMPLATE REWRITE
            // 38:52: -> bonSpecification(bs=$b)
            {
                retval.st = templateLib.getInstanceOf("bonSpecification",
              new STAttrMap().put("bs", list_b));
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
    // $ANTLR end bon_specification

    public static class specification_element_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start specification_element
    // BONSTTreeWalker.g:41:1: specification_element : ( informal_chart -> specificationElement(s=$informal_chart.st) | class_dictionary -> specificationElement(s=$class_dictionary.st) | static_diagram -> specificationElement(s=$static_diagram.st) | dynamic_diagram -> specificationElement(s=$dynamic_diagram.st) | notational_tuning -> specificationElement(s=$notational_tuning.st));
    public final specification_element_return specification_element() throws RecognitionException {
        specification_element_return retval = new specification_element_return();
        retval.start = input.LT(1);

        informal_chart_return informal_chart4 = null;

        class_dictionary_return class_dictionary5 = null;

        static_diagram_return static_diagram6 = null;

        dynamic_diagram_return dynamic_diagram7 = null;

        notational_tuning_return notational_tuning8 = null;


        try {
            // BONSTTreeWalker.g:41:24: ( informal_chart -> specificationElement(s=$informal_chart.st) | class_dictionary -> specificationElement(s=$class_dictionary.st) | static_diagram -> specificationElement(s=$static_diagram.st) | dynamic_diagram -> specificationElement(s=$dynamic_diagram.st) | notational_tuning -> specificationElement(s=$notational_tuning.st))
            int alt3=5;
            switch ( input.LA(1) ) {
            case CLASS_CHART:
            case SYSTEM_CHART:
            case CLUSTER_CHART:
            case EVENT_CHART:
            case SCENARIO_CHART:
            case CREATION_CHART:
                {
                alt3=1;
                }
                break;
            case CLASS_DICTIONARY:
                {
                alt3=2;
                }
                break;
            case STATIC_DIAGRAM:
                {
                alt3=3;
                }
                break;
            case DYNAMIC_DIAGRAM:
                {
                alt3=4;
                }
                break;
            case NOTATIONAL_TUNING:
                {
                alt3=5;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("41:1: specification_element : ( informal_chart -> specificationElement(s=$informal_chart.st) | class_dictionary -> specificationElement(s=$class_dictionary.st) | static_diagram -> specificationElement(s=$static_diagram.st) | dynamic_diagram -> specificationElement(s=$dynamic_diagram.st) | notational_tuning -> specificationElement(s=$notational_tuning.st));", 3, 0, input);

                throw nvae;
            }

            switch (alt3) {
                case 1 :
                    // BONSTTreeWalker.g:41:29: informal_chart
                    {
                    pushFollow(FOLLOW_informal_chart_in_specification_element215);
                    informal_chart4=informal_chart();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 41:48: -> specificationElement(s=$informal_chart.st)
                    {
                        retval.st = templateLib.getInstanceOf("specificationElement",
                      new STAttrMap().put("s", informal_chart4.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:42:29: class_dictionary
                    {
                    pushFollow(FOLLOW_class_dictionary_in_specification_element258);
                    class_dictionary5=class_dictionary();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 42:48: -> specificationElement(s=$class_dictionary.st)
                    {
                        retval.st = templateLib.getInstanceOf("specificationElement",
                      new STAttrMap().put("s", class_dictionary5.st));
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:43:29: static_diagram
                    {
                    pushFollow(FOLLOW_static_diagram_in_specification_element299);
                    static_diagram6=static_diagram();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 43:48: -> specificationElement(s=$static_diagram.st)
                    {
                        retval.st = templateLib.getInstanceOf("specificationElement",
                      new STAttrMap().put("s", static_diagram6.st));
                    }



                    }
                    break;
                case 4 :
                    // BONSTTreeWalker.g:44:29: dynamic_diagram
                    {
                    pushFollow(FOLLOW_dynamic_diagram_in_specification_element342);
                    dynamic_diagram7=dynamic_diagram();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 44:48: -> specificationElement(s=$dynamic_diagram.st)
                    {
                        retval.st = templateLib.getInstanceOf("specificationElement",
                      new STAttrMap().put("s", dynamic_diagram7.st));
                    }



                    }
                    break;
                case 5 :
                    // BONSTTreeWalker.g:45:29: notational_tuning
                    {
                    pushFollow(FOLLOW_notational_tuning_in_specification_element384);
                    notational_tuning8=notational_tuning();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 45:48: -> specificationElement(s=$notational_tuning.st)
                    {
                        retval.st = templateLib.getInstanceOf("specificationElement",
                      new STAttrMap().put("s", notational_tuning8.st));
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
        return retval;
    }
    // $ANTLR end specification_element

    public static class informal_chart_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start informal_chart
    // BONSTTreeWalker.g:48:1: informal_chart : ( system_chart -> informalChart(i=$system_chart.st) | cluster_chart -> informalChart(i=$cluster_chart.st) | class_chart -> informalChart(i=$class_chart.st) | event_chart -> informalChart(i=$event_chart.st) | scenario_chart -> informalChart(i=$scenario_chart.st) | creation_chart -> informalChart(i=$creation_chart.st));
    public final informal_chart_return informal_chart() throws RecognitionException {
        informal_chart_return retval = new informal_chart_return();
        retval.start = input.LT(1);

        system_chart_return system_chart9 = null;

        cluster_chart_return cluster_chart10 = null;

        class_chart_return class_chart11 = null;

        event_chart_return event_chart12 = null;

        scenario_chart_return scenario_chart13 = null;

        creation_chart_return creation_chart14 = null;


        try {
            // BONSTTreeWalker.g:52:17: ( system_chart -> informalChart(i=$system_chart.st) | cluster_chart -> informalChart(i=$cluster_chart.st) | class_chart -> informalChart(i=$class_chart.st) | event_chart -> informalChart(i=$event_chart.st) | scenario_chart -> informalChart(i=$scenario_chart.st) | creation_chart -> informalChart(i=$creation_chart.st))
            int alt4=6;
            switch ( input.LA(1) ) {
            case SYSTEM_CHART:
                {
                alt4=1;
                }
                break;
            case CLUSTER_CHART:
                {
                alt4=2;
                }
                break;
            case CLASS_CHART:
                {
                alt4=3;
                }
                break;
            case EVENT_CHART:
                {
                alt4=4;
                }
                break;
            case SCENARIO_CHART:
                {
                alt4=5;
                }
                break;
            case CREATION_CHART:
                {
                alt4=6;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("48:1: informal_chart : ( system_chart -> informalChart(i=$system_chart.st) | cluster_chart -> informalChart(i=$cluster_chart.st) | class_chart -> informalChart(i=$class_chart.st) | event_chart -> informalChart(i=$event_chart.st) | scenario_chart -> informalChart(i=$scenario_chart.st) | creation_chart -> informalChart(i=$creation_chart.st));", 4, 0, input);

                throw nvae;
            }

            switch (alt4) {
                case 1 :
                    // BONSTTreeWalker.g:52:22: system_chart
                    {
                    pushFollow(FOLLOW_system_chart_in_informal_chart433);
                    system_chart9=system_chart();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 52:38: -> informalChart(i=$system_chart.st)
                    {
                        retval.st = templateLib.getInstanceOf("informalChart",
                      new STAttrMap().put("i", system_chart9.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:53:22: cluster_chart
                    {
                    pushFollow(FOLLOW_cluster_chart_in_informal_chart468);
                    cluster_chart10=cluster_chart();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 53:38: -> informalChart(i=$cluster_chart.st)
                    {
                        retval.st = templateLib.getInstanceOf("informalChart",
                      new STAttrMap().put("i", cluster_chart10.st));
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:54:22: class_chart
                    {
                    pushFollow(FOLLOW_class_chart_in_informal_chart502);
                    class_chart11=class_chart();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 54:38: -> informalChart(i=$class_chart.st)
                    {
                        retval.st = templateLib.getInstanceOf("informalChart",
                      new STAttrMap().put("i", class_chart11.st));
                    }



                    }
                    break;
                case 4 :
                    // BONSTTreeWalker.g:55:22: event_chart
                    {
                    pushFollow(FOLLOW_event_chart_in_informal_chart538);
                    event_chart12=event_chart();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 55:38: -> informalChart(i=$event_chart.st)
                    {
                        retval.st = templateLib.getInstanceOf("informalChart",
                      new STAttrMap().put("i", event_chart12.st));
                    }



                    }
                    break;
                case 5 :
                    // BONSTTreeWalker.g:56:22: scenario_chart
                    {
                    pushFollow(FOLLOW_scenario_chart_in_informal_chart574);
                    scenario_chart13=scenario_chart();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 56:38: -> informalChart(i=$scenario_chart.st)
                    {
                        retval.st = templateLib.getInstanceOf("informalChart",
                      new STAttrMap().put("i", scenario_chart13.st));
                    }



                    }
                    break;
                case 6 :
                    // BONSTTreeWalker.g:57:22: creation_chart
                    {
                    pushFollow(FOLLOW_creation_chart_in_informal_chart607);
                    creation_chart14=creation_chart();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 57:38: -> informalChart(i=$creation_chart.st)
                    {
                        retval.st = templateLib.getInstanceOf("informalChart",
                      new STAttrMap().put("i", creation_chart14.st));
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
        return retval;
    }
    // $ANTLR end informal_chart

    public static class class_dictionary_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start class_dictionary
    // BONSTTreeWalker.g:60:1: class_dictionary : ( ^( CLASS_DICTIONARY system_name (ds+= dictionary_entry )+ ) -> classDictionary(name=$system_name.stdicEntries=$ds) | ^( CLASS_DICTIONARY PARSE_ERROR ) );
    public final class_dictionary_return class_dictionary() throws RecognitionException {
        class_dictionary_return retval = new class_dictionary_return();
        retval.start = input.LT(1);

        List list_ds=null;
        system_name_return system_name15 = null;

        RuleReturnScope ds = null;
        try {
            // BONSTTreeWalker.g:60:19: ( ^( CLASS_DICTIONARY system_name (ds+= dictionary_entry )+ ) -> classDictionary(name=$system_name.stdicEntries=$ds) | ^( CLASS_DICTIONARY PARSE_ERROR ) )
            int alt6=2;
            int LA6_0 = input.LA(1);

            if ( (LA6_0==CLASS_DICTIONARY) ) {
                int LA6_1 = input.LA(2);

                if ( (LA6_1==DOWN) ) {
                    int LA6_2 = input.LA(3);

                    if ( (LA6_2==PARSE_ERROR) ) {
                        alt6=2;
                    }
                    else if ( (LA6_2==SYSTEM_NAME) ) {
                        alt6=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("60:1: class_dictionary : ( ^( CLASS_DICTIONARY system_name (ds+= dictionary_entry )+ ) -> classDictionary(name=$system_name.stdicEntries=$ds) | ^( CLASS_DICTIONARY PARSE_ERROR ) );", 6, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("60:1: class_dictionary : ( ^( CLASS_DICTIONARY system_name (ds+= dictionary_entry )+ ) -> classDictionary(name=$system_name.stdicEntries=$ds) | ^( CLASS_DICTIONARY PARSE_ERROR ) );", 6, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("60:1: class_dictionary : ( ^( CLASS_DICTIONARY system_name (ds+= dictionary_entry )+ ) -> classDictionary(name=$system_name.stdicEntries=$ds) | ^( CLASS_DICTIONARY PARSE_ERROR ) );", 6, 0, input);

                throw nvae;
            }
            switch (alt6) {
                case 1 :
                    // BONSTTreeWalker.g:60:20: ^( CLASS_DICTIONARY system_name (ds+= dictionary_entry )+ )
                    {
                    match(input,CLASS_DICTIONARY,FOLLOW_CLASS_DICTIONARY_in_class_dictionary668); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_system_name_in_class_dictionary670);
                    system_name15=system_name();
                    _fsp--;

                    // BONSTTreeWalker.g:62:22: (ds+= dictionary_entry )+
                    int cnt5=0;
                    loop5:
                    do {
                        int alt5=2;
                        int LA5_0 = input.LA(1);

                        if ( (LA5_0==DICTIONARY_ENTRY) ) {
                            alt5=1;
                        }


                        switch (alt5) {
                    	case 1 :
                    	    // BONSTTreeWalker.g:62:23: ds+= dictionary_entry
                    	    {
                    	    pushFollow(FOLLOW_dictionary_entry_in_class_dictionary699);
                    	    ds=dictionary_entry();
                    	    _fsp--;

                    	    if (list_ds==null) list_ds=new ArrayList();
                    	    list_ds.add(ds.getTemplate());


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


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 64:20: -> classDictionary(name=$system_name.stdicEntries=$ds)
                    {
                        retval.st = templateLib.getInstanceOf("classDictionary",
                      new STAttrMap().put("name", system_name15.st).put("dicEntries", list_ds));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:67:20: ^( CLASS_DICTIONARY PARSE_ERROR )
                    {
                    match(input,CLASS_DICTIONARY,FOLLOW_CLASS_DICTIONARY_in_class_dictionary822); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_class_dictionary824); 

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
    // $ANTLR end class_dictionary

    public static class dictionary_entry_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start dictionary_entry
    // BONSTTreeWalker.g:70:1: dictionary_entry : ^( DICTIONARY_ENTRY class_name cluster_name description ) -> dictionaryEntry(name=$class_name.stclusterName=$cluster_name.stdesc=$description.st);
    public final dictionary_entry_return dictionary_entry() throws RecognitionException {
        dictionary_entry_return retval = new dictionary_entry_return();
        retval.start = input.LT(1);

        class_name_return class_name16 = null;

        cluster_name_return cluster_name17 = null;

        description_return description18 = null;


        try {
            // BONSTTreeWalker.g:70:19: ( ^( DICTIONARY_ENTRY class_name cluster_name description ) -> dictionaryEntry(name=$class_name.stclusterName=$cluster_name.stdesc=$description.st))
            // BONSTTreeWalker.g:70:20: ^( DICTIONARY_ENTRY class_name cluster_name description )
            {
            match(input,DICTIONARY_ENTRY,FOLLOW_DICTIONARY_ENTRY_in_dictionary_entry879); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_class_name_in_dictionary_entry881);
            class_name16=class_name();
            _fsp--;

            pushFollow(FOLLOW_cluster_name_in_dictionary_entry904);
            cluster_name17=cluster_name();
            _fsp--;

            pushFollow(FOLLOW_description_in_dictionary_entry906);
            description18=description();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 74:20: -> dictionaryEntry(name=$class_name.stclusterName=$cluster_name.stdesc=$description.st)
            {
                retval.st = templateLib.getInstanceOf("dictionaryEntry",
              new STAttrMap().put("name", class_name16.st).put("clusterName", cluster_name17.st).put("desc", description18.st));
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
    // $ANTLR end dictionary_entry

    public static class system_chart_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start system_chart
    // BONSTTreeWalker.g:78:1: system_chart : ^( SYSTEM_CHART system_name (o+= indexing )? (o+= explanation )? (o+= part )? (o+= cluster_entries )? ) -> systemChart(name=$system_name.stother=$o);
    public final system_chart_return system_chart() throws RecognitionException {
        system_chart_return retval = new system_chart_return();
        retval.start = input.LT(1);

        List list_o=null;
        system_name_return system_name19 = null;

        RuleReturnScope o = null;
        try {
            // BONSTTreeWalker.g:80:15: ( ^( SYSTEM_CHART system_name (o+= indexing )? (o+= explanation )? (o+= part )? (o+= cluster_entries )? ) -> systemChart(name=$system_name.stother=$o))
            // BONSTTreeWalker.g:80:16: ^( SYSTEM_CHART system_name (o+= indexing )? (o+= explanation )? (o+= part )? (o+= cluster_entries )? )
            {
            match(input,SYSTEM_CHART,FOLLOW_SYSTEM_CHART_in_system_chart1035); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_system_name_in_system_chart1037);
            system_name19=system_name();
            _fsp--;

            // BONSTTreeWalker.g:82:18: (o+= indexing )?
            int alt7=2;
            int LA7_0 = input.LA(1);

            if ( (LA7_0==INDEXING) ) {
                alt7=1;
            }
            switch (alt7) {
                case 1 :
                    // BONSTTreeWalker.g:82:19: o+= indexing
                    {
                    pushFollow(FOLLOW_indexing_in_system_chart1059);
                    o=indexing();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:83:18: (o+= explanation )?
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( (LA8_0==EXPLANATION) ) {
                alt8=1;
            }
            switch (alt8) {
                case 1 :
                    // BONSTTreeWalker.g:83:19: o+= explanation
                    {
                    pushFollow(FOLLOW_explanation_in_system_chart1083);
                    o=explanation();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:84:18: (o+= part )?
            int alt9=2;
            int LA9_0 = input.LA(1);

            if ( (LA9_0==PART) ) {
                alt9=1;
            }
            switch (alt9) {
                case 1 :
                    // BONSTTreeWalker.g:84:19: o+= part
                    {
                    pushFollow(FOLLOW_part_in_system_chart1108);
                    o=part();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:85:18: (o+= cluster_entries )?
            int alt10=2;
            int LA10_0 = input.LA(1);

            if ( (LA10_0==CLUSTER_ENTRIES) ) {
                alt10=1;
            }
            switch (alt10) {
                case 1 :
                    // BONSTTreeWalker.g:85:19: o+= cluster_entries
                    {
                    pushFollow(FOLLOW_cluster_entries_in_system_chart1133);
                    o=cluster_entries();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 87:16: -> systemChart(name=$system_name.stother=$o)
            {
                retval.st = templateLib.getInstanceOf("systemChart",
              new STAttrMap().put("name", system_name19.st).put("other", list_o));
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
    // $ANTLR end system_chart

    public static class explanation_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start explanation
    // BONSTTreeWalker.g:91:1: explanation : ( ^( EXPLANATION manifest_textblock ) -> explanation(s=$manifest_textblock.st) | ^( EXPLANATION PARSE_ERROR ) );
    public final explanation_return explanation() throws RecognitionException {
        explanation_return retval = new explanation_return();
        retval.start = input.LT(1);

        manifest_textblock_return manifest_textblock20 = null;


        try {
            // BONSTTreeWalker.g:91:14: ( ^( EXPLANATION manifest_textblock ) -> explanation(s=$manifest_textblock.st) | ^( EXPLANATION PARSE_ERROR ) )
            int alt11=2;
            int LA11_0 = input.LA(1);

            if ( (LA11_0==EXPLANATION) ) {
                int LA11_1 = input.LA(2);

                if ( (LA11_1==DOWN) ) {
                    int LA11_2 = input.LA(3);

                    if ( (LA11_2==PARSE_ERROR) ) {
                        alt11=2;
                    }
                    else if ( (LA11_2==MANIFEST_STRING||LA11_2==MANIFEST_TEXTBLOCK_START) ) {
                        alt11=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("91:1: explanation : ( ^( EXPLANATION manifest_textblock ) -> explanation(s=$manifest_textblock.st) | ^( EXPLANATION PARSE_ERROR ) );", 11, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("91:1: explanation : ( ^( EXPLANATION manifest_textblock ) -> explanation(s=$manifest_textblock.st) | ^( EXPLANATION PARSE_ERROR ) );", 11, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("91:1: explanation : ( ^( EXPLANATION manifest_textblock ) -> explanation(s=$manifest_textblock.st) | ^( EXPLANATION PARSE_ERROR ) );", 11, 0, input);

                throw nvae;
            }
            switch (alt11) {
                case 1 :
                    // BONSTTreeWalker.g:91:15: ^( EXPLANATION manifest_textblock )
                    {
                    match(input,EXPLANATION,FOLLOW_EXPLANATION_in_explanation1241); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_manifest_textblock_in_explanation1243);
                    manifest_textblock20=manifest_textblock();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 94:15: -> explanation(s=$manifest_textblock.st)
                    {
                        retval.st = templateLib.getInstanceOf("explanation",
                      new STAttrMap().put("s", manifest_textblock20.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:97:15: ^( EXPLANATION PARSE_ERROR )
                    {
                    match(input,EXPLANATION,FOLLOW_EXPLANATION_in_explanation1333); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_explanation1335); 

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
    // $ANTLR end explanation

    public static class indexing_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start indexing
    // BONSTTreeWalker.g:100:1: indexing : ( ^( INDEXING index_list ) -> indexing(i=$index_list.st) | ^( INDEXING PARSE_ERROR ) );
    public final indexing_return indexing() throws RecognitionException {
        indexing_return retval = new indexing_return();
        retval.start = input.LT(1);

        index_list_return index_list21 = null;


        try {
            // BONSTTreeWalker.g:100:11: ( ^( INDEXING index_list ) -> indexing(i=$index_list.st) | ^( INDEXING PARSE_ERROR ) )
            int alt12=2;
            int LA12_0 = input.LA(1);

            if ( (LA12_0==INDEXING) ) {
                int LA12_1 = input.LA(2);

                if ( (LA12_1==DOWN) ) {
                    int LA12_2 = input.LA(3);

                    if ( (LA12_2==PARSE_ERROR) ) {
                        alt12=2;
                    }
                    else if ( (LA12_2==INDEX_LIST) ) {
                        alt12=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("100:1: indexing : ( ^( INDEXING index_list ) -> indexing(i=$index_list.st) | ^( INDEXING PARSE_ERROR ) );", 12, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("100:1: indexing : ( ^( INDEXING index_list ) -> indexing(i=$index_list.st) | ^( INDEXING PARSE_ERROR ) );", 12, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("100:1: indexing : ( ^( INDEXING index_list ) -> indexing(i=$index_list.st) | ^( INDEXING PARSE_ERROR ) );", 12, 0, input);

                throw nvae;
            }
            switch (alt12) {
                case 1 :
                    // BONSTTreeWalker.g:100:12: ^( INDEXING index_list )
                    {
                    match(input,INDEXING,FOLLOW_INDEXING_in_indexing1374); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_index_list_in_indexing1376);
                    index_list21=index_list();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 103:12: -> indexing(i=$index_list.st)
                    {
                        retval.st = templateLib.getInstanceOf("indexing",
                      new STAttrMap().put("i", index_list21.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:106:12: ^( INDEXING PARSE_ERROR )
                    {
                    match(input,INDEXING,FOLLOW_INDEXING_in_indexing1452); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_indexing1454); 

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
    // $ANTLR end indexing

    public static class part_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start part
    // BONSTTreeWalker.g:109:1: part : ( ^( PART MANIFEST_STRING ) -> part(s=$MANIFEST_STRING.text) | ^( PART PARSE_ERROR ) );
    public final part_return part() throws RecognitionException {
        part_return retval = new part_return();
        retval.start = input.LT(1);

        CommonTree MANIFEST_STRING22=null;

        try {
            // BONSTTreeWalker.g:109:7: ( ^( PART MANIFEST_STRING ) -> part(s=$MANIFEST_STRING.text) | ^( PART PARSE_ERROR ) )
            int alt13=2;
            int LA13_0 = input.LA(1);

            if ( (LA13_0==PART) ) {
                int LA13_1 = input.LA(2);

                if ( (LA13_1==DOWN) ) {
                    int LA13_2 = input.LA(3);

                    if ( (LA13_2==MANIFEST_STRING) ) {
                        alt13=1;
                    }
                    else if ( (LA13_2==PARSE_ERROR) ) {
                        alt13=2;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("109:1: part : ( ^( PART MANIFEST_STRING ) -> part(s=$MANIFEST_STRING.text) | ^( PART PARSE_ERROR ) );", 13, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("109:1: part : ( ^( PART MANIFEST_STRING ) -> part(s=$MANIFEST_STRING.text) | ^( PART PARSE_ERROR ) );", 13, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("109:1: part : ( ^( PART MANIFEST_STRING ) -> part(s=$MANIFEST_STRING.text) | ^( PART PARSE_ERROR ) );", 13, 0, input);

                throw nvae;
            }
            switch (alt13) {
                case 1 :
                    // BONSTTreeWalker.g:109:8: ^( PART MANIFEST_STRING )
                    {
                    match(input,PART,FOLLOW_PART_in_part1486); 

                    match(input, Token.DOWN, null); 
                    MANIFEST_STRING22=(CommonTree)input.LT(1);
                    match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_part1488); 

                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 112:8: -> part(s=$MANIFEST_STRING.text)
                    {
                        retval.st = templateLib.getInstanceOf("part",
                      new STAttrMap().put("s", MANIFEST_STRING22.getText()));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:115:9: ^( PART PARSE_ERROR )
                    {
                    match(input,PART,FOLLOW_PART_in_part1544); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_part1546); 

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
    // $ANTLR end part

    public static class description_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start description
    // BONSTTreeWalker.g:118:1: description : ^( DESCRIPTION manifest_textblock ) -> description(s=$manifest_textblock.st);
    public final description_return description() throws RecognitionException {
        description_return retval = new description_return();
        retval.start = input.LT(1);

        manifest_textblock_return manifest_textblock23 = null;


        try {
            // BONSTTreeWalker.g:118:14: ( ^( DESCRIPTION manifest_textblock ) -> description(s=$manifest_textblock.st))
            // BONSTTreeWalker.g:118:15: ^( DESCRIPTION manifest_textblock )
            {
            match(input,DESCRIPTION,FOLLOW_DESCRIPTION_in_description1581); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_manifest_textblock_in_description1583);
            manifest_textblock23=manifest_textblock();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 121:15: -> description(s=$manifest_textblock.st)
            {
                retval.st = templateLib.getInstanceOf("description",
              new STAttrMap().put("s", manifest_textblock23.st));
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
    // $ANTLR end description

    public static class cluster_entries_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start cluster_entries
    // BONSTTreeWalker.g:125:1: cluster_entries : ^( CLUSTER_ENTRIES (c+= cluster_entry )+ ) -> clusterEntries(cs=$c);
    public final cluster_entries_return cluster_entries() throws RecognitionException {
        cluster_entries_return retval = new cluster_entries_return();
        retval.start = input.LT(1);

        List list_c=null;
        RuleReturnScope c = null;
        try {
            // BONSTTreeWalker.g:125:18: ( ^( CLUSTER_ENTRIES (c+= cluster_entry )+ ) -> clusterEntries(cs=$c))
            // BONSTTreeWalker.g:125:19: ^( CLUSTER_ENTRIES (c+= cluster_entry )+ )
            {
            match(input,CLUSTER_ENTRIES,FOLLOW_CLUSTER_ENTRIES_in_cluster_entries1686); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:126:37: (c+= cluster_entry )+
            int cnt14=0;
            loop14:
            do {
                int alt14=2;
                int LA14_0 = input.LA(1);

                if ( (LA14_0==CLUSTER_ENTRY) ) {
                    alt14=1;
                }


                switch (alt14) {
            	case 1 :
            	    // BONSTTreeWalker.g:126:38: c+= cluster_entry
            	    {
            	    pushFollow(FOLLOW_cluster_entry_in_cluster_entries1691);
            	    c=cluster_entry();
            	    _fsp--;

            	    if (list_c==null) list_c=new ArrayList();
            	    list_c.add(c.getTemplate());


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


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 128:19: -> clusterEntries(cs=$c)
            {
                retval.st = templateLib.getInstanceOf("clusterEntries",
              new STAttrMap().put("cs", list_c));
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
    // $ANTLR end cluster_entries

    public static class cluster_entry_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start cluster_entry
    // BONSTTreeWalker.g:132:1: cluster_entry : ^( CLUSTER_ENTRY cluster_name description ) -> clusterEntry(name=$cluster_name.stdesc=$description.st);
    public final cluster_entry_return cluster_entry() throws RecognitionException {
        cluster_entry_return retval = new cluster_entry_return();
        retval.start = input.LT(1);

        cluster_name_return cluster_name24 = null;

        description_return description25 = null;


        try {
            // BONSTTreeWalker.g:132:16: ( ^( CLUSTER_ENTRY cluster_name description ) -> clusterEntry(name=$cluster_name.stdesc=$description.st))
            // BONSTTreeWalker.g:132:17: ^( CLUSTER_ENTRY cluster_name description )
            {
            match(input,CLUSTER_ENTRY,FOLLOW_CLUSTER_ENTRY_in_cluster_entry1825); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_cluster_name_in_cluster_entry1827);
            cluster_name24=cluster_name();
            _fsp--;

            pushFollow(FOLLOW_description_in_cluster_entry1829);
            description25=description();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 135:17: -> clusterEntry(name=$cluster_name.stdesc=$description.st)
            {
                retval.st = templateLib.getInstanceOf("clusterEntry",
              new STAttrMap().put("name", cluster_name24.st).put("desc", description25.st));
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
    // $ANTLR end cluster_entry

    public static class system_name_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start system_name
    // BONSTTreeWalker.g:139:1: system_name : ^( SYSTEM_NAME IDENTIFIER ) -> systemName(name=$IDENTIFIER.text);
    public final system_name_return system_name() throws RecognitionException {
        system_name_return retval = new system_name_return();
        retval.start = input.LT(1);

        CommonTree IDENTIFIER26=null;

        try {
            // BONSTTreeWalker.g:139:14: ( ^( SYSTEM_NAME IDENTIFIER ) -> systemName(name=$IDENTIFIER.text))
            // BONSTTreeWalker.g:139:15: ^( SYSTEM_NAME IDENTIFIER )
            {
            match(input,SYSTEM_NAME,FOLLOW_SYSTEM_NAME_in_system_name1952); 

            match(input, Token.DOWN, null); 
            IDENTIFIER26=(CommonTree)input.LT(1);
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_system_name1954); 

            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 142:15: -> systemName(name=$IDENTIFIER.text)
            {
                retval.st = templateLib.getInstanceOf("systemName",
              new STAttrMap().put("name", IDENTIFIER26.getText()));
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
    // $ANTLR end system_name

    public static class index_list_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start index_list
    // BONSTTreeWalker.g:146:1: index_list : ^( INDEX_LIST (i+= index_clause )+ ) -> indexList(i=$i);
    public final index_list_return index_list() throws RecognitionException {
        index_list_return retval = new index_list_return();
        retval.start = input.LT(1);

        List list_i=null;
        RuleReturnScope i = null;
        try {
            // BONSTTreeWalker.g:148:13: ( ^( INDEX_LIST (i+= index_clause )+ ) -> indexList(i=$i))
            // BONSTTreeWalker.g:148:14: ^( INDEX_LIST (i+= index_clause )+ )
            {
            match(input,INDEX_LIST,FOLLOW_INDEX_LIST_in_index_list2052); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:149:27: (i+= index_clause )+
            int cnt15=0;
            loop15:
            do {
                int alt15=2;
                int LA15_0 = input.LA(1);

                if ( (LA15_0==INDEX_CLAUSE) ) {
                    alt15=1;
                }


                switch (alt15) {
            	case 1 :
            	    // BONSTTreeWalker.g:149:28: i+= index_clause
            	    {
            	    pushFollow(FOLLOW_index_clause_in_index_list2057);
            	    i=index_clause();
            	    _fsp--;

            	    if (list_i==null) list_i=new ArrayList();
            	    list_i.add(i.getTemplate());


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

            // TEMPLATE REWRITE
            // 151:14: -> indexList(i=$i)
            {
                retval.st = templateLib.getInstanceOf("indexList",
              new STAttrMap().put("i", list_i));
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
    // $ANTLR end index_list

    public static class index_clause_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start index_clause
    // BONSTTreeWalker.g:155:1: index_clause : ( ^( INDEX_CLAUSE IDENTIFIER index_term_list ) -> indexClause(id=$IDENTIFIER.texti=$index_term_list.st) | ^( INDEX_CLAUSE PARSE_ERROR ) );
    public final index_clause_return index_clause() throws RecognitionException {
        index_clause_return retval = new index_clause_return();
        retval.start = input.LT(1);

        CommonTree IDENTIFIER27=null;
        index_term_list_return index_term_list28 = null;


        try {
            // BONSTTreeWalker.g:155:15: ( ^( INDEX_CLAUSE IDENTIFIER index_term_list ) -> indexClause(id=$IDENTIFIER.texti=$index_term_list.st) | ^( INDEX_CLAUSE PARSE_ERROR ) )
            int alt16=2;
            int LA16_0 = input.LA(1);

            if ( (LA16_0==INDEX_CLAUSE) ) {
                int LA16_1 = input.LA(2);

                if ( (LA16_1==DOWN) ) {
                    int LA16_2 = input.LA(3);

                    if ( (LA16_2==PARSE_ERROR) ) {
                        alt16=2;
                    }
                    else if ( (LA16_2==IDENTIFIER) ) {
                        alt16=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("155:1: index_clause : ( ^( INDEX_CLAUSE IDENTIFIER index_term_list ) -> indexClause(id=$IDENTIFIER.texti=$index_term_list.st) | ^( INDEX_CLAUSE PARSE_ERROR ) );", 16, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("155:1: index_clause : ( ^( INDEX_CLAUSE IDENTIFIER index_term_list ) -> indexClause(id=$IDENTIFIER.texti=$index_term_list.st) | ^( INDEX_CLAUSE PARSE_ERROR ) );", 16, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("155:1: index_clause : ( ^( INDEX_CLAUSE IDENTIFIER index_term_list ) -> indexClause(id=$IDENTIFIER.texti=$index_term_list.st) | ^( INDEX_CLAUSE PARSE_ERROR ) );", 16, 0, input);

                throw nvae;
            }
            switch (alt16) {
                case 1 :
                    // BONSTTreeWalker.g:155:16: ^( INDEX_CLAUSE IDENTIFIER index_term_list )
                    {
                    match(input,INDEX_CLAUSE,FOLLOW_INDEX_CLAUSE_in_index_clause2164); 

                    match(input, Token.DOWN, null); 
                    IDENTIFIER27=(CommonTree)input.LT(1);
                    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_index_clause2166); 
                    pushFollow(FOLLOW_index_term_list_in_index_clause2168);
                    index_term_list28=index_term_list();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 158:16: -> indexClause(id=$IDENTIFIER.texti=$index_term_list.st)
                    {
                        retval.st = templateLib.getInstanceOf("indexClause",
                      new STAttrMap().put("id", IDENTIFIER27.getText()).put("i", index_term_list28.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:161:16: ^( INDEX_CLAUSE PARSE_ERROR )
                    {
                    match(input,INDEX_CLAUSE,FOLLOW_INDEX_CLAUSE_in_index_clause2267); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_index_clause2269); 

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
    // $ANTLR end index_clause

    public static class index_term_list_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start index_term_list
    // BONSTTreeWalker.g:164:1: index_term_list : ^( INDEX_TERM_LIST (i+= index_string )+ ) -> indexTermList(i=$i);
    public final index_term_list_return index_term_list() throws RecognitionException {
        index_term_list_return retval = new index_term_list_return();
        retval.start = input.LT(1);

        List list_i=null;
        RuleReturnScope i = null;
        try {
            // BONSTTreeWalker.g:164:18: ( ^( INDEX_TERM_LIST (i+= index_string )+ ) -> indexTermList(i=$i))
            // BONSTTreeWalker.g:164:19: ^( INDEX_TERM_LIST (i+= index_string )+ )
            {
            match(input,INDEX_TERM_LIST,FOLLOW_INDEX_TERM_LIST_in_index_term_list2332); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:165:37: (i+= index_string )+
            int cnt17=0;
            loop17:
            do {
                int alt17=2;
                int LA17_0 = input.LA(1);

                if ( (LA17_0==INDEX_STRING) ) {
                    alt17=1;
                }


                switch (alt17) {
            	case 1 :
            	    // BONSTTreeWalker.g:165:38: i+= index_string
            	    {
            	    pushFollow(FOLLOW_index_string_in_index_term_list2337);
            	    i=index_string();
            	    _fsp--;

            	    if (list_i==null) list_i=new ArrayList();
            	    list_i.add(i.getTemplate());


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


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 167:19: -> indexTermList(i=$i)
            {
                retval.st = templateLib.getInstanceOf("indexTermList",
              new STAttrMap().put("i", list_i));
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
    // $ANTLR end index_term_list

    public static class index_string_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start index_string
    // BONSTTreeWalker.g:171:1: index_string : ^( INDEX_STRING MANIFEST_STRING ) -> indexString(s=$MANIFEST_STRING.text);
    public final index_string_return index_string() throws RecognitionException {
        index_string_return retval = new index_string_return();
        retval.start = input.LT(1);

        CommonTree MANIFEST_STRING29=null;

        try {
            // BONSTTreeWalker.g:171:15: ( ^( INDEX_STRING MANIFEST_STRING ) -> indexString(s=$MANIFEST_STRING.text))
            // BONSTTreeWalker.g:171:16: ^( INDEX_STRING MANIFEST_STRING )
            {
            match(input,INDEX_STRING,FOLLOW_INDEX_STRING_in_index_string2469); 

            match(input, Token.DOWN, null); 
            MANIFEST_STRING29=(CommonTree)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_index_string2471); 

            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 174:16: -> indexString(s=$MANIFEST_STRING.text)
            {
                retval.st = templateLib.getInstanceOf("indexString",
              new STAttrMap().put("s", MANIFEST_STRING29.getText()));
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
    // $ANTLR end index_string

    public static class cluster_chart_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start cluster_chart
    // BONSTTreeWalker.g:178:1: cluster_chart : ^( CLUSTER_CHART cluster_name (o+= indexing )? (o+= explanation )? (o+= part )? (o+= class_entries )? (o+= cluster_entries )? ) -> clusterChart(name=$cluster_name.stother=$o);
    public final cluster_chart_return cluster_chart() throws RecognitionException {
        cluster_chart_return retval = new cluster_chart_return();
        retval.start = input.LT(1);

        List list_o=null;
        cluster_name_return cluster_name30 = null;

        RuleReturnScope o = null;
        try {
            // BONSTTreeWalker.g:180:16: ( ^( CLUSTER_CHART cluster_name (o+= indexing )? (o+= explanation )? (o+= part )? (o+= class_entries )? (o+= cluster_entries )? ) -> clusterChart(name=$cluster_name.stother=$o))
            // BONSTTreeWalker.g:180:17: ^( CLUSTER_CHART cluster_name (o+= indexing )? (o+= explanation )? (o+= part )? (o+= class_entries )? (o+= cluster_entries )? )
            {
            match(input,CLUSTER_CHART,FOLLOW_CLUSTER_CHART_in_cluster_chart2576); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_cluster_name_in_cluster_chart2578);
            cluster_name30=cluster_name();
            _fsp--;

            // BONSTTreeWalker.g:182:19: (o+= indexing )?
            int alt18=2;
            int LA18_0 = input.LA(1);

            if ( (LA18_0==INDEXING) ) {
                alt18=1;
            }
            switch (alt18) {
                case 1 :
                    // BONSTTreeWalker.g:182:20: o+= indexing
                    {
                    pushFollow(FOLLOW_indexing_in_cluster_chart2602);
                    o=indexing();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:183:19: (o+= explanation )?
            int alt19=2;
            int LA19_0 = input.LA(1);

            if ( (LA19_0==EXPLANATION) ) {
                alt19=1;
            }
            switch (alt19) {
                case 1 :
                    // BONSTTreeWalker.g:183:20: o+= explanation
                    {
                    pushFollow(FOLLOW_explanation_in_cluster_chart2628);
                    o=explanation();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:184:19: (o+= part )?
            int alt20=2;
            int LA20_0 = input.LA(1);

            if ( (LA20_0==PART) ) {
                alt20=1;
            }
            switch (alt20) {
                case 1 :
                    // BONSTTreeWalker.g:184:20: o+= part
                    {
                    pushFollow(FOLLOW_part_in_cluster_chart2654);
                    o=part();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:185:19: (o+= class_entries )?
            int alt21=2;
            int LA21_0 = input.LA(1);

            if ( (LA21_0==CLASS_ENTRIES) ) {
                alt21=1;
            }
            switch (alt21) {
                case 1 :
                    // BONSTTreeWalker.g:185:20: o+= class_entries
                    {
                    pushFollow(FOLLOW_class_entries_in_cluster_chart2680);
                    o=class_entries();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:186:19: (o+= cluster_entries )?
            int alt22=2;
            int LA22_0 = input.LA(1);

            if ( (LA22_0==CLUSTER_ENTRIES) ) {
                alt22=1;
            }
            switch (alt22) {
                case 1 :
                    // BONSTTreeWalker.g:186:20: o+= cluster_entries
                    {
                    pushFollow(FOLLOW_cluster_entries_in_cluster_chart2706);
                    o=cluster_entries();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 188:17: -> clusterChart(name=$cluster_name.stother=$o)
            {
                retval.st = templateLib.getInstanceOf("clusterChart",
              new STAttrMap().put("name", cluster_name30.st).put("other", list_o));
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
    // $ANTLR end cluster_chart

    public static class class_entries_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start class_entries
    // BONSTTreeWalker.g:192:1: class_entries : ^( CLASS_ENTRIES (c+= class_entry )+ ) -> classEntries(cs=$c);
    public final class_entries_return class_entries() throws RecognitionException {
        class_entries_return retval = new class_entries_return();
        retval.start = input.LT(1);

        List list_c=null;
        RuleReturnScope c = null;
        try {
            // BONSTTreeWalker.g:192:16: ( ^( CLASS_ENTRIES (c+= class_entry )+ ) -> classEntries(cs=$c))
            // BONSTTreeWalker.g:192:17: ^( CLASS_ENTRIES (c+= class_entry )+ )
            {
            match(input,CLASS_ENTRIES,FOLLOW_CLASS_ENTRIES_in_class_entries2834); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:193:33: (c+= class_entry )+
            int cnt23=0;
            loop23:
            do {
                int alt23=2;
                int LA23_0 = input.LA(1);

                if ( (LA23_0==CLASS_ENTRY) ) {
                    alt23=1;
                }


                switch (alt23) {
            	case 1 :
            	    // BONSTTreeWalker.g:193:34: c+= class_entry
            	    {
            	    pushFollow(FOLLOW_class_entry_in_class_entries2839);
            	    c=class_entry();
            	    _fsp--;

            	    if (list_c==null) list_c=new ArrayList();
            	    list_c.add(c.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt23 >= 1 ) break loop23;
                        EarlyExitException eee =
                            new EarlyExitException(23, input);
                        throw eee;
                }
                cnt23++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 195:17: -> classEntries(cs=$c)
            {
                retval.st = templateLib.getInstanceOf("classEntries",
              new STAttrMap().put("cs", list_c));
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
    // $ANTLR end class_entries

    public static class class_entry_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start class_entry
    // BONSTTreeWalker.g:199:1: class_entry : ^( CLASS_ENTRY class_name description ) -> classEntry(name=$class_name.stdesc=$description.st);
    public final class_entry_return class_entry() throws RecognitionException {
        class_entry_return retval = new class_entry_return();
        retval.start = input.LT(1);

        class_name_return class_name31 = null;

        description_return description32 = null;


        try {
            // BONSTTreeWalker.g:199:14: ( ^( CLASS_ENTRY class_name description ) -> classEntry(name=$class_name.stdesc=$description.st))
            // BONSTTreeWalker.g:199:15: ^( CLASS_ENTRY class_name description )
            {
            match(input,CLASS_ENTRY,FOLLOW_CLASS_ENTRY_in_class_entry2962); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_class_name_in_class_entry2964);
            class_name31=class_name();
            _fsp--;

            pushFollow(FOLLOW_description_in_class_entry2966);
            description32=description();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 202:15: -> classEntry(name=$class_name.stdesc=$description.st)
            {
                retval.st = templateLib.getInstanceOf("classEntry",
              new STAttrMap().put("name", class_name31.st).put("desc", description32.st));
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
    // $ANTLR end class_entry

    public static class cluster_name_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start cluster_name
    // BONSTTreeWalker.g:206:1: cluster_name : ^( CLUSTER_NAME IDENTIFIER ) -> clusterName(name=$IDENTIFIER.text);
    public final cluster_name_return cluster_name() throws RecognitionException {
        cluster_name_return retval = new cluster_name_return();
        retval.start = input.LT(1);

        CommonTree IDENTIFIER33=null;

        try {
            // BONSTTreeWalker.g:206:15: ( ^( CLUSTER_NAME IDENTIFIER ) -> clusterName(name=$IDENTIFIER.text))
            // BONSTTreeWalker.g:206:16: ^( CLUSTER_NAME IDENTIFIER )
            {
            match(input,CLUSTER_NAME,FOLLOW_CLUSTER_NAME_in_cluster_name3080); 

            match(input, Token.DOWN, null); 
            IDENTIFIER33=(CommonTree)input.LT(1);
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_cluster_name3082); 

            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 209:16: -> clusterName(name=$IDENTIFIER.text)
            {
                retval.st = templateLib.getInstanceOf("clusterName",
              new STAttrMap().put("name", IDENTIFIER33.getText()));
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
    // $ANTLR end cluster_name

    public static class class_chart_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start class_chart
    // BONSTTreeWalker.g:213:1: class_chart : ^( CLASS_CHART class_name (o+= indexing )? (o+= explanation )? (o+= part )? (o+= inherits )? (o+= queries )? (o+= commands )? (o+= constraints )? ) -> classChart(name=$class_name.textother=$o);
    public final class_chart_return class_chart() throws RecognitionException {
        class_chart_return retval = new class_chart_return();
        retval.start = input.LT(1);

        List list_o=null;
        class_name_return class_name34 = null;

        RuleReturnScope o = null;
        try {
            // BONSTTreeWalker.g:215:14: ( ^( CLASS_CHART class_name (o+= indexing )? (o+= explanation )? (o+= part )? (o+= inherits )? (o+= queries )? (o+= commands )? (o+= constraints )? ) -> classChart(name=$class_name.textother=$o))
            // BONSTTreeWalker.g:215:15: ^( CLASS_CHART class_name (o+= indexing )? (o+= explanation )? (o+= part )? (o+= inherits )? (o+= queries )? (o+= commands )? (o+= constraints )? )
            {
            match(input,CLASS_CHART,FOLLOW_CLASS_CHART_in_class_chart3186); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_class_name_in_class_chart3188);
            class_name34=class_name();
            _fsp--;

            // BONSTTreeWalker.g:217:17: (o+= indexing )?
            int alt24=2;
            int LA24_0 = input.LA(1);

            if ( (LA24_0==INDEXING) ) {
                alt24=1;
            }
            switch (alt24) {
                case 1 :
                    // BONSTTreeWalker.g:217:18: o+= indexing
                    {
                    pushFollow(FOLLOW_indexing_in_class_chart3209);
                    o=indexing();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:218:17: (o+= explanation )?
            int alt25=2;
            int LA25_0 = input.LA(1);

            if ( (LA25_0==EXPLANATION) ) {
                alt25=1;
            }
            switch (alt25) {
                case 1 :
                    // BONSTTreeWalker.g:218:18: o+= explanation
                    {
                    pushFollow(FOLLOW_explanation_in_class_chart3233);
                    o=explanation();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:219:17: (o+= part )?
            int alt26=2;
            int LA26_0 = input.LA(1);

            if ( (LA26_0==PART) ) {
                alt26=1;
            }
            switch (alt26) {
                case 1 :
                    // BONSTTreeWalker.g:219:18: o+= part
                    {
                    pushFollow(FOLLOW_part_in_class_chart3257);
                    o=part();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:220:17: (o+= inherits )?
            int alt27=2;
            int LA27_0 = input.LA(1);

            if ( (LA27_0==INHERITS) ) {
                alt27=1;
            }
            switch (alt27) {
                case 1 :
                    // BONSTTreeWalker.g:220:18: o+= inherits
                    {
                    pushFollow(FOLLOW_inherits_in_class_chart3281);
                    o=inherits();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:221:17: (o+= queries )?
            int alt28=2;
            int LA28_0 = input.LA(1);

            if ( (LA28_0==QUERIES) ) {
                alt28=1;
            }
            switch (alt28) {
                case 1 :
                    // BONSTTreeWalker.g:221:18: o+= queries
                    {
                    pushFollow(FOLLOW_queries_in_class_chart3304);
                    o=queries();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:222:17: (o+= commands )?
            int alt29=2;
            int LA29_0 = input.LA(1);

            if ( (LA29_0==COMMANDS) ) {
                alt29=1;
            }
            switch (alt29) {
                case 1 :
                    // BONSTTreeWalker.g:222:18: o+= commands
                    {
                    pushFollow(FOLLOW_commands_in_class_chart3328);
                    o=commands();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:223:17: (o+= constraints )?
            int alt30=2;
            int LA30_0 = input.LA(1);

            if ( (LA30_0==CONSTRAINTS) ) {
                alt30=1;
            }
            switch (alt30) {
                case 1 :
                    // BONSTTreeWalker.g:223:18: o+= constraints
                    {
                    pushFollow(FOLLOW_constraints_in_class_chart3352);
                    o=constraints();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 225:15: -> classChart(name=$class_name.textother=$o)
            {
                retval.st = templateLib.getInstanceOf("classChart",
              new STAttrMap().put("name", input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(class_name34.start),
              input.getTreeAdaptor().getTokenStopIndex(class_name34.start))).put("other", list_o));
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
    // $ANTLR end class_chart

    public static class inherits_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start inherits
    // BONSTTreeWalker.g:229:1: inherits : ( ^( INHERITS class_name_list ) -> inherits(l=$class_name_list.st) | ^( INHERITS PARSE_ERROR ) );
    public final inherits_return inherits() throws RecognitionException {
        inherits_return retval = new inherits_return();
        retval.start = input.LT(1);

        class_name_list_return class_name_list35 = null;


        try {
            // BONSTTreeWalker.g:229:11: ( ^( INHERITS class_name_list ) -> inherits(l=$class_name_list.st) | ^( INHERITS PARSE_ERROR ) )
            int alt31=2;
            int LA31_0 = input.LA(1);

            if ( (LA31_0==INHERITS) ) {
                int LA31_1 = input.LA(2);

                if ( (LA31_1==DOWN) ) {
                    int LA31_2 = input.LA(3);

                    if ( (LA31_2==PARSE_ERROR) ) {
                        alt31=2;
                    }
                    else if ( (LA31_2==CLASS_NAME_LIST) ) {
                        alt31=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("229:1: inherits : ( ^( INHERITS class_name_list ) -> inherits(l=$class_name_list.st) | ^( INHERITS PARSE_ERROR ) );", 31, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("229:1: inherits : ( ^( INHERITS class_name_list ) -> inherits(l=$class_name_list.st) | ^( INHERITS PARSE_ERROR ) );", 31, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("229:1: inherits : ( ^( INHERITS class_name_list ) -> inherits(l=$class_name_list.st) | ^( INHERITS PARSE_ERROR ) );", 31, 0, input);

                throw nvae;
            }
            switch (alt31) {
                case 1 :
                    // BONSTTreeWalker.g:229:14: ^( INHERITS class_name_list )
                    {
                    match(input,INHERITS,FOLLOW_INHERITS_in_inherits3438); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_class_name_list_in_inherits3440);
                    class_name_list35=class_name_list();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 229:42: -> inherits(l=$class_name_list.st)
                    {
                        retval.st = templateLib.getInstanceOf("inherits",
                      new STAttrMap().put("l", class_name_list35.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:231:14: ^( INHERITS PARSE_ERROR )
                    {
                    match(input,INHERITS,FOLLOW_INHERITS_in_inherits3480); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_inherits3482); 

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
    // $ANTLR end inherits

    public static class queries_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start queries
    // BONSTTreeWalker.g:234:1: queries : ^( QUERIES query_list ) -> queries(l=$query_list.st);
    public final queries_return queries() throws RecognitionException {
        queries_return retval = new queries_return();
        retval.start = input.LT(1);

        query_list_return query_list36 = null;


        try {
            // BONSTTreeWalker.g:234:10: ( ^( QUERIES query_list ) -> queries(l=$query_list.st))
            // BONSTTreeWalker.g:234:12: ^( QUERIES query_list )
            {
            match(input,QUERIES,FOLLOW_QUERIES_in_queries3504); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_query_list_in_queries3506);
            query_list36=query_list();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 234:34: -> queries(l=$query_list.st)
            {
                retval.st = templateLib.getInstanceOf("queries",
              new STAttrMap().put("l", query_list36.st));
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
    // $ANTLR end queries

    public static class commands_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start commands
    // BONSTTreeWalker.g:237:1: commands : ^( COMMANDS command_list ) -> commands(l=$command_list.st);
    public final commands_return commands() throws RecognitionException {
        commands_return retval = new commands_return();
        retval.start = input.LT(1);

        command_list_return command_list37 = null;


        try {
            // BONSTTreeWalker.g:237:11: ( ^( COMMANDS command_list ) -> commands(l=$command_list.st))
            // BONSTTreeWalker.g:237:13: ^( COMMANDS command_list )
            {
            match(input,COMMANDS,FOLLOW_COMMANDS_in_commands3545); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_command_list_in_commands3547);
            command_list37=command_list();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 237:38: -> commands(l=$command_list.st)
            {
                retval.st = templateLib.getInstanceOf("commands",
              new STAttrMap().put("l", command_list37.st));
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
    // $ANTLR end commands

    public static class constraints_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start constraints
    // BONSTTreeWalker.g:240:1: constraints : ^( CONSTRAINTS constraint_list ) -> constraints(l=$constraint_list.st);
    public final constraints_return constraints() throws RecognitionException {
        constraints_return retval = new constraints_return();
        retval.start = input.LT(1);

        constraint_list_return constraint_list38 = null;


        try {
            // BONSTTreeWalker.g:240:14: ( ^( CONSTRAINTS constraint_list ) -> constraints(l=$constraint_list.st))
            // BONSTTreeWalker.g:240:16: ^( CONSTRAINTS constraint_list )
            {
            match(input,CONSTRAINTS,FOLLOW_CONSTRAINTS_in_constraints3578); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_constraint_list_in_constraints3580);
            constraint_list38=constraint_list();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 240:47: -> constraints(l=$constraint_list.st)
            {
                retval.st = templateLib.getInstanceOf("constraints",
              new STAttrMap().put("l", constraint_list38.st));
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
    // $ANTLR end constraints

    public static class query_list_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start query_list
    // BONSTTreeWalker.g:243:1: query_list : ^( QUERY_LIST (m= manifest_textblock )+ ) -> queryList(qs=l);
    public final query_list_return query_list() throws RecognitionException {
        query_list_return retval = new query_list_return();
        retval.start = input.LT(1);

        manifest_textblock_return m = null;


        try {
            // BONSTTreeWalker.g:243:13: ( ^( QUERY_LIST (m= manifest_textblock )+ ) -> queryList(qs=l))
            // BONSTTreeWalker.g:243:14: ^( QUERY_LIST (m= manifest_textblock )+ )
            {
            match(input,QUERY_LIST,FOLLOW_QUERY_LIST_in_query_list3629); 

             LinkedList<String> l = new LinkedList<String>(); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:244:80: (m= manifest_textblock )+
            int cnt32=0;
            loop32:
            do {
                int alt32=2;
                int LA32_0 = input.LA(1);

                if ( (LA32_0==MANIFEST_STRING||LA32_0==MANIFEST_TEXTBLOCK_START) ) {
                    alt32=1;
                }


                switch (alt32) {
            	case 1 :
            	    // BONSTTreeWalker.g:244:81: m= manifest_textblock
            	    {
            	    pushFollow(FOLLOW_manifest_textblock_in_query_list3636);
            	    m=manifest_textblock();
            	    _fsp--;

            	     l.add(input.getTokenStream().toString(
            	      input.getTreeAdaptor().getTokenStartIndex(m.start),
            	      input.getTreeAdaptor().getTokenStopIndex(m.start))); 

            	    }
            	    break;

            	default :
            	    if ( cnt32 >= 1 ) break loop32;
                        EarlyExitException eee =
                            new EarlyExitException(32, input);
                        throw eee;
                }
                cnt32++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 246:14: -> queryList(qs=l)
            {
                retval.st = templateLib.getInstanceOf("queryList",
              new STAttrMap().put("qs", l));
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
    // $ANTLR end query_list

    public static class command_list_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start command_list
    // BONSTTreeWalker.g:250:1: command_list : ^( COMMAND_LIST (m= manifest_textblock )+ ) -> commandList(cs=l);
    public final command_list_return command_list() throws RecognitionException {
        command_list_return retval = new command_list_return();
        retval.start = input.LT(1);

        manifest_textblock_return m = null;


        try {
            // BONSTTreeWalker.g:250:15: ( ^( COMMAND_LIST (m= manifest_textblock )+ ) -> commandList(cs=l))
            // BONSTTreeWalker.g:250:16: ^( COMMAND_LIST (m= manifest_textblock )+ )
            {
            match(input,COMMAND_LIST,FOLLOW_COMMAND_LIST_in_command_list3746); 

             LinkedList<String> l = new LinkedList<String>(); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:251:84: (m= manifest_textblock )+
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
            	    // BONSTTreeWalker.g:251:85: m= manifest_textblock
            	    {
            	    pushFollow(FOLLOW_manifest_textblock_in_command_list3753);
            	    m=manifest_textblock();
            	    _fsp--;

            	     l.add(input.getTokenStream().toString(
            	      input.getTreeAdaptor().getTokenStartIndex(m.start),
            	      input.getTreeAdaptor().getTokenStopIndex(m.start))); 

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

            // TEMPLATE REWRITE
            // 253:16: -> commandList(cs=l)
            {
                retval.st = templateLib.getInstanceOf("commandList",
              new STAttrMap().put("cs", l));
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
    // $ANTLR end command_list

    public static class constraint_list_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start constraint_list
    // BONSTTreeWalker.g:257:1: constraint_list : ^( CONSTRAINT_LIST (m= manifest_textblock )+ ) -> constraintList(cs=l);
    public final constraint_list_return constraint_list() throws RecognitionException {
        constraint_list_return retval = new constraint_list_return();
        retval.start = input.LT(1);

        manifest_textblock_return m = null;


        try {
            // BONSTTreeWalker.g:257:18: ( ^( CONSTRAINT_LIST (m= manifest_textblock )+ ) -> constraintList(cs=l))
            // BONSTTreeWalker.g:257:19: ^( CONSTRAINT_LIST (m= manifest_textblock )+ )
            {
            match(input,CONSTRAINT_LIST,FOLLOW_CONSTRAINT_LIST_in_constraint_list3876); 

             LinkedList<String> l = new LinkedList<String>(); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:258:90: (m= manifest_textblock )+
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
            	    // BONSTTreeWalker.g:258:91: m= manifest_textblock
            	    {
            	    pushFollow(FOLLOW_manifest_textblock_in_constraint_list3883);
            	    m=manifest_textblock();
            	    _fsp--;

            	     l.add(input.getTokenStream().toString(
            	      input.getTreeAdaptor().getTokenStartIndex(m.start),
            	      input.getTreeAdaptor().getTokenStopIndex(m.start))); 

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

            // TEMPLATE REWRITE
            // 260:19: -> constraintList(cs=l)
            {
                retval.st = templateLib.getInstanceOf("constraintList",
              new STAttrMap().put("cs", l));
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
    // $ANTLR end constraint_list

    public static class class_name_list_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start class_name_list
    // BONSTTreeWalker.g:264:1: class_name_list : ^( CLASS_NAME_LIST (c+= class_name )+ ) -> classNameList(cs=$c);
    public final class_name_list_return class_name_list() throws RecognitionException {
        class_name_list_return retval = new class_name_list_return();
        retval.start = input.LT(1);

        List list_c=null;
        RuleReturnScope c = null;
        try {
            // BONSTTreeWalker.g:264:18: ( ^( CLASS_NAME_LIST (c+= class_name )+ ) -> classNameList(cs=$c))
            // BONSTTreeWalker.g:264:19: ^( CLASS_NAME_LIST (c+= class_name )+ )
            {
            match(input,CLASS_NAME_LIST,FOLLOW_CLASS_NAME_LIST_in_class_name_list4004); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:265:37: (c+= class_name )+
            int cnt35=0;
            loop35:
            do {
                int alt35=2;
                int LA35_0 = input.LA(1);

                if ( (LA35_0==CLASS_NAME) ) {
                    alt35=1;
                }


                switch (alt35) {
            	case 1 :
            	    // BONSTTreeWalker.g:265:38: c+= class_name
            	    {
            	    pushFollow(FOLLOW_class_name_in_class_name_list4009);
            	    c=class_name();
            	    _fsp--;

            	    if (list_c==null) list_c=new ArrayList();
            	    list_c.add(c.getTemplate());


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

            // TEMPLATE REWRITE
            // 267:19: -> classNameList(cs=$c)
            {
                retval.st = templateLib.getInstanceOf("classNameList",
              new STAttrMap().put("cs", list_c));
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
    // $ANTLR end class_name_list

    public static class class_name_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start class_name
    // BONSTTreeWalker.g:271:1: class_name : ^( CLASS_NAME IDENTIFIER ) -> className(name=$IDENTIFIER.text);
    public final class_name_return class_name() throws RecognitionException {
        class_name_return retval = new class_name_return();
        retval.start = input.LT(1);

        CommonTree IDENTIFIER39=null;

        try {
            // BONSTTreeWalker.g:271:13: ( ^( CLASS_NAME IDENTIFIER ) -> className(name=$IDENTIFIER.text))
            // BONSTTreeWalker.g:271:14: ^( CLASS_NAME IDENTIFIER )
            {
            match(input,CLASS_NAME,FOLLOW_CLASS_NAME_in_class_name4139); 

            match(input, Token.DOWN, null); 
            IDENTIFIER39=(CommonTree)input.LT(1);
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_class_name4141); 

            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 274:14: -> className(name=$IDENTIFIER.text)
            {
                retval.st = templateLib.getInstanceOf("className",
              new STAttrMap().put("name", IDENTIFIER39.getText()));
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
    // $ANTLR end class_name

    public static class event_chart_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start event_chart
    // BONSTTreeWalker.g:278:1: event_chart : ^( EVENT_CHART system_name (k+= 'incoming' )? (k+= 'outgoing' )? (o+= indexing )? (o+= explanation )? (o+= part )? (o+= event_entries )? ) -> eventChart(name=$system_name.stk=$kother=$o);
    public final event_chart_return event_chart() throws RecognitionException {
        event_chart_return retval = new event_chart_return();
        retval.start = input.LT(1);

        CommonTree k=null;
        List list_k=null;
        List list_o=null;
        system_name_return system_name40 = null;

        RuleReturnScope o = null;
        try {
            // BONSTTreeWalker.g:280:14: ( ^( EVENT_CHART system_name (k+= 'incoming' )? (k+= 'outgoing' )? (o+= indexing )? (o+= explanation )? (o+= part )? (o+= event_entries )? ) -> eventChart(name=$system_name.stk=$kother=$o))
            // BONSTTreeWalker.g:280:15: ^( EVENT_CHART system_name (k+= 'incoming' )? (k+= 'outgoing' )? (o+= indexing )? (o+= explanation )? (o+= part )? (o+= event_entries )? )
            {
            match(input,EVENT_CHART,FOLLOW_EVENT_CHART_in_event_chart4236); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_system_name_in_event_chart4254);
            system_name40=system_name();
            _fsp--;

            // BONSTTreeWalker.g:283:17: (k+= 'incoming' )?
            int alt36=2;
            int LA36_0 = input.LA(1);

            if ( (LA36_0==205) ) {
                alt36=1;
            }
            switch (alt36) {
                case 1 :
                    // BONSTTreeWalker.g:283:18: k+= 'incoming'
                    {
                    k=(CommonTree)input.LT(1);
                    match(input,205,FOLLOW_205_in_event_chart4276); 
                    if (list_k==null) list_k=new ArrayList();
                    list_k.add(k);


                    }
                    break;

            }

            // BONSTTreeWalker.g:283:34: (k+= 'outgoing' )?
            int alt37=2;
            int LA37_0 = input.LA(1);

            if ( (LA37_0==206) ) {
                alt37=1;
            }
            switch (alt37) {
                case 1 :
                    // BONSTTreeWalker.g:283:35: k+= 'outgoing'
                    {
                    k=(CommonTree)input.LT(1);
                    match(input,206,FOLLOW_206_in_event_chart4283); 
                    if (list_k==null) list_k=new ArrayList();
                    list_k.add(k);


                    }
                    break;

            }

            // BONSTTreeWalker.g:284:17: (o+= indexing )?
            int alt38=2;
            int LA38_0 = input.LA(1);

            if ( (LA38_0==INDEXING) ) {
                alt38=1;
            }
            switch (alt38) {
                case 1 :
                    // BONSTTreeWalker.g:284:18: o+= indexing
                    {
                    pushFollow(FOLLOW_indexing_in_event_chart4306);
                    o=indexing();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:285:17: (o+= explanation )?
            int alt39=2;
            int LA39_0 = input.LA(1);

            if ( (LA39_0==EXPLANATION) ) {
                alt39=1;
            }
            switch (alt39) {
                case 1 :
                    // BONSTTreeWalker.g:285:18: o+= explanation
                    {
                    pushFollow(FOLLOW_explanation_in_event_chart4329);
                    o=explanation();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:286:17: (o+= part )?
            int alt40=2;
            int LA40_0 = input.LA(1);

            if ( (LA40_0==PART) ) {
                alt40=1;
            }
            switch (alt40) {
                case 1 :
                    // BONSTTreeWalker.g:286:18: o+= part
                    {
                    pushFollow(FOLLOW_part_in_event_chart4352);
                    o=part();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:287:17: (o+= event_entries )?
            int alt41=2;
            int LA41_0 = input.LA(1);

            if ( (LA41_0==EVENT_ENTRIES) ) {
                alt41=1;
            }
            switch (alt41) {
                case 1 :
                    // BONSTTreeWalker.g:287:18: o+= event_entries
                    {
                    pushFollow(FOLLOW_event_entries_in_event_chart4375);
                    o=event_entries();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 289:15: -> eventChart(name=$system_name.stk=$kother=$o)
            {
                retval.st = templateLib.getInstanceOf("eventChart",
              new STAttrMap().put("name", system_name40.st).put("k", list_k).put("other", list_o));
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
    // $ANTLR end event_chart

    public static class event_entries_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start event_entries
    // BONSTTreeWalker.g:293:1: event_entries : ^( EVENT_ENTRIES (l+= event_entry )+ ) -> eventEntries(e=$l);
    public final event_entries_return event_entries() throws RecognitionException {
        event_entries_return retval = new event_entries_return();
        retval.start = input.LT(1);

        List list_l=null;
        RuleReturnScope l = null;
        try {
            // BONSTTreeWalker.g:293:16: ( ^( EVENT_ENTRIES (l+= event_entry )+ ) -> eventEntries(e=$l))
            // BONSTTreeWalker.g:293:17: ^( EVENT_ENTRIES (l+= event_entry )+ )
            {
            match(input,EVENT_ENTRIES,FOLLOW_EVENT_ENTRIES_in_event_entries4496); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:295:19: (l+= event_entry )+
            int cnt42=0;
            loop42:
            do {
                int alt42=2;
                int LA42_0 = input.LA(1);

                if ( (LA42_0==EVENT_ENTRY) ) {
                    alt42=1;
                }


                switch (alt42) {
            	case 1 :
            	    // BONSTTreeWalker.g:295:20: l+= event_entry
            	    {
            	    pushFollow(FOLLOW_event_entry_in_event_entries4519);
            	    l=event_entry();
            	    _fsp--;

            	    if (list_l==null) list_l=new ArrayList();
            	    list_l.add(l.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt42 >= 1 ) break loop42;
                        EarlyExitException eee =
                            new EarlyExitException(42, input);
                        throw eee;
                }
                cnt42++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 297:17: -> eventEntries(e=$l)
            {
                retval.st = templateLib.getInstanceOf("eventEntries",
              new STAttrMap().put("e", list_l));
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
    // $ANTLR end event_entries

    public static class event_entry_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start event_entry
    // BONSTTreeWalker.g:301:1: event_entry : ( ^( EVENT_ENTRY manifest_textblock class_name_list ) -> eventEntry(name=$manifest_textblock.textcnl=$class_name_list.st) | ^( EVENT_ENTRY PARSE_ERROR ) );
    public final event_entry_return event_entry() throws RecognitionException {
        event_entry_return retval = new event_entry_return();
        retval.start = input.LT(1);

        manifest_textblock_return manifest_textblock41 = null;

        class_name_list_return class_name_list42 = null;


        try {
            // BONSTTreeWalker.g:301:14: ( ^( EVENT_ENTRY manifest_textblock class_name_list ) -> eventEntry(name=$manifest_textblock.textcnl=$class_name_list.st) | ^( EVENT_ENTRY PARSE_ERROR ) )
            int alt43=2;
            int LA43_0 = input.LA(1);

            if ( (LA43_0==EVENT_ENTRY) ) {
                int LA43_1 = input.LA(2);

                if ( (LA43_1==DOWN) ) {
                    int LA43_2 = input.LA(3);

                    if ( (LA43_2==PARSE_ERROR) ) {
                        alt43=2;
                    }
                    else if ( (LA43_2==MANIFEST_STRING||LA43_2==MANIFEST_TEXTBLOCK_START) ) {
                        alt43=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("301:1: event_entry : ( ^( EVENT_ENTRY manifest_textblock class_name_list ) -> eventEntry(name=$manifest_textblock.textcnl=$class_name_list.st) | ^( EVENT_ENTRY PARSE_ERROR ) );", 43, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("301:1: event_entry : ( ^( EVENT_ENTRY manifest_textblock class_name_list ) -> eventEntry(name=$manifest_textblock.textcnl=$class_name_list.st) | ^( EVENT_ENTRY PARSE_ERROR ) );", 43, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("301:1: event_entry : ( ^( EVENT_ENTRY manifest_textblock class_name_list ) -> eventEntry(name=$manifest_textblock.textcnl=$class_name_list.st) | ^( EVENT_ENTRY PARSE_ERROR ) );", 43, 0, input);

                throw nvae;
            }
            switch (alt43) {
                case 1 :
                    // BONSTTreeWalker.g:301:15: ^( EVENT_ENTRY manifest_textblock class_name_list )
                    {
                    match(input,EVENT_ENTRY,FOLLOW_EVENT_ENTRY_in_event_entry4640); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_manifest_textblock_in_event_entry4658);
                    manifest_textblock41=manifest_textblock();
                    _fsp--;

                    pushFollow(FOLLOW_class_name_list_in_event_entry4676);
                    class_name_list42=class_name_list();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 306:15: -> eventEntry(name=$manifest_textblock.textcnl=$class_name_list.st)
                    {
                        retval.st = templateLib.getInstanceOf("eventEntry",
                      new STAttrMap().put("name", input.getTokenStream().toString(
                      input.getTreeAdaptor().getTokenStartIndex(manifest_textblock41.start),
                      input.getTreeAdaptor().getTokenStopIndex(manifest_textblock41.start))).put("cnl", class_name_list42.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:309:15: ^( EVENT_ENTRY PARSE_ERROR )
                    {
                    match(input,EVENT_ENTRY,FOLLOW_EVENT_ENTRY_in_event_entry4769); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_event_entry4771); 

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
    // $ANTLR end event_entry

    public static class scenario_chart_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start scenario_chart
    // BONSTTreeWalker.g:312:1: scenario_chart : ^( SCENARIO_CHART system_name (o+= indexing )? (o+= explanation )? (o+= part )? (o+= scenario_entries )? ) -> scenarioChart(name=$system_name.stother=$o);
    public final scenario_chart_return scenario_chart() throws RecognitionException {
        scenario_chart_return retval = new scenario_chart_return();
        retval.start = input.LT(1);

        List list_o=null;
        system_name_return system_name43 = null;

        RuleReturnScope o = null;
        try {
            // BONSTTreeWalker.g:314:17: ( ^( SCENARIO_CHART system_name (o+= indexing )? (o+= explanation )? (o+= part )? (o+= scenario_entries )? ) -> scenarioChart(name=$system_name.stother=$o))
            // BONSTTreeWalker.g:314:18: ^( SCENARIO_CHART system_name (o+= indexing )? (o+= explanation )? (o+= part )? (o+= scenario_entries )? )
            {
            match(input,SCENARIO_CHART,FOLLOW_SCENARIO_CHART_in_scenario_chart4819); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_system_name_in_scenario_chart4840);
            system_name43=system_name();
            _fsp--;

            // BONSTTreeWalker.g:317:20: (o+= indexing )?
            int alt44=2;
            int LA44_0 = input.LA(1);

            if ( (LA44_0==INDEXING) ) {
                alt44=1;
            }
            switch (alt44) {
                case 1 :
                    // BONSTTreeWalker.g:317:21: o+= indexing
                    {
                    pushFollow(FOLLOW_indexing_in_scenario_chart4864);
                    o=indexing();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:318:20: (o+= explanation )?
            int alt45=2;
            int LA45_0 = input.LA(1);

            if ( (LA45_0==EXPLANATION) ) {
                alt45=1;
            }
            switch (alt45) {
                case 1 :
                    // BONSTTreeWalker.g:318:21: o+= explanation
                    {
                    pushFollow(FOLLOW_explanation_in_scenario_chart4890);
                    o=explanation();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:319:20: (o+= part )?
            int alt46=2;
            int LA46_0 = input.LA(1);

            if ( (LA46_0==PART) ) {
                alt46=1;
            }
            switch (alt46) {
                case 1 :
                    // BONSTTreeWalker.g:319:21: o+= part
                    {
                    pushFollow(FOLLOW_part_in_scenario_chart4916);
                    o=part();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:320:20: (o+= scenario_entries )?
            int alt47=2;
            int LA47_0 = input.LA(1);

            if ( (LA47_0==SCENARIO_ENTRIES) ) {
                alt47=1;
            }
            switch (alt47) {
                case 1 :
                    // BONSTTreeWalker.g:320:21: o+= scenario_entries
                    {
                    pushFollow(FOLLOW_scenario_entries_in_scenario_chart4942);
                    o=scenario_entries();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 322:18: -> scenarioChart(name=$system_name.stother=$o)
            {
                retval.st = templateLib.getInstanceOf("scenarioChart",
              new STAttrMap().put("name", system_name43.st).put("other", list_o));
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
    // $ANTLR end scenario_chart

    public static class scenario_entries_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start scenario_entries
    // BONSTTreeWalker.g:326:1: scenario_entries : ^( SCENARIO_ENTRIES (l+= scenario_entry )+ ) -> scenarioEntries(e=$l);
    public final scenario_entries_return scenario_entries() throws RecognitionException {
        scenario_entries_return retval = new scenario_entries_return();
        retval.start = input.LT(1);

        List list_l=null;
        RuleReturnScope l = null;
        try {
            // BONSTTreeWalker.g:326:19: ( ^( SCENARIO_ENTRIES (l+= scenario_entry )+ ) -> scenarioEntries(e=$l))
            // BONSTTreeWalker.g:326:20: ^( SCENARIO_ENTRIES (l+= scenario_entry )+ )
            {
            match(input,SCENARIO_ENTRIES,FOLLOW_SCENARIO_ENTRIES_in_scenario_entries5077); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:328:22: (l+= scenario_entry )+
            int cnt48=0;
            loop48:
            do {
                int alt48=2;
                int LA48_0 = input.LA(1);

                if ( (LA48_0==SCENARIO_ENTRY) ) {
                    alt48=1;
                }


                switch (alt48) {
            	case 1 :
            	    // BONSTTreeWalker.g:328:23: l+= scenario_entry
            	    {
            	    pushFollow(FOLLOW_scenario_entry_in_scenario_entries5103);
            	    l=scenario_entry();
            	    _fsp--;

            	    if (list_l==null) list_l=new ArrayList();
            	    list_l.add(l.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt48 >= 1 ) break loop48;
                        EarlyExitException eee =
                            new EarlyExitException(48, input);
                        throw eee;
                }
                cnt48++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 330:20: -> scenarioEntries(e=$l)
            {
                retval.st = templateLib.getInstanceOf("scenarioEntries",
              new STAttrMap().put("e", list_l));
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
    // $ANTLR end scenario_entries

    public static class scenario_entry_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start scenario_entry
    // BONSTTreeWalker.g:334:1: scenario_entry : ^( SCENARIO_ENTRY MANIFEST_STRING description ) -> scenarioEntry(s=$MANIFEST_STRING.textd=$description.st);
    public final scenario_entry_return scenario_entry() throws RecognitionException {
        scenario_entry_return retval = new scenario_entry_return();
        retval.start = input.LT(1);

        CommonTree MANIFEST_STRING44=null;
        description_return description45 = null;


        try {
            // BONSTTreeWalker.g:334:17: ( ^( SCENARIO_ENTRY MANIFEST_STRING description ) -> scenarioEntry(s=$MANIFEST_STRING.textd=$description.st))
            // BONSTTreeWalker.g:334:18: ^( SCENARIO_ENTRY MANIFEST_STRING description )
            {
            match(input,SCENARIO_ENTRY,FOLLOW_SCENARIO_ENTRY_in_scenario_entry5265); 

            match(input, Token.DOWN, null); 
            MANIFEST_STRING44=(CommonTree)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_scenario_entry5286); 
            pushFollow(FOLLOW_description_in_scenario_entry5288);
            description45=description();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 338:18: -> scenarioEntry(s=$MANIFEST_STRING.textd=$description.st)
            {
                retval.st = templateLib.getInstanceOf("scenarioEntry",
              new STAttrMap().put("s", MANIFEST_STRING44.getText()).put("d", description45.st));
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
    // $ANTLR end scenario_entry

    public static class creation_chart_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start creation_chart
    // BONSTTreeWalker.g:342:1: creation_chart : ^( CREATION_CHART system_name (o+= indexing )? (o+= explanation )? (o+= part )? (o+= creation_entries )? ) -> creationChart(name=$system_name.stother=$o);
    public final creation_chart_return creation_chart() throws RecognitionException {
        creation_chart_return retval = new creation_chart_return();
        retval.start = input.LT(1);

        List list_o=null;
        system_name_return system_name46 = null;

        RuleReturnScope o = null;
        try {
            // BONSTTreeWalker.g:344:17: ( ^( CREATION_CHART system_name (o+= indexing )? (o+= explanation )? (o+= part )? (o+= creation_entries )? ) -> creationChart(name=$system_name.stother=$o))
            // BONSTTreeWalker.g:344:18: ^( CREATION_CHART system_name (o+= indexing )? (o+= explanation )? (o+= part )? (o+= creation_entries )? )
            {
            match(input,CREATION_CHART,FOLLOW_CREATION_CHART_in_creation_chart5407); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_system_name_in_creation_chart5428);
            system_name46=system_name();
            _fsp--;

            // BONSTTreeWalker.g:347:20: (o+= indexing )?
            int alt49=2;
            int LA49_0 = input.LA(1);

            if ( (LA49_0==INDEXING) ) {
                alt49=1;
            }
            switch (alt49) {
                case 1 :
                    // BONSTTreeWalker.g:347:21: o+= indexing
                    {
                    pushFollow(FOLLOW_indexing_in_creation_chart5452);
                    o=indexing();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:348:20: (o+= explanation )?
            int alt50=2;
            int LA50_0 = input.LA(1);

            if ( (LA50_0==EXPLANATION) ) {
                alt50=1;
            }
            switch (alt50) {
                case 1 :
                    // BONSTTreeWalker.g:348:21: o+= explanation
                    {
                    pushFollow(FOLLOW_explanation_in_creation_chart5478);
                    o=explanation();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:349:20: (o+= part )?
            int alt51=2;
            int LA51_0 = input.LA(1);

            if ( (LA51_0==PART) ) {
                alt51=1;
            }
            switch (alt51) {
                case 1 :
                    // BONSTTreeWalker.g:349:21: o+= part
                    {
                    pushFollow(FOLLOW_part_in_creation_chart5504);
                    o=part();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:350:20: (o+= creation_entries )?
            int alt52=2;
            int LA52_0 = input.LA(1);

            if ( (LA52_0==CREATION_ENTRIES) ) {
                alt52=1;
            }
            switch (alt52) {
                case 1 :
                    // BONSTTreeWalker.g:350:21: o+= creation_entries
                    {
                    pushFollow(FOLLOW_creation_entries_in_creation_chart5530);
                    o=creation_entries();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 352:18: -> creationChart(name=$system_name.stother=$o)
            {
                retval.st = templateLib.getInstanceOf("creationChart",
              new STAttrMap().put("name", system_name46.st).put("other", list_o));
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
    // $ANTLR end creation_chart

    public static class creation_entries_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start creation_entries
    // BONSTTreeWalker.g:356:1: creation_entries : ^( CREATION_ENTRIES (l+= creation_entry )+ ) -> creationEntries(l=$l);
    public final creation_entries_return creation_entries() throws RecognitionException {
        creation_entries_return retval = new creation_entries_return();
        retval.start = input.LT(1);

        List list_l=null;
        RuleReturnScope l = null;
        try {
            // BONSTTreeWalker.g:356:19: ( ^( CREATION_ENTRIES (l+= creation_entry )+ ) -> creationEntries(l=$l))
            // BONSTTreeWalker.g:356:20: ^( CREATION_ENTRIES (l+= creation_entry )+ )
            {
            match(input,CREATION_ENTRIES,FOLLOW_CREATION_ENTRIES_in_creation_entries5665); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:358:22: (l+= creation_entry )+
            int cnt53=0;
            loop53:
            do {
                int alt53=2;
                int LA53_0 = input.LA(1);

                if ( (LA53_0==CREATION_ENTRY) ) {
                    alt53=1;
                }


                switch (alt53) {
            	case 1 :
            	    // BONSTTreeWalker.g:358:23: l+= creation_entry
            	    {
            	    pushFollow(FOLLOW_creation_entry_in_creation_entries5691);
            	    l=creation_entry();
            	    _fsp--;

            	    if (list_l==null) list_l=new ArrayList();
            	    list_l.add(l.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt53 >= 1 ) break loop53;
                        EarlyExitException eee =
                            new EarlyExitException(53, input);
                        throw eee;
                }
                cnt53++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 360:20: -> creationEntries(l=$l)
            {
                retval.st = templateLib.getInstanceOf("creationEntries",
              new STAttrMap().put("l", list_l));
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
    // $ANTLR end creation_entries

    public static class creation_entry_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start creation_entry
    // BONSTTreeWalker.g:364:1: creation_entry : ^( CREATION_ENTRY class_name class_name_list ) -> creationEntry(name=$class_name.stcnl=$class_name_list.st);
    public final creation_entry_return creation_entry() throws RecognitionException {
        creation_entry_return retval = new creation_entry_return();
        retval.start = input.LT(1);

        class_name_return class_name47 = null;

        class_name_list_return class_name_list48 = null;


        try {
            // BONSTTreeWalker.g:364:17: ( ^( CREATION_ENTRY class_name class_name_list ) -> creationEntry(name=$class_name.stcnl=$class_name_list.st))
            // BONSTTreeWalker.g:364:18: ^( CREATION_ENTRY class_name class_name_list )
            {
            match(input,CREATION_ENTRY,FOLLOW_CREATION_ENTRY_in_creation_entry5830); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_class_name_in_creation_entry5851);
            class_name47=class_name();
            _fsp--;

            pushFollow(FOLLOW_class_name_list_in_creation_entry5873);
            class_name_list48=class_name_list();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 369:18: -> creationEntry(name=$class_name.stcnl=$class_name_list.st)
            {
                retval.st = templateLib.getInstanceOf("creationEntry",
              new STAttrMap().put("name", class_name47.st).put("cnl", class_name_list48.st));
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
    // $ANTLR end creation_entry

    public static class static_diagram_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start static_diagram
    // BONSTTreeWalker.g:373:1: static_diagram : ^( STATIC_DIAGRAM (p+= extended_id )? ( COMMENT )? (s+= static_block )? ) -> staticDiagram(ps=$psb=$s);
    public final static_diagram_return static_diagram() throws RecognitionException {
        static_diagram_return retval = new static_diagram_return();
        retval.start = input.LT(1);

        List list_p=null;
        List list_s=null;
        RuleReturnScope p = null;
        RuleReturnScope s = null;
        try {
            // BONSTTreeWalker.g:377:17: ( ^( STATIC_DIAGRAM (p+= extended_id )? ( COMMENT )? (s+= static_block )? ) -> staticDiagram(ps=$psb=$s))
            // BONSTTreeWalker.g:377:18: ^( STATIC_DIAGRAM (p+= extended_id )? ( COMMENT )? (s+= static_block )? )
            {
            match(input,STATIC_DIAGRAM,FOLLOW_STATIC_DIAGRAM_in_static_diagram5994); 

            if ( input.LA(1)==Token.DOWN ) {
                match(input, Token.DOWN, null); 
                // BONSTTreeWalker.g:379:20: (p+= extended_id )?
                int alt54=2;
                int LA54_0 = input.LA(1);

                if ( (LA54_0==EXTENDED_ID) ) {
                    alt54=1;
                }
                switch (alt54) {
                    case 1 :
                        // BONSTTreeWalker.g:379:21: p+= extended_id
                        {
                        pushFollow(FOLLOW_extended_id_in_static_diagram6018);
                        p=extended_id();
                        _fsp--;

                        if (list_p==null) list_p=new ArrayList();
                        list_p.add(p.getTemplate());


                        }
                        break;

                }

                // BONSTTreeWalker.g:379:38: ( COMMENT )?
                int alt55=2;
                int LA55_0 = input.LA(1);

                if ( (LA55_0==COMMENT) ) {
                    alt55=1;
                }
                switch (alt55) {
                    case 1 :
                        // BONSTTreeWalker.g:379:39: COMMENT
                        {
                        match(input,COMMENT,FOLLOW_COMMENT_in_static_diagram6023); 

                        }
                        break;

                }

                // BONSTTreeWalker.g:380:20: (s+= static_block )?
                int alt56=2;
                int LA56_0 = input.LA(1);

                if ( (LA56_0==STATIC_BLOCK) ) {
                    alt56=1;
                }
                switch (alt56) {
                    case 1 :
                        // BONSTTreeWalker.g:380:21: s+= static_block
                        {
                        pushFollow(FOLLOW_static_block_in_static_diagram6051);
                        s=static_block();
                        _fsp--;

                        if (list_s==null) list_s=new ArrayList();
                        list_s.add(s.getTemplate());


                        }
                        break;

                }


                match(input, Token.UP, null); 
            }

            // TEMPLATE REWRITE
            // 382:18: -> staticDiagram(ps=$psb=$s)
            {
                retval.st = templateLib.getInstanceOf("staticDiagram",
              new STAttrMap().put("ps", list_p).put("sb", list_s));
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
    // $ANTLR end static_diagram

    public static class extended_id_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start extended_id
    // BONSTTreeWalker.g:386:1: extended_id : ( ^( EXTENDED_ID IDENTIFIER ) -> extendedID(s=$IDENTIFIER.text) | ^( EXTENDED_ID INTEGER ) -> extendedID(s=$INTEGER.text));
    public final extended_id_return extended_id() throws RecognitionException {
        extended_id_return retval = new extended_id_return();
        retval.start = input.LT(1);

        CommonTree IDENTIFIER49=null;
        CommonTree INTEGER50=null;

        try {
            // BONSTTreeWalker.g:386:14: ( ^( EXTENDED_ID IDENTIFIER ) -> extendedID(s=$IDENTIFIER.text) | ^( EXTENDED_ID INTEGER ) -> extendedID(s=$INTEGER.text))
            int alt57=2;
            int LA57_0 = input.LA(1);

            if ( (LA57_0==EXTENDED_ID) ) {
                int LA57_1 = input.LA(2);

                if ( (LA57_1==DOWN) ) {
                    int LA57_2 = input.LA(3);

                    if ( (LA57_2==INTEGER) ) {
                        alt57=2;
                    }
                    else if ( (LA57_2==IDENTIFIER) ) {
                        alt57=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("386:1: extended_id : ( ^( EXTENDED_ID IDENTIFIER ) -> extendedID(s=$IDENTIFIER.text) | ^( EXTENDED_ID INTEGER ) -> extendedID(s=$INTEGER.text));", 57, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("386:1: extended_id : ( ^( EXTENDED_ID IDENTIFIER ) -> extendedID(s=$IDENTIFIER.text) | ^( EXTENDED_ID INTEGER ) -> extendedID(s=$INTEGER.text));", 57, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("386:1: extended_id : ( ^( EXTENDED_ID IDENTIFIER ) -> extendedID(s=$IDENTIFIER.text) | ^( EXTENDED_ID INTEGER ) -> extendedID(s=$INTEGER.text));", 57, 0, input);

                throw nvae;
            }
            switch (alt57) {
                case 1 :
                    // BONSTTreeWalker.g:386:15: ^( EXTENDED_ID IDENTIFIER )
                    {
                    match(input,EXTENDED_ID,FOLLOW_EXTENDED_ID_in_extended_id6182); 

                    match(input, Token.DOWN, null); 
                    IDENTIFIER49=(CommonTree)input.LT(1);
                    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_extended_id6184); 

                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 389:15: -> extendedID(s=$IDENTIFIER.text)
                    {
                        retval.st = templateLib.getInstanceOf("extendedID",
                      new STAttrMap().put("s", IDENTIFIER49.getText()));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:392:15: ^( EXTENDED_ID INTEGER )
                    {
                    match(input,EXTENDED_ID,FOLLOW_EXTENDED_ID_in_extended_id6290); 

                    match(input, Token.DOWN, null); 
                    INTEGER50=(CommonTree)input.LT(1);
                    match(input,INTEGER,FOLLOW_INTEGER_in_extended_id6292); 

                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 395:15: -> extendedID(s=$INTEGER.text)
                    {
                        retval.st = templateLib.getInstanceOf("extendedID",
                      new STAttrMap().put("s", INTEGER50.getText()));
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
        return retval;
    }
    // $ANTLR end extended_id

    public static class static_block_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start static_block
    // BONSTTreeWalker.g:399:1: static_block : ^( STATIC_BLOCK (c+= static_component )+ ) -> staticBlock(cs=$c);
    public final static_block_return static_block() throws RecognitionException {
        static_block_return retval = new static_block_return();
        retval.start = input.LT(1);

        List list_c=null;
        RuleReturnScope c = null;
        try {
            // BONSTTreeWalker.g:399:15: ( ^( STATIC_BLOCK (c+= static_component )+ ) -> staticBlock(cs=$c))
            // BONSTTreeWalker.g:399:16: ^( STATIC_BLOCK (c+= static_component )+ )
            {
            match(input,STATIC_BLOCK,FOLLOW_STATIC_BLOCK_in_static_block6402); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:400:31: (c+= static_component )+
            int cnt58=0;
            loop58:
            do {
                int alt58=2;
                int LA58_0 = input.LA(1);

                if ( (LA58_0==STATIC_COMPONENT) ) {
                    alt58=1;
                }


                switch (alt58) {
            	case 1 :
            	    // BONSTTreeWalker.g:400:32: c+= static_component
            	    {
            	    pushFollow(FOLLOW_static_component_in_static_block6407);
            	    c=static_component();
            	    _fsp--;

            	    if (list_c==null) list_c=new ArrayList();
            	    list_c.add(c.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt58 >= 1 ) break loop58;
                        EarlyExitException eee =
                            new EarlyExitException(58, input);
                        throw eee;
                }
                cnt58++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 402:16: -> staticBlock(cs=$c)
            {
                retval.st = templateLib.getInstanceOf("staticBlock",
              new STAttrMap().put("cs", list_c));
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
    // $ANTLR end static_block

    public static class static_component_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start static_component
    // BONSTTreeWalker.g:407:1: static_component : ( ^( STATIC_COMPONENT cluster ) -> staticComponent(sc=$cluster.st) | ^( STATIC_COMPONENT classX ) -> staticComponent(sc=$classX.st) | ^( STATIC_COMPONENT static_relation ) -> staticComponent(sc=$static_relation.st));
    public final static_component_return static_component() throws RecognitionException {
        static_component_return retval = new static_component_return();
        retval.start = input.LT(1);

        cluster_return cluster51 = null;

        classX_return classX52 = null;

        static_relation_return static_relation53 = null;


        try {
            // BONSTTreeWalker.g:407:19: ( ^( STATIC_COMPONENT cluster ) -> staticComponent(sc=$cluster.st) | ^( STATIC_COMPONENT classX ) -> staticComponent(sc=$classX.st) | ^( STATIC_COMPONENT static_relation ) -> staticComponent(sc=$static_relation.st))
            int alt59=3;
            int LA59_0 = input.LA(1);

            if ( (LA59_0==STATIC_COMPONENT) ) {
                int LA59_1 = input.LA(2);

                if ( (LA59_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case CLASS:
                        {
                        alt59=2;
                        }
                        break;
                    case STATIC_RELATION:
                        {
                        alt59=3;
                        }
                        break;
                    case CLUSTER:
                        {
                        alt59=1;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("407:1: static_component : ( ^( STATIC_COMPONENT cluster ) -> staticComponent(sc=$cluster.st) | ^( STATIC_COMPONENT classX ) -> staticComponent(sc=$classX.st) | ^( STATIC_COMPONENT static_relation ) -> staticComponent(sc=$static_relation.st));", 59, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("407:1: static_component : ( ^( STATIC_COMPONENT cluster ) -> staticComponent(sc=$cluster.st) | ^( STATIC_COMPONENT classX ) -> staticComponent(sc=$classX.st) | ^( STATIC_COMPONENT static_relation ) -> staticComponent(sc=$static_relation.st));", 59, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("407:1: static_component : ( ^( STATIC_COMPONENT cluster ) -> staticComponent(sc=$cluster.st) | ^( STATIC_COMPONENT classX ) -> staticComponent(sc=$classX.st) | ^( STATIC_COMPONENT static_relation ) -> staticComponent(sc=$static_relation.st));", 59, 0, input);

                throw nvae;
            }
            switch (alt59) {
                case 1 :
                    // BONSTTreeWalker.g:407:21: ^( STATIC_COMPONENT cluster )
                    {
                    match(input,STATIC_COMPONENT,FOLLOW_STATIC_COMPONENT_in_static_component6517); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_cluster_in_static_component6519);
                    cluster51=cluster();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 410:21: -> staticComponent(sc=$cluster.st)
                    {
                        retval.st = templateLib.getInstanceOf("staticComponent",
                      new STAttrMap().put("sc", cluster51.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:413:21: ^( STATIC_COMPONENT classX )
                    {
                    match(input,STATIC_COMPONENT,FOLLOW_STATIC_COMPONENT_in_static_component6661); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_classX_in_static_component6663);
                    classX52=classX();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 416:21: -> staticComponent(sc=$classX.st)
                    {
                        retval.st = templateLib.getInstanceOf("staticComponent",
                      new STAttrMap().put("sc", classX52.st));
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:419:21: ^( STATIC_COMPONENT static_relation )
                    {
                    match(input,STATIC_COMPONENT,FOLLOW_STATIC_COMPONENT_in_static_component6805); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_static_relation_in_static_component6807);
                    static_relation53=static_relation();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 422:21: -> staticComponent(sc=$static_relation.st)
                    {
                        retval.st = templateLib.getInstanceOf("staticComponent",
                      new STAttrMap().put("sc", static_relation53.st));
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
        return retval;
    }
    // $ANTLR end static_component

    public static class cluster_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start cluster
    // BONSTTreeWalker.g:426:1: cluster : ^( CLUSTER cluster_name (k+= 'reused' )? ( COMMENT )? (o+= cluster_components )? ) -> cluster(name=$cluster_name.stkey=$kcomponents=$o);
    public final cluster_return cluster() throws RecognitionException {
        cluster_return retval = new cluster_return();
        retval.start = input.LT(1);

        CommonTree k=null;
        List list_k=null;
        List list_o=null;
        cluster_name_return cluster_name54 = null;

        RuleReturnScope o = null;
        try {
            // BONSTTreeWalker.g:428:10: ( ^( CLUSTER cluster_name (k+= 'reused' )? ( COMMENT )? (o+= cluster_components )? ) -> cluster(name=$cluster_name.stkey=$kcomponents=$o))
            // BONSTTreeWalker.g:428:11: ^( CLUSTER cluster_name (k+= 'reused' )? ( COMMENT )? (o+= cluster_components )? )
            {
            match(input,CLUSTER,FOLLOW_CLUSTER_in_cluster6925); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_cluster_name_in_cluster6927);
            cluster_name54=cluster_name();
            _fsp--;

            // BONSTTreeWalker.g:430:13: (k+= 'reused' )?
            int alt60=2;
            int LA60_0 = input.LA(1);

            if ( (LA60_0==216) ) {
                alt60=1;
            }
            switch (alt60) {
                case 1 :
                    // BONSTTreeWalker.g:430:14: k+= 'reused'
                    {
                    k=(CommonTree)input.LT(1);
                    match(input,216,FOLLOW_216_in_cluster6944); 
                    if (list_k==null) list_k=new ArrayList();
                    list_k.add(k);


                    }
                    break;

            }

            // BONSTTreeWalker.g:430:28: ( COMMENT )?
            int alt61=2;
            int LA61_0 = input.LA(1);

            if ( (LA61_0==COMMENT) ) {
                alt61=1;
            }
            switch (alt61) {
                case 1 :
                    // BONSTTreeWalker.g:430:29: COMMENT
                    {
                    match(input,COMMENT,FOLLOW_COMMENT_in_cluster6949); 

                    }
                    break;

            }

            // BONSTTreeWalker.g:431:13: (o+= cluster_components )?
            int alt62=2;
            int LA62_0 = input.LA(1);

            if ( (LA62_0==CLUSTER_COMPONENTS) ) {
                alt62=1;
            }
            switch (alt62) {
                case 1 :
                    // BONSTTreeWalker.g:431:14: o+= cluster_components
                    {
                    pushFollow(FOLLOW_cluster_components_in_cluster6969);
                    o=cluster_components();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 433:11: -> cluster(name=$cluster_name.stkey=$kcomponents=$o)
            {
                retval.st = templateLib.getInstanceOf("cluster",
              new STAttrMap().put("name", cluster_name54.st).put("key", list_k).put("components", list_o));
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
    // $ANTLR end cluster

    public static class cluster_components_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start cluster_components
    // BONSTTreeWalker.g:437:1: cluster_components : ^( CLUSTER_COMPONENTS (o+= static_block )? ) -> clusterComponents(block=$o);
    public final cluster_components_return cluster_components() throws RecognitionException {
        cluster_components_return retval = new cluster_components_return();
        retval.start = input.LT(1);

        List list_o=null;
        RuleReturnScope o = null;
        try {
            // BONSTTreeWalker.g:437:21: ( ^( CLUSTER_COMPONENTS (o+= static_block )? ) -> clusterComponents(block=$o))
            // BONSTTreeWalker.g:437:22: ^( CLUSTER_COMPONENTS (o+= static_block )? )
            {
            match(input,CLUSTER_COMPONENTS,FOLLOW_CLUSTER_COMPONENTS_in_cluster_components7075); 

            if ( input.LA(1)==Token.DOWN ) {
                match(input, Token.DOWN, null); 
                // BONSTTreeWalker.g:438:43: (o+= static_block )?
                int alt63=2;
                int LA63_0 = input.LA(1);

                if ( (LA63_0==STATIC_BLOCK) ) {
                    alt63=1;
                }
                switch (alt63) {
                    case 1 :
                        // BONSTTreeWalker.g:438:44: o+= static_block
                        {
                        pushFollow(FOLLOW_static_block_in_cluster_components7080);
                        o=static_block();
                        _fsp--;

                        if (list_o==null) list_o=new ArrayList();
                        list_o.add(o.getTemplate());


                        }
                        break;

                }


                match(input, Token.UP, null); 
            }

            // TEMPLATE REWRITE
            // 440:22: -> clusterComponents(block=$o)
            {
                retval.st = templateLib.getInstanceOf("clusterComponents",
              new STAttrMap().put("block", list_o));
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
    // $ANTLR end cluster_components

    public static class classX_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start classX
    // BONSTTreeWalker.g:444:1: classX : ^( CLASS (k1+= 'root' )? (k1+= 'deferred' )? (k1+= 'effective' )? class_name (fg+= formal_generics )? (k2+= 'reused' )? (k2+= 'persistent' )? (k2+= 'interfaced' )? ( COMMENT )? (i+= class_interface )? ) -> classX(keywords1=$k1name=$class_name.stfgen=$fgkeywords2=$k2interface=$i);
    public final classX_return classX() throws RecognitionException {
        classX_return retval = new classX_return();
        retval.start = input.LT(1);

        CommonTree k1=null;
        CommonTree k2=null;
        List list_k1=null;
        List list_k2=null;
        List list_fg=null;
        List list_i=null;
        class_name_return class_name55 = null;

        RuleReturnScope fg = null;
        RuleReturnScope i = null;
        try {
            // BONSTTreeWalker.g:444:9: ( ^( CLASS (k1+= 'root' )? (k1+= 'deferred' )? (k1+= 'effective' )? class_name (fg+= formal_generics )? (k2+= 'reused' )? (k2+= 'persistent' )? (k2+= 'interfaced' )? ( COMMENT )? (i+= class_interface )? ) -> classX(keywords1=$k1name=$class_name.stfgen=$fgkeywords2=$k2interface=$i))
            // BONSTTreeWalker.g:444:10: ^( CLASS (k1+= 'root' )? (k1+= 'deferred' )? (k1+= 'effective' )? class_name (fg+= formal_generics )? (k2+= 'reused' )? (k2+= 'persistent' )? (k2+= 'interfaced' )? ( COMMENT )? (i+= class_interface )? )
            {
            match(input,CLASS,FOLLOW_CLASS_in_classX7222); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:446:12: (k1+= 'root' )?
            int alt64=2;
            int LA64_0 = input.LA(1);

            if ( (LA64_0==217) ) {
                alt64=1;
            }
            switch (alt64) {
                case 1 :
                    // BONSTTreeWalker.g:446:13: k1+= 'root'
                    {
                    k1=(CommonTree)input.LT(1);
                    match(input,217,FOLLOW_217_in_classX7238); 
                    if (list_k1==null) list_k1=new ArrayList();
                    list_k1.add(k1);


                    }
                    break;

            }

            // BONSTTreeWalker.g:446:26: (k1+= 'deferred' )?
            int alt65=2;
            int LA65_0 = input.LA(1);

            if ( (LA65_0==218) ) {
                alt65=1;
            }
            switch (alt65) {
                case 1 :
                    // BONSTTreeWalker.g:446:27: k1+= 'deferred'
                    {
                    k1=(CommonTree)input.LT(1);
                    match(input,218,FOLLOW_218_in_classX7245); 
                    if (list_k1==null) list_k1=new ArrayList();
                    list_k1.add(k1);


                    }
                    break;

            }

            // BONSTTreeWalker.g:446:44: (k1+= 'effective' )?
            int alt66=2;
            int LA66_0 = input.LA(1);

            if ( (LA66_0==219) ) {
                alt66=1;
            }
            switch (alt66) {
                case 1 :
                    // BONSTTreeWalker.g:446:45: k1+= 'effective'
                    {
                    k1=(CommonTree)input.LT(1);
                    match(input,219,FOLLOW_219_in_classX7252); 
                    if (list_k1==null) list_k1=new ArrayList();
                    list_k1.add(k1);


                    }
                    break;

            }

            pushFollow(FOLLOW_class_name_in_classX7268);
            class_name55=class_name();
            _fsp--;

            // BONSTTreeWalker.g:447:23: (fg+= formal_generics )?
            int alt67=2;
            int LA67_0 = input.LA(1);

            if ( (LA67_0==FORMAL_GENERICS) ) {
                alt67=1;
            }
            switch (alt67) {
                case 1 :
                    // BONSTTreeWalker.g:447:24: fg+= formal_generics
                    {
                    pushFollow(FOLLOW_formal_generics_in_classX7273);
                    fg=formal_generics();
                    _fsp--;

                    if (list_fg==null) list_fg=new ArrayList();
                    list_fg.add(fg.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:448:12: (k2+= 'reused' )?
            int alt68=2;
            int LA68_0 = input.LA(1);

            if ( (LA68_0==216) ) {
                alt68=1;
            }
            switch (alt68) {
                case 1 :
                    // BONSTTreeWalker.g:448:13: k2+= 'reused'
                    {
                    k2=(CommonTree)input.LT(1);
                    match(input,216,FOLLOW_216_in_classX7291); 
                    if (list_k2==null) list_k2=new ArrayList();
                    list_k2.add(k2);


                    }
                    break;

            }

            // BONSTTreeWalker.g:448:28: (k2+= 'persistent' )?
            int alt69=2;
            int LA69_0 = input.LA(1);

            if ( (LA69_0==220) ) {
                alt69=1;
            }
            switch (alt69) {
                case 1 :
                    // BONSTTreeWalker.g:448:29: k2+= 'persistent'
                    {
                    k2=(CommonTree)input.LT(1);
                    match(input,220,FOLLOW_220_in_classX7298); 
                    if (list_k2==null) list_k2=new ArrayList();
                    list_k2.add(k2);


                    }
                    break;

            }

            // BONSTTreeWalker.g:448:49: (k2+= 'interfaced' )?
            int alt70=2;
            int LA70_0 = input.LA(1);

            if ( (LA70_0==221) ) {
                alt70=1;
            }
            switch (alt70) {
                case 1 :
                    // BONSTTreeWalker.g:448:50: k2+= 'interfaced'
                    {
                    k2=(CommonTree)input.LT(1);
                    match(input,221,FOLLOW_221_in_classX7306); 
                    if (list_k2==null) list_k2=new ArrayList();
                    list_k2.add(k2);


                    }
                    break;

            }

            // BONSTTreeWalker.g:448:69: ( COMMENT )?
            int alt71=2;
            int LA71_0 = input.LA(1);

            if ( (LA71_0==COMMENT) ) {
                alt71=1;
            }
            switch (alt71) {
                case 1 :
                    // BONSTTreeWalker.g:448:70: COMMENT
                    {
                    match(input,COMMENT,FOLLOW_COMMENT_in_classX7311); 

                    }
                    break;

            }

            // BONSTTreeWalker.g:449:12: (i+= class_interface )?
            int alt72=2;
            int LA72_0 = input.LA(1);

            if ( (LA72_0==CLASS_INTERFACE) ) {
                alt72=1;
            }
            switch (alt72) {
                case 1 :
                    // BONSTTreeWalker.g:449:13: i+= class_interface
                    {
                    pushFollow(FOLLOW_class_interface_in_classX7329);
                    i=class_interface();
                    _fsp--;

                    if (list_i==null) list_i=new ArrayList();
                    list_i.add(i.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 451:10: -> classX(keywords1=$k1name=$class_name.stfgen=$fgkeywords2=$k2interface=$i)
            {
                retval.st = templateLib.getInstanceOf("classX",
              new STAttrMap().put("keywords1", list_k1).put("name", class_name55.st).put("fgen", list_fg).put("keywords2", list_k2).put("interface", list_i));
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
    // $ANTLR end classX

    public static class static_relation_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start static_relation
    // BONSTTreeWalker.g:455:1: static_relation : ( ^( STATIC_RELATION inheritance_relation ) -> staticRelation(r=$inheritance_relation.st) | ^( STATIC_RELATION client_relation ) -> staticRelation(r=$client_relation.st));
    public final static_relation_return static_relation() throws RecognitionException {
        static_relation_return retval = new static_relation_return();
        retval.start = input.LT(1);

        inheritance_relation_return inheritance_relation56 = null;

        client_relation_return client_relation57 = null;


        try {
            // BONSTTreeWalker.g:455:18: ( ^( STATIC_RELATION inheritance_relation ) -> staticRelation(r=$inheritance_relation.st) | ^( STATIC_RELATION client_relation ) -> staticRelation(r=$client_relation.st))
            int alt73=2;
            int LA73_0 = input.LA(1);

            if ( (LA73_0==STATIC_RELATION) ) {
                int LA73_1 = input.LA(2);

                if ( (LA73_1==DOWN) ) {
                    int LA73_2 = input.LA(3);

                    if ( (LA73_2==CLIENT_RELATION) ) {
                        alt73=2;
                    }
                    else if ( (LA73_2==INHERITENCE_RELATION) ) {
                        alt73=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("455:1: static_relation : ( ^( STATIC_RELATION inheritance_relation ) -> staticRelation(r=$inheritance_relation.st) | ^( STATIC_RELATION client_relation ) -> staticRelation(r=$client_relation.st));", 73, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("455:1: static_relation : ( ^( STATIC_RELATION inheritance_relation ) -> staticRelation(r=$inheritance_relation.st) | ^( STATIC_RELATION client_relation ) -> staticRelation(r=$client_relation.st));", 73, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("455:1: static_relation : ( ^( STATIC_RELATION inheritance_relation ) -> staticRelation(r=$inheritance_relation.st) | ^( STATIC_RELATION client_relation ) -> staticRelation(r=$client_relation.st));", 73, 0, input);

                throw nvae;
            }
            switch (alt73) {
                case 1 :
                    // BONSTTreeWalker.g:455:19: ^( STATIC_RELATION inheritance_relation )
                    {
                    match(input,STATIC_RELATION,FOLLOW_STATIC_RELATION_in_static_relation7441); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_inheritance_relation_in_static_relation7443);
                    inheritance_relation56=inheritance_relation();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 458:19: -> staticRelation(r=$inheritance_relation.st)
                    {
                        retval.st = templateLib.getInstanceOf("staticRelation",
                      new STAttrMap().put("r", inheritance_relation56.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:460:19: ^( STATIC_RELATION client_relation )
                    {
                    match(input,STATIC_RELATION,FOLLOW_STATIC_RELATION_in_static_relation7553); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_client_relation_in_static_relation7555);
                    client_relation57=client_relation();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 463:19: -> staticRelation(r=$client_relation.st)
                    {
                        retval.st = templateLib.getInstanceOf("staticRelation",
                      new STAttrMap().put("r", client_relation57.st));
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
        return retval;
    }
    // $ANTLR end static_relation

    public static class inheritance_relation_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start inheritance_relation
    // BONSTTreeWalker.g:466:1: inheritance_relation : ^( INHERITENCE_RELATION child (m+= multiplicity )? parent (s+= semantic_label )? ) -> inheritenceRelation(child=$child.stmult=$mparent=$parent.stsem=$s);
    public final inheritance_relation_return inheritance_relation() throws RecognitionException {
        inheritance_relation_return retval = new inheritance_relation_return();
        retval.start = input.LT(1);

        List list_m=null;
        List list_s=null;
        child_return child58 = null;

        parent_return parent59 = null;

        RuleReturnScope m = null;
        RuleReturnScope s = null;
        try {
            // BONSTTreeWalker.g:468:23: ( ^( INHERITENCE_RELATION child (m+= multiplicity )? parent (s+= semantic_label )? ) -> inheritenceRelation(child=$child.stmult=$mparent=$parent.stsem=$s))
            // BONSTTreeWalker.g:468:24: ^( INHERITENCE_RELATION child (m+= multiplicity )? parent (s+= semantic_label )? )
            {
            match(input,INHERITENCE_RELATION,FOLLOW_INHERITENCE_RELATION_in_inheritance_relation7659); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_child_in_inheritance_relation7686);
            child58=child();
            _fsp--;

            // BONSTTreeWalker.g:470:32: (m+= multiplicity )?
            int alt74=2;
            int LA74_0 = input.LA(1);

            if ( (LA74_0==MULTIPLICITY) ) {
                alt74=1;
            }
            switch (alt74) {
                case 1 :
                    // BONSTTreeWalker.g:470:33: m+= multiplicity
                    {
                    pushFollow(FOLLOW_multiplicity_in_inheritance_relation7691);
                    m=multiplicity();
                    _fsp--;

                    if (list_m==null) list_m=new ArrayList();
                    list_m.add(m.getTemplate());


                    }
                    break;

            }

            pushFollow(FOLLOW_parent_in_inheritance_relation7721);
            parent59=parent();
            _fsp--;

            // BONSTTreeWalker.g:471:33: (s+= semantic_label )?
            int alt75=2;
            int LA75_0 = input.LA(1);

            if ( (LA75_0==SEMANTIC_LABEL) ) {
                alt75=1;
            }
            switch (alt75) {
                case 1 :
                    // BONSTTreeWalker.g:471:34: s+= semantic_label
                    {
                    pushFollow(FOLLOW_semantic_label_in_inheritance_relation7726);
                    s=semantic_label();
                    _fsp--;

                    if (list_s==null) list_s=new ArrayList();
                    list_s.add(s.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 473:24: -> inheritenceRelation(child=$child.stmult=$mparent=$parent.stsem=$s)
            {
                retval.st = templateLib.getInstanceOf("inheritenceRelation",
              new STAttrMap().put("child", child58.st).put("mult", list_m).put("parent", parent59.st).put("sem", list_s));
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
    // $ANTLR end inheritance_relation

    public static class client_relation_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start client_relation
    // BONSTTreeWalker.g:477:1: client_relation : ^( CLIENT_RELATION client (ce+= client_entities )? (tm+= type_mark )? supplier (s+= semantic_label )? ) -> clientRelation(client=$client.stce=$cetm=$tmsupplier=$supplier.stsem=$s);
    public final client_relation_return client_relation() throws RecognitionException {
        client_relation_return retval = new client_relation_return();
        retval.start = input.LT(1);

        List list_ce=null;
        List list_tm=null;
        List list_s=null;
        client_return client60 = null;

        supplier_return supplier61 = null;

        RuleReturnScope ce = null;
        RuleReturnScope tm = null;
        RuleReturnScope s = null;
        try {
            // BONSTTreeWalker.g:477:18: ( ^( CLIENT_RELATION client (ce+= client_entities )? (tm+= type_mark )? supplier (s+= semantic_label )? ) -> clientRelation(client=$client.stce=$cetm=$tmsupplier=$supplier.stsem=$s))
            // BONSTTreeWalker.g:477:19: ^( CLIENT_RELATION client (ce+= client_entities )? (tm+= type_mark )? supplier (s+= semantic_label )? )
            {
            match(input,CLIENT_RELATION,FOLLOW_CLIENT_RELATION_in_client_relation7897); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_client_in_client_relation7919);
            client60=client();
            _fsp--;

            // BONSTTreeWalker.g:479:28: (ce+= client_entities )?
            int alt76=2;
            int LA76_0 = input.LA(1);

            if ( (LA76_0==CLIENT_ENTITIES) ) {
                alt76=1;
            }
            switch (alt76) {
                case 1 :
                    // BONSTTreeWalker.g:479:29: ce+= client_entities
                    {
                    pushFollow(FOLLOW_client_entities_in_client_relation7924);
                    ce=client_entities();
                    _fsp--;

                    if (list_ce==null) list_ce=new ArrayList();
                    list_ce.add(ce.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:479:51: (tm+= type_mark )?
            int alt77=2;
            int LA77_0 = input.LA(1);

            if ( (LA77_0==TYPE_MARK) ) {
                alt77=1;
            }
            switch (alt77) {
                case 1 :
                    // BONSTTreeWalker.g:479:52: tm+= type_mark
                    {
                    pushFollow(FOLLOW_type_mark_in_client_relation7931);
                    tm=type_mark();
                    _fsp--;

                    if (list_tm==null) list_tm=new ArrayList();
                    list_tm.add(tm.getTemplate());


                    }
                    break;

            }

            pushFollow(FOLLOW_supplier_in_client_relation7956);
            supplier61=supplier();
            _fsp--;

            // BONSTTreeWalker.g:480:30: (s+= semantic_label )?
            int alt78=2;
            int LA78_0 = input.LA(1);

            if ( (LA78_0==SEMANTIC_LABEL) ) {
                alt78=1;
            }
            switch (alt78) {
                case 1 :
                    // BONSTTreeWalker.g:480:31: s+= semantic_label
                    {
                    pushFollow(FOLLOW_semantic_label_in_client_relation7961);
                    s=semantic_label();
                    _fsp--;

                    if (list_s==null) list_s=new ArrayList();
                    list_s.add(s.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 482:19: -> clientRelation(client=$client.stce=$cetm=$tmsupplier=$supplier.stsem=$s)
            {
                retval.st = templateLib.getInstanceOf("clientRelation",
              new STAttrMap().put("client", client60.st).put("ce", list_ce).put("tm", list_tm).put("supplier", supplier61.st).put("sem", list_s));
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
    // $ANTLR end client_relation

    public static class client_entities_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start client_entities
    // BONSTTreeWalker.g:486:1: client_entities : ^( CLIENT_ENTITIES client_entity_expression ) -> clientEntities(cee=$client_entity_expression.st);
    public final client_entities_return client_entities() throws RecognitionException {
        client_entities_return retval = new client_entities_return();
        retval.start = input.LT(1);

        client_entity_expression_return client_entity_expression62 = null;


        try {
            // BONSTTreeWalker.g:486:18: ( ^( CLIENT_ENTITIES client_entity_expression ) -> clientEntities(cee=$client_entity_expression.st))
            // BONSTTreeWalker.g:486:19: ^( CLIENT_ENTITIES client_entity_expression )
            {
            match(input,CLIENT_ENTITIES,FOLLOW_CLIENT_ENTITIES_in_client_entities8113); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_client_entity_expression_in_client_entities8135);
            client_entity_expression62=client_entity_expression();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 490:19: -> clientEntities(cee=$client_entity_expression.st)
            {
                retval.st = templateLib.getInstanceOf("clientEntities",
              new STAttrMap().put("cee", client_entity_expression62.st));
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
    // $ANTLR end client_entities

    public static class client_entity_expression_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start client_entity_expression
    // BONSTTreeWalker.g:494:1: client_entity_expression : ( ^( CLIENT_ENTITY_EXPRESSION client_entity_list ) -> clientEntityExpression(e=$client_entity_list.st) | ^( CLIENT_ENTITY_EXPRESSION multiplicity ) -> clientEntityExpression(e=$multiplicity.st));
    public final client_entity_expression_return client_entity_expression() throws RecognitionException {
        client_entity_expression_return retval = new client_entity_expression_return();
        retval.start = input.LT(1);

        client_entity_list_return client_entity_list63 = null;

        multiplicity_return multiplicity64 = null;


        try {
            // BONSTTreeWalker.g:494:27: ( ^( CLIENT_ENTITY_EXPRESSION client_entity_list ) -> clientEntityExpression(e=$client_entity_list.st) | ^( CLIENT_ENTITY_EXPRESSION multiplicity ) -> clientEntityExpression(e=$multiplicity.st))
            int alt79=2;
            int LA79_0 = input.LA(1);

            if ( (LA79_0==CLIENT_ENTITY_EXPRESSION) ) {
                int LA79_1 = input.LA(2);

                if ( (LA79_1==DOWN) ) {
                    int LA79_2 = input.LA(3);

                    if ( (LA79_2==CLIENT_ENTITY_LIST) ) {
                        alt79=1;
                    }
                    else if ( (LA79_2==MULTIPLICITY) ) {
                        alt79=2;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("494:1: client_entity_expression : ( ^( CLIENT_ENTITY_EXPRESSION client_entity_list ) -> clientEntityExpression(e=$client_entity_list.st) | ^( CLIENT_ENTITY_EXPRESSION multiplicity ) -> clientEntityExpression(e=$multiplicity.st));", 79, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("494:1: client_entity_expression : ( ^( CLIENT_ENTITY_EXPRESSION client_entity_list ) -> clientEntityExpression(e=$client_entity_list.st) | ^( CLIENT_ENTITY_EXPRESSION multiplicity ) -> clientEntityExpression(e=$multiplicity.st));", 79, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("494:1: client_entity_expression : ( ^( CLIENT_ENTITY_EXPRESSION client_entity_list ) -> clientEntityExpression(e=$client_entity_list.st) | ^( CLIENT_ENTITY_EXPRESSION multiplicity ) -> clientEntityExpression(e=$multiplicity.st));", 79, 0, input);

                throw nvae;
            }
            switch (alt79) {
                case 1 :
                    // BONSTTreeWalker.g:494:28: ^( CLIENT_ENTITY_EXPRESSION client_entity_list )
                    {
                    match(input,CLIENT_ENTITY_EXPRESSION,FOLLOW_CLIENT_ENTITY_EXPRESSION_in_client_entity_expression8277); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_client_entity_list_in_client_entity_expression8279);
                    client_entity_list63=client_entity_list();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 497:28: -> clientEntityExpression(e=$client_entity_list.st)
                    {
                        retval.st = templateLib.getInstanceOf("clientEntityExpression",
                      new STAttrMap().put("e", client_entity_list63.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:500:28: ^( CLIENT_ENTITY_EXPRESSION multiplicity )
                    {
                    match(input,CLIENT_ENTITY_EXPRESSION,FOLLOW_CLIENT_ENTITY_EXPRESSION_in_client_entity_expression8463); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_multiplicity_in_client_entity_expression8465);
                    multiplicity64=multiplicity();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 503:28: -> clientEntityExpression(e=$multiplicity.st)
                    {
                        retval.st = templateLib.getInstanceOf("clientEntityExpression",
                      new STAttrMap().put("e", multiplicity64.st));
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
        return retval;
    }
    // $ANTLR end client_entity_expression

    public static class client_entity_list_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start client_entity_list
    // BONSTTreeWalker.g:507:1: client_entity_list : ^( CLIENT_ENTITY_LIST (l+= client_entity )+ ) -> clientEntityList(l=$l);
    public final client_entity_list_return client_entity_list() throws RecognitionException {
        client_entity_list_return retval = new client_entity_list_return();
        retval.start = input.LT(1);

        List list_l=null;
        RuleReturnScope l = null;
        try {
            // BONSTTreeWalker.g:507:21: ( ^( CLIENT_ENTITY_LIST (l+= client_entity )+ ) -> clientEntityList(l=$l))
            // BONSTTreeWalker.g:507:22: ^( CLIENT_ENTITY_LIST (l+= client_entity )+ )
            {
            match(input,CLIENT_ENTITY_LIST,FOLLOW_CLIENT_ENTITY_LIST_in_client_entity_list8646); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:508:43: (l+= client_entity )+
            int cnt80=0;
            loop80:
            do {
                int alt80=2;
                int LA80_0 = input.LA(1);

                if ( (LA80_0==CLIENT_ENTITY) ) {
                    alt80=1;
                }


                switch (alt80) {
            	case 1 :
            	    // BONSTTreeWalker.g:508:44: l+= client_entity
            	    {
            	    pushFollow(FOLLOW_client_entity_in_client_entity_list8651);
            	    l=client_entity();
            	    _fsp--;

            	    if (list_l==null) list_l=new ArrayList();
            	    list_l.add(l.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt80 >= 1 ) break loop80;
                        EarlyExitException eee =
                            new EarlyExitException(80, input);
                        throw eee;
                }
                cnt80++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 510:22: -> clientEntityList(l=$l)
            {
                retval.st = templateLib.getInstanceOf("clientEntityList",
              new STAttrMap().put("l", list_l));
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
    // $ANTLR end client_entity_list

    public static class client_entity_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start client_entity
    // BONSTTreeWalker.g:514:1: client_entity : ( ^( CLIENT_ENTITY prefix ) -> clientEntity(e=$prefix.st) | ^( CLIENT_ENTITY infix ) -> clientEntity(e=$infix.st) | ^( CLIENT_ENTITY supplier_indirection ) -> clientEntity(e=$supplier_indirection.st) | ^( CLIENT_ENTITY parent_indirection ) -> clientEntity(e=$parent_indirection.st));
    public final client_entity_return client_entity() throws RecognitionException {
        client_entity_return retval = new client_entity_return();
        retval.start = input.LT(1);

        prefix_return prefix65 = null;

        infix_return infix66 = null;

        supplier_indirection_return supplier_indirection67 = null;

        parent_indirection_return parent_indirection68 = null;


        try {
            // BONSTTreeWalker.g:514:16: ( ^( CLIENT_ENTITY prefix ) -> clientEntity(e=$prefix.st) | ^( CLIENT_ENTITY infix ) -> clientEntity(e=$infix.st) | ^( CLIENT_ENTITY supplier_indirection ) -> clientEntity(e=$supplier_indirection.st) | ^( CLIENT_ENTITY parent_indirection ) -> clientEntity(e=$parent_indirection.st))
            int alt81=4;
            int LA81_0 = input.LA(1);

            if ( (LA81_0==CLIENT_ENTITY) ) {
                int LA81_1 = input.LA(2);

                if ( (LA81_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case SUPPLIER_INDIRECTION:
                        {
                        alt81=3;
                        }
                        break;
                    case PREFIX:
                        {
                        alt81=1;
                        }
                        break;
                    case PARENT_INDIRECTION:
                        {
                        alt81=4;
                        }
                        break;
                    case INFIX:
                        {
                        alt81=2;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("514:1: client_entity : ( ^( CLIENT_ENTITY prefix ) -> clientEntity(e=$prefix.st) | ^( CLIENT_ENTITY infix ) -> clientEntity(e=$infix.st) | ^( CLIENT_ENTITY supplier_indirection ) -> clientEntity(e=$supplier_indirection.st) | ^( CLIENT_ENTITY parent_indirection ) -> clientEntity(e=$parent_indirection.st));", 81, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("514:1: client_entity : ( ^( CLIENT_ENTITY prefix ) -> clientEntity(e=$prefix.st) | ^( CLIENT_ENTITY infix ) -> clientEntity(e=$infix.st) | ^( CLIENT_ENTITY supplier_indirection ) -> clientEntity(e=$supplier_indirection.st) | ^( CLIENT_ENTITY parent_indirection ) -> clientEntity(e=$parent_indirection.st));", 81, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("514:1: client_entity : ( ^( CLIENT_ENTITY prefix ) -> clientEntity(e=$prefix.st) | ^( CLIENT_ENTITY infix ) -> clientEntity(e=$infix.st) | ^( CLIENT_ENTITY supplier_indirection ) -> clientEntity(e=$supplier_indirection.st) | ^( CLIENT_ENTITY parent_indirection ) -> clientEntity(e=$parent_indirection.st));", 81, 0, input);

                throw nvae;
            }
            switch (alt81) {
                case 1 :
                    // BONSTTreeWalker.g:514:19: ^( CLIENT_ENTITY prefix )
                    {
                    match(input,CLIENT_ENTITY,FOLLOW_CLIENT_ENTITY_in_client_entity8803); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_prefix_in_client_entity8805);
                    prefix65=prefix();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 517:19: -> clientEntity(e=$prefix.st)
                    {
                        retval.st = templateLib.getInstanceOf("clientEntity",
                      new STAttrMap().put("e", prefix65.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:520:19: ^( CLIENT_ENTITY infix )
                    {
                    match(input,CLIENT_ENTITY,FOLLOW_CLIENT_ENTITY_in_client_entity8936); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_infix_in_client_entity8938);
                    infix66=infix();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 523:19: -> clientEntity(e=$infix.st)
                    {
                        retval.st = templateLib.getInstanceOf("clientEntity",
                      new STAttrMap().put("e", infix66.st));
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:526:19: ^( CLIENT_ENTITY supplier_indirection )
                    {
                    match(input,CLIENT_ENTITY,FOLLOW_CLIENT_ENTITY_in_client_entity9069); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_supplier_indirection_in_client_entity9071);
                    supplier_indirection67=supplier_indirection();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 529:19: -> clientEntity(e=$supplier_indirection.st)
                    {
                        retval.st = templateLib.getInstanceOf("clientEntity",
                      new STAttrMap().put("e", supplier_indirection67.st));
                    }



                    }
                    break;
                case 4 :
                    // BONSTTreeWalker.g:532:19: ^( CLIENT_ENTITY parent_indirection )
                    {
                    match(input,CLIENT_ENTITY,FOLLOW_CLIENT_ENTITY_in_client_entity9202); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_parent_indirection_in_client_entity9204);
                    parent_indirection68=parent_indirection();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 535:19: -> clientEntity(e=$parent_indirection.st)
                    {
                        retval.st = templateLib.getInstanceOf("clientEntity",
                      new STAttrMap().put("e", parent_indirection68.st));
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
        return retval;
    }
    // $ANTLR end client_entity

    public static class supplier_indirection_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start supplier_indirection
    // BONSTTreeWalker.g:539:1: supplier_indirection : ^( SUPPLIER_INDIRECTION (ifp+= indirection_feature_part )? generic_indirection ) -> supplierIndirection(ifp=$ifpgi=$generic_indirection.st);
    public final supplier_indirection_return supplier_indirection() throws RecognitionException {
        supplier_indirection_return retval = new supplier_indirection_return();
        retval.start = input.LT(1);

        List list_ifp=null;
        generic_indirection_return generic_indirection69 = null;

        RuleReturnScope ifp = null;
        try {
            // BONSTTreeWalker.g:539:23: ( ^( SUPPLIER_INDIRECTION (ifp+= indirection_feature_part )? generic_indirection ) -> supplierIndirection(ifp=$ifpgi=$generic_indirection.st))
            // BONSTTreeWalker.g:539:24: ^( SUPPLIER_INDIRECTION (ifp+= indirection_feature_part )? generic_indirection )
            {
            match(input,SUPPLIER_INDIRECTION,FOLLOW_SUPPLIER_INDIRECTION_in_supplier_indirection9338); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:540:47: (ifp+= indirection_feature_part )?
            int alt82=2;
            int LA82_0 = input.LA(1);

            if ( (LA82_0==INDIRECTION_FEATURE_PART) ) {
                alt82=1;
            }
            switch (alt82) {
                case 1 :
                    // BONSTTreeWalker.g:540:48: ifp+= indirection_feature_part
                    {
                    pushFollow(FOLLOW_indirection_feature_part_in_supplier_indirection9343);
                    ifp=indirection_feature_part();
                    _fsp--;

                    if (list_ifp==null) list_ifp=new ArrayList();
                    list_ifp.add(ifp.getTemplate());


                    }
                    break;

            }

            pushFollow(FOLLOW_generic_indirection_in_supplier_indirection9347);
            generic_indirection69=generic_indirection();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 542:24: -> supplierIndirection(ifp=$ifpgi=$generic_indirection.st)
            {
                retval.st = templateLib.getInstanceOf("supplierIndirection",
              new STAttrMap().put("ifp", list_ifp).put("gi", generic_indirection69.st));
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
    // $ANTLR end supplier_indirection

    public static class indirection_feature_part_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start indirection_feature_part
    // BONSTTreeWalker.g:546:1: indirection_feature_part : ( ^( INDIRECTION_FEATURE_PART feature_name ) -> indirectionFeaturePart(ifp=$feature_name.st) | ^( INDIRECTION_FEATURE_PART indirection_feature_list ) -> indirectionFeaturePart(ifp=$indirection_feature_list.st));
    public final indirection_feature_part_return indirection_feature_part() throws RecognitionException {
        indirection_feature_part_return retval = new indirection_feature_part_return();
        retval.start = input.LT(1);

        feature_name_return feature_name70 = null;

        indirection_feature_list_return indirection_feature_list71 = null;


        try {
            // BONSTTreeWalker.g:546:27: ( ^( INDIRECTION_FEATURE_PART feature_name ) -> indirectionFeaturePart(ifp=$feature_name.st) | ^( INDIRECTION_FEATURE_PART indirection_feature_list ) -> indirectionFeaturePart(ifp=$indirection_feature_list.st))
            int alt83=2;
            int LA83_0 = input.LA(1);

            if ( (LA83_0==INDIRECTION_FEATURE_PART) ) {
                int LA83_1 = input.LA(2);

                if ( (LA83_1==DOWN) ) {
                    int LA83_2 = input.LA(3);

                    if ( (LA83_2==FEATURE_NAME) ) {
                        alt83=1;
                    }
                    else if ( (LA83_2==INDIRECTION_FEATURE_LIST) ) {
                        alt83=2;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("546:1: indirection_feature_part : ( ^( INDIRECTION_FEATURE_PART feature_name ) -> indirectionFeaturePart(ifp=$feature_name.st) | ^( INDIRECTION_FEATURE_PART indirection_feature_list ) -> indirectionFeaturePart(ifp=$indirection_feature_list.st));", 83, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("546:1: indirection_feature_part : ( ^( INDIRECTION_FEATURE_PART feature_name ) -> indirectionFeaturePart(ifp=$feature_name.st) | ^( INDIRECTION_FEATURE_PART indirection_feature_list ) -> indirectionFeaturePart(ifp=$indirection_feature_list.st));", 83, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("546:1: indirection_feature_part : ( ^( INDIRECTION_FEATURE_PART feature_name ) -> indirectionFeaturePart(ifp=$feature_name.st) | ^( INDIRECTION_FEATURE_PART indirection_feature_list ) -> indirectionFeaturePart(ifp=$indirection_feature_list.st));", 83, 0, input);

                throw nvae;
            }
            switch (alt83) {
                case 1 :
                    // BONSTTreeWalker.g:546:28: ^( INDIRECTION_FEATURE_PART feature_name )
                    {
                    match(input,INDIRECTION_FEATURE_PART,FOLLOW_INDIRECTION_FEATURE_PART_in_indirection_feature_part9519); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_feature_name_in_indirection_feature_part9521);
                    feature_name70=feature_name();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 549:28: -> indirectionFeaturePart(ifp=$feature_name.st)
                    {
                        retval.st = templateLib.getInstanceOf("indirectionFeaturePart",
                      new STAttrMap().put("ifp", feature_name70.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:552:28: ^( INDIRECTION_FEATURE_PART indirection_feature_list )
                    {
                    match(input,INDIRECTION_FEATURE_PART,FOLLOW_INDIRECTION_FEATURE_PART_in_indirection_feature_part9705); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_indirection_feature_list_in_indirection_feature_part9707);
                    indirection_feature_list71=indirection_feature_list();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 555:28: -> indirectionFeaturePart(ifp=$indirection_feature_list.st)
                    {
                        retval.st = templateLib.getInstanceOf("indirectionFeaturePart",
                      new STAttrMap().put("ifp", indirection_feature_list71.st));
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
        return retval;
    }
    // $ANTLR end indirection_feature_part

    public static class indirection_feature_list_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start indirection_feature_list
    // BONSTTreeWalker.g:559:1: indirection_feature_list : ^( INDIRECTION_FEATURE_LIST feature_name_list ) -> indirectionFeatureList(ifl=$feature_name_list.st);
    public final indirection_feature_list_return indirection_feature_list() throws RecognitionException {
        indirection_feature_list_return retval = new indirection_feature_list_return();
        retval.start = input.LT(1);

        feature_name_list_return feature_name_list72 = null;


        try {
            // BONSTTreeWalker.g:559:27: ( ^( INDIRECTION_FEATURE_LIST feature_name_list ) -> indirectionFeatureList(ifl=$feature_name_list.st))
            // BONSTTreeWalker.g:559:28: ^( INDIRECTION_FEATURE_LIST feature_name_list )
            {
            match(input,INDIRECTION_FEATURE_LIST,FOLLOW_INDIRECTION_FEATURE_LIST_in_indirection_feature_list9895); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_feature_name_list_in_indirection_feature_list9897);
            feature_name_list72=feature_name_list();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 562:28: -> indirectionFeatureList(ifl=$feature_name_list.st)
            {
                retval.st = templateLib.getInstanceOf("indirectionFeatureList",
              new STAttrMap().put("ifl", feature_name_list72.st));
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
    // $ANTLR end indirection_feature_list

    public static class parent_indirection_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start parent_indirection
    // BONSTTreeWalker.g:566:1: parent_indirection : ^( PARENT_INDIRECTION generic_indirection ) -> parentIndirection(pi=$generic_indirection.st);
    public final parent_indirection_return parent_indirection() throws RecognitionException {
        parent_indirection_return retval = new parent_indirection_return();
        retval.start = input.LT(1);

        generic_indirection_return generic_indirection73 = null;


        try {
            // BONSTTreeWalker.g:566:21: ( ^( PARENT_INDIRECTION generic_indirection ) -> parentIndirection(pi=$generic_indirection.st))
            // BONSTTreeWalker.g:566:22: ^( PARENT_INDIRECTION generic_indirection )
            {
            match(input,PARENT_INDIRECTION,FOLLOW_PARENT_INDIRECTION_in_parent_indirection10078); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_generic_indirection_in_parent_indirection10080);
            generic_indirection73=generic_indirection();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 569:22: -> parentIndirection(pi=$generic_indirection.st)
            {
                retval.st = templateLib.getInstanceOf("parentIndirection",
              new STAttrMap().put("pi", generic_indirection73.st));
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
    // $ANTLR end parent_indirection

    public static class generic_indirection_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start generic_indirection
    // BONSTTreeWalker.g:573:1: generic_indirection : ^( GENERIC_INDIRECTION indirection_element ) -> genericIndirection(gi=$indirection_element.st);
    public final generic_indirection_return generic_indirection() throws RecognitionException {
        generic_indirection_return retval = new generic_indirection_return();
        retval.start = input.LT(1);

        indirection_element_return indirection_element74 = null;


        try {
            // BONSTTreeWalker.g:575:22: ( ^( GENERIC_INDIRECTION indirection_element ) -> genericIndirection(gi=$indirection_element.st))
            // BONSTTreeWalker.g:582:23: ^( GENERIC_INDIRECTION indirection_element )
            {
            match(input,GENERIC_INDIRECTION,FOLLOW_GENERIC_INDIRECTION_in_generic_indirection10244); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_indirection_element_in_generic_indirection10246);
            indirection_element74=indirection_element();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 585:23: -> genericIndirection(gi=$indirection_element.st)
            {
                retval.st = templateLib.getInstanceOf("genericIndirection",
              new STAttrMap().put("gi", indirection_element74.st));
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
    // $ANTLR end generic_indirection

    public static class named_indirection_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start named_indirection
    // BONSTTreeWalker.g:589:1: named_indirection : ( ^( NAMED_INDIRECTION class_name indirection_list ) -> namedIndirection(name=$class_name.stil=$indirection_list.st) | ^( NAMED_INDIRECTION PARSE_ERROR ) );
    public final named_indirection_return named_indirection() throws RecognitionException {
        named_indirection_return retval = new named_indirection_return();
        retval.start = input.LT(1);

        class_name_return class_name75 = null;

        indirection_list_return indirection_list76 = null;


        try {
            // BONSTTreeWalker.g:589:20: ( ^( NAMED_INDIRECTION class_name indirection_list ) -> namedIndirection(name=$class_name.stil=$indirection_list.st) | ^( NAMED_INDIRECTION PARSE_ERROR ) )
            int alt84=2;
            int LA84_0 = input.LA(1);

            if ( (LA84_0==NAMED_INDIRECTION) ) {
                int LA84_1 = input.LA(2);

                if ( (LA84_1==DOWN) ) {
                    int LA84_2 = input.LA(3);

                    if ( (LA84_2==PARSE_ERROR) ) {
                        alt84=2;
                    }
                    else if ( (LA84_2==CLASS_NAME) ) {
                        alt84=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("589:1: named_indirection : ( ^( NAMED_INDIRECTION class_name indirection_list ) -> namedIndirection(name=$class_name.stil=$indirection_list.st) | ^( NAMED_INDIRECTION PARSE_ERROR ) );", 84, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("589:1: named_indirection : ( ^( NAMED_INDIRECTION class_name indirection_list ) -> namedIndirection(name=$class_name.stil=$indirection_list.st) | ^( NAMED_INDIRECTION PARSE_ERROR ) );", 84, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("589:1: named_indirection : ( ^( NAMED_INDIRECTION class_name indirection_list ) -> namedIndirection(name=$class_name.stil=$indirection_list.st) | ^( NAMED_INDIRECTION PARSE_ERROR ) );", 84, 0, input);

                throw nvae;
            }
            switch (alt84) {
                case 1 :
                    // BONSTTreeWalker.g:589:21: ^( NAMED_INDIRECTION class_name indirection_list )
                    {
                    match(input,NAMED_INDIRECTION,FOLLOW_NAMED_INDIRECTION_in_named_indirection10401); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_class_name_in_named_indirection10403);
                    class_name75=class_name();
                    _fsp--;

                    pushFollow(FOLLOW_indirection_list_in_named_indirection10405);
                    indirection_list76=indirection_list();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 592:21: -> namedIndirection(name=$class_name.stil=$indirection_list.st)
                    {
                        retval.st = templateLib.getInstanceOf("namedIndirection",
                      new STAttrMap().put("name", class_name75.st).put("il", indirection_list76.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:595:21: ^( NAMED_INDIRECTION PARSE_ERROR )
                    {
                    match(input,NAMED_INDIRECTION,FOLLOW_NAMED_INDIRECTION_in_named_indirection10529); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_named_indirection10531); 

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
    // $ANTLR end named_indirection

    public static class indirection_list_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start indirection_list
    // BONSTTreeWalker.g:598:1: indirection_list : ^( INDIRECTION_LIST (il+= indirection_element )+ ) -> indirectionList(il=$il);
    public final indirection_list_return indirection_list() throws RecognitionException {
        indirection_list_return retval = new indirection_list_return();
        retval.start = input.LT(1);

        List list_il=null;
        RuleReturnScope il = null;
        try {
            // BONSTTreeWalker.g:598:19: ( ^( INDIRECTION_LIST (il+= indirection_element )+ ) -> indirectionList(il=$il))
            // BONSTTreeWalker.g:598:20: ^( INDIRECTION_LIST (il+= indirection_element )+ )
            {
            match(input,INDIRECTION_LIST,FOLLOW_INDIRECTION_LIST_in_indirection_list10602); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:599:39: (il+= indirection_element )+
            int cnt85=0;
            loop85:
            do {
                int alt85=2;
                int LA85_0 = input.LA(1);

                if ( (LA85_0==INDIRECTION_ELEMENT) ) {
                    alt85=1;
                }


                switch (alt85) {
            	case 1 :
            	    // BONSTTreeWalker.g:599:40: il+= indirection_element
            	    {
            	    pushFollow(FOLLOW_indirection_element_in_indirection_list10607);
            	    il=indirection_element();
            	    _fsp--;

            	    if (list_il==null) list_il=new ArrayList();
            	    list_il.add(il.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt85 >= 1 ) break loop85;
                        EarlyExitException eee =
                            new EarlyExitException(85, input);
                        throw eee;
                }
                cnt85++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 601:20: -> indirectionList(il=$il)
            {
                retval.st = templateLib.getInstanceOf("indirectionList",
              new STAttrMap().put("il", list_il));
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
    // $ANTLR end indirection_list

    public static class indirection_element_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start indirection_element
    // BONSTTreeWalker.g:605:1: indirection_element : ( ^( INDIRECTION_ELEMENT t= '...' ) -> indirectionElement(ie=$t.text) | ^( INDIRECTION_ELEMENT named_indirection ) -> indirectionElement(ie=$named_indirection.st) | ^( INDIRECTION_ELEMENT class_name ) -> indirectionElement(ie=$class_name.st));
    public final indirection_element_return indirection_element() throws RecognitionException {
        indirection_element_return retval = new indirection_element_return();
        retval.start = input.LT(1);

        CommonTree t=null;
        named_indirection_return named_indirection77 = null;

        class_name_return class_name78 = null;


        try {
            // BONSTTreeWalker.g:605:22: ( ^( INDIRECTION_ELEMENT t= '...' ) -> indirectionElement(ie=$t.text) | ^( INDIRECTION_ELEMENT named_indirection ) -> indirectionElement(ie=$named_indirection.st) | ^( INDIRECTION_ELEMENT class_name ) -> indirectionElement(ie=$class_name.st))
            int alt86=3;
            int LA86_0 = input.LA(1);

            if ( (LA86_0==INDIRECTION_ELEMENT) ) {
                int LA86_1 = input.LA(2);

                if ( (LA86_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case 230:
                        {
                        alt86=1;
                        }
                        break;
                    case CLASS_NAME:
                        {
                        alt86=3;
                        }
                        break;
                    case NAMED_INDIRECTION:
                        {
                        alt86=2;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("605:1: indirection_element : ( ^( INDIRECTION_ELEMENT t= '...' ) -> indirectionElement(ie=$t.text) | ^( INDIRECTION_ELEMENT named_indirection ) -> indirectionElement(ie=$named_indirection.st) | ^( INDIRECTION_ELEMENT class_name ) -> indirectionElement(ie=$class_name.st));", 86, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("605:1: indirection_element : ( ^( INDIRECTION_ELEMENT t= '...' ) -> indirectionElement(ie=$t.text) | ^( INDIRECTION_ELEMENT named_indirection ) -> indirectionElement(ie=$named_indirection.st) | ^( INDIRECTION_ELEMENT class_name ) -> indirectionElement(ie=$class_name.st));", 86, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("605:1: indirection_element : ( ^( INDIRECTION_ELEMENT t= '...' ) -> indirectionElement(ie=$t.text) | ^( INDIRECTION_ELEMENT named_indirection ) -> indirectionElement(ie=$named_indirection.st) | ^( INDIRECTION_ELEMENT class_name ) -> indirectionElement(ie=$class_name.st));", 86, 0, input);

                throw nvae;
            }
            switch (alt86) {
                case 1 :
                    // BONSTTreeWalker.g:605:24: ^( INDIRECTION_ELEMENT t= '...' )
                    {
                    match(input,INDIRECTION_ELEMENT,FOLLOW_INDIRECTION_ELEMENT_in_indirection_element10753); 

                    match(input, Token.DOWN, null); 
                    t=(CommonTree)input.LT(1);
                    match(input,230,FOLLOW_230_in_indirection_element10757); 

                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 608:24: -> indirectionElement(ie=$t.text)
                    {
                        retval.st = templateLib.getInstanceOf("indirectionElement",
                      new STAttrMap().put("ie", t.getText()));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:611:24: ^( INDIRECTION_ELEMENT named_indirection )
                    {
                    match(input,INDIRECTION_ELEMENT,FOLLOW_INDIRECTION_ELEMENT_in_indirection_element10917); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_named_indirection_in_indirection_element10919);
                    named_indirection77=named_indirection();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 614:24: -> indirectionElement(ie=$named_indirection.st)
                    {
                        retval.st = templateLib.getInstanceOf("indirectionElement",
                      new STAttrMap().put("ie", named_indirection77.st));
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:617:24: ^( INDIRECTION_ELEMENT class_name )
                    {
                    match(input,INDIRECTION_ELEMENT,FOLLOW_INDIRECTION_ELEMENT_in_indirection_element11079); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_class_name_in_indirection_element11081);
                    class_name78=class_name();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 620:24: -> indirectionElement(ie=$class_name.st)
                    {
                        retval.st = templateLib.getInstanceOf("indirectionElement",
                      new STAttrMap().put("ie", class_name78.st));
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
        return retval;
    }
    // $ANTLR end indirection_element

    public static class type_mark_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start type_mark
    // BONSTTreeWalker.g:625:1: type_mark : ( ^( TYPE_MARK t= ':' ) -> typeMark(tm=$t.text) | ^( TYPE_MARK t= ':{' ) -> typeMark(tm=$t.text) | ^( TYPE_MARK shared_mark ) -> typeMark(tm=$shared_mark.st));
    public final type_mark_return type_mark() throws RecognitionException {
        type_mark_return retval = new type_mark_return();
        retval.start = input.LT(1);

        CommonTree t=null;
        shared_mark_return shared_mark79 = null;


        try {
            // BONSTTreeWalker.g:625:12: ( ^( TYPE_MARK t= ':' ) -> typeMark(tm=$t.text) | ^( TYPE_MARK t= ':{' ) -> typeMark(tm=$t.text) | ^( TYPE_MARK shared_mark ) -> typeMark(tm=$shared_mark.st))
            int alt87=3;
            int LA87_0 = input.LA(1);

            if ( (LA87_0==TYPE_MARK) ) {
                int LA87_1 = input.LA(2);

                if ( (LA87_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case 231:
                        {
                        alt87=2;
                        }
                        break;
                    case 196:
                        {
                        alt87=1;
                        }
                        break;
                    case SHARED_MARK:
                        {
                        alt87=3;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("625:1: type_mark : ( ^( TYPE_MARK t= ':' ) -> typeMark(tm=$t.text) | ^( TYPE_MARK t= ':{' ) -> typeMark(tm=$t.text) | ^( TYPE_MARK shared_mark ) -> typeMark(tm=$shared_mark.st));", 87, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("625:1: type_mark : ( ^( TYPE_MARK t= ':' ) -> typeMark(tm=$t.text) | ^( TYPE_MARK t= ':{' ) -> typeMark(tm=$t.text) | ^( TYPE_MARK shared_mark ) -> typeMark(tm=$shared_mark.st));", 87, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("625:1: type_mark : ( ^( TYPE_MARK t= ':' ) -> typeMark(tm=$t.text) | ^( TYPE_MARK t= ':{' ) -> typeMark(tm=$t.text) | ^( TYPE_MARK shared_mark ) -> typeMark(tm=$shared_mark.st));", 87, 0, input);

                throw nvae;
            }
            switch (alt87) {
                case 1 :
                    // BONSTTreeWalker.g:625:13: ^( TYPE_MARK t= ':' )
                    {
                    match(input,TYPE_MARK,FOLLOW_TYPE_MARK_in_type_mark11232); 

                    match(input, Token.DOWN, null); 
                    t=(CommonTree)input.LT(1);
                    match(input,196,FOLLOW_196_in_type_mark11236); 

                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 628:13: -> typeMark(tm=$t.text)
                    {
                        retval.st = templateLib.getInstanceOf("typeMark",
                      new STAttrMap().put("tm", t.getText()));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:631:13: ^( TYPE_MARK t= ':{' )
                    {
                    match(input,TYPE_MARK,FOLLOW_TYPE_MARK_in_type_mark11330); 

                    match(input, Token.DOWN, null); 
                    t=(CommonTree)input.LT(1);
                    match(input,231,FOLLOW_231_in_type_mark11334); 

                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 634:13: -> typeMark(tm=$t.text)
                    {
                        retval.st = templateLib.getInstanceOf("typeMark",
                      new STAttrMap().put("tm", t.getText()));
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:637:13: ^( TYPE_MARK shared_mark )
                    {
                    match(input,TYPE_MARK,FOLLOW_TYPE_MARK_in_type_mark11429); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_shared_mark_in_type_mark11431);
                    shared_mark79=shared_mark();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 640:13: -> typeMark(tm=$shared_mark.st)
                    {
                        retval.st = templateLib.getInstanceOf("typeMark",
                      new STAttrMap().put("tm", shared_mark79.st));
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
        return retval;
    }
    // $ANTLR end type_mark

    public static class shared_mark_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start shared_mark
    // BONSTTreeWalker.g:644:1: shared_mark : ^( SHARED_MARK multiplicity ) -> sharedMark(mult=$multiplicity.st);
    public final shared_mark_return shared_mark() throws RecognitionException {
        shared_mark_return retval = new shared_mark_return();
        retval.start = input.LT(1);

        multiplicity_return multiplicity80 = null;


        try {
            // BONSTTreeWalker.g:644:14: ( ^( SHARED_MARK multiplicity ) -> sharedMark(mult=$multiplicity.st))
            // BONSTTreeWalker.g:644:15: ^( SHARED_MARK multiplicity )
            {
            match(input,SHARED_MARK,FOLLOW_SHARED_MARK_in_shared_mark11530); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_multiplicity_in_shared_mark11532);
            multiplicity80=multiplicity();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 647:15: -> sharedMark(mult=$multiplicity.st)
            {
                retval.st = templateLib.getInstanceOf("sharedMark",
              new STAttrMap().put("mult", multiplicity80.st));
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
    // $ANTLR end shared_mark

    public static class child_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start child
    // BONSTTreeWalker.g:651:1: child : ^( CHILD static_ref ) -> child(c=$static_ref.st);
    public final child_return child() throws RecognitionException {
        child_return retval = new child_return();
        retval.start = input.LT(1);

        static_ref_return static_ref81 = null;


        try {
            // BONSTTreeWalker.g:653:8: ( ^( CHILD static_ref ) -> child(c=$static_ref.st))
            // BONSTTreeWalker.g:653:9: ^( CHILD static_ref )
            {
            match(input,CHILD,FOLLOW_CHILD_in_child11625); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_static_ref_in_child11627);
            static_ref81=static_ref();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 656:9: -> child(c=$static_ref.st)
            {
                retval.st = templateLib.getInstanceOf("child",
              new STAttrMap().put("c", static_ref81.st));
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
    // $ANTLR end child

    public static class parent_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start parent
    // BONSTTreeWalker.g:660:1: parent : ^( PARENT static_ref ) -> parent(p=$static_ref.st);
    public final parent_return parent() throws RecognitionException {
        parent_return retval = new parent_return();
        retval.start = input.LT(1);

        static_ref_return static_ref82 = null;


        try {
            // BONSTTreeWalker.g:660:9: ( ^( PARENT static_ref ) -> parent(p=$static_ref.st))
            // BONSTTreeWalker.g:660:10: ^( PARENT static_ref )
            {
            match(input,PARENT,FOLLOW_PARENT_in_parent11701); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_static_ref_in_parent11703);
            static_ref82=static_ref();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 663:10: -> parent(p=$static_ref.st)
            {
                retval.st = templateLib.getInstanceOf("parent",
              new STAttrMap().put("p", static_ref82.st));
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
    // $ANTLR end parent

    public static class client_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start client
    // BONSTTreeWalker.g:667:1: client : ^( CLIENT static_ref ) -> client(c=$static_ref.st);
    public final client_return client() throws RecognitionException {
        client_return retval = new client_return();
        retval.start = input.LT(1);

        static_ref_return static_ref83 = null;


        try {
            // BONSTTreeWalker.g:667:9: ( ^( CLIENT static_ref ) -> client(c=$static_ref.st))
            // BONSTTreeWalker.g:667:10: ^( CLIENT static_ref )
            {
            match(input,CLIENT,FOLLOW_CLIENT_in_client11782); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_static_ref_in_client11784);
            static_ref83=static_ref();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 670:10: -> client(c=$static_ref.st)
            {
                retval.st = templateLib.getInstanceOf("client",
              new STAttrMap().put("c", static_ref83.st));
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
    // $ANTLR end client

    public static class supplier_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start supplier
    // BONSTTreeWalker.g:674:1: supplier : ^( SUPPLIER static_ref ) -> supplier(s=$static_ref.st);
    public final supplier_return supplier() throws RecognitionException {
        supplier_return retval = new supplier_return();
        retval.start = input.LT(1);

        static_ref_return static_ref84 = null;


        try {
            // BONSTTreeWalker.g:674:11: ( ^( SUPPLIER static_ref ) -> supplier(s=$static_ref.st))
            // BONSTTreeWalker.g:674:12: ^( SUPPLIER static_ref )
            {
            match(input,SUPPLIER,FOLLOW_SUPPLIER_in_supplier11865); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_static_ref_in_supplier11867);
            static_ref84=static_ref();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 677:12: -> supplier(s=$static_ref.st)
            {
                retval.st = templateLib.getInstanceOf("supplier",
              new STAttrMap().put("s", static_ref84.st));
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
    // $ANTLR end supplier

    public static class static_ref_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start static_ref
    // BONSTTreeWalker.g:681:1: static_ref : ^( STATIC_REF (cp+= cluster_prefix )? static_component_name ) -> staticRef(cp=$cpname=$static_component_name.st);
    public final static_ref_return static_ref() throws RecognitionException {
        static_ref_return retval = new static_ref_return();
        retval.start = input.LT(1);

        List list_cp=null;
        static_component_name_return static_component_name85 = null;

        RuleReturnScope cp = null;
        try {
            // BONSTTreeWalker.g:681:13: ( ^( STATIC_REF (cp+= cluster_prefix )? static_component_name ) -> staticRef(cp=$cpname=$static_component_name.st))
            // BONSTTreeWalker.g:681:14: ^( STATIC_REF (cp+= cluster_prefix )? static_component_name )
            {
            match(input,STATIC_REF,FOLLOW_STATIC_REF_in_static_ref11960); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:682:27: (cp+= cluster_prefix )?
            int alt88=2;
            int LA88_0 = input.LA(1);

            if ( (LA88_0==CLUSTER_PREFIX) ) {
                alt88=1;
            }
            switch (alt88) {
                case 1 :
                    // BONSTTreeWalker.g:682:28: cp+= cluster_prefix
                    {
                    pushFollow(FOLLOW_cluster_prefix_in_static_ref11965);
                    cp=cluster_prefix();
                    _fsp--;

                    if (list_cp==null) list_cp=new ArrayList();
                    list_cp.add(cp.getTemplate());


                    }
                    break;

            }

            pushFollow(FOLLOW_static_component_name_in_static_ref11969);
            static_component_name85=static_component_name();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 684:14: -> staticRef(cp=$cpname=$static_component_name.st)
            {
                retval.st = templateLib.getInstanceOf("staticRef",
              new STAttrMap().put("cp", list_cp).put("name", static_component_name85.st));
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
    // $ANTLR end static_ref

    public static class cluster_prefix_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start cluster_prefix
    // BONSTTreeWalker.g:688:1: cluster_prefix : ^( CLUSTER_PREFIX (cn+= cluster_name )+ ) -> clusterPrefix(cns=$cn);
    public final cluster_prefix_return cluster_prefix() throws RecognitionException {
        cluster_prefix_return retval = new cluster_prefix_return();
        retval.start = input.LT(1);

        List list_cn=null;
        RuleReturnScope cn = null;
        try {
            // BONSTTreeWalker.g:688:17: ( ^( CLUSTER_PREFIX (cn+= cluster_name )+ ) -> clusterPrefix(cns=$cn))
            // BONSTTreeWalker.g:688:18: ^( CLUSTER_PREFIX (cn+= cluster_name )+ )
            {
            match(input,CLUSTER_PREFIX,FOLLOW_CLUSTER_PREFIX_in_cluster_prefix12080); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:689:35: (cn+= cluster_name )+
            int cnt89=0;
            loop89:
            do {
                int alt89=2;
                int LA89_0 = input.LA(1);

                if ( (LA89_0==CLUSTER_NAME) ) {
                    alt89=1;
                }


                switch (alt89) {
            	case 1 :
            	    // BONSTTreeWalker.g:689:36: cn+= cluster_name
            	    {
            	    pushFollow(FOLLOW_cluster_name_in_cluster_prefix12085);
            	    cn=cluster_name();
            	    _fsp--;

            	    if (list_cn==null) list_cn=new ArrayList();
            	    list_cn.add(cn.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt89 >= 1 ) break loop89;
                        EarlyExitException eee =
                            new EarlyExitException(89, input);
                        throw eee;
                }
                cnt89++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 691:18: -> clusterPrefix(cns=$cn)
            {
                retval.st = templateLib.getInstanceOf("clusterPrefix",
              new STAttrMap().put("cns", list_cn));
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
    // $ANTLR end cluster_prefix

    public static class static_component_name_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start static_component_name
    // BONSTTreeWalker.g:695:1: static_component_name : ^( STATIC_COMPONENT_NAME IDENTIFIER ) -> staticComponentName(name=$IDENTIFIER.text);
    public final static_component_name_return static_component_name() throws RecognitionException {
        static_component_name_return retval = new static_component_name_return();
        retval.start = input.LT(1);

        CommonTree IDENTIFIER86=null;

        try {
            // BONSTTreeWalker.g:695:24: ( ^( STATIC_COMPONENT_NAME IDENTIFIER ) -> staticComponentName(name=$IDENTIFIER.text))
            // BONSTTreeWalker.g:695:25: ^( STATIC_COMPONENT_NAME IDENTIFIER )
            {
            match(input,STATIC_COMPONENT_NAME,FOLLOW_STATIC_COMPONENT_NAME_in_static_component_name12207); 

            match(input, Token.DOWN, null); 
            IDENTIFIER86=(CommonTree)input.LT(1);
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_static_component_name12209); 

            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 698:25: -> staticComponentName(name=$IDENTIFIER.text)
            {
                retval.st = templateLib.getInstanceOf("staticComponentName",
              new STAttrMap().put("name", IDENTIFIER86.getText()));
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
    // $ANTLR end static_component_name

    public static class multiplicity_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start multiplicity
    // BONSTTreeWalker.g:702:1: multiplicity : ^( MULTIPLICITY INTEGER ) -> multiplicity(i=$INTEGER.text);
    public final multiplicity_return multiplicity() throws RecognitionException {
        multiplicity_return retval = new multiplicity_return();
        retval.start = input.LT(1);

        CommonTree INTEGER87=null;

        try {
            // BONSTTreeWalker.g:702:15: ( ^( MULTIPLICITY INTEGER ) -> multiplicity(i=$INTEGER.text))
            // BONSTTreeWalker.g:702:16: ^( MULTIPLICITY INTEGER )
            {
            match(input,MULTIPLICITY,FOLLOW_MULTIPLICITY_in_multiplicity12369); 

            match(input, Token.DOWN, null); 
            INTEGER87=(CommonTree)input.LT(1);
            match(input,INTEGER,FOLLOW_INTEGER_in_multiplicity12371); 

            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 705:16: -> multiplicity(i=$INTEGER.text)
            {
                retval.st = templateLib.getInstanceOf("multiplicity",
              new STAttrMap().put("i", INTEGER87.getText()));
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
    // $ANTLR end multiplicity

    public static class semantic_label_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start semantic_label
    // BONSTTreeWalker.g:709:1: semantic_label : ^( SEMANTIC_LABEL MANIFEST_STRING ) -> semanticLabel(l=$MANIFEST_STRING.text);
    public final semantic_label_return semantic_label() throws RecognitionException {
        semantic_label_return retval = new semantic_label_return();
        retval.start = input.LT(1);

        CommonTree MANIFEST_STRING88=null;

        try {
            // BONSTTreeWalker.g:709:17: ( ^( SEMANTIC_LABEL MANIFEST_STRING ) -> semanticLabel(l=$MANIFEST_STRING.text))
            // BONSTTreeWalker.g:709:18: ^( SEMANTIC_LABEL MANIFEST_STRING )
            {
            match(input,SEMANTIC_LABEL,FOLLOW_SEMANTIC_LABEL_in_semantic_label12488); 

            match(input, Token.DOWN, null); 
            MANIFEST_STRING88=(CommonTree)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_semantic_label12490); 

            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 712:18: -> semanticLabel(l=$MANIFEST_STRING.text)
            {
                retval.st = templateLib.getInstanceOf("semanticLabel",
              new STAttrMap().put("l", MANIFEST_STRING88.getText()));
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
    // $ANTLR end semantic_label

    public static class class_interface_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start class_interface
    // BONSTTreeWalker.g:716:1: class_interface : ^( CLASS_INTERFACE (o+= indexing )? (o+= parent_class_list )? features (inv+= class_invariant )? ) -> classInterface(other=$ofeatures=$features.stinv=$inv);
    public final class_interface_return class_interface() throws RecognitionException {
        class_interface_return retval = new class_interface_return();
        retval.start = input.LT(1);

        List list_o=null;
        List list_inv=null;
        features_return features89 = null;

        RuleReturnScope o = null;
        RuleReturnScope inv = null;
        try {
            // BONSTTreeWalker.g:720:18: ( ^( CLASS_INTERFACE (o+= indexing )? (o+= parent_class_list )? features (inv+= class_invariant )? ) -> classInterface(other=$ofeatures=$features.stinv=$inv))
            // BONSTTreeWalker.g:720:19: ^( CLASS_INTERFACE (o+= indexing )? (o+= parent_class_list )? features (inv+= class_invariant )? )
            {
            match(input,CLASS_INTERFACE,FOLLOW_CLASS_INTERFACE_in_class_interface12605); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:722:21: (o+= indexing )?
            int alt90=2;
            int LA90_0 = input.LA(1);

            if ( (LA90_0==INDEXING) ) {
                alt90=1;
            }
            switch (alt90) {
                case 1 :
                    // BONSTTreeWalker.g:722:22: o+= indexing
                    {
                    pushFollow(FOLLOW_indexing_in_class_interface12630);
                    o=indexing();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:723:21: (o+= parent_class_list )?
            int alt91=2;
            int LA91_0 = input.LA(1);

            if ( (LA91_0==PARENT_CLASS_LIST) ) {
                alt91=1;
            }
            switch (alt91) {
                case 1 :
                    // BONSTTreeWalker.g:723:22: o+= parent_class_list
                    {
                    pushFollow(FOLLOW_parent_class_list_in_class_interface12657);
                    o=parent_class_list();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            pushFollow(FOLLOW_features_in_class_interface12681);
            features89=features();
            _fsp--;

            // BONSTTreeWalker.g:725:21: (inv+= class_invariant )?
            int alt92=2;
            int LA92_0 = input.LA(1);

            if ( (LA92_0==CLASS_INVARIANT) ) {
                alt92=1;
            }
            switch (alt92) {
                case 1 :
                    // BONSTTreeWalker.g:725:22: inv+= class_invariant
                    {
                    pushFollow(FOLLOW_class_invariant_in_class_interface12706);
                    inv=class_invariant();
                    _fsp--;

                    if (list_inv==null) list_inv=new ArrayList();
                    list_inv.add(inv.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 727:19: -> classInterface(other=$ofeatures=$features.stinv=$inv)
            {
                retval.st = templateLib.getInstanceOf("classInterface",
              new STAttrMap().put("other", list_o).put("features", features89.st).put("inv", list_inv));
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
    // $ANTLR end class_interface

    public static class class_invariant_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start class_invariant
    // BONSTTreeWalker.g:731:1: class_invariant : ^( CLASS_INVARIANT assertion ) -> classInvariant(ass=$assertion.st);
    public final class_invariant_return class_invariant() throws RecognitionException {
        class_invariant_return retval = new class_invariant_return();
        retval.start = input.LT(1);

        assertion_return assertion90 = null;


        try {
            // BONSTTreeWalker.g:731:18: ( ^( CLASS_INVARIANT assertion ) -> classInvariant(ass=$assertion.st))
            // BONSTTreeWalker.g:731:19: ^( CLASS_INVARIANT assertion )
            {
            match(input,CLASS_INVARIANT,FOLLOW_CLASS_INVARIANT_in_class_invariant12852); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_assertion_in_class_invariant12854);
            assertion90=assertion();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 734:19: -> classInvariant(ass=$assertion.st)
            {
                retval.st = templateLib.getInstanceOf("classInvariant",
              new STAttrMap().put("ass", assertion90.st));
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
    // $ANTLR end class_invariant

    public static class parent_class_list_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start parent_class_list
    // BONSTTreeWalker.g:738:1: parent_class_list : ( ^( PARENT_CLASS_LIST (pcl+= class_type )+ ) -> parentClassList(pcl=$pcl) | ^( PARENT_CLASS_LIST PARSE_ERROR ) );
    public final parent_class_list_return parent_class_list() throws RecognitionException {
        parent_class_list_return retval = new parent_class_list_return();
        retval.start = input.LT(1);

        List list_pcl=null;
        RuleReturnScope pcl = null;
        try {
            // BONSTTreeWalker.g:738:20: ( ^( PARENT_CLASS_LIST (pcl+= class_type )+ ) -> parentClassList(pcl=$pcl) | ^( PARENT_CLASS_LIST PARSE_ERROR ) )
            int alt94=2;
            int LA94_0 = input.LA(1);

            if ( (LA94_0==PARENT_CLASS_LIST) ) {
                int LA94_1 = input.LA(2);

                if ( (LA94_1==DOWN) ) {
                    int LA94_2 = input.LA(3);

                    if ( (LA94_2==PARSE_ERROR) ) {
                        alt94=2;
                    }
                    else if ( (LA94_2==CLASS_TYPE) ) {
                        alt94=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("738:1: parent_class_list : ( ^( PARENT_CLASS_LIST (pcl+= class_type )+ ) -> parentClassList(pcl=$pcl) | ^( PARENT_CLASS_LIST PARSE_ERROR ) );", 94, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("738:1: parent_class_list : ( ^( PARENT_CLASS_LIST (pcl+= class_type )+ ) -> parentClassList(pcl=$pcl) | ^( PARENT_CLASS_LIST PARSE_ERROR ) );", 94, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("738:1: parent_class_list : ( ^( PARENT_CLASS_LIST (pcl+= class_type )+ ) -> parentClassList(pcl=$pcl) | ^( PARENT_CLASS_LIST PARSE_ERROR ) );", 94, 0, input);

                throw nvae;
            }
            switch (alt94) {
                case 1 :
                    // BONSTTreeWalker.g:738:21: ^( PARENT_CLASS_LIST (pcl+= class_type )+ )
                    {
                    match(input,PARENT_CLASS_LIST,FOLLOW_PARENT_CLASS_LIST_in_parent_class_list12989); 

                    match(input, Token.DOWN, null); 
                    // BONSTTreeWalker.g:739:41: (pcl+= class_type )+
                    int cnt93=0;
                    loop93:
                    do {
                        int alt93=2;
                        int LA93_0 = input.LA(1);

                        if ( (LA93_0==CLASS_TYPE) ) {
                            alt93=1;
                        }


                        switch (alt93) {
                    	case 1 :
                    	    // BONSTTreeWalker.g:739:42: pcl+= class_type
                    	    {
                    	    pushFollow(FOLLOW_class_type_in_parent_class_list12994);
                    	    pcl=class_type();
                    	    _fsp--;

                    	    if (list_pcl==null) list_pcl=new ArrayList();
                    	    list_pcl.add(pcl.getTemplate());


                    	    }
                    	    break;

                    	default :
                    	    if ( cnt93 >= 1 ) break loop93;
                                EarlyExitException eee =
                                    new EarlyExitException(93, input);
                                throw eee;
                        }
                        cnt93++;
                    } while (true);


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 741:21: -> parentClassList(pcl=$pcl)
                    {
                        retval.st = templateLib.getInstanceOf("parentClassList",
                      new STAttrMap().put("pcl", list_pcl));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:744:21: ^( PARENT_CLASS_LIST PARSE_ERROR )
                    {
                    match(input,PARENT_CLASS_LIST,FOLLOW_PARENT_CLASS_LIST_in_parent_class_list13115); 

                    match(input, Token.DOWN, null); 
                    match(input,PARSE_ERROR,FOLLOW_PARSE_ERROR_in_parent_class_list13117); 

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
    // $ANTLR end parent_class_list

    public static class features_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start features
    // BONSTTreeWalker.g:747:1: features : ^( FEATURES (fc+= feature_clause )+ ) -> features(fcl=$fc);
    public final features_return features() throws RecognitionException {
        features_return retval = new features_return();
        retval.start = input.LT(1);

        List list_fc=null;
        RuleReturnScope fc = null;
        try {
            // BONSTTreeWalker.g:747:11: ( ^( FEATURES (fc+= feature_clause )+ ) -> features(fcl=$fc))
            // BONSTTreeWalker.g:747:12: ^( FEATURES (fc+= feature_clause )+ )
            {
            match(input,FEATURES,FOLLOW_FEATURES_in_features13181); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:748:23: (fc+= feature_clause )+
            int cnt95=0;
            loop95:
            do {
                int alt95=2;
                int LA95_0 = input.LA(1);

                if ( (LA95_0==FEATURE_CLAUSE) ) {
                    alt95=1;
                }


                switch (alt95) {
            	case 1 :
            	    // BONSTTreeWalker.g:748:24: fc+= feature_clause
            	    {
            	    pushFollow(FOLLOW_feature_clause_in_features13186);
            	    fc=feature_clause();
            	    _fsp--;

            	    if (list_fc==null) list_fc=new ArrayList();
            	    list_fc.add(fc.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt95 >= 1 ) break loop95;
                        EarlyExitException eee =
                            new EarlyExitException(95, input);
                        throw eee;
                }
                cnt95++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 750:12: -> features(fcl=$fc)
            {
                retval.st = templateLib.getInstanceOf("features",
              new STAttrMap().put("fcl", list_fc));
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
    // $ANTLR end features

    public static class feature_clause_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start feature_clause
    // BONSTTreeWalker.g:754:1: feature_clause : ^( FEATURE_CLAUSE (se+= selective_export )? ( COMMENT )? feature_specifications ) -> featureClause(se=$sefspecs=$feature_specifications.st);
    public final feature_clause_return feature_clause() throws RecognitionException {
        feature_clause_return retval = new feature_clause_return();
        retval.start = input.LT(1);

        List list_se=null;
        feature_specifications_return feature_specifications91 = null;

        RuleReturnScope se = null;
        try {
            // BONSTTreeWalker.g:756:17: ( ^( FEATURE_CLAUSE (se+= selective_export )? ( COMMENT )? feature_specifications ) -> featureClause(se=$sefspecs=$feature_specifications.st))
            // BONSTTreeWalker.g:756:18: ^( FEATURE_CLAUSE (se+= selective_export )? ( COMMENT )? feature_specifications )
            {
            match(input,FEATURE_CLAUSE,FOLLOW_FEATURE_CLAUSE_in_feature_clause13288); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:758:20: (se+= selective_export )?
            int alt96=2;
            int LA96_0 = input.LA(1);

            if ( (LA96_0==SELECTIVE_EXPORT) ) {
                alt96=1;
            }
            switch (alt96) {
                case 1 :
                    // BONSTTreeWalker.g:758:21: se+= selective_export
                    {
                    pushFollow(FOLLOW_selective_export_in_feature_clause13312);
                    se=selective_export();
                    _fsp--;

                    if (list_se==null) list_se=new ArrayList();
                    list_se.add(se.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:759:20: ( COMMENT )?
            int alt97=2;
            int LA97_0 = input.LA(1);

            if ( (LA97_0==COMMENT) ) {
                alt97=1;
            }
            switch (alt97) {
                case 1 :
                    // BONSTTreeWalker.g:759:21: COMMENT
                    {
                    match(input,COMMENT,FOLLOW_COMMENT_in_feature_clause13337); 

                    }
                    break;

            }

            pushFollow(FOLLOW_feature_specifications_in_feature_clause13361);
            feature_specifications91=feature_specifications();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 762:18: -> featureClause(se=$sefspecs=$feature_specifications.st)
            {
                retval.st = templateLib.getInstanceOf("featureClause",
              new STAttrMap().put("se", list_se).put("fspecs", feature_specifications91.st));
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
    // $ANTLR end feature_clause

    public static class feature_specifications_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start feature_specifications
    // BONSTTreeWalker.g:766:1: feature_specifications : ^( FEATURE_SPECIFICATIONS (fcl+= feature_specification )+ ) -> featureSpecifications(fcl=$fcl);
    public final feature_specifications_return feature_specifications() throws RecognitionException {
        feature_specifications_return retval = new feature_specifications_return();
        retval.start = input.LT(1);

        List list_fcl=null;
        RuleReturnScope fcl = null;
        try {
            // BONSTTreeWalker.g:766:25: ( ^( FEATURE_SPECIFICATIONS (fcl+= feature_specification )+ ) -> featureSpecifications(fcl=$fcl))
            // BONSTTreeWalker.g:766:26: ^( FEATURE_SPECIFICATIONS (fcl+= feature_specification )+ )
            {
            match(input,FEATURE_SPECIFICATIONS,FOLLOW_FEATURE_SPECIFICATIONS_in_feature_specifications13501); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:768:28: (fcl+= feature_specification )+
            int cnt98=0;
            loop98:
            do {
                int alt98=2;
                int LA98_0 = input.LA(1);

                if ( (LA98_0==FEATURE_SPECIFICATION) ) {
                    alt98=1;
                }


                switch (alt98) {
            	case 1 :
            	    // BONSTTreeWalker.g:768:29: fcl+= feature_specification
            	    {
            	    pushFollow(FOLLOW_feature_specification_in_feature_specifications13533);
            	    fcl=feature_specification();
            	    _fsp--;

            	    if (list_fcl==null) list_fcl=new ArrayList();
            	    list_fcl.add(fcl.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt98 >= 1 ) break loop98;
                        EarlyExitException eee =
                            new EarlyExitException(98, input);
                        throw eee;
                }
                cnt98++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 770:26: -> featureSpecifications(fcl=$fcl)
            {
                retval.st = templateLib.getInstanceOf("featureSpecifications",
              new STAttrMap().put("fcl", list_fcl));
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
    // $ANTLR end feature_specifications

    public static class feature_specification_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start feature_specification
    // BONSTTreeWalker.g:774:1: feature_specification : ^( FEATURE_SPECIFICATION (key+= 'deferred' )? (key+= 'effective' )? (key+= 'redefined' )? feature_name_list (a+= has_type )? (a+= rename_clause )? ( COMMENT )? (o+= feature_arguments )? (o+= contract_clause )? ) -> featureSpecification(key=$keyfnl=$feature_name_list.staft=$aother=$o);
    public final feature_specification_return feature_specification() throws RecognitionException {
        feature_specification_return retval = new feature_specification_return();
        retval.start = input.LT(1);

        CommonTree key=null;
        List list_key=null;
        List list_a=null;
        List list_o=null;
        feature_name_list_return feature_name_list92 = null;

        RuleReturnScope a = null;
        RuleReturnScope o = null;
        try {
            // BONSTTreeWalker.g:774:24: ( ^( FEATURE_SPECIFICATION (key+= 'deferred' )? (key+= 'effective' )? (key+= 'redefined' )? feature_name_list (a+= has_type )? (a+= rename_clause )? ( COMMENT )? (o+= feature_arguments )? (o+= contract_clause )? ) -> featureSpecification(key=$keyfnl=$feature_name_list.staft=$aother=$o))
            // BONSTTreeWalker.g:774:25: ^( FEATURE_SPECIFICATION (key+= 'deferred' )? (key+= 'effective' )? (key+= 'redefined' )? feature_name_list (a+= has_type )? (a+= rename_clause )? ( COMMENT )? (o+= feature_arguments )? (o+= contract_clause )? )
            {
            match(input,FEATURE_SPECIFICATION,FOLLOW_FEATURE_SPECIFICATION_in_feature_specification13710); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:776:27: (key+= 'deferred' )?
            int alt99=2;
            int LA99_0 = input.LA(1);

            if ( (LA99_0==218) ) {
                alt99=1;
            }
            switch (alt99) {
                case 1 :
                    // BONSTTreeWalker.g:776:28: key+= 'deferred'
                    {
                    key=(CommonTree)input.LT(1);
                    match(input,218,FOLLOW_218_in_feature_specification13741); 
                    if (list_key==null) list_key=new ArrayList();
                    list_key.add(key);


                    }
                    break;

            }

            // BONSTTreeWalker.g:776:46: (key+= 'effective' )?
            int alt100=2;
            int LA100_0 = input.LA(1);

            if ( (LA100_0==219) ) {
                alt100=1;
            }
            switch (alt100) {
                case 1 :
                    // BONSTTreeWalker.g:776:47: key+= 'effective'
                    {
                    key=(CommonTree)input.LT(1);
                    match(input,219,FOLLOW_219_in_feature_specification13748); 
                    if (list_key==null) list_key=new ArrayList();
                    list_key.add(key);


                    }
                    break;

            }

            // BONSTTreeWalker.g:776:66: (key+= 'redefined' )?
            int alt101=2;
            int LA101_0 = input.LA(1);

            if ( (LA101_0==235) ) {
                alt101=1;
            }
            switch (alt101) {
                case 1 :
                    // BONSTTreeWalker.g:776:67: key+= 'redefined'
                    {
                    key=(CommonTree)input.LT(1);
                    match(input,235,FOLLOW_235_in_feature_specification13755); 
                    if (list_key==null) list_key=new ArrayList();
                    list_key.add(key);


                    }
                    break;

            }

            pushFollow(FOLLOW_feature_name_list_in_feature_specification13785);
            feature_name_list92=feature_name_list();
            _fsp--;

            // BONSTTreeWalker.g:777:45: (a+= has_type )?
            int alt102=2;
            int LA102_0 = input.LA(1);

            if ( (LA102_0==HAS_TYPE) ) {
                alt102=1;
            }
            switch (alt102) {
                case 1 :
                    // BONSTTreeWalker.g:777:46: a+= has_type
                    {
                    pushFollow(FOLLOW_has_type_in_feature_specification13790);
                    a=has_type();
                    _fsp--;

                    if (list_a==null) list_a=new ArrayList();
                    list_a.add(a.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:778:27: (a+= rename_clause )?
            int alt103=2;
            int LA103_0 = input.LA(1);

            if ( (LA103_0==RENAME_CLAUSE) ) {
                alt103=1;
            }
            switch (alt103) {
                case 1 :
                    // BONSTTreeWalker.g:778:28: a+= rename_clause
                    {
                    pushFollow(FOLLOW_rename_clause_in_feature_specification13823);
                    a=rename_clause();
                    _fsp--;

                    if (list_a==null) list_a=new ArrayList();
                    list_a.add(a.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:779:27: ( COMMENT )?
            int alt104=2;
            int LA104_0 = input.LA(1);

            if ( (LA104_0==COMMENT) ) {
                alt104=1;
            }
            switch (alt104) {
                case 1 :
                    // BONSTTreeWalker.g:779:28: COMMENT
                    {
                    match(input,COMMENT,FOLLOW_COMMENT_in_feature_specification13854); 

                    }
                    break;

            }

            // BONSTTreeWalker.g:780:27: (o+= feature_arguments )?
            int alt105=2;
            int LA105_0 = input.LA(1);

            if ( (LA105_0==FEATURE_ARGUMENTS) ) {
                alt105=1;
            }
            switch (alt105) {
                case 1 :
                    // BONSTTreeWalker.g:780:28: o+= feature_arguments
                    {
                    pushFollow(FOLLOW_feature_arguments_in_feature_specification13887);
                    o=feature_arguments();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }

            // BONSTTreeWalker.g:781:27: (o+= contract_clause )?
            int alt106=2;
            int LA106_0 = input.LA(1);

            if ( (LA106_0==CONTRACT_CLAUSE) ) {
                alt106=1;
            }
            switch (alt106) {
                case 1 :
                    // BONSTTreeWalker.g:781:28: o+= contract_clause
                    {
                    pushFollow(FOLLOW_contract_clause_in_feature_specification13920);
                    o=contract_clause();
                    _fsp--;

                    if (list_o==null) list_o=new ArrayList();
                    list_o.add(o.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 783:25: -> featureSpecification(key=$keyfnl=$feature_name_list.staft=$aother=$o)
            {
                retval.st = templateLib.getInstanceOf("featureSpecification",
              new STAttrMap().put("key", list_key).put("fnl", feature_name_list92.st).put("aft", list_a).put("other", list_o));
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
    // $ANTLR end feature_specification

    public static class has_type_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start has_type
    // BONSTTreeWalker.g:787:1: has_type : ^( HAS_TYPE type_mark type ) -> hasType(tm=$type_mark.sttype=$type.st);
    public final has_type_return has_type() throws RecognitionException {
        has_type_return retval = new has_type_return();
        retval.start = input.LT(1);

        type_mark_return type_mark93 = null;

        type_return type94 = null;


        try {
            // BONSTTreeWalker.g:787:11: ( ^( HAS_TYPE type_mark type ) -> hasType(tm=$type_mark.sttype=$type.st))
            // BONSTTreeWalker.g:787:13: ^( HAS_TYPE type_mark type )
            {
            match(input,HAS_TYPE,FOLLOW_HAS_TYPE_in_has_type14055); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_type_mark_in_has_type14057);
            type_mark93=type_mark();
            _fsp--;

            pushFollow(FOLLOW_type_in_has_type14059);
            type94=type();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 788:13: -> hasType(tm=$type_mark.sttype=$type.st)
            {
                retval.st = templateLib.getInstanceOf("hasType",
              new STAttrMap().put("tm", type_mark93.st).put("type", type94.st));
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
    // $ANTLR end has_type

    public static class contract_clause_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start contract_clause
    // BONSTTreeWalker.g:792:1: contract_clause : ^( CONTRACT_CLAUSE contracting_conditions ) -> contractClause(cc=$contracting_conditions.st);
    public final contract_clause_return contract_clause() throws RecognitionException {
        contract_clause_return retval = new contract_clause_return();
        retval.start = input.LT(1);

        contracting_conditions_return contracting_conditions95 = null;


        try {
            // BONSTTreeWalker.g:794:18: ( ^( CONTRACT_CLAUSE contracting_conditions ) -> contractClause(cc=$contracting_conditions.st))
            // BONSTTreeWalker.g:794:19: ^( CONTRACT_CLAUSE contracting_conditions )
            {
            match(input,CONTRACT_CLAUSE,FOLLOW_CONTRACT_CLAUSE_in_contract_clause14143); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_contracting_conditions_in_contract_clause14145);
            contracting_conditions95=contracting_conditions();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 797:19: -> contractClause(cc=$contracting_conditions.st)
            {
                retval.st = templateLib.getInstanceOf("contractClause",
              new STAttrMap().put("cc", contracting_conditions95.st));
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
    // $ANTLR end contract_clause

    public static class contracting_conditions_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start contracting_conditions
    // BONSTTreeWalker.g:801:1: contracting_conditions : ^( CONTRACTING_CONDITIONS (cc+= precondition )? (cc+= postcondition )? ) -> contractingConditions(cc=$cc);
    public final contracting_conditions_return contracting_conditions() throws RecognitionException {
        contracting_conditions_return retval = new contracting_conditions_return();
        retval.start = input.LT(1);

        List list_cc=null;
        RuleReturnScope cc = null;
        try {
            // BONSTTreeWalker.g:801:25: ( ^( CONTRACTING_CONDITIONS (cc+= precondition )? (cc+= postcondition )? ) -> contractingConditions(cc=$cc))
            // BONSTTreeWalker.g:801:26: ^( CONTRACTING_CONDITIONS (cc+= precondition )? (cc+= postcondition )? )
            {
            match(input,CONTRACTING_CONDITIONS,FOLLOW_CONTRACTING_CONDITIONS_in_contracting_conditions14282); 

            if ( input.LA(1)==Token.DOWN ) {
                match(input, Token.DOWN, null); 
                // BONSTTreeWalker.g:802:51: (cc+= precondition )?
                int alt107=2;
                int LA107_0 = input.LA(1);

                if ( (LA107_0==PRECONDITION) ) {
                    alt107=1;
                }
                switch (alt107) {
                    case 1 :
                        // BONSTTreeWalker.g:802:52: cc+= precondition
                        {
                        pushFollow(FOLLOW_precondition_in_contracting_conditions14287);
                        cc=precondition();
                        _fsp--;

                        if (list_cc==null) list_cc=new ArrayList();
                        list_cc.add(cc.getTemplate());


                        }
                        break;

                }

                // BONSTTreeWalker.g:802:71: (cc+= postcondition )?
                int alt108=2;
                int LA108_0 = input.LA(1);

                if ( (LA108_0==POSTCONDITION) ) {
                    alt108=1;
                }
                switch (alt108) {
                    case 1 :
                        // BONSTTreeWalker.g:802:72: cc+= postcondition
                        {
                        pushFollow(FOLLOW_postcondition_in_contracting_conditions14294);
                        cc=postcondition();
                        _fsp--;

                        if (list_cc==null) list_cc=new ArrayList();
                        list_cc.add(cc.getTemplate());


                        }
                        break;

                }


                match(input, Token.UP, null); 
            }

            // TEMPLATE REWRITE
            // 804:26: -> contractingConditions(cc=$cc)
            {
                retval.st = templateLib.getInstanceOf("contractingConditions",
              new STAttrMap().put("cc", list_cc));
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
    // $ANTLR end contracting_conditions

    public static class precondition_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start precondition
    // BONSTTreeWalker.g:808:1: precondition : ^( PRECONDITION assertion ) -> precondition(ass=$assertion.st);
    public final precondition_return precondition() throws RecognitionException {
        precondition_return retval = new precondition_return();
        retval.start = input.LT(1);

        assertion_return assertion96 = null;


        try {
            // BONSTTreeWalker.g:808:15: ( ^( PRECONDITION assertion ) -> precondition(ass=$assertion.st))
            // BONSTTreeWalker.g:808:16: ^( PRECONDITION assertion )
            {
            match(input,PRECONDITION,FOLLOW_PRECONDITION_in_precondition14446); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_assertion_in_precondition14448);
            assertion96=assertion();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 811:16: -> precondition(ass=$assertion.st)
            {
                retval.st = templateLib.getInstanceOf("precondition",
              new STAttrMap().put("ass", assertion96.st));
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
    // $ANTLR end precondition

    public static class postcondition_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start postcondition
    // BONSTTreeWalker.g:815:1: postcondition : ^( POSTCONDITION assertion ) -> postcondition(ass=$assertion.st);
    public final postcondition_return postcondition() throws RecognitionException {
        postcondition_return retval = new postcondition_return();
        retval.start = input.LT(1);

        assertion_return assertion97 = null;


        try {
            // BONSTTreeWalker.g:815:16: ( ^( POSTCONDITION assertion ) -> postcondition(ass=$assertion.st))
            // BONSTTreeWalker.g:815:17: ^( POSTCONDITION assertion )
            {
            match(input,POSTCONDITION,FOLLOW_POSTCONDITION_in_postcondition14564); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_assertion_in_postcondition14566);
            assertion97=assertion();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 818:17: -> postcondition(ass=$assertion.st)
            {
                retval.st = templateLib.getInstanceOf("postcondition",
              new STAttrMap().put("ass", assertion97.st));
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
    // $ANTLR end postcondition

    public static class selective_export_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start selective_export
    // BONSTTreeWalker.g:822:1: selective_export : ^( SELECTIVE_EXPORT class_name_list ) -> selectiveExport(cnl=$class_name_list.st);
    public final selective_export_return selective_export() throws RecognitionException {
        selective_export_return retval = new selective_export_return();
        retval.start = input.LT(1);

        class_name_list_return class_name_list98 = null;


        try {
            // BONSTTreeWalker.g:824:19: ( ^( SELECTIVE_EXPORT class_name_list ) -> selectiveExport(cnl=$class_name_list.st))
            // BONSTTreeWalker.g:824:20: ^( SELECTIVE_EXPORT class_name_list )
            {
            match(input,SELECTIVE_EXPORT,FOLLOW_SELECTIVE_EXPORT_in_selective_export14678); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_class_name_list_in_selective_export14680);
            class_name_list98=class_name_list();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 827:20: -> selectiveExport(cnl=$class_name_list.st)
            {
                retval.st = templateLib.getInstanceOf("selectiveExport",
              new STAttrMap().put("cnl", class_name_list98.st));
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
    // $ANTLR end selective_export

    public static class feature_name_list_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start feature_name_list
    // BONSTTreeWalker.g:831:1: feature_name_list : ^( FEATURE_NAME_LIST (fnl+= feature_name )+ ) -> featureNameList(fnl=$fnl);
    public final feature_name_list_return feature_name_list() throws RecognitionException {
        feature_name_list_return retval = new feature_name_list_return();
        retval.start = input.LT(1);

        List list_fnl=null;
        RuleReturnScope fnl = null;
        try {
            // BONSTTreeWalker.g:831:20: ( ^( FEATURE_NAME_LIST (fnl+= feature_name )+ ) -> featureNameList(fnl=$fnl))
            // BONSTTreeWalker.g:831:21: ^( FEATURE_NAME_LIST (fnl+= feature_name )+ )
            {
            match(input,FEATURE_NAME_LIST,FOLLOW_FEATURE_NAME_LIST_in_feature_name_list14820); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:832:41: (fnl+= feature_name )+
            int cnt109=0;
            loop109:
            do {
                int alt109=2;
                int LA109_0 = input.LA(1);

                if ( (LA109_0==FEATURE_NAME) ) {
                    alt109=1;
                }


                switch (alt109) {
            	case 1 :
            	    // BONSTTreeWalker.g:832:42: fnl+= feature_name
            	    {
            	    pushFollow(FOLLOW_feature_name_in_feature_name_list14825);
            	    fnl=feature_name();
            	    _fsp--;

            	    if (list_fnl==null) list_fnl=new ArrayList();
            	    list_fnl.add(fnl.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt109 >= 1 ) break loop109;
                        EarlyExitException eee =
                            new EarlyExitException(109, input);
                        throw eee;
                }
                cnt109++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 834:21: -> featureNameList(fnl=$fnl)
            {
                retval.st = templateLib.getInstanceOf("featureNameList",
              new STAttrMap().put("fnl", list_fnl));
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
    // $ANTLR end feature_name_list

    public static class feature_name_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start feature_name
    // BONSTTreeWalker.g:838:1: feature_name : ( ^( FEATURE_NAME IDENTIFIER ) -> featureName(name=$IDENTIFIER.text) | ^( FEATURE_NAME prefix ) -> featureName(name=$prefix.st) | ^( FEATURE_NAME infix ) -> featureName(name=$infix.st));
    public final feature_name_return feature_name() throws RecognitionException {
        feature_name_return retval = new feature_name_return();
        retval.start = input.LT(1);

        CommonTree IDENTIFIER99=null;
        prefix_return prefix100 = null;

        infix_return infix101 = null;


        try {
            // BONSTTreeWalker.g:838:15: ( ^( FEATURE_NAME IDENTIFIER ) -> featureName(name=$IDENTIFIER.text) | ^( FEATURE_NAME prefix ) -> featureName(name=$prefix.st) | ^( FEATURE_NAME infix ) -> featureName(name=$infix.st))
            int alt110=3;
            int LA110_0 = input.LA(1);

            if ( (LA110_0==FEATURE_NAME) ) {
                int LA110_1 = input.LA(2);

                if ( (LA110_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case IDENTIFIER:
                        {
                        alt110=1;
                        }
                        break;
                    case INFIX:
                        {
                        alt110=3;
                        }
                        break;
                    case PREFIX:
                        {
                        alt110=2;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("838:1: feature_name : ( ^( FEATURE_NAME IDENTIFIER ) -> featureName(name=$IDENTIFIER.text) | ^( FEATURE_NAME prefix ) -> featureName(name=$prefix.st) | ^( FEATURE_NAME infix ) -> featureName(name=$infix.st));", 110, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("838:1: feature_name : ( ^( FEATURE_NAME IDENTIFIER ) -> featureName(name=$IDENTIFIER.text) | ^( FEATURE_NAME prefix ) -> featureName(name=$prefix.st) | ^( FEATURE_NAME infix ) -> featureName(name=$infix.st));", 110, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("838:1: feature_name : ( ^( FEATURE_NAME IDENTIFIER ) -> featureName(name=$IDENTIFIER.text) | ^( FEATURE_NAME prefix ) -> featureName(name=$prefix.st) | ^( FEATURE_NAME infix ) -> featureName(name=$infix.st));", 110, 0, input);

                throw nvae;
            }
            switch (alt110) {
                case 1 :
                    // BONSTTreeWalker.g:838:16: ^( FEATURE_NAME IDENTIFIER )
                    {
                    match(input,FEATURE_NAME,FOLLOW_FEATURE_NAME_in_feature_name14967); 

                    match(input, Token.DOWN, null); 
                    IDENTIFIER99=(CommonTree)input.LT(1);
                    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_feature_name14969); 

                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 841:16: -> featureName(name=$IDENTIFIER.text)
                    {
                        retval.st = templateLib.getInstanceOf("featureName",
                      new STAttrMap().put("name", IDENTIFIER99.getText()));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:844:16: ^( FEATURE_NAME prefix )
                    {
                    match(input,FEATURE_NAME,FOLLOW_FEATURE_NAME_in_feature_name15082); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_prefix_in_feature_name15084);
                    prefix100=prefix();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 847:16: -> featureName(name=$prefix.st)
                    {
                        retval.st = templateLib.getInstanceOf("featureName",
                      new STAttrMap().put("name", prefix100.st));
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:850:16: ^( FEATURE_NAME infix )
                    {
                    match(input,FEATURE_NAME,FOLLOW_FEATURE_NAME_in_feature_name15197); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_infix_in_feature_name15199);
                    infix101=infix();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 853:16: -> featureName(name=$infix.st)
                    {
                        retval.st = templateLib.getInstanceOf("featureName",
                      new STAttrMap().put("name", infix101.st));
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
        return retval;
    }
    // $ANTLR end feature_name

    public static class rename_clause_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start rename_clause
    // BONSTTreeWalker.g:857:1: rename_clause : ^( RENAME_CLAUSE renaming ) -> renameClause(re=$renaming.st);
    public final rename_clause_return rename_clause() throws RecognitionException {
        rename_clause_return retval = new rename_clause_return();
        retval.start = input.LT(1);

        renaming_return renaming102 = null;


        try {
            // BONSTTreeWalker.g:857:16: ( ^( RENAME_CLAUSE renaming ) -> renameClause(re=$renaming.st))
            // BONSTTreeWalker.g:857:17: ^( RENAME_CLAUSE renaming )
            {
            match(input,RENAME_CLAUSE,FOLLOW_RENAME_CLAUSE_in_rename_clause15315); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_renaming_in_rename_clause15317);
            renaming102=renaming();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 860:17: -> renameClause(re=$renaming.st)
            {
                retval.st = templateLib.getInstanceOf("renameClause",
              new STAttrMap().put("re", renaming102.st));
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
    // $ANTLR end rename_clause

    public static class renaming_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start renaming
    // BONSTTreeWalker.g:864:1: renaming : ^( RENAMING class_name feature_name ) -> renaming(cname=$class_name.stfname=$feature_name.st);
    public final renaming_return renaming() throws RecognitionException {
        renaming_return retval = new renaming_return();
        retval.start = input.LT(1);

        class_name_return class_name103 = null;

        feature_name_return feature_name104 = null;


        try {
            // BONSTTreeWalker.g:864:11: ( ^( RENAMING class_name feature_name ) -> renaming(cname=$class_name.stfname=$feature_name.st))
            // BONSTTreeWalker.g:864:12: ^( RENAMING class_name feature_name )
            {
            match(input,RENAMING,FOLLOW_RENAMING_in_renaming15433); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_class_name_in_renaming15435);
            class_name103=class_name();
            _fsp--;

            pushFollow(FOLLOW_feature_name_in_renaming15437);
            feature_name104=feature_name();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 867:12: -> renaming(cname=$class_name.stfname=$feature_name.st)
            {
                retval.st = templateLib.getInstanceOf("renaming",
              new STAttrMap().put("cname", class_name103.st).put("fname", feature_name104.st));
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
    // $ANTLR end renaming

    public static class feature_arguments_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start feature_arguments
    // BONSTTreeWalker.g:871:1: feature_arguments : ^( FEATURE_ARGUMENTS (fal+= feature_argument )+ ) -> featureArguments(fal=$fal);
    public final feature_arguments_return feature_arguments() throws RecognitionException {
        feature_arguments_return retval = new feature_arguments_return();
        retval.start = input.LT(1);

        List list_fal=null;
        RuleReturnScope fal = null;
        try {
            // BONSTTreeWalker.g:871:20: ( ^( FEATURE_ARGUMENTS (fal+= feature_argument )+ ) -> featureArguments(fal=$fal))
            // BONSTTreeWalker.g:871:21: ^( FEATURE_ARGUMENTS (fal+= feature_argument )+ )
            {
            match(input,FEATURE_ARGUMENTS,FOLLOW_FEATURE_ARGUMENTS_in_feature_arguments15541); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:872:41: (fal+= feature_argument )+
            int cnt111=0;
            loop111:
            do {
                int alt111=2;
                int LA111_0 = input.LA(1);

                if ( (LA111_0==FEATURE_ARGUMENT) ) {
                    alt111=1;
                }


                switch (alt111) {
            	case 1 :
            	    // BONSTTreeWalker.g:872:42: fal+= feature_argument
            	    {
            	    pushFollow(FOLLOW_feature_argument_in_feature_arguments15546);
            	    fal=feature_argument();
            	    _fsp--;

            	    if (list_fal==null) list_fal=new ArrayList();
            	    list_fal.add(fal.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt111 >= 1 ) break loop111;
                        EarlyExitException eee =
                            new EarlyExitException(111, input);
                        throw eee;
                }
                cnt111++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 874:21: -> featureArguments(fal=$fal)
            {
                retval.st = templateLib.getInstanceOf("featureArguments",
              new STAttrMap().put("fal", list_fal));
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
    // $ANTLR end feature_arguments

    public static class feature_argument_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start feature_argument
    // BONSTTreeWalker.g:878:1: feature_argument : ^( FEATURE_ARGUMENT (il+= identifier_list )? type ) -> featureArgument(il=$iltype=$type.st);
    public final feature_argument_return feature_argument() throws RecognitionException {
        feature_argument_return retval = new feature_argument_return();
        retval.start = input.LT(1);

        List list_il=null;
        type_return type105 = null;

        RuleReturnScope il = null;
        try {
            // BONSTTreeWalker.g:878:19: ( ^( FEATURE_ARGUMENT (il+= identifier_list )? type ) -> featureArgument(il=$iltype=$type.st))
            // BONSTTreeWalker.g:878:20: ^( FEATURE_ARGUMENT (il+= identifier_list )? type )
            {
            match(input,FEATURE_ARGUMENT,FOLLOW_FEATURE_ARGUMENT_in_feature_argument15693); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:879:39: (il+= identifier_list )?
            int alt112=2;
            int LA112_0 = input.LA(1);

            if ( (LA112_0==IDENTIFIER_LIST) ) {
                alt112=1;
            }
            switch (alt112) {
                case 1 :
                    // BONSTTreeWalker.g:879:40: il+= identifier_list
                    {
                    pushFollow(FOLLOW_identifier_list_in_feature_argument15698);
                    il=identifier_list();
                    _fsp--;

                    if (list_il==null) list_il=new ArrayList();
                    list_il.add(il.getTemplate());


                    }
                    break;

            }

            pushFollow(FOLLOW_type_in_feature_argument15702);
            type105=type();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 881:20: -> featureArgument(il=$iltype=$type.st)
            {
                retval.st = templateLib.getInstanceOf("featureArgument",
              new STAttrMap().put("il", list_il).put("type", type105.st));
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
    // $ANTLR end feature_argument

    public static class identifier_list_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start identifier_list
    // BONSTTreeWalker.g:885:1: identifier_list : ^( IDENTIFIER_LIST (il+= IDENTIFIER )+ ) -> identifierList(il=$il);
    public final identifier_list_return identifier_list() throws RecognitionException {
        identifier_list_return retval = new identifier_list_return();
        retval.start = input.LT(1);

        CommonTree il=null;
        List list_il=null;

        try {
            // BONSTTreeWalker.g:885:18: ( ^( IDENTIFIER_LIST (il+= IDENTIFIER )+ ) -> identifierList(il=$il))
            // BONSTTreeWalker.g:885:19: ^( IDENTIFIER_LIST (il+= IDENTIFIER )+ )
            {
            match(input,IDENTIFIER_LIST,FOLLOW_IDENTIFIER_LIST_in_identifier_list15844); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:886:37: (il+= IDENTIFIER )+
            int cnt113=0;
            loop113:
            do {
                int alt113=2;
                int LA113_0 = input.LA(1);

                if ( (LA113_0==IDENTIFIER) ) {
                    alt113=1;
                }


                switch (alt113) {
            	case 1 :
            	    // BONSTTreeWalker.g:886:38: il+= IDENTIFIER
            	    {
            	    il=(CommonTree)input.LT(1);
            	    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_identifier_list15849); 
            	    if (list_il==null) list_il=new ArrayList();
            	    list_il.add(il);


            	    }
            	    break;

            	default :
            	    if ( cnt113 >= 1 ) break loop113;
                        EarlyExitException eee =
                            new EarlyExitException(113, input);
                        throw eee;
                }
                cnt113++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 888:19: -> identifierList(il=$il)
            {
                retval.st = templateLib.getInstanceOf("identifierList",
              new STAttrMap().put("il", list_il));
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
    // $ANTLR end identifier_list

    public static class prefix_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start prefix
    // BONSTTreeWalker.g:892:1: prefix : ^( PREFIX prefix_operator ) -> prefix(op=$prefix_operator.st);
    public final prefix_return prefix() throws RecognitionException {
        prefix_return retval = new prefix_return();
        retval.start = input.LT(1);

        prefix_operator_return prefix_operator106 = null;


        try {
            // BONSTTreeWalker.g:892:9: ( ^( PREFIX prefix_operator ) -> prefix(op=$prefix_operator.st))
            // BONSTTreeWalker.g:892:10: ^( PREFIX prefix_operator )
            {
            match(input,PREFIX,FOLLOW_PREFIX_in_prefix15972); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_prefix_operator_in_prefix15974);
            prefix_operator106=prefix_operator();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 895:10: -> prefix(op=$prefix_operator.st)
            {
                retval.st = templateLib.getInstanceOf("prefix",
              new STAttrMap().put("op", prefix_operator106.st));
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
    // $ANTLR end prefix

    public static class infix_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start infix
    // BONSTTreeWalker.g:899:1: infix : ^( INFIX infix_operator ) -> infix(op=$infix_operator.st);
    public final infix_return infix() throws RecognitionException {
        infix_return retval = new infix_return();
        retval.start = input.LT(1);

        infix_operator_return infix_operator107 = null;


        try {
            // BONSTTreeWalker.g:899:8: ( ^( INFIX infix_operator ) -> infix(op=$infix_operator.st))
            // BONSTTreeWalker.g:899:9: ^( INFIX infix_operator )
            {
            match(input,INFIX,FOLLOW_INFIX_in_infix16053); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_infix_operator_in_infix16055);
            infix_operator107=infix_operator();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 902:9: -> infix(op=$infix_operator.st)
            {
                retval.st = templateLib.getInstanceOf("infix",
              new STAttrMap().put("op", infix_operator107.st));
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
    // $ANTLR end infix

    public static class prefix_operator_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start prefix_operator
    // BONSTTreeWalker.g:906:1: prefix_operator : ^( PREFIX_OPERATOR unary ) -> prefixOperator(un=$unary.st);
    public final prefix_operator_return prefix_operator() throws RecognitionException {
        prefix_operator_return retval = new prefix_operator_return();
        retval.start = input.LT(1);

        unary_return unary108 = null;


        try {
            // BONSTTreeWalker.g:906:18: ( ^( PREFIX_OPERATOR unary ) -> prefixOperator(un=$unary.st))
            // BONSTTreeWalker.g:906:19: ^( PREFIX_OPERATOR unary )
            {
            match(input,PREFIX_OPERATOR,FOLLOW_PREFIX_OPERATOR_in_prefix_operator16138); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_unary_in_prefix_operator16140);
            unary108=unary();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 909:19: -> prefixOperator(un=$unary.st)
            {
                retval.st = templateLib.getInstanceOf("prefixOperator",
              new STAttrMap().put("un", unary108.st));
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
    // $ANTLR end prefix_operator

    public static class infix_operator_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start infix_operator
    // BONSTTreeWalker.g:913:1: infix_operator : ^( INFIX_OPERATOR binary ) -> infixOperator(bin=$binary.st);
    public final infix_operator_return infix_operator() throws RecognitionException {
        infix_operator_return retval = new infix_operator_return();
        retval.start = input.LT(1);

        binary_return binary109 = null;


        try {
            // BONSTTreeWalker.g:913:17: ( ^( INFIX_OPERATOR binary ) -> infixOperator(bin=$binary.st))
            // BONSTTreeWalker.g:913:18: ^( INFIX_OPERATOR binary )
            {
            match(input,INFIX_OPERATOR,FOLLOW_INFIX_OPERATOR_in_infix_operator16271); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_binary_in_infix_operator16273);
            binary109=binary();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 916:18: -> infixOperator(bin=$binary.st)
            {
                retval.st = templateLib.getInstanceOf("infixOperator",
              new STAttrMap().put("bin", binary109.st));
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
    // $ANTLR end infix_operator

    public static class formal_generics_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start formal_generics
    // BONSTTreeWalker.g:920:1: formal_generics : ^( FORMAL_GENERICS formal_generic_list ) -> formalGenerics(fgl=$formal_generic_list.st);
    public final formal_generics_return formal_generics() throws RecognitionException {
        formal_generics_return retval = new formal_generics_return();
        retval.start = input.LT(1);

        formal_generic_list_return formal_generic_list110 = null;


        try {
            // BONSTTreeWalker.g:922:18: ( ^( FORMAL_GENERICS formal_generic_list ) -> formalGenerics(fgl=$formal_generic_list.st))
            // BONSTTreeWalker.g:922:19: ^( FORMAL_GENERICS formal_generic_list )
            {
            match(input,FORMAL_GENERICS,FOLLOW_FORMAL_GENERICS_in_formal_generics16388); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_formal_generic_list_in_formal_generics16390);
            formal_generic_list110=formal_generic_list();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 925:19: -> formalGenerics(fgl=$formal_generic_list.st)
            {
                retval.st = templateLib.getInstanceOf("formalGenerics",
              new STAttrMap().put("fgl", formal_generic_list110.st));
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
    // $ANTLR end formal_generics

    public static class formal_generic_list_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start formal_generic_list
    // BONSTTreeWalker.g:929:1: formal_generic_list : ^( FORMAL_GENERIC_LIST (fgl+= formal_generic )+ ) -> formalGenericList(fgl=$fgl);
    public final formal_generic_list_return formal_generic_list() throws RecognitionException {
        formal_generic_list_return retval = new formal_generic_list_return();
        retval.start = input.LT(1);

        List list_fgl=null;
        RuleReturnScope fgl = null;
        try {
            // BONSTTreeWalker.g:929:22: ( ^( FORMAL_GENERIC_LIST (fgl+= formal_generic )+ ) -> formalGenericList(fgl=$fgl))
            // BONSTTreeWalker.g:929:23: ^( FORMAL_GENERIC_LIST (fgl+= formal_generic )+ )
            {
            match(input,FORMAL_GENERIC_LIST,FOLLOW_FORMAL_GENERIC_LIST_in_formal_generic_list16527); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:930:45: (fgl+= formal_generic )+
            int cnt114=0;
            loop114:
            do {
                int alt114=2;
                int LA114_0 = input.LA(1);

                if ( (LA114_0==FORMAL_GENERIC) ) {
                    alt114=1;
                }


                switch (alt114) {
            	case 1 :
            	    // BONSTTreeWalker.g:930:46: fgl+= formal_generic
            	    {
            	    pushFollow(FOLLOW_formal_generic_in_formal_generic_list16532);
            	    fgl=formal_generic();
            	    _fsp--;

            	    if (list_fgl==null) list_fgl=new ArrayList();
            	    list_fgl.add(fgl.getTemplate());


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

            // TEMPLATE REWRITE
            // 932:23: -> formalGenericList(fgl=$fgl)
            {
                retval.st = templateLib.getInstanceOf("formalGenericList",
              new STAttrMap().put("fgl", list_fgl));
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
    // $ANTLR end formal_generic_list

    public static class formal_generic_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start formal_generic
    // BONSTTreeWalker.g:936:1: formal_generic : ^( FORMAL_GENERIC formal_generic_name (t+= class_type )? ) -> formalGeneric(name=$formal_generic_name.sttype=$t);
    public final formal_generic_return formal_generic() throws RecognitionException {
        formal_generic_return retval = new formal_generic_return();
        retval.start = input.LT(1);

        List list_t=null;
        formal_generic_name_return formal_generic_name111 = null;

        RuleReturnScope t = null;
        try {
            // BONSTTreeWalker.g:936:17: ( ^( FORMAL_GENERIC formal_generic_name (t+= class_type )? ) -> formalGeneric(name=$formal_generic_name.sttype=$t))
            // BONSTTreeWalker.g:936:18: ^( FORMAL_GENERIC formal_generic_name (t+= class_type )? )
            {
            match(input,FORMAL_GENERIC,FOLLOW_FORMAL_GENERIC_in_formal_generic16686); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_formal_generic_name_in_formal_generic16688);
            formal_generic_name111=formal_generic_name();
            _fsp--;

            // BONSTTreeWalker.g:937:55: (t+= class_type )?
            int alt115=2;
            int LA115_0 = input.LA(1);

            if ( (LA115_0==CLASS_TYPE) ) {
                alt115=1;
            }
            switch (alt115) {
                case 1 :
                    // BONSTTreeWalker.g:937:56: t+= class_type
                    {
                    pushFollow(FOLLOW_class_type_in_formal_generic16693);
                    t=class_type();
                    _fsp--;

                    if (list_t==null) list_t=new ArrayList();
                    list_t.add(t.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 939:18: -> formalGeneric(name=$formal_generic_name.sttype=$t)
            {
                retval.st = templateLib.getInstanceOf("formalGeneric",
              new STAttrMap().put("name", formal_generic_name111.st).put("type", list_t));
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
    // $ANTLR end formal_generic

    public static class formal_generic_name_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start formal_generic_name
    // BONSTTreeWalker.g:943:1: formal_generic_name : ^( FORMAL_GENERIC_NAME IDENTIFIER ) -> formalGenericName(name=$IDENTIFIER.text);
    public final formal_generic_name_return formal_generic_name() throws RecognitionException {
        formal_generic_name_return retval = new formal_generic_name_return();
        retval.start = input.LT(1);

        CommonTree IDENTIFIER112=null;

        try {
            // BONSTTreeWalker.g:943:22: ( ^( FORMAL_GENERIC_NAME IDENTIFIER ) -> formalGenericName(name=$IDENTIFIER.text))
            // BONSTTreeWalker.g:943:23: ^( FORMAL_GENERIC_NAME IDENTIFIER )
            {
            match(input,FORMAL_GENERIC_NAME,FOLLOW_FORMAL_GENERIC_NAME_in_formal_generic_name16831); 

            match(input, Token.DOWN, null); 
            IDENTIFIER112=(CommonTree)input.LT(1);
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_formal_generic_name16833); 

            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 946:23: -> formalGenericName(name=$IDENTIFIER.text)
            {
                retval.st = templateLib.getInstanceOf("formalGenericName",
              new STAttrMap().put("name", IDENTIFIER112.getText()));
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
    // $ANTLR end formal_generic_name

    public static class class_type_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start class_type
    // BONSTTreeWalker.g:950:1: class_type : ^( CLASS_TYPE class_name (ag+= actual_generics )? ) -> classType(name=$class_name.stgen=$ag);
    public final class_type_return class_type() throws RecognitionException {
        class_type_return retval = new class_type_return();
        retval.start = input.LT(1);

        List list_ag=null;
        class_name_return class_name113 = null;

        RuleReturnScope ag = null;
        try {
            // BONSTTreeWalker.g:950:13: ( ^( CLASS_TYPE class_name (ag+= actual_generics )? ) -> classType(name=$class_name.stgen=$ag))
            // BONSTTreeWalker.g:950:14: ^( CLASS_TYPE class_name (ag+= actual_generics )? )
            {
            match(input,CLASS_TYPE,FOLLOW_CLASS_TYPE_in_class_type16981); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_class_name_in_class_type16983);
            class_name113=class_name();
            _fsp--;

            // BONSTTreeWalker.g:951:38: (ag+= actual_generics )?
            int alt116=2;
            int LA116_0 = input.LA(1);

            if ( (LA116_0==ACTUAL_GENERICS) ) {
                alt116=1;
            }
            switch (alt116) {
                case 1 :
                    // BONSTTreeWalker.g:951:39: ag+= actual_generics
                    {
                    pushFollow(FOLLOW_actual_generics_in_class_type16988);
                    ag=actual_generics();
                    _fsp--;

                    if (list_ag==null) list_ag=new ArrayList();
                    list_ag.add(ag.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 953:14: -> classType(name=$class_name.stgen=$ag)
            {
                retval.st = templateLib.getInstanceOf("classType",
              new STAttrMap().put("name", class_name113.st).put("gen", list_ag));
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
    // $ANTLR end class_type

    public static class actual_generics_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start actual_generics
    // BONSTTreeWalker.g:957:1: actual_generics : ^( ACTUAL_GENERICS type_list ) -> actualGenerics(tl=$type_list.st);
    public final actual_generics_return actual_generics() throws RecognitionException {
        actual_generics_return retval = new actual_generics_return();
        retval.start = input.LT(1);

        type_list_return type_list114 = null;


        try {
            // BONSTTreeWalker.g:957:18: ( ^( ACTUAL_GENERICS type_list ) -> actualGenerics(tl=$type_list.st))
            // BONSTTreeWalker.g:957:19: ^( ACTUAL_GENERICS type_list )
            {
            match(input,ACTUAL_GENERICS,FOLLOW_ACTUAL_GENERICS_in_actual_generics17103); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_type_list_in_actual_generics17105);
            type_list114=type_list();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 960:19: -> actualGenerics(tl=$type_list.st)
            {
                retval.st = templateLib.getInstanceOf("actualGenerics",
              new STAttrMap().put("tl", type_list114.st));
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
    // $ANTLR end actual_generics

    public static class type_list_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start type_list
    // BONSTTreeWalker.g:964:1: type_list : ^( TYPE_LIST (tl+= type )+ ) -> typeList(tl=$tl);
    public final type_list_return type_list() throws RecognitionException {
        type_list_return retval = new type_list_return();
        retval.start = input.LT(1);

        List list_tl=null;
        RuleReturnScope tl = null;
        try {
            // BONSTTreeWalker.g:964:12: ( ^( TYPE_LIST (tl+= type )+ ) -> typeList(tl=$tl))
            // BONSTTreeWalker.g:964:13: ^( TYPE_LIST (tl+= type )+ )
            {
            match(input,TYPE_LIST,FOLLOW_TYPE_LIST_in_type_list17233); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:965:25: (tl+= type )+
            int cnt117=0;
            loop117:
            do {
                int alt117=2;
                int LA117_0 = input.LA(1);

                if ( (LA117_0==TYPE) ) {
                    alt117=1;
                }


                switch (alt117) {
            	case 1 :
            	    // BONSTTreeWalker.g:965:26: tl+= type
            	    {
            	    pushFollow(FOLLOW_type_in_type_list17238);
            	    tl=type();
            	    _fsp--;

            	    if (list_tl==null) list_tl=new ArrayList();
            	    list_tl.add(tl.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt117 >= 1 ) break loop117;
                        EarlyExitException eee =
                            new EarlyExitException(117, input);
                        throw eee;
                }
                cnt117++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 967:13: -> typeList(tl=$tl)
            {
                retval.st = templateLib.getInstanceOf("typeList",
              new STAttrMap().put("tl", list_tl));
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
    // $ANTLR end type_list

    public static class type_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start type
    // BONSTTreeWalker.g:971:1: type : ^( TYPE IDENTIFIER (ag+= actual_generics )? ) -> type(id=$IDENTIFIER.textgen=$ag);
    public final type_return type() throws RecognitionException {
        type_return retval = new type_return();
        retval.start = input.LT(1);

        CommonTree IDENTIFIER115=null;
        List list_ag=null;
        RuleReturnScope ag = null;
        try {
            // BONSTTreeWalker.g:971:7: ( ^( TYPE IDENTIFIER (ag+= actual_generics )? ) -> type(id=$IDENTIFIER.textgen=$ag))
            // BONSTTreeWalker.g:971:8: ^( TYPE IDENTIFIER (ag+= actual_generics )? )
            {
            match(input,TYPE,FOLLOW_TYPE_in_type17321); 

            match(input, Token.DOWN, null); 
            IDENTIFIER115=(CommonTree)input.LT(1);
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_type17323); 
            // BONSTTreeWalker.g:972:26: (ag+= actual_generics )?
            int alt118=2;
            int LA118_0 = input.LA(1);

            if ( (LA118_0==ACTUAL_GENERICS) ) {
                alt118=1;
            }
            switch (alt118) {
                case 1 :
                    // BONSTTreeWalker.g:972:27: ag+= actual_generics
                    {
                    pushFollow(FOLLOW_actual_generics_in_type17328);
                    ag=actual_generics();
                    _fsp--;

                    if (list_ag==null) list_ag=new ArrayList();
                    list_ag.add(ag.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 974:8: -> type(id=$IDENTIFIER.textgen=$ag)
            {
                retval.st = templateLib.getInstanceOf("type",
              new STAttrMap().put("id", IDENTIFIER115.getText()).put("gen", list_ag));
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
    // $ANTLR end type

    public static class assertion_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start assertion
    // BONSTTreeWalker.g:978:1: assertion : ^( ASSERTION (acl+= assertion_clause )+ ) -> assertion(acl=$acl);
    public final assertion_return assertion() throws RecognitionException {
        assertion_return retval = new assertion_return();
        retval.start = input.LT(1);

        List list_acl=null;
        RuleReturnScope acl = null;
        try {
            // BONSTTreeWalker.g:982:12: ( ^( ASSERTION (acl+= assertion_clause )+ ) -> assertion(acl=$acl))
            // BONSTTreeWalker.g:982:13: ^( ASSERTION (acl+= assertion_clause )+ )
            {
            match(input,ASSERTION,FOLLOW_ASSERTION_in_assertion17403); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:983:25: (acl+= assertion_clause )+
            int cnt119=0;
            loop119:
            do {
                int alt119=2;
                int LA119_0 = input.LA(1);

                if ( (LA119_0==ASSERTION_CLAUSE) ) {
                    alt119=1;
                }


                switch (alt119) {
            	case 1 :
            	    // BONSTTreeWalker.g:983:26: acl+= assertion_clause
            	    {
            	    pushFollow(FOLLOW_assertion_clause_in_assertion17408);
            	    acl=assertion_clause();
            	    _fsp--;

            	    if (list_acl==null) list_acl=new ArrayList();
            	    list_acl.add(acl.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt119 >= 1 ) break loop119;
                        EarlyExitException eee =
                            new EarlyExitException(119, input);
                        throw eee;
                }
                cnt119++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 985:13: -> assertion(acl=$acl)
            {
                retval.st = templateLib.getInstanceOf("assertion",
              new STAttrMap().put("acl", list_acl));
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
    // $ANTLR end assertion

    public static class assertion_clause_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start assertion_clause
    // BONSTTreeWalker.g:989:1: assertion_clause : ^( ASSERTION_CLAUSE boolean_expression ) -> assertionClause(exp=$boolean_expression.st);
    public final assertion_clause_return assertion_clause() throws RecognitionException {
        assertion_clause_return retval = new assertion_clause_return();
        retval.start = input.LT(1);

        boolean_expression_return boolean_expression116 = null;


        try {
            // BONSTTreeWalker.g:989:19: ( ^( ASSERTION_CLAUSE boolean_expression ) -> assertionClause(exp=$boolean_expression.st))
            // BONSTTreeWalker.g:989:20: ^( ASSERTION_CLAUSE boolean_expression )
            {
            match(input,ASSERTION_CLAUSE,FOLLOW_ASSERTION_CLAUSE_in_assertion_clause17514); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_boolean_expression_in_assertion_clause17516);
            boolean_expression116=boolean_expression();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 992:20: -> assertionClause(exp=$boolean_expression.st)
            {
                retval.st = templateLib.getInstanceOf("assertionClause",
              new STAttrMap().put("exp", boolean_expression116.st));
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
    // $ANTLR end assertion_clause

    public static class boolean_expression_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start boolean_expression
    // BONSTTreeWalker.g:996:1: boolean_expression : ^( BOOLEAN_EXPRESSION expression ) -> booleanExpression(exp=$expression.st);
    public final boolean_expression_return boolean_expression() throws RecognitionException {
        boolean_expression_return retval = new boolean_expression_return();
        retval.start = input.LT(1);

        expression_return expression117 = null;


        try {
            // BONSTTreeWalker.g:996:21: ( ^( BOOLEAN_EXPRESSION expression ) -> booleanExpression(exp=$expression.st))
            // BONSTTreeWalker.g:996:22: ^( BOOLEAN_EXPRESSION expression )
            {
            match(input,BOOLEAN_EXPRESSION,FOLLOW_BOOLEAN_EXPRESSION_in_boolean_expression17656); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_expression_in_boolean_expression17658);
            expression117=expression();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 999:22: -> booleanExpression(exp=$expression.st)
            {
                retval.st = templateLib.getInstanceOf("booleanExpression",
              new STAttrMap().put("exp", expression117.st));
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
    // $ANTLR end boolean_expression

    public static class quantification_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start quantification
    // BONSTTreeWalker.g:1003:1: quantification : ^( QUANTIFICATION quantifier range_expression (restr+= restriction )? proposition ) -> quantification(q=$quantifier.stre=$range_expression.strestr=$restrprop=$proposition.st);
    public final quantification_return quantification() throws RecognitionException {
        quantification_return retval = new quantification_return();
        retval.start = input.LT(1);

        List list_restr=null;
        quantifier_return quantifier118 = null;

        range_expression_return range_expression119 = null;

        proposition_return proposition120 = null;

        RuleReturnScope restr = null;
        try {
            // BONSTTreeWalker.g:1003:17: ( ^( QUANTIFICATION quantifier range_expression (restr+= restriction )? proposition ) -> quantification(q=$quantifier.stre=$range_expression.strestr=$restrprop=$proposition.st))
            // BONSTTreeWalker.g:1003:18: ^( QUANTIFICATION quantifier range_expression (restr+= restriction )? proposition )
            {
            match(input,QUANTIFICATION,FOLLOW_QUANTIFICATION_in_quantification17797); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_quantifier_in_quantification17818);
            quantifier118=quantifier();
            _fsp--;

            pushFollow(FOLLOW_range_expression_in_quantification17841);
            range_expression119=range_expression();
            _fsp--;

            // BONSTTreeWalker.g:1007:20: (restr+= restriction )?
            int alt120=2;
            int LA120_0 = input.LA(1);

            if ( (LA120_0==RESTRICTION) ) {
                alt120=1;
            }
            switch (alt120) {
                case 1 :
                    // BONSTTreeWalker.g:1007:21: restr+= restriction
                    {
                    pushFollow(FOLLOW_restriction_in_quantification17866);
                    restr=restriction();
                    _fsp--;

                    if (list_restr==null) list_restr=new ArrayList();
                    list_restr.add(restr.getTemplate());


                    }
                    break;

            }

            pushFollow(FOLLOW_proposition_in_quantification17890);
            proposition120=proposition();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1010:18: -> quantification(q=$quantifier.stre=$range_expression.strestr=$restrprop=$proposition.st)
            {
                retval.st = templateLib.getInstanceOf("quantification",
              new STAttrMap().put("q", quantifier118.st).put("re", range_expression119.st).put("restr", list_restr).put("prop", proposition120.st));
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
    // $ANTLR end quantification

    public static class quantifier_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start quantifier
    // BONSTTreeWalker.g:1014:1: quantifier : ( ^( QUANTIFIER t= 'for_all' ) -> quantifier(t=$t.text) | ^( QUANTIFIER t= 'exists' ) -> quantifier(t=$t.text));
    public final quantifier_return quantifier() throws RecognitionException {
        quantifier_return retval = new quantifier_return();
        retval.start = input.LT(1);

        CommonTree t=null;

        try {
            // BONSTTreeWalker.g:1014:13: ( ^( QUANTIFIER t= 'for_all' ) -> quantifier(t=$t.text) | ^( QUANTIFIER t= 'exists' ) -> quantifier(t=$t.text))
            int alt121=2;
            int LA121_0 = input.LA(1);

            if ( (LA121_0==QUANTIFIER) ) {
                int LA121_1 = input.LA(2);

                if ( (LA121_1==DOWN) ) {
                    int LA121_2 = input.LA(3);

                    if ( (LA121_2==242) ) {
                        alt121=1;
                    }
                    else if ( (LA121_2==243) ) {
                        alt121=2;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("1014:1: quantifier : ( ^( QUANTIFIER t= 'for_all' ) -> quantifier(t=$t.text) | ^( QUANTIFIER t= 'exists' ) -> quantifier(t=$t.text));", 121, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1014:1: quantifier : ( ^( QUANTIFIER t= 'for_all' ) -> quantifier(t=$t.text) | ^( QUANTIFIER t= 'exists' ) -> quantifier(t=$t.text));", 121, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1014:1: quantifier : ( ^( QUANTIFIER t= 'for_all' ) -> quantifier(t=$t.text) | ^( QUANTIFIER t= 'exists' ) -> quantifier(t=$t.text));", 121, 0, input);

                throw nvae;
            }
            switch (alt121) {
                case 1 :
                    // BONSTTreeWalker.g:1014:14: ^( QUANTIFIER t= 'for_all' )
                    {
                    match(input,QUANTIFIER,FOLLOW_QUANTIFIER_in_quantifier18026); 

                    match(input, Token.DOWN, null); 
                    t=(CommonTree)input.LT(1);
                    match(input,242,FOLLOW_242_in_quantifier18030); 

                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1017:14: -> quantifier(t=$t.text)
                    {
                        retval.st = templateLib.getInstanceOf("quantifier",
                      new STAttrMap().put("t", t.getText()));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1020:14: ^( QUANTIFIER t= 'exists' )
                    {
                    match(input,QUANTIFIER,FOLLOW_QUANTIFIER_in_quantifier18130); 

                    match(input, Token.DOWN, null); 
                    t=(CommonTree)input.LT(1);
                    match(input,243,FOLLOW_243_in_quantifier18134); 

                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1023:14: -> quantifier(t=$t.text)
                    {
                        retval.st = templateLib.getInstanceOf("quantifier",
                      new STAttrMap().put("t", t.getText()));
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
        return retval;
    }
    // $ANTLR end quantifier

    public static class range_expression_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start range_expression
    // BONSTTreeWalker.g:1027:1: range_expression : ^( RANGE_EXPRESSION (vrl+= variable_range )+ ) -> rangeExpression(vrl=$vrl);
    public final range_expression_return range_expression() throws RecognitionException {
        range_expression_return retval = new range_expression_return();
        retval.start = input.LT(1);

        List list_vrl=null;
        RuleReturnScope vrl = null;
        try {
            // BONSTTreeWalker.g:1027:19: ( ^( RANGE_EXPRESSION (vrl+= variable_range )+ ) -> rangeExpression(vrl=$vrl))
            // BONSTTreeWalker.g:1027:20: ^( RANGE_EXPRESSION (vrl+= variable_range )+ )
            {
            match(input,RANGE_EXPRESSION,FOLLOW_RANGE_EXPRESSION_in_range_expression18243); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:1028:39: (vrl+= variable_range )+
            int cnt122=0;
            loop122:
            do {
                int alt122=2;
                int LA122_0 = input.LA(1);

                if ( (LA122_0==VARIABLE_RANGE) ) {
                    alt122=1;
                }


                switch (alt122) {
            	case 1 :
            	    // BONSTTreeWalker.g:1028:40: vrl+= variable_range
            	    {
            	    pushFollow(FOLLOW_variable_range_in_range_expression18248);
            	    vrl=variable_range();
            	    _fsp--;

            	    if (list_vrl==null) list_vrl=new ArrayList();
            	    list_vrl.add(vrl.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt122 >= 1 ) break loop122;
                        EarlyExitException eee =
                            new EarlyExitException(122, input);
                        throw eee;
                }
                cnt122++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1030:20: -> rangeExpression(vrl=$vrl)
            {
                retval.st = templateLib.getInstanceOf("rangeExpression",
              new STAttrMap().put("vrl", list_vrl));
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
    // $ANTLR end range_expression

    public static class restriction_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start restriction
    // BONSTTreeWalker.g:1034:1: restriction : ^( RESTRICTION boolean_expression ) -> restriction(exp=$boolean_expression.st);
    public final restriction_return restriction() throws RecognitionException {
        restriction_return retval = new restriction_return();
        retval.start = input.LT(1);

        boolean_expression_return boolean_expression121 = null;


        try {
            // BONSTTreeWalker.g:1034:14: ( ^( RESTRICTION boolean_expression ) -> restriction(exp=$boolean_expression.st))
            // BONSTTreeWalker.g:1034:15: ^( RESTRICTION boolean_expression )
            {
            match(input,RESTRICTION,FOLLOW_RESTRICTION_in_restriction18384); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_boolean_expression_in_restriction18386);
            boolean_expression121=boolean_expression();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1037:15: -> restriction(exp=$boolean_expression.st)
            {
                retval.st = templateLib.getInstanceOf("restriction",
              new STAttrMap().put("exp", boolean_expression121.st));
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
    // $ANTLR end restriction

    public static class proposition_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start proposition
    // BONSTTreeWalker.g:1041:1: proposition : ^( PROPOSITION boolean_expression ) -> poposition(exp=$boolean_expression.st);
    public final proposition_return proposition() throws RecognitionException {
        proposition_return retval = new proposition_return();
        retval.start = input.LT(1);

        boolean_expression_return boolean_expression122 = null;


        try {
            // BONSTTreeWalker.g:1041:14: ( ^( PROPOSITION boolean_expression ) -> poposition(exp=$boolean_expression.st))
            // BONSTTreeWalker.g:1041:15: ^( PROPOSITION boolean_expression )
            {
            match(input,PROPOSITION,FOLLOW_PROPOSITION_in_proposition18496); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_boolean_expression_in_proposition18498);
            boolean_expression122=boolean_expression();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1044:15: -> poposition(exp=$boolean_expression.st)
            {
                retval.st = templateLib.getInstanceOf("poposition",
              new STAttrMap().put("exp", boolean_expression122.st));
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
    // $ANTLR end proposition

    public static class variable_range_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start variable_range
    // BONSTTreeWalker.g:1048:1: variable_range : ( ^( VARIABLE_RANGE member_range ) -> variableRange(r=$member_range.st) | ^( VARIABLE_RANGE type_range ) -> variableRange(r=$type_range.st));
    public final variable_range_return variable_range() throws RecognitionException {
        variable_range_return retval = new variable_range_return();
        retval.start = input.LT(1);

        member_range_return member_range123 = null;

        type_range_return type_range124 = null;


        try {
            // BONSTTreeWalker.g:1048:17: ( ^( VARIABLE_RANGE member_range ) -> variableRange(r=$member_range.st) | ^( VARIABLE_RANGE type_range ) -> variableRange(r=$type_range.st))
            int alt123=2;
            int LA123_0 = input.LA(1);

            if ( (LA123_0==VARIABLE_RANGE) ) {
                int LA123_1 = input.LA(2);

                if ( (LA123_1==DOWN) ) {
                    int LA123_2 = input.LA(3);

                    if ( (LA123_2==MEMBER_RANGE) ) {
                        alt123=1;
                    }
                    else if ( (LA123_2==TYPE_RANGE) ) {
                        alt123=2;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("1048:1: variable_range : ( ^( VARIABLE_RANGE member_range ) -> variableRange(r=$member_range.st) | ^( VARIABLE_RANGE type_range ) -> variableRange(r=$type_range.st));", 123, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1048:1: variable_range : ( ^( VARIABLE_RANGE member_range ) -> variableRange(r=$member_range.st) | ^( VARIABLE_RANGE type_range ) -> variableRange(r=$type_range.st));", 123, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1048:1: variable_range : ( ^( VARIABLE_RANGE member_range ) -> variableRange(r=$member_range.st) | ^( VARIABLE_RANGE type_range ) -> variableRange(r=$type_range.st));", 123, 0, input);

                throw nvae;
            }
            switch (alt123) {
                case 1 :
                    // BONSTTreeWalker.g:1048:18: ^( VARIABLE_RANGE member_range )
                    {
                    match(input,VARIABLE_RANGE,FOLLOW_VARIABLE_RANGE_in_variable_range18610); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_member_range_in_variable_range18612);
                    member_range123=member_range();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1051:18: -> variableRange(r=$member_range.st)
                    {
                        retval.st = templateLib.getInstanceOf("variableRange",
                      new STAttrMap().put("r", member_range123.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1054:18: ^( VARIABLE_RANGE type_range )
                    {
                    match(input,VARIABLE_RANGE,FOLLOW_VARIABLE_RANGE_in_variable_range18736); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_type_range_in_variable_range18738);
                    type_range124=type_range();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1057:18: -> variableRange(r=$type_range.st)
                    {
                        retval.st = templateLib.getInstanceOf("variableRange",
                      new STAttrMap().put("r", type_range124.st));
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
        return retval;
    }
    // $ANTLR end variable_range

    public static class member_range_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start member_range
    // BONSTTreeWalker.g:1061:1: member_range : ^( MEMBER_RANGE identifier_list expression ) -> memberRange(il=$identifier_list.stexp=$expression.st);
    public final member_range_return member_range() throws RecognitionException {
        member_range_return retval = new member_range_return();
        retval.start = input.LT(1);

        identifier_list_return identifier_list125 = null;

        expression_return expression126 = null;


        try {
            // BONSTTreeWalker.g:1061:15: ( ^( MEMBER_RANGE identifier_list expression ) -> memberRange(il=$identifier_list.stexp=$expression.st))
            // BONSTTreeWalker.g:1061:16: ^( MEMBER_RANGE identifier_list expression )
            {
            match(input,MEMBER_RANGE,FOLLOW_MEMBER_RANGE_in_member_range18863); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_identifier_list_in_member_range18865);
            identifier_list125=identifier_list();
            _fsp--;

            pushFollow(FOLLOW_expression_in_member_range18867);
            expression126=expression();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1064:16: -> memberRange(il=$identifier_list.stexp=$expression.st)
            {
                retval.st = templateLib.getInstanceOf("memberRange",
              new STAttrMap().put("il", identifier_list125.st).put("exp", expression126.st));
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
    // $ANTLR end member_range

    public static class type_range_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start type_range
    // BONSTTreeWalker.g:1068:1: type_range : ^( TYPE_RANGE identifier_list type ) -> typeRange(il=$identifier_list.sttype=$type.st);
    public final type_range_return type_range() throws RecognitionException {
        type_range_return retval = new type_range_return();
        retval.start = input.LT(1);

        identifier_list_return identifier_list127 = null;

        type_return type128 = null;


        try {
            // BONSTTreeWalker.g:1068:13: ( ^( TYPE_RANGE identifier_list type ) -> typeRange(il=$identifier_list.sttype=$type.st))
            // BONSTTreeWalker.g:1068:14: ^( TYPE_RANGE identifier_list type )
            {
            match(input,TYPE_RANGE,FOLLOW_TYPE_RANGE_in_type_range18984); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_identifier_list_in_type_range18986);
            identifier_list127=identifier_list();
            _fsp--;

            pushFollow(FOLLOW_type_in_type_range18988);
            type128=type();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1071:14: -> typeRange(il=$identifier_list.sttype=$type.st)
            {
                retval.st = templateLib.getInstanceOf("typeRange",
              new STAttrMap().put("il", identifier_list127.st).put("type", type128.st));
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
    // $ANTLR end type_range

    public static class call_chain_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start call_chain
    // BONSTTreeWalker.g:1075:1: call_chain : ^( CALL_CHAIN (ucl+= unqualified_call )+ ) -> callChain(ucl=$ucl);
    public final call_chain_return call_chain() throws RecognitionException {
        call_chain_return retval = new call_chain_return();
        retval.start = input.LT(1);

        List list_ucl=null;
        RuleReturnScope ucl = null;
        try {
            // BONSTTreeWalker.g:1085:13: ( ^( CALL_CHAIN (ucl+= unqualified_call )+ ) -> callChain(ucl=$ucl))
            // BONSTTreeWalker.g:1085:14: ^( CALL_CHAIN (ucl+= unqualified_call )+ )
            {
            match(input,CALL_CHAIN,FOLLOW_CALL_CHAIN_in_call_chain19119); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:1086:27: (ucl+= unqualified_call )+
            int cnt124=0;
            loop124:
            do {
                int alt124=2;
                int LA124_0 = input.LA(1);

                if ( (LA124_0==UNQUALIFIED_CALL) ) {
                    alt124=1;
                }


                switch (alt124) {
            	case 1 :
            	    // BONSTTreeWalker.g:1086:28: ucl+= unqualified_call
            	    {
            	    pushFollow(FOLLOW_unqualified_call_in_call_chain19124);
            	    ucl=unqualified_call();
            	    _fsp--;

            	    if (list_ucl==null) list_ucl=new ArrayList();
            	    list_ucl.add(ucl.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt124 >= 1 ) break loop124;
                        EarlyExitException eee =
                            new EarlyExitException(124, input);
                        throw eee;
                }
                cnt124++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1088:14: -> callChain(ucl=$ucl)
            {
                retval.st = templateLib.getInstanceOf("callChain",
              new STAttrMap().put("ucl", list_ucl));
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
    // $ANTLR end call_chain

    public static class unqualified_call_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start unqualified_call
    // BONSTTreeWalker.g:1092:1: unqualified_call : ^( UNQUALIFIED_CALL IDENTIFIER (aa+= actual_arguments )? ) -> unqualifiedCall(id=$IDENTIFIER.textaa=$aa);
    public final unqualified_call_return unqualified_call() throws RecognitionException {
        unqualified_call_return retval = new unqualified_call_return();
        retval.start = input.LT(1);

        CommonTree IDENTIFIER129=null;
        List list_aa=null;
        RuleReturnScope aa = null;
        try {
            // BONSTTreeWalker.g:1092:19: ( ^( UNQUALIFIED_CALL IDENTIFIER (aa+= actual_arguments )? ) -> unqualifiedCall(id=$IDENTIFIER.textaa=$aa))
            // BONSTTreeWalker.g:1092:20: ^( UNQUALIFIED_CALL IDENTIFIER (aa+= actual_arguments )? )
            {
            match(input,UNQUALIFIED_CALL,FOLLOW_UNQUALIFIED_CALL_in_unqualified_call19235); 

            match(input, Token.DOWN, null); 
            IDENTIFIER129=(CommonTree)input.LT(1);
            match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_unqualified_call19237); 
            // BONSTTreeWalker.g:1093:50: (aa+= actual_arguments )?
            int alt125=2;
            int LA125_0 = input.LA(1);

            if ( (LA125_0==ACTUAL_ARGUMENTS) ) {
                alt125=1;
            }
            switch (alt125) {
                case 1 :
                    // BONSTTreeWalker.g:1093:51: aa+= actual_arguments
                    {
                    pushFollow(FOLLOW_actual_arguments_in_unqualified_call19242);
                    aa=actual_arguments();
                    _fsp--;

                    if (list_aa==null) list_aa=new ArrayList();
                    list_aa.add(aa.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1095:20: -> unqualifiedCall(id=$IDENTIFIER.textaa=$aa)
            {
                retval.st = templateLib.getInstanceOf("unqualifiedCall",
              new STAttrMap().put("id", IDENTIFIER129.getText()).put("aa", list_aa));
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
    // $ANTLR end unqualified_call

    public static class actual_arguments_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start actual_arguments
    // BONSTTreeWalker.g:1099:1: actual_arguments : ( ACTUAL_ARGUMENTS -> actualArguments() | ^( ACTUAL_ARGUMENTS expression_list ) -> actualArguments(el=$expression_list.st));
    public final actual_arguments_return actual_arguments() throws RecognitionException {
        actual_arguments_return retval = new actual_arguments_return();
        retval.start = input.LT(1);

        expression_list_return expression_list130 = null;


        try {
            // BONSTTreeWalker.g:1099:19: ( ACTUAL_ARGUMENTS -> actualArguments() | ^( ACTUAL_ARGUMENTS expression_list ) -> actualArguments(el=$expression_list.st))
            int alt126=2;
            int LA126_0 = input.LA(1);

            if ( (LA126_0==ACTUAL_ARGUMENTS) ) {
                int LA126_1 = input.LA(2);

                if ( (LA126_1==DOWN) ) {
                    alt126=2;
                }
                else if ( (LA126_1==UP) ) {
                    alt126=1;
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1099:1: actual_arguments : ( ACTUAL_ARGUMENTS -> actualArguments() | ^( ACTUAL_ARGUMENTS expression_list ) -> actualArguments(el=$expression_list.st));", 126, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1099:1: actual_arguments : ( ACTUAL_ARGUMENTS -> actualArguments() | ^( ACTUAL_ARGUMENTS expression_list ) -> actualArguments(el=$expression_list.st));", 126, 0, input);

                throw nvae;
            }
            switch (alt126) {
                case 1 :
                    // BONSTTreeWalker.g:1099:21: ACTUAL_ARGUMENTS
                    {
                    match(input,ACTUAL_ARGUMENTS,FOLLOW_ACTUAL_ARGUMENTS_in_actual_arguments19366); 

                    // TEMPLATE REWRITE
                    // 1100:20: -> actualArguments()
                    {
                        retval.st = templateLib.getInstanceOf("actualArguments");
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1103:21: ^( ACTUAL_ARGUMENTS expression_list )
                    {
                    match(input,ACTUAL_ARGUMENTS,FOLLOW_ACTUAL_ARGUMENTS_in_actual_arguments19480); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_expression_list_in_actual_arguments19482);
                    expression_list130=expression_list();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1106:20: -> actualArguments(el=$expression_list.st)
                    {
                        retval.st = templateLib.getInstanceOf("actualArguments",
                      new STAttrMap().put("el", expression_list130.st));
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
        return retval;
    }
    // $ANTLR end actual_arguments

    public static class expression_list_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start expression_list
    // BONSTTreeWalker.g:1110:1: expression_list : ^( EXPRESSION_LIST (el+= expression )+ ) -> expressionList(el=$el);
    public final expression_list_return expression_list() throws RecognitionException {
        expression_list_return retval = new expression_list_return();
        retval.start = input.LT(1);

        List list_el=null;
        RuleReturnScope el = null;
        try {
            // BONSTTreeWalker.g:1110:18: ( ^( EXPRESSION_LIST (el+= expression )+ ) -> expressionList(el=$el))
            // BONSTTreeWalker.g:1110:19: ^( EXPRESSION_LIST (el+= expression )+ )
            {
            match(input,EXPRESSION_LIST,FOLLOW_EXPRESSION_LIST_in_expression_list19617); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:1111:37: (el+= expression )+
            int cnt127=0;
            loop127:
            do {
                int alt127=2;
                int LA127_0 = input.LA(1);

                if ( (LA127_0==EXPRESSION) ) {
                    alt127=1;
                }


                switch (alt127) {
            	case 1 :
            	    // BONSTTreeWalker.g:1111:38: el+= expression
            	    {
            	    pushFollow(FOLLOW_expression_in_expression_list19622);
            	    el=expression();
            	    _fsp--;

            	    if (list_el==null) list_el=new ArrayList();
            	    list_el.add(el.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt127 >= 1 ) break loop127;
                        EarlyExitException eee =
                            new EarlyExitException(127, input);
                        throw eee;
                }
                cnt127++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1113:19: -> expressionList(el=$el)
            {
                retval.st = templateLib.getInstanceOf("expressionList",
              new STAttrMap().put("el", list_el));
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
    // $ANTLR end expression_list

    public static class enumerated_set_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start enumerated_set
    // BONSTTreeWalker.g:1117:1: enumerated_set : ^( ENUMERATED_SET enumeration_list ) -> enumeratedSet(el=$enumeration_list.st);
    public final enumerated_set_return enumerated_set() throws RecognitionException {
        enumerated_set_return retval = new enumerated_set_return();
        retval.start = input.LT(1);

        enumeration_list_return enumeration_list131 = null;


        try {
            // BONSTTreeWalker.g:1119:17: ( ^( ENUMERATED_SET enumeration_list ) -> enumeratedSet(el=$enumeration_list.st))
            // BONSTTreeWalker.g:1119:18: ^( ENUMERATED_SET enumeration_list )
            {
            match(input,ENUMERATED_SET,FOLLOW_ENUMERATED_SET_in_enumerated_set19758); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_enumeration_list_in_enumerated_set19760);
            enumeration_list131=enumeration_list();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1122:18: -> enumeratedSet(el=$enumeration_list.st)
            {
                retval.st = templateLib.getInstanceOf("enumeratedSet",
              new STAttrMap().put("el", enumeration_list131.st));
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
    // $ANTLR end enumerated_set

    public static class enumeration_list_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start enumeration_list
    // BONSTTreeWalker.g:1126:1: enumeration_list : ^( ENUMERATION_LIST (el+= enumeration_element )+ ) -> enumerationList(el=$el);
    public final enumeration_list_return enumeration_list() throws RecognitionException {
        enumeration_list_return retval = new enumeration_list_return();
        retval.start = input.LT(1);

        List list_el=null;
        RuleReturnScope el = null;
        try {
            // BONSTTreeWalker.g:1126:19: ( ^( ENUMERATION_LIST (el+= enumeration_element )+ ) -> enumerationList(el=$el))
            // BONSTTreeWalker.g:1126:20: ^( ENUMERATION_LIST (el+= enumeration_element )+ )
            {
            match(input,ENUMERATION_LIST,FOLLOW_ENUMERATION_LIST_in_enumeration_list19889); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:1127:39: (el+= enumeration_element )+
            int cnt128=0;
            loop128:
            do {
                int alt128=2;
                int LA128_0 = input.LA(1);

                if ( (LA128_0==ENUMERATION_ELEMENT) ) {
                    alt128=1;
                }


                switch (alt128) {
            	case 1 :
            	    // BONSTTreeWalker.g:1127:40: el+= enumeration_element
            	    {
            	    pushFollow(FOLLOW_enumeration_element_in_enumeration_list19894);
            	    el=enumeration_element();
            	    _fsp--;

            	    if (list_el==null) list_el=new ArrayList();
            	    list_el.add(el.getTemplate());


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

            // TEMPLATE REWRITE
            // 1129:20: -> enumerationList(el=$el)
            {
                retval.st = templateLib.getInstanceOf("enumerationList",
              new STAttrMap().put("el", list_el));
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
    // $ANTLR end enumeration_list

    public static class enumeration_element_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start enumeration_element
    // BONSTTreeWalker.g:1133:1: enumeration_element : ( ^( ENUMERATION_ELEMENT expression ) -> enumeration_element(ee=$expression.st) | ^( ENUMERATION_ELEMENT interval ) -> enumeration_element(ee=$interval.st));
    public final enumeration_element_return enumeration_element() throws RecognitionException {
        enumeration_element_return retval = new enumeration_element_return();
        retval.start = input.LT(1);

        expression_return expression132 = null;

        interval_return interval133 = null;


        try {
            // BONSTTreeWalker.g:1133:22: ( ^( ENUMERATION_ELEMENT expression ) -> enumeration_element(ee=$expression.st) | ^( ENUMERATION_ELEMENT interval ) -> enumeration_element(ee=$interval.st))
            int alt129=2;
            int LA129_0 = input.LA(1);

            if ( (LA129_0==ENUMERATION_ELEMENT) ) {
                int LA129_1 = input.LA(2);

                if ( (LA129_1==DOWN) ) {
                    int LA129_2 = input.LA(3);

                    if ( (LA129_2==INTERVAL) ) {
                        alt129=2;
                    }
                    else if ( (LA129_2==EXPRESSION) ) {
                        alt129=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("1133:1: enumeration_element : ( ^( ENUMERATION_ELEMENT expression ) -> enumeration_element(ee=$expression.st) | ^( ENUMERATION_ELEMENT interval ) -> enumeration_element(ee=$interval.st));", 129, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1133:1: enumeration_element : ( ^( ENUMERATION_ELEMENT expression ) -> enumeration_element(ee=$expression.st) | ^( ENUMERATION_ELEMENT interval ) -> enumeration_element(ee=$interval.st));", 129, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1133:1: enumeration_element : ( ^( ENUMERATION_ELEMENT expression ) -> enumeration_element(ee=$expression.st) | ^( ENUMERATION_ELEMENT interval ) -> enumeration_element(ee=$interval.st));", 129, 0, input);

                throw nvae;
            }
            switch (alt129) {
                case 1 :
                    // BONSTTreeWalker.g:1133:23: ^( ENUMERATION_ELEMENT expression )
                    {
                    match(input,ENUMERATION_ELEMENT,FOLLOW_ENUMERATION_ELEMENT_in_enumeration_element20029); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_expression_in_enumeration_element20031);
                    expression132=expression();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1136:23: -> enumeration_element(ee=$expression.st)
                    {
                        retval.st = templateLib.getInstanceOf("enumeration_element",
                      new STAttrMap().put("ee", expression132.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1139:23: ^( ENUMERATION_ELEMENT interval )
                    {
                    match(input,ENUMERATION_ELEMENT,FOLLOW_ENUMERATION_ELEMENT_in_enumeration_element20186); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_interval_in_enumeration_element20188);
                    interval133=interval();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1142:23: -> enumeration_element(ee=$interval.st)
                    {
                        retval.st = templateLib.getInstanceOf("enumeration_element",
                      new STAttrMap().put("ee", interval133.st));
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
        return retval;
    }
    // $ANTLR end enumeration_element

    public static class interval_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start interval
    // BONSTTreeWalker.g:1146:1: interval : ( ^( INTERVAL integer_interval ) -> interval(i=$integer_interval.st) | ^( INTERVAL character_interval ) -> interval(i=$character_interval.st));
    public final interval_return interval() throws RecognitionException {
        interval_return retval = new interval_return();
        retval.start = input.LT(1);

        integer_interval_return integer_interval134 = null;

        character_interval_return character_interval135 = null;


        try {
            // BONSTTreeWalker.g:1146:11: ( ^( INTERVAL integer_interval ) -> interval(i=$integer_interval.st) | ^( INTERVAL character_interval ) -> interval(i=$character_interval.st))
            int alt130=2;
            int LA130_0 = input.LA(1);

            if ( (LA130_0==INTERVAL) ) {
                int LA130_1 = input.LA(2);

                if ( (LA130_1==DOWN) ) {
                    int LA130_2 = input.LA(3);

                    if ( (LA130_2==INTEGER_INTERVAL) ) {
                        alt130=1;
                    }
                    else if ( (LA130_2==CHARACTER_INTERVAL) ) {
                        alt130=2;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("1146:1: interval : ( ^( INTERVAL integer_interval ) -> interval(i=$integer_interval.st) | ^( INTERVAL character_interval ) -> interval(i=$character_interval.st));", 130, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1146:1: interval : ( ^( INTERVAL integer_interval ) -> interval(i=$integer_interval.st) | ^( INTERVAL character_interval ) -> interval(i=$character_interval.st));", 130, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1146:1: interval : ( ^( INTERVAL integer_interval ) -> interval(i=$integer_interval.st) | ^( INTERVAL character_interval ) -> interval(i=$character_interval.st));", 130, 0, input);

                throw nvae;
            }
            switch (alt130) {
                case 1 :
                    // BONSTTreeWalker.g:1146:12: ^( INTERVAL integer_interval )
                    {
                    match(input,INTERVAL,FOLLOW_INTERVAL_in_interval20334); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_integer_interval_in_interval20336);
                    integer_interval134=integer_interval();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1149:12: -> interval(i=$integer_interval.st)
                    {
                        retval.st = templateLib.getInstanceOf("interval",
                      new STAttrMap().put("i", integer_interval134.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1152:12: ^( INTERVAL character_interval )
                    {
                    match(input,INTERVAL,FOLLOW_INTERVAL_in_interval20426); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_character_interval_in_interval20428);
                    character_interval135=character_interval();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1155:12: -> interval(i=$character_interval.st)
                    {
                        retval.st = templateLib.getInstanceOf("interval",
                      new STAttrMap().put("i", character_interval135.st));
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
        return retval;
    }
    // $ANTLR end interval

    public static class integer_interval_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start integer_interval
    // BONSTTreeWalker.g:1159:1: integer_interval : ^( INTEGER_INTERVAL i1= integer_constant i2= integer_constant ) -> integerInterval(i1=$i1.texti2=$i2.text);
    public final integer_interval_return integer_interval() throws RecognitionException {
        integer_interval_return retval = new integer_interval_return();
        retval.start = input.LT(1);

        integer_constant_return i1 = null;

        integer_constant_return i2 = null;


        try {
            // BONSTTreeWalker.g:1159:19: ( ^( INTEGER_INTERVAL i1= integer_constant i2= integer_constant ) -> integerInterval(i1=$i1.texti2=$i2.text))
            // BONSTTreeWalker.g:1159:20: ^( INTEGER_INTERVAL i1= integer_constant i2= integer_constant )
            {
            match(input,INTEGER_INTERVAL,FOLLOW_INTEGER_INTERVAL_in_integer_interval20528); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_integer_constant_in_integer_interval20532);
            i1=integer_constant();
            _fsp--;

            pushFollow(FOLLOW_integer_constant_in_integer_interval20536);
            i2=integer_constant();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1162:20: -> integerInterval(i1=$i1.texti2=$i2.text)
            {
                retval.st = templateLib.getInstanceOf("integerInterval",
              new STAttrMap().put("i1", input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(i1.start),
              input.getTreeAdaptor().getTokenStopIndex(i1.start))).put("i2", input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(i2.start),
              input.getTreeAdaptor().getTokenStopIndex(i2.start))));
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
    // $ANTLR end integer_interval

    public static class character_interval_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start character_interval
    // BONSTTreeWalker.g:1166:1: character_interval : ^( CHARACTER_INTERVAL c1= CHARACTER_CONSTANT c2= CHARACTER_CONSTANT ) -> character_interval(c1=$c1.textc2=$c2.text);
    public final character_interval_return character_interval() throws RecognitionException {
        character_interval_return retval = new character_interval_return();
        retval.start = input.LT(1);

        CommonTree c1=null;
        CommonTree c2=null;

        try {
            // BONSTTreeWalker.g:1166:21: ( ^( CHARACTER_INTERVAL c1= CHARACTER_CONSTANT c2= CHARACTER_CONSTANT ) -> character_interval(c1=$c1.textc2=$c2.text))
            // BONSTTreeWalker.g:1166:22: ^( CHARACTER_INTERVAL c1= CHARACTER_CONSTANT c2= CHARACTER_CONSTANT )
            {
            match(input,CHARACTER_INTERVAL,FOLLOW_CHARACTER_INTERVAL_in_character_interval20681); 

            match(input, Token.DOWN, null); 
            c1=(CommonTree)input.LT(1);
            match(input,CHARACTER_CONSTANT,FOLLOW_CHARACTER_CONSTANT_in_character_interval20685); 
            c2=(CommonTree)input.LT(1);
            match(input,CHARACTER_CONSTANT,FOLLOW_CHARACTER_CONSTANT_in_character_interval20689); 

            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1169:22: -> character_interval(c1=$c1.textc2=$c2.text)
            {
                retval.st = templateLib.getInstanceOf("character_interval",
              new STAttrMap().put("c1", c1.getText()).put("c2", c2.getText()));
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
    // $ANTLR end character_interval

    public static class constant_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start constant
    // BONSTTreeWalker.g:1172:1: constant : ( ^( CONSTANT manifest_constant ) -> constant(c=$manifest_constant.st) | ^( CONSTANT t= 'Current' ) -> constant(c=$t.text) | ^( CONSTANT t= 'Void' ) -> constant(c=$t.text));
    public final constant_return constant() throws RecognitionException {
        constant_return retval = new constant_return();
        retval.start = input.LT(1);

        CommonTree t=null;
        manifest_constant_return manifest_constant136 = null;


        try {
            // BONSTTreeWalker.g:1174:11: ( ^( CONSTANT manifest_constant ) -> constant(c=$manifest_constant.st) | ^( CONSTANT t= 'Current' ) -> constant(c=$t.text) | ^( CONSTANT t= 'Void' ) -> constant(c=$t.text))
            int alt131=3;
            int LA131_0 = input.LA(1);

            if ( (LA131_0==CONSTANT) ) {
                int LA131_1 = input.LA(2);

                if ( (LA131_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case 248:
                        {
                        alt131=2;
                        }
                        break;
                    case 249:
                        {
                        alt131=3;
                        }
                        break;
                    case MANIFEST_CONSTANT:
                        {
                        alt131=1;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("1172:1: constant : ( ^( CONSTANT manifest_constant ) -> constant(c=$manifest_constant.st) | ^( CONSTANT t= 'Current' ) -> constant(c=$t.text) | ^( CONSTANT t= 'Void' ) -> constant(c=$t.text));", 131, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1172:1: constant : ( ^( CONSTANT manifest_constant ) -> constant(c=$manifest_constant.st) | ^( CONSTANT t= 'Current' ) -> constant(c=$t.text) | ^( CONSTANT t= 'Void' ) -> constant(c=$t.text));", 131, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1172:1: constant : ( ^( CONSTANT manifest_constant ) -> constant(c=$manifest_constant.st) | ^( CONSTANT t= 'Current' ) -> constant(c=$t.text) | ^( CONSTANT t= 'Void' ) -> constant(c=$t.text));", 131, 0, input);

                throw nvae;
            }
            switch (alt131) {
                case 1 :
                    // BONSTTreeWalker.g:1174:12: ^( CONSTANT manifest_constant )
                    {
                    match(input,CONSTANT,FOLLOW_CONSTANT_in_constant20817); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_manifest_constant_in_constant20819);
                    manifest_constant136=manifest_constant();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1177:12: -> constant(c=$manifest_constant.st)
                    {
                        retval.st = templateLib.getInstanceOf("constant",
                      new STAttrMap().put("c", manifest_constant136.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1180:12: ^( CONSTANT t= 'Current' )
                    {
                    match(input,CONSTANT,FOLLOW_CONSTANT_in_constant20907); 

                    match(input, Token.DOWN, null); 
                    t=(CommonTree)input.LT(1);
                    match(input,248,FOLLOW_248_in_constant20911); 

                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1183:12: -> constant(c=$t.text)
                    {
                        retval.st = templateLib.getInstanceOf("constant",
                      new STAttrMap().put("c", t.getText()));
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:1186:12: ^( CONSTANT t= 'Void' )
                    {
                    match(input,CONSTANT,FOLLOW_CONSTANT_in_constant20999); 

                    match(input, Token.DOWN, null); 
                    t=(CommonTree)input.LT(1);
                    match(input,249,FOLLOW_249_in_constant21003); 

                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1189:12: -> constant(c=$t.text)
                    {
                        retval.st = templateLib.getInstanceOf("constant",
                      new STAttrMap().put("c", t.getText()));
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
        return retval;
    }
    // $ANTLR end constant

    public static class manifest_constant_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start manifest_constant
    // BONSTTreeWalker.g:1193:1: manifest_constant : ( ^( MANIFEST_CONSTANT boolean_constant ) -> manifest_constant(mc=$boolean_constant.text) | ^( MANIFEST_CONSTANT CHARACTER_CONSTANT ) -> manifest_constant(mc=$CHARACTER_CONSTANT.text) | ^( MANIFEST_CONSTANT integer_constant ) -> manifest_constant(mc=$integer_constant.st) | ^( MANIFEST_CONSTANT real_constant ) -> manifest_constant(mc=$real_constant.st) | ^( MANIFEST_CONSTANT MANIFEST_STRING ) -> manifest_constant(mc=$MANIFEST_STRING.text) | ^( MANIFEST_CONSTANT enumerated_set ) -> manifest_constant(mc=$enumerated_set.st));
    public final manifest_constant_return manifest_constant() throws RecognitionException {
        manifest_constant_return retval = new manifest_constant_return();
        retval.start = input.LT(1);

        CommonTree CHARACTER_CONSTANT138=null;
        CommonTree MANIFEST_STRING141=null;
        boolean_constant_return boolean_constant137 = null;

        integer_constant_return integer_constant139 = null;

        real_constant_return real_constant140 = null;

        enumerated_set_return enumerated_set142 = null;


        try {
            // BONSTTreeWalker.g:1193:20: ( ^( MANIFEST_CONSTANT boolean_constant ) -> manifest_constant(mc=$boolean_constant.text) | ^( MANIFEST_CONSTANT CHARACTER_CONSTANT ) -> manifest_constant(mc=$CHARACTER_CONSTANT.text) | ^( MANIFEST_CONSTANT integer_constant ) -> manifest_constant(mc=$integer_constant.st) | ^( MANIFEST_CONSTANT real_constant ) -> manifest_constant(mc=$real_constant.st) | ^( MANIFEST_CONSTANT MANIFEST_STRING ) -> manifest_constant(mc=$MANIFEST_STRING.text) | ^( MANIFEST_CONSTANT enumerated_set ) -> manifest_constant(mc=$enumerated_set.st))
            int alt132=6;
            int LA132_0 = input.LA(1);

            if ( (LA132_0==MANIFEST_CONSTANT) ) {
                int LA132_1 = input.LA(2);

                if ( (LA132_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case MANIFEST_STRING:
                        {
                        alt132=5;
                        }
                        break;
                    case CHARACTER_CONSTANT:
                        {
                        alt132=2;
                        }
                        break;
                    case BOOLEAN_CONSTANT:
                        {
                        alt132=1;
                        }
                        break;
                    case ENUMERATED_SET:
                        {
                        alt132=6;
                        }
                        break;
                    case REAL_CONSTANT:
                        {
                        alt132=4;
                        }
                        break;
                    case INTEGER_CONSTANT:
                        {
                        alt132=3;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("1193:1: manifest_constant : ( ^( MANIFEST_CONSTANT boolean_constant ) -> manifest_constant(mc=$boolean_constant.text) | ^( MANIFEST_CONSTANT CHARACTER_CONSTANT ) -> manifest_constant(mc=$CHARACTER_CONSTANT.text) | ^( MANIFEST_CONSTANT integer_constant ) -> manifest_constant(mc=$integer_constant.st) | ^( MANIFEST_CONSTANT real_constant ) -> manifest_constant(mc=$real_constant.st) | ^( MANIFEST_CONSTANT MANIFEST_STRING ) -> manifest_constant(mc=$MANIFEST_STRING.text) | ^( MANIFEST_CONSTANT enumerated_set ) -> manifest_constant(mc=$enumerated_set.st));", 132, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1193:1: manifest_constant : ( ^( MANIFEST_CONSTANT boolean_constant ) -> manifest_constant(mc=$boolean_constant.text) | ^( MANIFEST_CONSTANT CHARACTER_CONSTANT ) -> manifest_constant(mc=$CHARACTER_CONSTANT.text) | ^( MANIFEST_CONSTANT integer_constant ) -> manifest_constant(mc=$integer_constant.st) | ^( MANIFEST_CONSTANT real_constant ) -> manifest_constant(mc=$real_constant.st) | ^( MANIFEST_CONSTANT MANIFEST_STRING ) -> manifest_constant(mc=$MANIFEST_STRING.text) | ^( MANIFEST_CONSTANT enumerated_set ) -> manifest_constant(mc=$enumerated_set.st));", 132, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1193:1: manifest_constant : ( ^( MANIFEST_CONSTANT boolean_constant ) -> manifest_constant(mc=$boolean_constant.text) | ^( MANIFEST_CONSTANT CHARACTER_CONSTANT ) -> manifest_constant(mc=$CHARACTER_CONSTANT.text) | ^( MANIFEST_CONSTANT integer_constant ) -> manifest_constant(mc=$integer_constant.st) | ^( MANIFEST_CONSTANT real_constant ) -> manifest_constant(mc=$real_constant.st) | ^( MANIFEST_CONSTANT MANIFEST_STRING ) -> manifest_constant(mc=$MANIFEST_STRING.text) | ^( MANIFEST_CONSTANT enumerated_set ) -> manifest_constant(mc=$enumerated_set.st));", 132, 0, input);

                throw nvae;
            }
            switch (alt132) {
                case 1 :
                    // BONSTTreeWalker.g:1193:22: ^( MANIFEST_CONSTANT boolean_constant )
                    {
                    match(input,MANIFEST_CONSTANT,FOLLOW_MANIFEST_CONSTANT_in_manifest_constant21095); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_boolean_constant_in_manifest_constant21097);
                    boolean_constant137=boolean_constant();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1196:22: -> manifest_constant(mc=$boolean_constant.text)
                    {
                        retval.st = templateLib.getInstanceOf("manifest_constant",
                      new STAttrMap().put("mc", input.getTokenStream().toString(
                      input.getTreeAdaptor().getTokenStartIndex(boolean_constant137.start),
                      input.getTreeAdaptor().getTokenStopIndex(boolean_constant137.start))));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1199:22: ^( MANIFEST_CONSTANT CHARACTER_CONSTANT )
                    {
                    match(input,MANIFEST_CONSTANT,FOLLOW_MANIFEST_CONSTANT_in_manifest_constant21246); 

                    match(input, Token.DOWN, null); 
                    CHARACTER_CONSTANT138=(CommonTree)input.LT(1);
                    match(input,CHARACTER_CONSTANT,FOLLOW_CHARACTER_CONSTANT_in_manifest_constant21248); 

                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1202:22: -> manifest_constant(mc=$CHARACTER_CONSTANT.text)
                    {
                        retval.st = templateLib.getInstanceOf("manifest_constant",
                      new STAttrMap().put("mc", CHARACTER_CONSTANT138.getText()));
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:1205:22: ^( MANIFEST_CONSTANT integer_constant )
                    {
                    match(input,MANIFEST_CONSTANT,FOLLOW_MANIFEST_CONSTANT_in_manifest_constant21397); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_integer_constant_in_manifest_constant21399);
                    integer_constant139=integer_constant();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1208:22: -> manifest_constant(mc=$integer_constant.st)
                    {
                        retval.st = templateLib.getInstanceOf("manifest_constant",
                      new STAttrMap().put("mc", integer_constant139.st));
                    }



                    }
                    break;
                case 4 :
                    // BONSTTreeWalker.g:1211:22: ^( MANIFEST_CONSTANT real_constant )
                    {
                    match(input,MANIFEST_CONSTANT,FOLLOW_MANIFEST_CONSTANT_in_manifest_constant21548); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_real_constant_in_manifest_constant21550);
                    real_constant140=real_constant();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1214:22: -> manifest_constant(mc=$real_constant.st)
                    {
                        retval.st = templateLib.getInstanceOf("manifest_constant",
                      new STAttrMap().put("mc", real_constant140.st));
                    }



                    }
                    break;
                case 5 :
                    // BONSTTreeWalker.g:1217:22: ^( MANIFEST_CONSTANT MANIFEST_STRING )
                    {
                    match(input,MANIFEST_CONSTANT,FOLLOW_MANIFEST_CONSTANT_in_manifest_constant21699); 

                    match(input, Token.DOWN, null); 
                    MANIFEST_STRING141=(CommonTree)input.LT(1);
                    match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_manifest_constant21701); 

                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1220:22: -> manifest_constant(mc=$MANIFEST_STRING.text)
                    {
                        retval.st = templateLib.getInstanceOf("manifest_constant",
                      new STAttrMap().put("mc", MANIFEST_STRING141.getText()));
                    }



                    }
                    break;
                case 6 :
                    // BONSTTreeWalker.g:1223:22: ^( MANIFEST_CONSTANT enumerated_set )
                    {
                    match(input,MANIFEST_CONSTANT,FOLLOW_MANIFEST_CONSTANT_in_manifest_constant21850); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_enumerated_set_in_manifest_constant21852);
                    enumerated_set142=enumerated_set();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1226:22: -> manifest_constant(mc=$enumerated_set.st)
                    {
                        retval.st = templateLib.getInstanceOf("manifest_constant",
                      new STAttrMap().put("mc", enumerated_set142.st));
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
        return retval;
    }
    // $ANTLR end manifest_constant

    public static class sign_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start sign
    // BONSTTreeWalker.g:1230:1: sign : ^( SIGN add_sub_op ) -> sign(s=$add_sub_op.st);
    public final sign_return sign() throws RecognitionException {
        sign_return retval = new sign_return();
        retval.start = input.LT(1);

        add_sub_op_return add_sub_op143 = null;


        try {
            // BONSTTreeWalker.g:1230:7: ( ^( SIGN add_sub_op ) -> sign(s=$add_sub_op.st))
            // BONSTTreeWalker.g:1230:8: ^( SIGN add_sub_op )
            {
            match(input,SIGN,FOLLOW_SIGN_in_sign21987); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_add_sub_op_in_sign21989);
            add_sub_op143=add_sub_op();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1233:8: -> sign(s=$add_sub_op.st)
            {
                retval.st = templateLib.getInstanceOf("sign",
              new STAttrMap().put("s", add_sub_op143.st));
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
    // $ANTLR end sign

    public static class boolean_constant_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start boolean_constant
    // BONSTTreeWalker.g:1237:1: boolean_constant : ( ^( BOOLEAN_CONSTANT t= 'true' ) -> booleanConstant(bc=$t.text) | ^( BOOLEAN_CONSTANT t= 'false' ) -> booleanConstant(bc=$t.text));
    public final boolean_constant_return boolean_constant() throws RecognitionException {
        boolean_constant_return retval = new boolean_constant_return();
        retval.start = input.LT(1);

        CommonTree t=null;

        try {
            // BONSTTreeWalker.g:1237:19: ( ^( BOOLEAN_CONSTANT t= 'true' ) -> booleanConstant(bc=$t.text) | ^( BOOLEAN_CONSTANT t= 'false' ) -> booleanConstant(bc=$t.text))
            int alt133=2;
            int LA133_0 = input.LA(1);

            if ( (LA133_0==BOOLEAN_CONSTANT) ) {
                int LA133_1 = input.LA(2);

                if ( (LA133_1==DOWN) ) {
                    int LA133_2 = input.LA(3);

                    if ( (LA133_2==251) ) {
                        alt133=2;
                    }
                    else if ( (LA133_2==250) ) {
                        alt133=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("1237:1: boolean_constant : ( ^( BOOLEAN_CONSTANT t= 'true' ) -> booleanConstant(bc=$t.text) | ^( BOOLEAN_CONSTANT t= 'false' ) -> booleanConstant(bc=$t.text));", 133, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1237:1: boolean_constant : ( ^( BOOLEAN_CONSTANT t= 'true' ) -> booleanConstant(bc=$t.text) | ^( BOOLEAN_CONSTANT t= 'false' ) -> booleanConstant(bc=$t.text));", 133, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1237:1: boolean_constant : ( ^( BOOLEAN_CONSTANT t= 'true' ) -> booleanConstant(bc=$t.text) | ^( BOOLEAN_CONSTANT t= 'false' ) -> booleanConstant(bc=$t.text));", 133, 0, input);

                throw nvae;
            }
            switch (alt133) {
                case 1 :
                    // BONSTTreeWalker.g:1237:20: ^( BOOLEAN_CONSTANT t= 'true' )
                    {
                    match(input,BOOLEAN_CONSTANT,FOLLOW_BOOLEAN_CONSTANT_in_boolean_constant22068); 

                    match(input, Token.DOWN, null); 
                    t=(CommonTree)input.LT(1);
                    match(input,250,FOLLOW_250_in_boolean_constant22072); 

                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1240:20: -> booleanConstant(bc=$t.text)
                    {
                        retval.st = templateLib.getInstanceOf("booleanConstant",
                      new STAttrMap().put("bc", t.getText()));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1243:20: ^( BOOLEAN_CONSTANT t= 'false' )
                    {
                    match(input,BOOLEAN_CONSTANT,FOLLOW_BOOLEAN_CONSTANT_in_boolean_constant22208); 

                    match(input, Token.DOWN, null); 
                    t=(CommonTree)input.LT(1);
                    match(input,251,FOLLOW_251_in_boolean_constant22212); 

                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1246:20: -> booleanConstant(bc=$t.text)
                    {
                        retval.st = templateLib.getInstanceOf("booleanConstant",
                      new STAttrMap().put("bc", t.getText()));
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
        return retval;
    }
    // $ANTLR end boolean_constant

    public static class integer_constant_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start integer_constant
    // BONSTTreeWalker.g:1250:1: integer_constant : ^( INTEGER_CONSTANT (s+= sign )? INTEGER ) -> integerConstant(sign=$si=$INTEGER.text);
    public final integer_constant_return integer_constant() throws RecognitionException {
        integer_constant_return retval = new integer_constant_return();
        retval.start = input.LT(1);

        CommonTree INTEGER144=null;
        List list_s=null;
        RuleReturnScope s = null;
        try {
            // BONSTTreeWalker.g:1250:19: ( ^( INTEGER_CONSTANT (s+= sign )? INTEGER ) -> integerConstant(sign=$si=$INTEGER.text))
            // BONSTTreeWalker.g:1250:20: ^( INTEGER_CONSTANT (s+= sign )? INTEGER )
            {
            match(input,INTEGER_CONSTANT,FOLLOW_INTEGER_CONSTANT_in_integer_constant22353); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:1252:22: (s+= sign )?
            int alt134=2;
            int LA134_0 = input.LA(1);

            if ( (LA134_0==SIGN) ) {
                alt134=1;
            }
            switch (alt134) {
                case 1 :
                    // BONSTTreeWalker.g:1252:23: s+= sign
                    {
                    pushFollow(FOLLOW_sign_in_integer_constant22379);
                    s=sign();
                    _fsp--;

                    if (list_s==null) list_s=new ArrayList();
                    list_s.add(s.getTemplate());


                    }
                    break;

            }

            INTEGER144=(CommonTree)input.LT(1);
            match(input,INTEGER,FOLLOW_INTEGER_in_integer_constant22383); 

            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1254:20: -> integerConstant(sign=$si=$INTEGER.text)
            {
                retval.st = templateLib.getInstanceOf("integerConstant",
              new STAttrMap().put("sign", list_s).put("i", INTEGER144.getText()));
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
    // $ANTLR end integer_constant

    public static class real_constant_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start real_constant
    // BONSTTreeWalker.g:1258:1: real_constant : ^( REAL_CONSTANT (s+= sign )? REAL ) -> realConstant(sign=$sr=$REAL.text);
    public final real_constant_return real_constant() throws RecognitionException {
        real_constant_return retval = new real_constant_return();
        retval.start = input.LT(1);

        CommonTree REAL145=null;
        List list_s=null;
        RuleReturnScope s = null;
        try {
            // BONSTTreeWalker.g:1258:16: ( ^( REAL_CONSTANT (s+= sign )? REAL ) -> realConstant(sign=$sr=$REAL.text))
            // BONSTTreeWalker.g:1258:17: ^( REAL_CONSTANT (s+= sign )? REAL )
            {
            match(input,REAL_CONSTANT,FOLLOW_REAL_CONSTANT_in_real_constant22523); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:1260:19: (s+= sign )?
            int alt135=2;
            int LA135_0 = input.LA(1);

            if ( (LA135_0==SIGN) ) {
                alt135=1;
            }
            switch (alt135) {
                case 1 :
                    // BONSTTreeWalker.g:1260:20: s+= sign
                    {
                    pushFollow(FOLLOW_sign_in_real_constant22546);
                    s=sign();
                    _fsp--;

                    if (list_s==null) list_s=new ArrayList();
                    list_s.add(s.getTemplate());


                    }
                    break;

            }

            REAL145=(CommonTree)input.LT(1);
            match(input,REAL,FOLLOW_REAL_in_real_constant22550); 

            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1262:17: -> realConstant(sign=$sr=$REAL.text)
            {
                retval.st = templateLib.getInstanceOf("realConstant",
              new STAttrMap().put("sign", list_s).put("r", REAL145.getText()));
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
    // $ANTLR end real_constant

    public static class dynamic_diagram_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start dynamic_diagram
    // BONSTTreeWalker.g:1266:1: dynamic_diagram : ^( DYNAMIC_DIAGRAM (exid+= extended_id )? ( COMMENT )? (db+= dynamic_block )? ) -> dynamicDiagram(exid=$exiddynblock=$db);
    public final dynamic_diagram_return dynamic_diagram() throws RecognitionException {
        dynamic_diagram_return retval = new dynamic_diagram_return();
        retval.start = input.LT(1);

        List list_exid=null;
        List list_db=null;
        RuleReturnScope exid = null;
        RuleReturnScope db = null;
        try {
            // BONSTTreeWalker.g:1270:18: ( ^( DYNAMIC_DIAGRAM (exid+= extended_id )? ( COMMENT )? (db+= dynamic_block )? ) -> dynamicDiagram(exid=$exiddynblock=$db))
            // BONSTTreeWalker.g:1270:19: ^( DYNAMIC_DIAGRAM (exid+= extended_id )? ( COMMENT )? (db+= dynamic_block )? )
            {
            match(input,DYNAMIC_DIAGRAM,FOLLOW_DYNAMIC_DIAGRAM_in_dynamic_diagram22665); 

            if ( input.LA(1)==Token.DOWN ) {
                match(input, Token.DOWN, null); 
                // BONSTTreeWalker.g:1272:21: (exid+= extended_id )?
                int alt136=2;
                int LA136_0 = input.LA(1);

                if ( (LA136_0==EXTENDED_ID) ) {
                    alt136=1;
                }
                switch (alt136) {
                    case 1 :
                        // BONSTTreeWalker.g:1272:22: exid+= extended_id
                        {
                        pushFollow(FOLLOW_extended_id_in_dynamic_diagram22690);
                        exid=extended_id();
                        _fsp--;

                        if (list_exid==null) list_exid=new ArrayList();
                        list_exid.add(exid.getTemplate());


                        }
                        break;

                }

                // BONSTTreeWalker.g:1272:42: ( COMMENT )?
                int alt137=2;
                int LA137_0 = input.LA(1);

                if ( (LA137_0==COMMENT) ) {
                    alt137=1;
                }
                switch (alt137) {
                    case 1 :
                        // BONSTTreeWalker.g:1272:43: COMMENT
                        {
                        match(input,COMMENT,FOLLOW_COMMENT_in_dynamic_diagram22695); 

                        }
                        break;

                }

                // BONSTTreeWalker.g:1273:21: (db+= dynamic_block )?
                int alt138=2;
                int LA138_0 = input.LA(1);

                if ( (LA138_0==DYNAMIC_BLOCK) ) {
                    alt138=1;
                }
                switch (alt138) {
                    case 1 :
                        // BONSTTreeWalker.g:1273:22: db+= dynamic_block
                        {
                        pushFollow(FOLLOW_dynamic_block_in_dynamic_diagram22722);
                        db=dynamic_block();
                        _fsp--;

                        if (list_db==null) list_db=new ArrayList();
                        list_db.add(db.getTemplate());


                        }
                        break;

                }


                match(input, Token.UP, null); 
            }

            // TEMPLATE REWRITE
            // 1275:19: -> dynamicDiagram(exid=$exiddynblock=$db)
            {
                retval.st = templateLib.getInstanceOf("dynamicDiagram",
              new STAttrMap().put("exid", list_exid).put("dynblock", list_db));
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
    // $ANTLR end dynamic_diagram

    public static class dynamic_block_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start dynamic_block
    // BONSTTreeWalker.g:1279:1: dynamic_block : ^( DYNAMIC_BLOCK (dcl+= dynamic_component )+ ) -> dynamicBlock(dcl=$dcl);
    public final dynamic_block_return dynamic_block() throws RecognitionException {
        dynamic_block_return retval = new dynamic_block_return();
        retval.start = input.LT(1);

        List list_dcl=null;
        RuleReturnScope dcl = null;
        try {
            // BONSTTreeWalker.g:1279:16: ( ^( DYNAMIC_BLOCK (dcl+= dynamic_component )+ ) -> dynamicBlock(dcl=$dcl))
            // BONSTTreeWalker.g:1279:17: ^( DYNAMIC_BLOCK (dcl+= dynamic_component )+ )
            {
            match(input,DYNAMIC_BLOCK,FOLLOW_DYNAMIC_BLOCK_in_dynamic_block22859); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:1281:19: (dcl+= dynamic_component )+
            int cnt139=0;
            loop139:
            do {
                int alt139=2;
                int LA139_0 = input.LA(1);

                if ( (LA139_0==DYNAMIC_COMPONENT) ) {
                    alt139=1;
                }


                switch (alt139) {
            	case 1 :
            	    // BONSTTreeWalker.g:1281:20: dcl+= dynamic_component
            	    {
            	    pushFollow(FOLLOW_dynamic_component_in_dynamic_block22882);
            	    dcl=dynamic_component();
            	    _fsp--;

            	    if (list_dcl==null) list_dcl=new ArrayList();
            	    list_dcl.add(dcl.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt139 >= 1 ) break loop139;
                        EarlyExitException eee =
                            new EarlyExitException(139, input);
                        throw eee;
                }
                cnt139++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1283:17: -> dynamicBlock(dcl=$dcl)
            {
                retval.st = templateLib.getInstanceOf("dynamicBlock",
              new STAttrMap().put("dcl", list_dcl));
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
    // $ANTLR end dynamic_block

    public static class dynamic_component_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start dynamic_component
    // BONSTTreeWalker.g:1287:1: dynamic_component : ( ^( DYNAMIC_COMPONENT scenario_description ) -> dynamicComponent(dc=$scenario_description.st) | ^( DYNAMIC_COMPONENT object_group ) -> dynamicComponent(dc=$object_group.st) | ^( DYNAMIC_COMPONENT object_stack ) -> dynamicComponent(dc=$object_stack.st) | ^( DYNAMIC_COMPONENT object ) -> dynamicComponent(dc=$object.st) | ^( DYNAMIC_COMPONENT message_relation ) -> dynamicComponent(dc=$message_relation.st));
    public final dynamic_component_return dynamic_component() throws RecognitionException {
        dynamic_component_return retval = new dynamic_component_return();
        retval.start = input.LT(1);

        scenario_description_return scenario_description146 = null;

        object_group_return object_group147 = null;

        object_stack_return object_stack148 = null;

        object_return object149 = null;

        message_relation_return message_relation150 = null;


        try {
            // BONSTTreeWalker.g:1287:20: ( ^( DYNAMIC_COMPONENT scenario_description ) -> dynamicComponent(dc=$scenario_description.st) | ^( DYNAMIC_COMPONENT object_group ) -> dynamicComponent(dc=$object_group.st) | ^( DYNAMIC_COMPONENT object_stack ) -> dynamicComponent(dc=$object_stack.st) | ^( DYNAMIC_COMPONENT object ) -> dynamicComponent(dc=$object.st) | ^( DYNAMIC_COMPONENT message_relation ) -> dynamicComponent(dc=$message_relation.st))
            int alt140=5;
            int LA140_0 = input.LA(1);

            if ( (LA140_0==DYNAMIC_COMPONENT) ) {
                int LA140_1 = input.LA(2);

                if ( (LA140_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case SCENARIO_DESCRIPTION:
                        {
                        alt140=1;
                        }
                        break;
                    case OBJECT_GROUP:
                        {
                        alt140=2;
                        }
                        break;
                    case OBJECT:
                        {
                        alt140=4;
                        }
                        break;
                    case MESSAGE_RELATION:
                        {
                        alt140=5;
                        }
                        break;
                    case OBJECT_STACK:
                        {
                        alt140=3;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("1287:1: dynamic_component : ( ^( DYNAMIC_COMPONENT scenario_description ) -> dynamicComponent(dc=$scenario_description.st) | ^( DYNAMIC_COMPONENT object_group ) -> dynamicComponent(dc=$object_group.st) | ^( DYNAMIC_COMPONENT object_stack ) -> dynamicComponent(dc=$object_stack.st) | ^( DYNAMIC_COMPONENT object ) -> dynamicComponent(dc=$object.st) | ^( DYNAMIC_COMPONENT message_relation ) -> dynamicComponent(dc=$message_relation.st));", 140, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1287:1: dynamic_component : ( ^( DYNAMIC_COMPONENT scenario_description ) -> dynamicComponent(dc=$scenario_description.st) | ^( DYNAMIC_COMPONENT object_group ) -> dynamicComponent(dc=$object_group.st) | ^( DYNAMIC_COMPONENT object_stack ) -> dynamicComponent(dc=$object_stack.st) | ^( DYNAMIC_COMPONENT object ) -> dynamicComponent(dc=$object.st) | ^( DYNAMIC_COMPONENT message_relation ) -> dynamicComponent(dc=$message_relation.st));", 140, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1287:1: dynamic_component : ( ^( DYNAMIC_COMPONENT scenario_description ) -> dynamicComponent(dc=$scenario_description.st) | ^( DYNAMIC_COMPONENT object_group ) -> dynamicComponent(dc=$object_group.st) | ^( DYNAMIC_COMPONENT object_stack ) -> dynamicComponent(dc=$object_stack.st) | ^( DYNAMIC_COMPONENT object ) -> dynamicComponent(dc=$object.st) | ^( DYNAMIC_COMPONENT message_relation ) -> dynamicComponent(dc=$message_relation.st));", 140, 0, input);

                throw nvae;
            }
            switch (alt140) {
                case 1 :
                    // BONSTTreeWalker.g:1287:22: ^( DYNAMIC_COMPONENT scenario_description )
                    {
                    match(input,DYNAMIC_COMPONENT,FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component23011); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_scenario_description_in_dynamic_component23013);
                    scenario_description146=scenario_description();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1290:22: -> dynamicComponent(dc=$scenario_description.st)
                    {
                        retval.st = templateLib.getInstanceOf("dynamicComponent",
                      new STAttrMap().put("dc", scenario_description146.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1293:22: ^( DYNAMIC_COMPONENT object_group )
                    {
                    match(input,DYNAMIC_COMPONENT,FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component23161); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_object_group_in_dynamic_component23163);
                    object_group147=object_group();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1296:22: -> dynamicComponent(dc=$object_group.st)
                    {
                        retval.st = templateLib.getInstanceOf("dynamicComponent",
                      new STAttrMap().put("dc", object_group147.st));
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:1299:22: ^( DYNAMIC_COMPONENT object_stack )
                    {
                    match(input,DYNAMIC_COMPONENT,FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component23311); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_object_stack_in_dynamic_component23313);
                    object_stack148=object_stack();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1302:22: -> dynamicComponent(dc=$object_stack.st)
                    {
                        retval.st = templateLib.getInstanceOf("dynamicComponent",
                      new STAttrMap().put("dc", object_stack148.st));
                    }



                    }
                    break;
                case 4 :
                    // BONSTTreeWalker.g:1305:22: ^( DYNAMIC_COMPONENT object )
                    {
                    match(input,DYNAMIC_COMPONENT,FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component23462); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_object_in_dynamic_component23464);
                    object149=object();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1308:22: -> dynamicComponent(dc=$object.st)
                    {
                        retval.st = templateLib.getInstanceOf("dynamicComponent",
                      new STAttrMap().put("dc", object149.st));
                    }



                    }
                    break;
                case 5 :
                    // BONSTTreeWalker.g:1311:22: ^( DYNAMIC_COMPONENT message_relation )
                    {
                    match(input,DYNAMIC_COMPONENT,FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component23613); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_message_relation_in_dynamic_component23615);
                    message_relation150=message_relation();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1314:22: -> dynamicComponent(dc=$message_relation.st)
                    {
                        retval.st = templateLib.getInstanceOf("dynamicComponent",
                      new STAttrMap().put("dc", message_relation150.st));
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
        return retval;
    }
    // $ANTLR end dynamic_component

    public static class scenario_description_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start scenario_description
    // BONSTTreeWalker.g:1318:1: scenario_description : ^( SCENARIO_DESCRIPTION scenario_name ( COMMENT )? labelled_actions ) -> scenarioDescription(name=$scenario_name.stla=$labelled_actions.st);
    public final scenario_description_return scenario_description() throws RecognitionException {
        scenario_description_return retval = new scenario_description_return();
        retval.start = input.LT(1);

        scenario_name_return scenario_name151 = null;

        labelled_actions_return labelled_actions152 = null;


        try {
            // BONSTTreeWalker.g:1320:23: ( ^( SCENARIO_DESCRIPTION scenario_name ( COMMENT )? labelled_actions ) -> scenarioDescription(name=$scenario_name.stla=$labelled_actions.st))
            // BONSTTreeWalker.g:1320:24: ^( SCENARIO_DESCRIPTION scenario_name ( COMMENT )? labelled_actions )
            {
            match(input,SCENARIO_DESCRIPTION,FOLLOW_SCENARIO_DESCRIPTION_in_scenario_description23751); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_scenario_name_in_scenario_description23779);
            scenario_name151=scenario_name();
            _fsp--;

            // BONSTTreeWalker.g:1322:40: ( COMMENT )?
            int alt141=2;
            int LA141_0 = input.LA(1);

            if ( (LA141_0==COMMENT) ) {
                alt141=1;
            }
            switch (alt141) {
                case 1 :
                    // BONSTTreeWalker.g:1322:41: COMMENT
                    {
                    match(input,COMMENT,FOLLOW_COMMENT_in_scenario_description23782); 

                    }
                    break;

            }

            pushFollow(FOLLOW_labelled_actions_in_scenario_description23811);
            labelled_actions152=labelled_actions();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1325:24: -> scenarioDescription(name=$scenario_name.stla=$labelled_actions.st)
            {
                retval.st = templateLib.getInstanceOf("scenarioDescription",
              new STAttrMap().put("name", scenario_name151.st).put("la", labelled_actions152.st));
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
    // $ANTLR end scenario_description

    public static class labelled_actions_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start labelled_actions
    // BONSTTreeWalker.g:1329:1: labelled_actions : ^( LABELLED_ACTIONS (lal+= labelled_action )+ ) -> labelledActions(lal=$lal);
    public final labelled_actions_return labelled_actions() throws RecognitionException {
        labelled_actions_return retval = new labelled_actions_return();
        retval.start = input.LT(1);

        List list_lal=null;
        RuleReturnScope lal = null;
        try {
            // BONSTTreeWalker.g:1329:19: ( ^( LABELLED_ACTIONS (lal+= labelled_action )+ ) -> labelledActions(lal=$lal))
            // BONSTTreeWalker.g:1329:20: ^( LABELLED_ACTIONS (lal+= labelled_action )+ )
            {
            match(input,LABELLED_ACTIONS,FOLLOW_LABELLED_ACTIONS_in_labelled_actions23975); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:1330:39: (lal+= labelled_action )+
            int cnt142=0;
            loop142:
            do {
                int alt142=2;
                int LA142_0 = input.LA(1);

                if ( (LA142_0==LABELLED_ACTION) ) {
                    alt142=1;
                }


                switch (alt142) {
            	case 1 :
            	    // BONSTTreeWalker.g:1330:40: lal+= labelled_action
            	    {
            	    pushFollow(FOLLOW_labelled_action_in_labelled_actions23980);
            	    lal=labelled_action();
            	    _fsp--;

            	    if (list_lal==null) list_lal=new ArrayList();
            	    list_lal.add(lal.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt142 >= 1 ) break loop142;
                        EarlyExitException eee =
                            new EarlyExitException(142, input);
                        throw eee;
                }
                cnt142++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1332:20: -> labelledActions(lal=$lal)
            {
                retval.st = templateLib.getInstanceOf("labelledActions",
              new STAttrMap().put("lal", list_lal));
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
    // $ANTLR end labelled_actions

    public static class labelled_action_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start labelled_action
    // BONSTTreeWalker.g:1336:1: labelled_action : ^( LABELLED_ACTION action_label action_description ) -> labelledAction(l=$action_label.stad=$action_description.st);
    public final labelled_action_return labelled_action() throws RecognitionException {
        labelled_action_return retval = new labelled_action_return();
        retval.start = input.LT(1);

        action_label_return action_label153 = null;

        action_description_return action_description154 = null;


        try {
            // BONSTTreeWalker.g:1336:18: ( ^( LABELLED_ACTION action_label action_description ) -> labelledAction(l=$action_label.stad=$action_description.st))
            // BONSTTreeWalker.g:1336:19: ^( LABELLED_ACTION action_label action_description )
            {
            match(input,LABELLED_ACTION,FOLLOW_LABELLED_ACTION_in_labelled_action24120); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_action_label_in_labelled_action24122);
            action_label153=action_label();
            _fsp--;

            pushFollow(FOLLOW_action_description_in_labelled_action24124);
            action_description154=action_description();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1339:19: -> labelledAction(l=$action_label.stad=$action_description.st)
            {
                retval.st = templateLib.getInstanceOf("labelledAction",
              new STAttrMap().put("l", action_label153.st).put("ad", action_description154.st));
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
    // $ANTLR end labelled_action

    public static class action_label_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start action_label
    // BONSTTreeWalker.g:1343:1: action_label : ^( ACTION_LABEL MANIFEST_STRING ) -> actionLabel(al=$MANIFEST_STRING.text);
    public final action_label_return action_label() throws RecognitionException {
        action_label_return retval = new action_label_return();
        retval.start = input.LT(1);

        CommonTree MANIFEST_STRING155=null;

        try {
            // BONSTTreeWalker.g:1343:15: ( ^( ACTION_LABEL MANIFEST_STRING ) -> actionLabel(al=$MANIFEST_STRING.text))
            // BONSTTreeWalker.g:1343:16: ^( ACTION_LABEL MANIFEST_STRING )
            {
            match(input,ACTION_LABEL,FOLLOW_ACTION_LABEL_in_action_label24258); 

            match(input, Token.DOWN, null); 
            MANIFEST_STRING155=(CommonTree)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_action_label24260); 

            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1346:16: -> actionLabel(al=$MANIFEST_STRING.text)
            {
                retval.st = templateLib.getInstanceOf("actionLabel",
              new STAttrMap().put("al", MANIFEST_STRING155.getText()));
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
    // $ANTLR end action_label

    public static class action_description_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start action_description
    // BONSTTreeWalker.g:1350:1: action_description : ^( ACTION_DESCRIPTION manifest_textblock ) -> actionDescription(ad=$manifest_textblock.st);
    public final action_description_return action_description() throws RecognitionException {
        action_description_return retval = new action_description_return();
        retval.start = input.LT(1);

        manifest_textblock_return manifest_textblock156 = null;


        try {
            // BONSTTreeWalker.g:1350:21: ( ^( ACTION_DESCRIPTION manifest_textblock ) -> actionDescription(ad=$manifest_textblock.st))
            // BONSTTreeWalker.g:1350:22: ^( ACTION_DESCRIPTION manifest_textblock )
            {
            match(input,ACTION_DESCRIPTION,FOLLOW_ACTION_DESCRIPTION_in_action_description24381); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_manifest_textblock_in_action_description24383);
            manifest_textblock156=manifest_textblock();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1353:22: -> actionDescription(ad=$manifest_textblock.st)
            {
                retval.st = templateLib.getInstanceOf("actionDescription",
              new STAttrMap().put("ad", manifest_textblock156.st));
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
    // $ANTLR end action_description

    public static class scenario_name_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start scenario_name
    // BONSTTreeWalker.g:1357:1: scenario_name : ^( SCENARIO_NAME manifest_textblock ) -> scenarioName(name=$manifest_textblock.text);
    public final scenario_name_return scenario_name() throws RecognitionException {
        scenario_name_return retval = new scenario_name_return();
        retval.start = input.LT(1);

        manifest_textblock_return manifest_textblock157 = null;


        try {
            // BONSTTreeWalker.g:1357:16: ( ^( SCENARIO_NAME manifest_textblock ) -> scenarioName(name=$manifest_textblock.text))
            // BONSTTreeWalker.g:1357:17: ^( SCENARIO_NAME manifest_textblock )
            {
            match(input,SCENARIO_NAME,FOLLOW_SCENARIO_NAME_in_scenario_name24529); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_manifest_textblock_in_scenario_name24531);
            manifest_textblock157=manifest_textblock();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1360:17: -> scenarioName(name=$manifest_textblock.text)
            {
                retval.st = templateLib.getInstanceOf("scenarioName",
              new STAttrMap().put("name", input.getTokenStream().toString(
              input.getTreeAdaptor().getTokenStartIndex(manifest_textblock157.start),
              input.getTreeAdaptor().getTokenStopIndex(manifest_textblock157.start))));
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
    // $ANTLR end scenario_name

    public static class object_group_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start object_group
    // BONSTTreeWalker.g:1364:1: object_group : ^( OBJECT_GROUP (n+= 'nameless' )? group_name ( COMMENT )? (gc+= group_components )? ) -> objectGroup(n=$nname=$group_name.stgc=$gc);
    public final object_group_return object_group() throws RecognitionException {
        object_group_return retval = new object_group_return();
        retval.start = input.LT(1);

        CommonTree n=null;
        List list_n=null;
        List list_gc=null;
        group_name_return group_name158 = null;

        RuleReturnScope gc = null;
        try {
            // BONSTTreeWalker.g:1366:15: ( ^( OBJECT_GROUP (n+= 'nameless' )? group_name ( COMMENT )? (gc+= group_components )? ) -> objectGroup(n=$nname=$group_name.stgc=$gc))
            // BONSTTreeWalker.g:1366:16: ^( OBJECT_GROUP (n+= 'nameless' )? group_name ( COMMENT )? (gc+= group_components )? )
            {
            match(input,OBJECT_GROUP,FOLLOW_OBJECT_GROUP_in_object_group24639); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:1367:31: (n+= 'nameless' )?
            int alt143=2;
            int LA143_0 = input.LA(1);

            if ( (LA143_0==254) ) {
                alt143=1;
            }
            switch (alt143) {
                case 1 :
                    // BONSTTreeWalker.g:1367:32: n+= 'nameless'
                    {
                    n=(CommonTree)input.LT(1);
                    match(input,254,FOLLOW_254_in_object_group24644); 
                    if (list_n==null) list_n=new ArrayList();
                    list_n.add(n);


                    }
                    break;

            }

            pushFollow(FOLLOW_group_name_in_object_group24648);
            group_name158=group_name();
            _fsp--;

            // BONSTTreeWalker.g:1367:59: ( COMMENT )?
            int alt144=2;
            int LA144_0 = input.LA(1);

            if ( (LA144_0==COMMENT) ) {
                alt144=1;
            }
            switch (alt144) {
                case 1 :
                    // BONSTTreeWalker.g:1367:60: COMMENT
                    {
                    match(input,COMMENT,FOLLOW_COMMENT_in_object_group24651); 

                    }
                    break;

            }

            // BONSTTreeWalker.g:1367:70: (gc+= group_components )?
            int alt145=2;
            int LA145_0 = input.LA(1);

            if ( (LA145_0==GROUP_COMPONENTS) ) {
                alt145=1;
            }
            switch (alt145) {
                case 1 :
                    // BONSTTreeWalker.g:1367:71: gc+= group_components
                    {
                    pushFollow(FOLLOW_group_components_in_object_group24658);
                    gc=group_components();
                    _fsp--;

                    if (list_gc==null) list_gc=new ArrayList();
                    list_gc.add(gc.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1369:16: -> objectGroup(n=$nname=$group_name.stgc=$gc)
            {
                retval.st = templateLib.getInstanceOf("objectGroup",
              new STAttrMap().put("n", list_n).put("name", group_name158.st).put("gc", list_gc));
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
    // $ANTLR end object_group

    public static class group_components_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start group_components
    // BONSTTreeWalker.g:1373:1: group_components : ^( GROUP_COMPONENTS dynamic_block ) -> groupComponents(db=$dynamic_block.st);
    public final group_components_return group_components() throws RecognitionException {
        group_components_return retval = new group_components_return();
        retval.start = input.LT(1);

        dynamic_block_return dynamic_block159 = null;


        try {
            // BONSTTreeWalker.g:1373:19: ( ^( GROUP_COMPONENTS dynamic_block ) -> groupComponents(db=$dynamic_block.st))
            // BONSTTreeWalker.g:1373:20: ^( GROUP_COMPONENTS dynamic_block )
            {
            match(input,GROUP_COMPONENTS,FOLLOW_GROUP_COMPONENTS_in_group_components24788); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_dynamic_block_in_group_components24790);
            dynamic_block159=dynamic_block();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1376:20: -> groupComponents(db=$dynamic_block.st)
            {
                retval.st = templateLib.getInstanceOf("groupComponents",
              new STAttrMap().put("db", dynamic_block159.st));
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
    // $ANTLR end group_components

    public static class object_stack_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start object_stack
    // BONSTTreeWalker.g:1380:1: object_stack : ^( OBJECT_STACK object_name ( COMMENT )? ) -> objectStack(name=$object_name.st);
    public final object_stack_return object_stack() throws RecognitionException {
        object_stack_return retval = new object_stack_return();
        retval.start = input.LT(1);

        object_name_return object_name160 = null;


        try {
            // BONSTTreeWalker.g:1380:15: ( ^( OBJECT_STACK object_name ( COMMENT )? ) -> objectStack(name=$object_name.st))
            // BONSTTreeWalker.g:1380:16: ^( OBJECT_STACK object_name ( COMMENT )? )
            {
            match(input,OBJECT_STACK,FOLLOW_OBJECT_STACK_in_object_stack24926); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_object_name_in_object_stack24928);
            object_name160=object_name();
            _fsp--;

            // BONSTTreeWalker.g:1381:43: ( COMMENT )?
            int alt146=2;
            int LA146_0 = input.LA(1);

            if ( (LA146_0==COMMENT) ) {
                alt146=1;
            }
            switch (alt146) {
                case 1 :
                    // BONSTTreeWalker.g:1381:44: COMMENT
                    {
                    match(input,COMMENT,FOLLOW_COMMENT_in_object_stack24931); 

                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1383:16: -> objectStack(name=$object_name.st)
            {
                retval.st = templateLib.getInstanceOf("objectStack",
              new STAttrMap().put("name", object_name160.st));
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
    // $ANTLR end object_stack

    public static class object_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start object
    // BONSTTreeWalker.g:1387:1: object : ^( OBJECT object_name ( COMMENT )? ) -> object(name=$object_name.st);
    public final object_return object() throws RecognitionException {
        object_return retval = new object_return();
        retval.start = input.LT(1);

        object_name_return object_name161 = null;


        try {
            // BONSTTreeWalker.g:1387:9: ( ^( OBJECT object_name ( COMMENT )? ) -> object(name=$object_name.st))
            // BONSTTreeWalker.g:1387:10: ^( OBJECT object_name ( COMMENT )? )
            {
            match(input,OBJECT,FOLLOW_OBJECT_in_object25042); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_object_name_in_object25044);
            object_name161=object_name();
            _fsp--;

            // BONSTTreeWalker.g:1388:31: ( COMMENT )?
            int alt147=2;
            int LA147_0 = input.LA(1);

            if ( (LA147_0==COMMENT) ) {
                alt147=1;
            }
            switch (alt147) {
                case 1 :
                    // BONSTTreeWalker.g:1388:32: COMMENT
                    {
                    match(input,COMMENT,FOLLOW_COMMENT_in_object25047); 

                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1390:10: -> object(name=$object_name.st)
            {
                retval.st = templateLib.getInstanceOf("object",
              new STAttrMap().put("name", object_name161.st));
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
    // $ANTLR end object

    public static class message_relation_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start message_relation
    // BONSTTreeWalker.g:1394:1: message_relation : ^( MESSAGE_RELATION caller receiver (ml+= message_label )? ) -> messageRelation(caller=$caller.streceiver=$receiver.stlabel=$ml);
    public final message_relation_return message_relation() throws RecognitionException {
        message_relation_return retval = new message_relation_return();
        retval.start = input.LT(1);

        List list_ml=null;
        caller_return caller162 = null;

        receiver_return receiver163 = null;

        RuleReturnScope ml = null;
        try {
            // BONSTTreeWalker.g:1396:19: ( ^( MESSAGE_RELATION caller receiver (ml+= message_label )? ) -> messageRelation(caller=$caller.streceiver=$receiver.stlabel=$ml))
            // BONSTTreeWalker.g:1396:20: ^( MESSAGE_RELATION caller receiver (ml+= message_label )? )
            {
            match(input,MESSAGE_RELATION,FOLLOW_MESSAGE_RELATION_in_message_relation25133); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_caller_in_message_relation25135);
            caller162=caller();
            _fsp--;

            pushFollow(FOLLOW_receiver_in_message_relation25137);
            receiver163=receiver();
            _fsp--;

            // BONSTTreeWalker.g:1397:55: (ml+= message_label )?
            int alt148=2;
            int LA148_0 = input.LA(1);

            if ( (LA148_0==MESSAGE_LABEL) ) {
                alt148=1;
            }
            switch (alt148) {
                case 1 :
                    // BONSTTreeWalker.g:1397:56: ml+= message_label
                    {
                    pushFollow(FOLLOW_message_label_in_message_relation25142);
                    ml=message_label();
                    _fsp--;

                    if (list_ml==null) list_ml=new ArrayList();
                    list_ml.add(ml.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1399:20: -> messageRelation(caller=$caller.streceiver=$receiver.stlabel=$ml)
            {
                retval.st = templateLib.getInstanceOf("messageRelation",
              new STAttrMap().put("caller", caller162.st).put("receiver", receiver163.st).put("label", list_ml));
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
    // $ANTLR end message_relation

    public static class caller_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start caller
    // BONSTTreeWalker.g:1403:1: caller : ^( RECEIVER dynamic_ref ) -> caller(c=$dynamic_ref.st);
    public final caller_return caller() throws RecognitionException {
        caller_return retval = new caller_return();
        retval.start = input.LT(1);

        dynamic_ref_return dynamic_ref164 = null;


        try {
            // BONSTTreeWalker.g:1403:9: ( ^( RECEIVER dynamic_ref ) -> caller(c=$dynamic_ref.st))
            // BONSTTreeWalker.g:1403:10: ^( RECEIVER dynamic_ref )
            {
            match(input,RECEIVER,FOLLOW_RECEIVER_in_caller25281); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_dynamic_ref_in_caller25283);
            dynamic_ref164=dynamic_ref();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1406:10: -> caller(c=$dynamic_ref.st)
            {
                retval.st = templateLib.getInstanceOf("caller",
              new STAttrMap().put("c", dynamic_ref164.st));
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
    // $ANTLR end caller

    public static class receiver_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start receiver
    // BONSTTreeWalker.g:1410:1: receiver : ^( RECEIVER dynamic_ref ) -> receiver(r=$dynamic_ref.st);
    public final receiver_return receiver() throws RecognitionException {
        receiver_return retval = new receiver_return();
        retval.start = input.LT(1);

        dynamic_ref_return dynamic_ref165 = null;


        try {
            // BONSTTreeWalker.g:1410:11: ( ^( RECEIVER dynamic_ref ) -> receiver(r=$dynamic_ref.st))
            // BONSTTreeWalker.g:1410:12: ^( RECEIVER dynamic_ref )
            {
            match(input,RECEIVER,FOLLOW_RECEIVER_in_receiver25364); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_dynamic_ref_in_receiver25366);
            dynamic_ref165=dynamic_ref();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1413:12: -> receiver(r=$dynamic_ref.st)
            {
                retval.st = templateLib.getInstanceOf("receiver",
              new STAttrMap().put("r", dynamic_ref165.st));
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
    // $ANTLR end receiver

    public static class dynamic_ref_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start dynamic_ref
    // BONSTTreeWalker.g:1417:1: dynamic_ref : ^( DYNAMIC_REF (eil+= extended_id )+ ) -> dynamicRef(eil=$eil);
    public final dynamic_ref_return dynamic_ref() throws RecognitionException {
        dynamic_ref_return retval = new dynamic_ref_return();
        retval.start = input.LT(1);

        List list_eil=null;
        RuleReturnScope eil = null;
        try {
            // BONSTTreeWalker.g:1417:14: ( ^( DYNAMIC_REF (eil+= extended_id )+ ) -> dynamicRef(eil=$eil))
            // BONSTTreeWalker.g:1417:15: ^( DYNAMIC_REF (eil+= extended_id )+ )
            {
            match(input,DYNAMIC_REF,FOLLOW_DYNAMIC_REF_in_dynamic_ref25460); 

            match(input, Token.DOWN, null); 
            // BONSTTreeWalker.g:1418:29: (eil+= extended_id )+
            int cnt149=0;
            loop149:
            do {
                int alt149=2;
                int LA149_0 = input.LA(1);

                if ( (LA149_0==EXTENDED_ID) ) {
                    alt149=1;
                }


                switch (alt149) {
            	case 1 :
            	    // BONSTTreeWalker.g:1418:30: eil+= extended_id
            	    {
            	    pushFollow(FOLLOW_extended_id_in_dynamic_ref25465);
            	    eil=extended_id();
            	    _fsp--;

            	    if (list_eil==null) list_eil=new ArrayList();
            	    list_eil.add(eil.getTemplate());


            	    }
            	    break;

            	default :
            	    if ( cnt149 >= 1 ) break loop149;
                        EarlyExitException eee =
                            new EarlyExitException(149, input);
                        throw eee;
                }
                cnt149++;
            } while (true);


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1420:15: -> dynamicRef(eil=$eil)
            {
                retval.st = templateLib.getInstanceOf("dynamicRef",
              new STAttrMap().put("eil", list_eil));
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
    // $ANTLR end dynamic_ref

    public static class dynamic_component_name_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start dynamic_component_name
    // BONSTTreeWalker.g:1424:1: dynamic_component_name : ( ^( DYNAMIC_COMPONENT_NAME IDENTIFIER (ei+= extended_id )? ) -> dynamicComponentName(a=$IDENTIFIER.textb=$ei) | ^( DYNAMIC_COMPONENT_NAME INTEGER ) -> dynamicComponentName(a=$INTEGER.text));
    public final dynamic_component_name_return dynamic_component_name() throws RecognitionException {
        dynamic_component_name_return retval = new dynamic_component_name_return();
        retval.start = input.LT(1);

        CommonTree IDENTIFIER166=null;
        CommonTree INTEGER167=null;
        List list_ei=null;
        RuleReturnScope ei = null;
        try {
            // BONSTTreeWalker.g:1424:25: ( ^( DYNAMIC_COMPONENT_NAME IDENTIFIER (ei+= extended_id )? ) -> dynamicComponentName(a=$IDENTIFIER.textb=$ei) | ^( DYNAMIC_COMPONENT_NAME INTEGER ) -> dynamicComponentName(a=$INTEGER.text))
            int alt151=2;
            int LA151_0 = input.LA(1);

            if ( (LA151_0==DYNAMIC_COMPONENT_NAME) ) {
                int LA151_1 = input.LA(2);

                if ( (LA151_1==DOWN) ) {
                    int LA151_2 = input.LA(3);

                    if ( (LA151_2==INTEGER) ) {
                        alt151=2;
                    }
                    else if ( (LA151_2==IDENTIFIER) ) {
                        alt151=1;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("1424:1: dynamic_component_name : ( ^( DYNAMIC_COMPONENT_NAME IDENTIFIER (ei+= extended_id )? ) -> dynamicComponentName(a=$IDENTIFIER.textb=$ei) | ^( DYNAMIC_COMPONENT_NAME INTEGER ) -> dynamicComponentName(a=$INTEGER.text));", 151, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1424:1: dynamic_component_name : ( ^( DYNAMIC_COMPONENT_NAME IDENTIFIER (ei+= extended_id )? ) -> dynamicComponentName(a=$IDENTIFIER.textb=$ei) | ^( DYNAMIC_COMPONENT_NAME INTEGER ) -> dynamicComponentName(a=$INTEGER.text));", 151, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1424:1: dynamic_component_name : ( ^( DYNAMIC_COMPONENT_NAME IDENTIFIER (ei+= extended_id )? ) -> dynamicComponentName(a=$IDENTIFIER.textb=$ei) | ^( DYNAMIC_COMPONENT_NAME INTEGER ) -> dynamicComponentName(a=$INTEGER.text));", 151, 0, input);

                throw nvae;
            }
            switch (alt151) {
                case 1 :
                    // BONSTTreeWalker.g:1424:26: ^( DYNAMIC_COMPONENT_NAME IDENTIFIER (ei+= extended_id )? )
                    {
                    match(input,DYNAMIC_COMPONENT_NAME,FOLLOW_DYNAMIC_COMPONENT_NAME_in_dynamic_component_name25574); 

                    match(input, Token.DOWN, null); 
                    IDENTIFIER166=(CommonTree)input.LT(1);
                    match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_dynamic_component_name25576); 
                    // BONSTTreeWalker.g:1425:62: (ei+= extended_id )?
                    int alt150=2;
                    int LA150_0 = input.LA(1);

                    if ( (LA150_0==EXTENDED_ID) ) {
                        alt150=1;
                    }
                    switch (alt150) {
                        case 1 :
                            // BONSTTreeWalker.g:1425:63: ei+= extended_id
                            {
                            pushFollow(FOLLOW_extended_id_in_dynamic_component_name25581);
                            ei=extended_id();
                            _fsp--;

                            if (list_ei==null) list_ei=new ArrayList();
                            list_ei.add(ei.getTemplate());


                            }
                            break;

                    }


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1427:26: -> dynamicComponentName(a=$IDENTIFIER.textb=$ei)
                    {
                        retval.st = templateLib.getInstanceOf("dynamicComponentName",
                      new STAttrMap().put("a", IDENTIFIER166.getText()).put("b", list_ei));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1430:26: ^( DYNAMIC_COMPONENT_NAME INTEGER )
                    {
                    match(input,DYNAMIC_COMPONENT_NAME,FOLLOW_DYNAMIC_COMPONENT_NAME_in_dynamic_component_name25759); 

                    match(input, Token.DOWN, null); 
                    INTEGER167=(CommonTree)input.LT(1);
                    match(input,INTEGER,FOLLOW_INTEGER_in_dynamic_component_name25761); 

                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1433:26: -> dynamicComponentName(a=$INTEGER.text)
                    {
                        retval.st = templateLib.getInstanceOf("dynamicComponentName",
                      new STAttrMap().put("a", INTEGER167.getText()));
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
        return retval;
    }
    // $ANTLR end dynamic_component_name

    public static class object_name_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start object_name
    // BONSTTreeWalker.g:1437:1: object_name : ^( OBJECT_NAME class_name (ei+= extended_id )? ) -> objectName(a=$class_name.stb=$ei);
    public final object_name_return object_name() throws RecognitionException {
        object_name_return retval = new object_name_return();
        retval.start = input.LT(1);

        List list_ei=null;
        class_name_return class_name168 = null;

        RuleReturnScope ei = null;
        try {
            // BONSTTreeWalker.g:1437:14: ( ^( OBJECT_NAME class_name (ei+= extended_id )? ) -> objectName(a=$class_name.stb=$ei))
            // BONSTTreeWalker.g:1437:15: ^( OBJECT_NAME class_name (ei+= extended_id )? )
            {
            match(input,OBJECT_NAME,FOLLOW_OBJECT_NAME_in_object_name25901); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_class_name_in_object_name25903);
            class_name168=class_name();
            _fsp--;

            // BONSTTreeWalker.g:1438:40: (ei+= extended_id )?
            int alt152=2;
            int LA152_0 = input.LA(1);

            if ( (LA152_0==EXTENDED_ID) ) {
                alt152=1;
            }
            switch (alt152) {
                case 1 :
                    // BONSTTreeWalker.g:1438:41: ei+= extended_id
                    {
                    pushFollow(FOLLOW_extended_id_in_object_name25908);
                    ei=extended_id();
                    _fsp--;

                    if (list_ei==null) list_ei=new ArrayList();
                    list_ei.add(ei.getTemplate());


                    }
                    break;

            }


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1440:15: -> objectName(a=$class_name.stb=$ei)
            {
                retval.st = templateLib.getInstanceOf("objectName",
              new STAttrMap().put("a", class_name168.st).put("b", list_ei));
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
    // $ANTLR end object_name

    public static class group_name_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start group_name
    // BONSTTreeWalker.g:1444:1: group_name : ^( GROUP_NAME extended_id ) -> groupName(name=$extended_id.st);
    public final group_name_return group_name() throws RecognitionException {
        group_name_return retval = new group_name_return();
        retval.start = input.LT(1);

        extended_id_return extended_id169 = null;


        try {
            // BONSTTreeWalker.g:1444:13: ( ^( GROUP_NAME extended_id ) -> groupName(name=$extended_id.st))
            // BONSTTreeWalker.g:1444:14: ^( GROUP_NAME extended_id )
            {
            match(input,GROUP_NAME,FOLLOW_GROUP_NAME_in_group_name26022); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_extended_id_in_group_name26024);
            extended_id169=extended_id();
            _fsp--;


            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1447:14: -> groupName(name=$extended_id.st)
            {
                retval.st = templateLib.getInstanceOf("groupName",
              new STAttrMap().put("name", extended_id169.st));
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
    // $ANTLR end group_name

    public static class message_label_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start message_label
    // BONSTTreeWalker.g:1451:1: message_label : ^( MESSAGE_LABEL MANIFEST_STRING ) -> messageLabel(l=$MANIFEST_STRING.text);
    public final message_label_return message_label() throws RecognitionException {
        message_label_return retval = new message_label_return();
        retval.start = input.LT(1);

        CommonTree MANIFEST_STRING170=null;

        try {
            // BONSTTreeWalker.g:1451:16: ( ^( MESSAGE_LABEL MANIFEST_STRING ) -> messageLabel(l=$MANIFEST_STRING.text))
            // BONSTTreeWalker.g:1451:17: ^( MESSAGE_LABEL MANIFEST_STRING )
            {
            match(input,MESSAGE_LABEL,FOLLOW_MESSAGE_LABEL_in_message_label26131); 

            match(input, Token.DOWN, null); 
            MANIFEST_STRING170=(CommonTree)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_message_label26133); 

            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1454:17: -> messageLabel(l=$MANIFEST_STRING.text)
            {
                retval.st = templateLib.getInstanceOf("messageLabel",
              new STAttrMap().put("l", MANIFEST_STRING170.getText()));
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
    // $ANTLR end message_label

    public static class notational_tuning_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start notational_tuning
    // BONSTTreeWalker.g:1458:1: notational_tuning : ( ^( NOTATIONAL_TUNING change_string_marks ) -> notationalTuning(nt=$change_string_marks.st) | ^( NOTATIONAL_TUNING change_concatenator ) -> notationalTuning(nt=$change_concatenator.st) | ^( NOTATIONAL_TUNING change_prefix ) -> notationalTuning(nt=$change_prefix.st));
    public final notational_tuning_return notational_tuning() throws RecognitionException {
        notational_tuning_return retval = new notational_tuning_return();
        retval.start = input.LT(1);

        change_string_marks_return change_string_marks171 = null;

        change_concatenator_return change_concatenator172 = null;

        change_prefix_return change_prefix173 = null;


        try {
            // BONSTTreeWalker.g:1461:20: ( ^( NOTATIONAL_TUNING change_string_marks ) -> notationalTuning(nt=$change_string_marks.st) | ^( NOTATIONAL_TUNING change_concatenator ) -> notationalTuning(nt=$change_concatenator.st) | ^( NOTATIONAL_TUNING change_prefix ) -> notationalTuning(nt=$change_prefix.st))
            int alt153=3;
            int LA153_0 = input.LA(1);

            if ( (LA153_0==NOTATIONAL_TUNING) ) {
                int LA153_1 = input.LA(2);

                if ( (LA153_1==DOWN) ) {
                    switch ( input.LA(3) ) {
                    case CHANGE_CONCATENATOR:
                        {
                        alt153=2;
                        }
                        break;
                    case CHANGE_STRING_MARKS:
                        {
                        alt153=1;
                        }
                        break;
                    case CHANGE_PREFIX:
                        {
                        alt153=3;
                        }
                        break;
                    default:
                        NoViableAltException nvae =
                            new NoViableAltException("1458:1: notational_tuning : ( ^( NOTATIONAL_TUNING change_string_marks ) -> notationalTuning(nt=$change_string_marks.st) | ^( NOTATIONAL_TUNING change_concatenator ) -> notationalTuning(nt=$change_concatenator.st) | ^( NOTATIONAL_TUNING change_prefix ) -> notationalTuning(nt=$change_prefix.st));", 153, 2, input);

                        throw nvae;
                    }

                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1458:1: notational_tuning : ( ^( NOTATIONAL_TUNING change_string_marks ) -> notationalTuning(nt=$change_string_marks.st) | ^( NOTATIONAL_TUNING change_concatenator ) -> notationalTuning(nt=$change_concatenator.st) | ^( NOTATIONAL_TUNING change_prefix ) -> notationalTuning(nt=$change_prefix.st));", 153, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1458:1: notational_tuning : ( ^( NOTATIONAL_TUNING change_string_marks ) -> notationalTuning(nt=$change_string_marks.st) | ^( NOTATIONAL_TUNING change_concatenator ) -> notationalTuning(nt=$change_concatenator.st) | ^( NOTATIONAL_TUNING change_prefix ) -> notationalTuning(nt=$change_prefix.st));", 153, 0, input);

                throw nvae;
            }
            switch (alt153) {
                case 1 :
                    // BONSTTreeWalker.g:1461:21: ^( NOTATIONAL_TUNING change_string_marks )
                    {
                    match(input,NOTATIONAL_TUNING,FOLLOW_NOTATIONAL_TUNING_in_notational_tuning26245); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_change_string_marks_in_notational_tuning26247);
                    change_string_marks171=change_string_marks();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1464:21: -> notationalTuning(nt=$change_string_marks.st)
                    {
                        retval.st = templateLib.getInstanceOf("notationalTuning",
                      new STAttrMap().put("nt", change_string_marks171.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1467:21: ^( NOTATIONAL_TUNING change_concatenator )
                    {
                    match(input,NOTATIONAL_TUNING,FOLLOW_NOTATIONAL_TUNING_in_notational_tuning26389); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_change_concatenator_in_notational_tuning26391);
                    change_concatenator172=change_concatenator();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1470:21: -> notationalTuning(nt=$change_concatenator.st)
                    {
                        retval.st = templateLib.getInstanceOf("notationalTuning",
                      new STAttrMap().put("nt", change_concatenator172.st));
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:1473:21: ^( NOTATIONAL_TUNING change_prefix )
                    {
                    match(input,NOTATIONAL_TUNING,FOLLOW_NOTATIONAL_TUNING_in_notational_tuning26534); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_change_prefix_in_notational_tuning26536);
                    change_prefix173=change_prefix();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1476:21: -> notationalTuning(nt=$change_prefix.st)
                    {
                        retval.st = templateLib.getInstanceOf("notationalTuning",
                      new STAttrMap().put("nt", change_prefix173.st));
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
        return retval;
    }
    // $ANTLR end notational_tuning

    public static class change_string_marks_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start change_string_marks
    // BONSTTreeWalker.g:1480:1: change_string_marks : ^( CHANGE_STRING_MARKS m1= MANIFEST_STRING m2= MANIFEST_STRING ) -> changeStringMarks(m1=$m1.textm2=$m2.text);
    public final change_string_marks_return change_string_marks() throws RecognitionException {
        change_string_marks_return retval = new change_string_marks_return();
        retval.start = input.LT(1);

        CommonTree m1=null;
        CommonTree m2=null;

        try {
            // BONSTTreeWalker.g:1480:22: ( ^( CHANGE_STRING_MARKS m1= MANIFEST_STRING m2= MANIFEST_STRING ) -> changeStringMarks(m1=$m1.textm2=$m2.text))
            // BONSTTreeWalker.g:1480:23: ^( CHANGE_STRING_MARKS m1= MANIFEST_STRING m2= MANIFEST_STRING )
            {
            match(input,CHANGE_STRING_MARKS,FOLLOW_CHANGE_STRING_MARKS_in_change_string_marks26683); 

            match(input, Token.DOWN, null); 
            m1=(CommonTree)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_string_marks26687); 
            m2=(CommonTree)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_string_marks26691); 

            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1483:23: -> changeStringMarks(m1=$m1.textm2=$m2.text)
            {
                retval.st = templateLib.getInstanceOf("changeStringMarks",
              new STAttrMap().put("m1", m1.getText()).put("m2", m2.getText()));
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
    // $ANTLR end change_string_marks

    public static class change_concatenator_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start change_concatenator
    // BONSTTreeWalker.g:1487:1: change_concatenator : ^( CHANGE_CONCATENATOR MANIFEST_STRING ) -> changeConcatenator(cc=$MANIFEST_STRING.text);
    public final change_concatenator_return change_concatenator() throws RecognitionException {
        change_concatenator_return retval = new change_concatenator_return();
        retval.start = input.LT(1);

        CommonTree MANIFEST_STRING174=null;

        try {
            // BONSTTreeWalker.g:1487:22: ( ^( CHANGE_CONCATENATOR MANIFEST_STRING ) -> changeConcatenator(cc=$MANIFEST_STRING.text))
            // BONSTTreeWalker.g:1487:23: ^( CHANGE_CONCATENATOR MANIFEST_STRING )
            {
            match(input,CHANGE_CONCATENATOR,FOLLOW_CHANGE_CONCATENATOR_in_change_concatenator26852); 

            match(input, Token.DOWN, null); 
            MANIFEST_STRING174=(CommonTree)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_concatenator26854); 

            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1490:23: -> changeConcatenator(cc=$MANIFEST_STRING.text)
            {
                retval.st = templateLib.getInstanceOf("changeConcatenator",
              new STAttrMap().put("cc", MANIFEST_STRING174.getText()));
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
    // $ANTLR end change_concatenator

    public static class change_prefix_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start change_prefix
    // BONSTTreeWalker.g:1494:1: change_prefix : ^( CHANGE_PREFIX MANIFEST_STRING ) -> changePrefix(cp=$MANIFEST_STRING.text);
    public final change_prefix_return change_prefix() throws RecognitionException {
        change_prefix_return retval = new change_prefix_return();
        retval.start = input.LT(1);

        CommonTree MANIFEST_STRING175=null;

        try {
            // BONSTTreeWalker.g:1494:16: ( ^( CHANGE_PREFIX MANIFEST_STRING ) -> changePrefix(cp=$MANIFEST_STRING.text))
            // BONSTTreeWalker.g:1494:17: ^( CHANGE_PREFIX MANIFEST_STRING )
            {
            match(input,CHANGE_PREFIX,FOLLOW_CHANGE_PREFIX_in_change_prefix27005); 

            match(input, Token.DOWN, null); 
            MANIFEST_STRING175=(CommonTree)input.LT(1);
            match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_change_prefix27007); 

            match(input, Token.UP, null); 

            // TEMPLATE REWRITE
            // 1497:17: -> changePrefix(cp=$MANIFEST_STRING.text)
            {
                retval.st = templateLib.getInstanceOf("changePrefix",
              new STAttrMap().put("cp", MANIFEST_STRING175.getText()));
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
    // $ANTLR end change_prefix

    public static class expression_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start expression
    // BONSTTreeWalker.g:1501:1: expression : ( ^( EXPRESSION equivalence_expression ) -> expressionAsIs(exp=$equivalence_expression.st) | ^( EXPRESSION quantification ) -> expressionAsIs(exp=$quantification.st));
    public final expression_return expression() throws RecognitionException {
        expression_return retval = new expression_return();
        retval.start = input.LT(1);

        equivalence_expression_return equivalence_expression176 = null;

        quantification_return quantification177 = null;


        try {
            // BONSTTreeWalker.g:1505:13: ( ^( EXPRESSION equivalence_expression ) -> expressionAsIs(exp=$equivalence_expression.st) | ^( EXPRESSION quantification ) -> expressionAsIs(exp=$quantification.st))
            int alt154=2;
            int LA154_0 = input.LA(1);

            if ( (LA154_0==EXPRESSION) ) {
                int LA154_1 = input.LA(2);

                if ( (LA154_1==DOWN) ) {
                    int LA154_2 = input.LA(3);

                    if ( (LA154_2==CALL_CHAIN||LA154_2==CONSTANT||LA154_2==NOT_MEMBER_OF||LA154_2==MOD_POW_OP||LA154_2==196||LA154_2==225||LA154_2==227||LA154_2==246||(LA154_2>=262 && LA154_2<=278)||LA154_2==280) ) {
                        alt154=1;
                    }
                    else if ( (LA154_2==QUANTIFICATION) ) {
                        alt154=2;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("1501:1: expression : ( ^( EXPRESSION equivalence_expression ) -> expressionAsIs(exp=$equivalence_expression.st) | ^( EXPRESSION quantification ) -> expressionAsIs(exp=$quantification.st));", 154, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1501:1: expression : ( ^( EXPRESSION equivalence_expression ) -> expressionAsIs(exp=$equivalence_expression.st) | ^( EXPRESSION quantification ) -> expressionAsIs(exp=$quantification.st));", 154, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1501:1: expression : ( ^( EXPRESSION equivalence_expression ) -> expressionAsIs(exp=$equivalence_expression.st) | ^( EXPRESSION quantification ) -> expressionAsIs(exp=$quantification.st));", 154, 0, input);

                throw nvae;
            }
            switch (alt154) {
                case 1 :
                    // BONSTTreeWalker.g:1505:14: ^( EXPRESSION equivalence_expression )
                    {
                    match(input,EXPRESSION,FOLLOW_EXPRESSION_in_expression27117); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_equivalence_expression_in_expression27119);
                    equivalence_expression176=equivalence_expression();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1508:14: -> expressionAsIs(exp=$equivalence_expression.st)
                    {
                        retval.st = templateLib.getInstanceOf("expressionAsIs",
                      new STAttrMap().put("exp", equivalence_expression176.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1511:14: ^( EXPRESSION quantification )
                    {
                    match(input,EXPRESSION,FOLLOW_EXPRESSION_in_expression27220); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_quantification_in_expression27222);
                    quantification177=quantification();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1514:14: -> expressionAsIs(exp=$quantification.st)
                    {
                        retval.st = templateLib.getInstanceOf("expressionAsIs",
                      new STAttrMap().put("exp", quantification177.st));
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
        return retval;
    }
    // $ANTLR end expression

    public static class equivalence_expression_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start equivalence_expression
    // BONSTTreeWalker.g:1518:1: equivalence_expression : ( ^( '<->' e1= equivalence_expression e2= equivalence_expression ) -> equivalence_expression(e1=$e1.ste2=$e2.st) | implies_expression -> expressionAsIs(exp=$implies_expression.st));
    public final equivalence_expression_return equivalence_expression() throws RecognitionException {
        equivalence_expression_return retval = new equivalence_expression_return();
        retval.start = input.LT(1);

        equivalence_expression_return e1 = null;

        equivalence_expression_return e2 = null;

        implies_expression_return implies_expression178 = null;


        try {
            // BONSTTreeWalker.g:1518:24: ( ^( '<->' e1= equivalence_expression e2= equivalence_expression ) -> equivalence_expression(e1=$e1.ste2=$e2.st) | implies_expression -> expressionAsIs(exp=$implies_expression.st))
            int alt155=2;
            int LA155_0 = input.LA(1);

            if ( (LA155_0==262) ) {
                alt155=1;
            }
            else if ( (LA155_0==CALL_CHAIN||LA155_0==CONSTANT||LA155_0==NOT_MEMBER_OF||LA155_0==MOD_POW_OP||LA155_0==196||LA155_0==225||LA155_0==227||LA155_0==246||(LA155_0>=263 && LA155_0<=278)||LA155_0==280) ) {
                alt155=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1518:1: equivalence_expression : ( ^( '<->' e1= equivalence_expression e2= equivalence_expression ) -> equivalence_expression(e1=$e1.ste2=$e2.st) | implies_expression -> expressionAsIs(exp=$implies_expression.st));", 155, 0, input);

                throw nvae;
            }
            switch (alt155) {
                case 1 :
                    // BONSTTreeWalker.g:1518:27: ^( '<->' e1= equivalence_expression e2= equivalence_expression )
                    {
                    match(input,262,FOLLOW_262_in_equivalence_expression27300); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_equivalence_expression_in_equivalence_expression27304);
                    e1=equivalence_expression();
                    _fsp--;

                    pushFollow(FOLLOW_equivalence_expression_in_equivalence_expression27308);
                    e2=equivalence_expression();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1518:88: -> equivalence_expression(e1=$e1.ste2=$e2.st)
                    {
                        retval.st = templateLib.getInstanceOf("equivalence_expression",
                      new STAttrMap().put("e1", e1.st).put("e2", e2.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1519:16: implies_expression
                    {
                    pushFollow(FOLLOW_implies_expression_in_equivalence_expression27339);
                    implies_expression178=implies_expression();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1519:35: -> expressionAsIs(exp=$implies_expression.st)
                    {
                        retval.st = templateLib.getInstanceOf("expressionAsIs",
                      new STAttrMap().put("exp", implies_expression178.st));
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
        return retval;
    }
    // $ANTLR end equivalence_expression

    public static class implies_expression_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start implies_expression
    // BONSTTreeWalker.g:1523:1: implies_expression : ( ^( '->' e1= implies_expression e2= implies_expression ) -> impliesExpression(e1=$e1.ste2=$e2.st) | and_or_xor_expression -> expressionAsIs(exp=$and_or_xor_expression.st));
    public final implies_expression_return implies_expression() throws RecognitionException {
        implies_expression_return retval = new implies_expression_return();
        retval.start = input.LT(1);

        implies_expression_return e1 = null;

        implies_expression_return e2 = null;

        and_or_xor_expression_return and_or_xor_expression179 = null;


        try {
            // BONSTTreeWalker.g:1523:21: ( ^( '->' e1= implies_expression e2= implies_expression ) -> impliesExpression(e1=$e1.ste2=$e2.st) | and_or_xor_expression -> expressionAsIs(exp=$and_or_xor_expression.st))
            int alt156=2;
            int LA156_0 = input.LA(1);

            if ( (LA156_0==227) ) {
                alt156=1;
            }
            else if ( (LA156_0==CALL_CHAIN||LA156_0==CONSTANT||LA156_0==NOT_MEMBER_OF||LA156_0==MOD_POW_OP||LA156_0==196||LA156_0==225||LA156_0==246||(LA156_0>=263 && LA156_0<=278)||LA156_0==280) ) {
                alt156=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1523:1: implies_expression : ( ^( '->' e1= implies_expression e2= implies_expression ) -> impliesExpression(e1=$e1.ste2=$e2.st) | and_or_xor_expression -> expressionAsIs(exp=$and_or_xor_expression.st));", 156, 0, input);

                throw nvae;
            }
            switch (alt156) {
                case 1 :
                    // BONSTTreeWalker.g:1523:24: ^( '->' e1= implies_expression e2= implies_expression )
                    {
                    match(input,227,FOLLOW_227_in_implies_expression27385); 

                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_implies_expression_in_implies_expression27389);
                    e1=implies_expression();
                    _fsp--;

                    pushFollow(FOLLOW_implies_expression_in_implies_expression27393);
                    e2=implies_expression();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1523:76: -> impliesExpression(e1=$e1.ste2=$e2.st)
                    {
                        retval.st = templateLib.getInstanceOf("impliesExpression",
                      new STAttrMap().put("e1", e1.st).put("e2", e2.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1524:25: and_or_xor_expression
                    {
                    pushFollow(FOLLOW_and_or_xor_expression_in_implies_expression27433);
                    and_or_xor_expression179=and_or_xor_expression();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1524:47: -> expressionAsIs(exp=$and_or_xor_expression.st)
                    {
                        retval.st = templateLib.getInstanceOf("expressionAsIs",
                      new STAttrMap().put("exp", and_or_xor_expression179.st));
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
        return retval;
    }
    // $ANTLR end implies_expression

    public static class and_or_xor_expression_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start and_or_xor_expression
    // BONSTTreeWalker.g:1527:1: and_or_xor_expression : ( ^( and_or_xor_op e1= and_or_xor_expression e2= and_or_xor_expression ) -> andOrXorExpression(op=$and_or_xor_op.ste1=$e1.ste2=$e2.st) | comparison_expression -> expressionAsIs(exp=$comparison_expression.st));
    public final and_or_xor_expression_return and_or_xor_expression() throws RecognitionException {
        and_or_xor_expression_return retval = new and_or_xor_expression_return();
        retval.start = input.LT(1);

        and_or_xor_expression_return e1 = null;

        and_or_xor_expression_return e2 = null;

        and_or_xor_op_return and_or_xor_op180 = null;

        comparison_expression_return comparison_expression181 = null;


        try {
            // BONSTTreeWalker.g:1527:24: ( ^( and_or_xor_op e1= and_or_xor_expression e2= and_or_xor_expression ) -> andOrXorExpression(op=$and_or_xor_op.ste1=$e1.ste2=$e2.st) | comparison_expression -> expressionAsIs(exp=$comparison_expression.st))
            int alt157=2;
            int LA157_0 = input.LA(1);

            if ( ((LA157_0>=265 && LA157_0<=267)) ) {
                alt157=1;
            }
            else if ( (LA157_0==CALL_CHAIN||LA157_0==CONSTANT||LA157_0==NOT_MEMBER_OF||LA157_0==MOD_POW_OP||LA157_0==196||LA157_0==225||LA157_0==246||(LA157_0>=263 && LA157_0<=264)||(LA157_0>=268 && LA157_0<=278)||LA157_0==280) ) {
                alt157=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1527:1: and_or_xor_expression : ( ^( and_or_xor_op e1= and_or_xor_expression e2= and_or_xor_expression ) -> andOrXorExpression(op=$and_or_xor_op.ste1=$e1.ste2=$e2.st) | comparison_expression -> expressionAsIs(exp=$comparison_expression.st));", 157, 0, input);

                throw nvae;
            }
            switch (alt157) {
                case 1 :
                    // BONSTTreeWalker.g:1527:27: ^( and_or_xor_op e1= and_or_xor_expression e2= and_or_xor_expression )
                    {
                    pushFollow(FOLLOW_and_or_xor_op_in_and_or_xor_expression27474);
                    and_or_xor_op180=and_or_xor_op();
                    _fsp--;


                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_and_or_xor_expression_in_and_or_xor_expression27478);
                    e1=and_or_xor_expression();
                    _fsp--;

                    pushFollow(FOLLOW_and_or_xor_expression_in_and_or_xor_expression27482);
                    e2=and_or_xor_expression();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1527:94: -> andOrXorExpression(op=$and_or_xor_op.ste1=$e1.ste2=$e2.st)
                    {
                        retval.st = templateLib.getInstanceOf("andOrXorExpression",
                      new STAttrMap().put("op", and_or_xor_op180.st).put("e1", e1.st).put("e2", e2.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1528:16: comparison_expression
                    {
                    pushFollow(FOLLOW_comparison_expression_in_and_or_xor_expression27517);
                    comparison_expression181=comparison_expression();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1528:38: -> expressionAsIs(exp=$comparison_expression.st)
                    {
                        retval.st = templateLib.getInstanceOf("expressionAsIs",
                      new STAttrMap().put("exp", comparison_expression181.st));
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
        return retval;
    }
    // $ANTLR end and_or_xor_expression

    public static class comparison_expression_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start comparison_expression
    // BONSTTreeWalker.g:1531:1: comparison_expression : ( ^( comparison_op e1= comparison_expression e2= comparison_expression ) -> comparisonExpression(op=$comparison_op.ste1=$e1.ste2=$e2.st) | add_sub_expression -> expressionAsIs(exp=$add_sub_expression.st));
    public final comparison_expression_return comparison_expression() throws RecognitionException {
        comparison_expression_return retval = new comparison_expression_return();
        retval.start = input.LT(1);

        comparison_expression_return e1 = null;

        comparison_expression_return e2 = null;

        comparison_op_return comparison_op182 = null;

        add_sub_expression_return add_sub_expression183 = null;


        try {
            // BONSTTreeWalker.g:1531:24: ( ^( comparison_op e1= comparison_expression e2= comparison_expression ) -> comparisonExpression(op=$comparison_op.ste1=$e1.ste2=$e2.st) | add_sub_expression -> expressionAsIs(exp=$add_sub_expression.st))
            int alt158=2;
            int LA158_0 = input.LA(1);

            if ( (LA158_0==NOT_MEMBER_OF||LA158_0==196||LA158_0==246||(LA158_0>=271 && LA158_0<=276)) ) {
                alt158=1;
            }
            else if ( (LA158_0==CALL_CHAIN||LA158_0==CONSTANT||LA158_0==MOD_POW_OP||LA158_0==225||(LA158_0>=263 && LA158_0<=264)||(LA158_0>=268 && LA158_0<=270)||(LA158_0>=277 && LA158_0<=278)||LA158_0==280) ) {
                alt158=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1531:1: comparison_expression : ( ^( comparison_op e1= comparison_expression e2= comparison_expression ) -> comparisonExpression(op=$comparison_op.ste1=$e1.ste2=$e2.st) | add_sub_expression -> expressionAsIs(exp=$add_sub_expression.st));", 158, 0, input);

                throw nvae;
            }
            switch (alt158) {
                case 1 :
                    // BONSTTreeWalker.g:1531:27: ^( comparison_op e1= comparison_expression e2= comparison_expression )
                    {
                    pushFollow(FOLLOW_comparison_op_in_comparison_expression27561);
                    comparison_op182=comparison_op();
                    _fsp--;


                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_comparison_expression_in_comparison_expression27566);
                    e1=comparison_expression();
                    _fsp--;

                    pushFollow(FOLLOW_comparison_expression_in_comparison_expression27570);
                    e2=comparison_expression();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1531:95: -> comparisonExpression(op=$comparison_op.ste1=$e1.ste2=$e2.st)
                    {
                        retval.st = templateLib.getInstanceOf("comparisonExpression",
                      new STAttrMap().put("op", comparison_op182.st).put("e1", e1.st).put("e2", e2.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1532:16: add_sub_expression
                    {
                    pushFollow(FOLLOW_add_sub_expression_in_comparison_expression27605);
                    add_sub_expression183=add_sub_expression();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1532:35: -> expressionAsIs(exp=$add_sub_expression.st)
                    {
                        retval.st = templateLib.getInstanceOf("expressionAsIs",
                      new STAttrMap().put("exp", add_sub_expression183.st));
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
        return retval;
    }
    // $ANTLR end comparison_expression

    public static class add_sub_expression_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start add_sub_expression
    // BONSTTreeWalker.g:1535:1: add_sub_expression : ( ^( add_sub_op e1= add_sub_expression e2= add_sub_expression ) -> addSubExpression(op=$add_sub_op.ste1=$e1.ste2=$e2.st) | mul_div_expression -> expressionAsIs(exp=$mul_div_expression.st));
    public final add_sub_expression_return add_sub_expression() throws RecognitionException {
        add_sub_expression_return retval = new add_sub_expression_return();
        retval.start = input.LT(1);

        add_sub_expression_return e1 = null;

        add_sub_expression_return e2 = null;

        add_sub_op_return add_sub_op184 = null;

        mul_div_expression_return mul_div_expression185 = null;


        try {
            // BONSTTreeWalker.g:1535:21: ( ^( add_sub_op e1= add_sub_expression e2= add_sub_expression ) -> addSubExpression(op=$add_sub_op.ste1=$e1.ste2=$e2.st) | mul_div_expression -> expressionAsIs(exp=$mul_div_expression.st))
            int alt159=2;
            switch ( input.LA(1) ) {
            case 263:
                {
                int LA159_1 = input.LA(2);

                if ( (LA159_1==CALL_CHAIN||LA159_1==CONSTANT||LA159_1==225||(LA159_1>=263 && LA159_1<=264)||(LA159_1>=268 && LA159_1<=270)) ) {
                    alt159=2;
                }
                else if ( (LA159_1==DOWN) ) {
                    alt159=1;
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1535:1: add_sub_expression : ( ^( add_sub_op e1= add_sub_expression e2= add_sub_expression ) -> addSubExpression(op=$add_sub_op.ste1=$e1.ste2=$e2.st) | mul_div_expression -> expressionAsIs(exp=$mul_div_expression.st));", 159, 1, input);

                    throw nvae;
                }
                }
                break;
            case 264:
                {
                int LA159_2 = input.LA(2);

                if ( (LA159_2==CALL_CHAIN||LA159_2==CONSTANT||LA159_2==225||(LA159_2>=263 && LA159_2<=264)||(LA159_2>=268 && LA159_2<=270)) ) {
                    alt159=2;
                }
                else if ( (LA159_2==DOWN) ) {
                    alt159=1;
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("1535:1: add_sub_expression : ( ^( add_sub_op e1= add_sub_expression e2= add_sub_expression ) -> addSubExpression(op=$add_sub_op.ste1=$e1.ste2=$e2.st) | mul_div_expression -> expressionAsIs(exp=$mul_div_expression.st));", 159, 2, input);

                    throw nvae;
                }
                }
                break;
            case CALL_CHAIN:
            case CONSTANT:
            case MOD_POW_OP:
            case 225:
            case 268:
            case 269:
            case 270:
            case 277:
            case 278:
            case 280:
                {
                alt159=2;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("1535:1: add_sub_expression : ( ^( add_sub_op e1= add_sub_expression e2= add_sub_expression ) -> addSubExpression(op=$add_sub_op.ste1=$e1.ste2=$e2.st) | mul_div_expression -> expressionAsIs(exp=$mul_div_expression.st));", 159, 0, input);

                throw nvae;
            }

            switch (alt159) {
                case 1 :
                    // BONSTTreeWalker.g:1535:24: ^( add_sub_op e1= add_sub_expression e2= add_sub_expression )
                    {
                    pushFollow(FOLLOW_add_sub_op_in_add_sub_expression27649);
                    add_sub_op184=add_sub_op();
                    _fsp--;


                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_add_sub_expression_in_add_sub_expression27653);
                    e1=add_sub_expression();
                    _fsp--;

                    pushFollow(FOLLOW_add_sub_expression_in_add_sub_expression27657);
                    e2=add_sub_expression();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1535:82: -> addSubExpression(op=$add_sub_op.ste1=$e1.ste2=$e2.st)
                    {
                        retval.st = templateLib.getInstanceOf("addSubExpression",
                      new STAttrMap().put("op", add_sub_op184.st).put("e1", e1.st).put("e2", e2.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1536:14: mul_div_expression
                    {
                    pushFollow(FOLLOW_mul_div_expression_in_add_sub_expression27690);
                    mul_div_expression185=mul_div_expression();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1536:33: -> expressionAsIs(exp=$mul_div_expression.st)
                    {
                        retval.st = templateLib.getInstanceOf("expressionAsIs",
                      new STAttrMap().put("exp", mul_div_expression185.st));
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
        return retval;
    }
    // $ANTLR end add_sub_expression

    public static class mul_div_expression_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start mul_div_expression
    // BONSTTreeWalker.g:1539:1: mul_div_expression : ( ^( mul_div_op e1= mul_div_expression e2= mul_div_expression ) -> mulDivExpression(op=$mul_div_op.ste1=$e1.ste2=$e2.st) | mod_pow_expression -> expressionAsIs(exp=$mod_pow_expression.st));
    public final mul_div_expression_return mul_div_expression() throws RecognitionException {
        mul_div_expression_return retval = new mul_div_expression_return();
        retval.start = input.LT(1);

        mul_div_expression_return e1 = null;

        mul_div_expression_return e2 = null;

        mul_div_op_return mul_div_op186 = null;

        mod_pow_expression_return mod_pow_expression187 = null;


        try {
            // BONSTTreeWalker.g:1539:21: ( ^( mul_div_op e1= mul_div_expression e2= mul_div_expression ) -> mulDivExpression(op=$mul_div_op.ste1=$e1.ste2=$e2.st) | mod_pow_expression -> expressionAsIs(exp=$mod_pow_expression.st))
            int alt160=2;
            int LA160_0 = input.LA(1);

            if ( ((LA160_0>=277 && LA160_0<=278)||LA160_0==280) ) {
                alt160=1;
            }
            else if ( (LA160_0==CALL_CHAIN||LA160_0==CONSTANT||LA160_0==MOD_POW_OP||LA160_0==225||(LA160_0>=263 && LA160_0<=264)||(LA160_0>=268 && LA160_0<=270)) ) {
                alt160=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1539:1: mul_div_expression : ( ^( mul_div_op e1= mul_div_expression e2= mul_div_expression ) -> mulDivExpression(op=$mul_div_op.ste1=$e1.ste2=$e2.st) | mod_pow_expression -> expressionAsIs(exp=$mod_pow_expression.st));", 160, 0, input);

                throw nvae;
            }
            switch (alt160) {
                case 1 :
                    // BONSTTreeWalker.g:1539:24: ^( mul_div_op e1= mul_div_expression e2= mul_div_expression )
                    {
                    pushFollow(FOLLOW_mul_div_op_in_mul_div_expression27731);
                    mul_div_op186=mul_div_op();
                    _fsp--;


                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_mul_div_expression_in_mul_div_expression27735);
                    e1=mul_div_expression();
                    _fsp--;

                    pushFollow(FOLLOW_mul_div_expression_in_mul_div_expression27739);
                    e2=mul_div_expression();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1539:82: -> mulDivExpression(op=$mul_div_op.ste1=$e1.ste2=$e2.st)
                    {
                        retval.st = templateLib.getInstanceOf("mulDivExpression",
                      new STAttrMap().put("op", mul_div_op186.st).put("e1", e1.st).put("e2", e2.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1540:14: mod_pow_expression
                    {
                    pushFollow(FOLLOW_mod_pow_expression_in_mul_div_expression27772);
                    mod_pow_expression187=mod_pow_expression();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1540:33: -> expressionAsIs(exp=$mod_pow_expression.st)
                    {
                        retval.st = templateLib.getInstanceOf("expressionAsIs",
                      new STAttrMap().put("exp", mod_pow_expression187.st));
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
        return retval;
    }
    // $ANTLR end mul_div_expression

    public static class mod_pow_expression_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start mod_pow_expression
    // BONSTTreeWalker.g:1544:1: mod_pow_expression : ( ^( mod_pow_op e1= mod_pow_expression e2= mod_pow_expression ) -> mod_pow_expression(op=$mod_pow_op.ste1=$e1.ste2=$e2.st) | lowest_expression -> expressionAsIs(exp=$lowest_expression.st));
    public final mod_pow_expression_return mod_pow_expression() throws RecognitionException {
        mod_pow_expression_return retval = new mod_pow_expression_return();
        retval.start = input.LT(1);

        mod_pow_expression_return e1 = null;

        mod_pow_expression_return e2 = null;

        mod_pow_op_return mod_pow_op188 = null;

        lowest_expression_return lowest_expression189 = null;


        try {
            // BONSTTreeWalker.g:1544:21: ( ^( mod_pow_op e1= mod_pow_expression e2= mod_pow_expression ) -> mod_pow_expression(op=$mod_pow_op.ste1=$e1.ste2=$e2.st) | lowest_expression -> expressionAsIs(exp=$lowest_expression.st))
            int alt161=2;
            int LA161_0 = input.LA(1);

            if ( (LA161_0==MOD_POW_OP) ) {
                alt161=1;
            }
            else if ( (LA161_0==CALL_CHAIN||LA161_0==CONSTANT||LA161_0==225||(LA161_0>=263 && LA161_0<=264)||(LA161_0>=268 && LA161_0<=270)) ) {
                alt161=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1544:1: mod_pow_expression : ( ^( mod_pow_op e1= mod_pow_expression e2= mod_pow_expression ) -> mod_pow_expression(op=$mod_pow_op.ste1=$e1.ste2=$e2.st) | lowest_expression -> expressionAsIs(exp=$lowest_expression.st));", 161, 0, input);

                throw nvae;
            }
            switch (alt161) {
                case 1 :
                    // BONSTTreeWalker.g:1544:24: ^( mod_pow_op e1= mod_pow_expression e2= mod_pow_expression )
                    {
                    pushFollow(FOLLOW_mod_pow_op_in_mod_pow_expression27814);
                    mod_pow_op188=mod_pow_op();
                    _fsp--;


                    match(input, Token.DOWN, null); 
                    pushFollow(FOLLOW_mod_pow_expression_in_mod_pow_expression27818);
                    e1=mod_pow_expression();
                    _fsp--;

                    pushFollow(FOLLOW_mod_pow_expression_in_mod_pow_expression27822);
                    e2=mod_pow_expression();
                    _fsp--;


                    match(input, Token.UP, null); 

                    // TEMPLATE REWRITE
                    // 1544:82: -> mod_pow_expression(op=$mod_pow_op.ste1=$e1.ste2=$e2.st)
                    {
                        retval.st = templateLib.getInstanceOf("mod_pow_expression",
                      new STAttrMap().put("op", mod_pow_op188.st).put("e1", e1.st).put("e2", e2.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1545:24: lowest_expression
                    {
                    pushFollow(FOLLOW_lowest_expression_in_mod_pow_expression27865);
                    lowest_expression189=lowest_expression();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1545:42: -> expressionAsIs(exp=$lowest_expression.st)
                    {
                        retval.st = templateLib.getInstanceOf("expressionAsIs",
                      new STAttrMap().put("exp", lowest_expression189.st));
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
        return retval;
    }
    // $ANTLR end mod_pow_expression

    public static class lowest_expression_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start lowest_expression
    // BONSTTreeWalker.g:1548:1: lowest_expression : ( constant -> expressionAsIs(exp=$constant.st) | unary t= lowest_expression -> unaryExpression(unary=$unary.stexp=$t.st) | '(' expression ')' ( '.' cc+= call_chain )? -> parenthesisExpression(exp=$expression.stcc=$cc) | call_chain -> expressionAsIs(exp=$call_chain.st));
    public final lowest_expression_return lowest_expression() throws RecognitionException {
        lowest_expression_return retval = new lowest_expression_return();
        retval.start = input.LT(1);

        List list_cc=null;
        lowest_expression_return t = null;

        constant_return constant190 = null;

        unary_return unary191 = null;

        expression_return expression192 = null;

        call_chain_return call_chain193 = null;

        RuleReturnScope cc = null;
        try {
            // BONSTTreeWalker.g:1548:20: ( constant -> expressionAsIs(exp=$constant.st) | unary t= lowest_expression -> unaryExpression(unary=$unary.stexp=$t.st) | '(' expression ')' ( '.' cc+= call_chain )? -> parenthesisExpression(exp=$expression.stcc=$cc) | call_chain -> expressionAsIs(exp=$call_chain.st))
            int alt163=4;
            switch ( input.LA(1) ) {
            case CONSTANT:
                {
                alt163=1;
                }
                break;
            case 263:
            case 264:
            case 268:
            case 269:
            case 270:
                {
                alt163=2;
                }
                break;
            case 225:
                {
                alt163=3;
                }
                break;
            case CALL_CHAIN:
                {
                alt163=4;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("1548:1: lowest_expression : ( constant -> expressionAsIs(exp=$constant.st) | unary t= lowest_expression -> unaryExpression(unary=$unary.stexp=$t.st) | '(' expression ')' ( '.' cc+= call_chain )? -> parenthesisExpression(exp=$expression.stcc=$cc) | call_chain -> expressionAsIs(exp=$call_chain.st));", 163, 0, input);

                throw nvae;
            }

            switch (alt163) {
                case 1 :
                    // BONSTTreeWalker.g:1548:23: constant
                    {
                    pushFollow(FOLLOW_constant_in_lowest_expression27905);
                    constant190=constant();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1548:32: -> expressionAsIs(exp=$constant.st)
                    {
                        retval.st = templateLib.getInstanceOf("expressionAsIs",
                      new STAttrMap().put("exp", constant190.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1549:13: unary t= lowest_expression
                    {
                    pushFollow(FOLLOW_unary_in_lowest_expression27928);
                    unary191=unary();
                    _fsp--;

                    pushFollow(FOLLOW_lowest_expression_in_lowest_expression27932);
                    t=lowest_expression();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1549:39: -> unaryExpression(unary=$unary.stexp=$t.st)
                    {
                        retval.st = templateLib.getInstanceOf("unaryExpression",
                      new STAttrMap().put("unary", unary191.st).put("exp", t.st));
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:1550:18: '(' expression ')' ( '.' cc+= call_chain )?
                    {
                    match(input,225,FOLLOW_225_in_lowest_expression27964); 
                    pushFollow(FOLLOW_expression_in_lowest_expression27966);
                    expression192=expression();
                    _fsp--;

                    match(input,226,FOLLOW_226_in_lowest_expression27968); 
                    // BONSTTreeWalker.g:1550:37: ( '.' cc+= call_chain )?
                    int alt162=2;
                    int LA162_0 = input.LA(1);

                    if ( (LA162_0==232) ) {
                        alt162=1;
                    }
                    switch (alt162) {
                        case 1 :
                            // BONSTTreeWalker.g:1550:38: '.' cc+= call_chain
                            {
                            match(input,232,FOLLOW_232_in_lowest_expression27971); 
                            pushFollow(FOLLOW_call_chain_in_lowest_expression27975);
                            cc=call_chain();
                            _fsp--;

                            if (list_cc==null) list_cc=new ArrayList();
                            list_cc.add(cc.getTemplate());


                            }
                            break;

                    }


                    // TEMPLATE REWRITE
                    // 1550:59: -> parenthesisExpression(exp=$expression.stcc=$cc)
                    {
                        retval.st = templateLib.getInstanceOf("parenthesisExpression",
                      new STAttrMap().put("exp", expression192.st).put("cc", list_cc));
                    }



                    }
                    break;
                case 4 :
                    // BONSTTreeWalker.g:1551:18: call_chain
                    {
                    pushFollow(FOLLOW_call_chain_in_lowest_expression28009);
                    call_chain193=call_chain();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1551:29: -> expressionAsIs(exp=$call_chain.st)
                    {
                        retval.st = templateLib.getInstanceOf("expressionAsIs",
                      new STAttrMap().put("exp", call_chain193.st));
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
        return retval;
    }
    // $ANTLR end lowest_expression

    public static class manifest_textblock_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start manifest_textblock
    // BONSTTreeWalker.g:1561:1: manifest_textblock : ( MANIFEST_STRING -> manifestTextBlock(s=$MANIFEST_STRING.text) | ms= MANIFEST_TEXTBLOCK_START (m= MANIFEST_TEXTBLOCK_MIDDLE )* me= MANIFEST_TEXTBLOCK_END -> manifestTextBlock(s=t));
    public final manifest_textblock_return manifest_textblock() throws RecognitionException {
        manifest_textblock_return retval = new manifest_textblock_return();
        retval.start = input.LT(1);

        CommonTree ms=null;
        CommonTree m=null;
        CommonTree me=null;
        CommonTree MANIFEST_STRING194=null;

        try {
            // BONSTTreeWalker.g:1561:21: ( MANIFEST_STRING -> manifestTextBlock(s=$MANIFEST_STRING.text) | ms= MANIFEST_TEXTBLOCK_START (m= MANIFEST_TEXTBLOCK_MIDDLE )* me= MANIFEST_TEXTBLOCK_END -> manifestTextBlock(s=t))
            int alt165=2;
            int LA165_0 = input.LA(1);

            if ( (LA165_0==MANIFEST_STRING) ) {
                alt165=1;
            }
            else if ( (LA165_0==MANIFEST_TEXTBLOCK_START) ) {
                alt165=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1561:1: manifest_textblock : ( MANIFEST_STRING -> manifestTextBlock(s=$MANIFEST_STRING.text) | ms= MANIFEST_TEXTBLOCK_START (m= MANIFEST_TEXTBLOCK_MIDDLE )* me= MANIFEST_TEXTBLOCK_END -> manifestTextBlock(s=t));", 165, 0, input);

                throw nvae;
            }
            switch (alt165) {
                case 1 :
                    // BONSTTreeWalker.g:1561:25: MANIFEST_STRING
                    {
                    MANIFEST_STRING194=(CommonTree)input.LT(1);
                    match(input,MANIFEST_STRING,FOLLOW_MANIFEST_STRING_in_manifest_textblock28049); 

                    // TEMPLATE REWRITE
                    // 1561:41: -> manifestTextBlock(s=$MANIFEST_STRING.text)
                    {
                        retval.st = templateLib.getInstanceOf("manifestTextBlock",
                      new STAttrMap().put("s", MANIFEST_STRING194.getText()));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1562:14: ms= MANIFEST_TEXTBLOCK_START (m= MANIFEST_TEXTBLOCK_MIDDLE )* me= MANIFEST_TEXTBLOCK_END
                    {
                    ms=(CommonTree)input.LT(1);
                    match(input,MANIFEST_TEXTBLOCK_START,FOLLOW_MANIFEST_TEXTBLOCK_START_in_manifest_textblock28075); 
                     String t = ms.getText(); 
                    // BONSTTreeWalker.g:1564:13: (m= MANIFEST_TEXTBLOCK_MIDDLE )*
                    loop164:
                    do {
                        int alt164=2;
                        int LA164_0 = input.LA(1);

                        if ( (LA164_0==MANIFEST_TEXTBLOCK_MIDDLE) ) {
                            alt164=1;
                        }


                        switch (alt164) {
                    	case 1 :
                    	    // BONSTTreeWalker.g:1564:14: m= MANIFEST_TEXTBLOCK_MIDDLE
                    	    {
                    	    m=(CommonTree)input.LT(1);
                    	    match(input,MANIFEST_TEXTBLOCK_MIDDLE,FOLLOW_MANIFEST_TEXTBLOCK_MIDDLE_in_manifest_textblock28108); 
                    	     t+=m.getText(); 

                    	    }
                    	    break;

                    	default :
                    	    break loop164;
                        }
                    } while (true);

                    me=(CommonTree)input.LT(1);
                    match(input,MANIFEST_TEXTBLOCK_END,FOLLOW_MANIFEST_TEXTBLOCK_END_in_manifest_textblock28129); 
                     t+=me.getText(); 

                    // TEMPLATE REWRITE
                    // 1567:12: -> manifestTextBlock(s=t)
                    {
                        retval.st = templateLib.getInstanceOf("manifestTextBlock",
                      new STAttrMap().put("s", t));
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
        return retval;
    }
    // $ANTLR end manifest_textblock

    public static class add_sub_op_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start add_sub_op
    // BONSTTreeWalker.g:1572:1: add_sub_op : ( '+' -> plus() | '-' -> minus());
    public final add_sub_op_return add_sub_op() throws RecognitionException {
        add_sub_op_return retval = new add_sub_op_return();
        retval.start = input.LT(1);

        try {
            // BONSTTreeWalker.g:1576:13: ( '+' -> plus() | '-' -> minus())
            int alt166=2;
            int LA166_0 = input.LA(1);

            if ( (LA166_0==263) ) {
                alt166=1;
            }
            else if ( (LA166_0==264) ) {
                alt166=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1572:1: add_sub_op : ( '+' -> plus() | '-' -> minus());", 166, 0, input);

                throw nvae;
            }
            switch (alt166) {
                case 1 :
                    // BONSTTreeWalker.g:1576:16: '+'
                    {
                    match(input,263,FOLLOW_263_in_add_sub_op28212); 

                    // TEMPLATE REWRITE
                    // 1576:20: -> plus()
                    {
                        retval.st = templateLib.getInstanceOf("plus");
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1577:16: '-'
                    {
                    match(input,264,FOLLOW_264_in_add_sub_op28235); 

                    // TEMPLATE REWRITE
                    // 1577:20: -> minus()
                    {
                        retval.st = templateLib.getInstanceOf("minus");
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
        return retval;
    }
    // $ANTLR end add_sub_op

    public static class and_or_xor_op_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start and_or_xor_op
    // BONSTTreeWalker.g:1580:1: and_or_xor_op : ( 'and' -> and() | 'or' -> or() | 'xor' -> xor());
    public final and_or_xor_op_return and_or_xor_op() throws RecognitionException {
        and_or_xor_op_return retval = new and_or_xor_op_return();
        retval.start = input.LT(1);

        try {
            // BONSTTreeWalker.g:1580:16: ( 'and' -> and() | 'or' -> or() | 'xor' -> xor())
            int alt167=3;
            switch ( input.LA(1) ) {
            case 265:
                {
                alt167=1;
                }
                break;
            case 266:
                {
                alt167=2;
                }
                break;
            case 267:
                {
                alt167=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("1580:1: and_or_xor_op : ( 'and' -> and() | 'or' -> or() | 'xor' -> xor());", 167, 0, input);

                throw nvae;
            }

            switch (alt167) {
                case 1 :
                    // BONSTTreeWalker.g:1580:19: 'and'
                    {
                    match(input,265,FOLLOW_265_in_and_or_xor_op28264); 

                    // TEMPLATE REWRITE
                    // 1580:25: -> and()
                    {
                        retval.st = templateLib.getInstanceOf("and");
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1581:19: 'or'
                    {
                    match(input,266,FOLLOW_266_in_and_or_xor_op28290); 

                    // TEMPLATE REWRITE
                    // 1581:25: -> or()
                    {
                        retval.st = templateLib.getInstanceOf("or");
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:1582:19: 'xor'
                    {
                    match(input,267,FOLLOW_267_in_and_or_xor_op28317); 

                    // TEMPLATE REWRITE
                    // 1582:25: -> xor()
                    {
                        retval.st = templateLib.getInstanceOf("xor");
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
        return retval;
    }
    // $ANTLR end and_or_xor_op

    public static class unary_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start unary
    // BONSTTreeWalker.g:1585:1: unary : ( other_unary -> unary(u=$other_unary.st) | add_sub_op -> unary(ou=$add_sub_op.st));
    public final unary_return unary() throws RecognitionException {
        unary_return retval = new unary_return();
        retval.start = input.LT(1);

        other_unary_return other_unary195 = null;

        add_sub_op_return add_sub_op196 = null;


        try {
            // BONSTTreeWalker.g:1585:9: ( other_unary -> unary(u=$other_unary.st) | add_sub_op -> unary(ou=$add_sub_op.st))
            int alt168=2;
            int LA168_0 = input.LA(1);

            if ( ((LA168_0>=268 && LA168_0<=270)) ) {
                alt168=1;
            }
            else if ( ((LA168_0>=263 && LA168_0<=264)) ) {
                alt168=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("1585:1: unary : ( other_unary -> unary(u=$other_unary.st) | add_sub_op -> unary(ou=$add_sub_op.st));", 168, 0, input);

                throw nvae;
            }
            switch (alt168) {
                case 1 :
                    // BONSTTreeWalker.g:1585:13: other_unary
                    {
                    pushFollow(FOLLOW_other_unary_in_unary28352);
                    other_unary195=other_unary();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1585:25: -> unary(u=$other_unary.st)
                    {
                        retval.st = templateLib.getInstanceOf("unary",
                      new STAttrMap().put("u", other_unary195.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1586:13: add_sub_op
                    {
                    pushFollow(FOLLOW_add_sub_op_in_unary28375);
                    add_sub_op196=add_sub_op();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1586:24: -> unary(ou=$add_sub_op.st)
                    {
                        retval.st = templateLib.getInstanceOf("unary",
                      new STAttrMap().put("ou", add_sub_op196.st));
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
        return retval;
    }
    // $ANTLR end unary

    public static class other_unary_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start other_unary
    // BONSTTreeWalker.g:1589:1: other_unary : ( 'delta' -> delta() | 'old' -> old() | 'not' -> not());
    public final other_unary_return other_unary() throws RecognitionException {
        other_unary_return retval = new other_unary_return();
        retval.start = input.LT(1);

        try {
            // BONSTTreeWalker.g:1589:14: ( 'delta' -> delta() | 'old' -> old() | 'not' -> not())
            int alt169=3;
            switch ( input.LA(1) ) {
            case 268:
                {
                alt169=1;
                }
                break;
            case 269:
                {
                alt169=2;
                }
                break;
            case 270:
                {
                alt169=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("1589:1: other_unary : ( 'delta' -> delta() | 'old' -> old() | 'not' -> not());", 169, 0, input);

                throw nvae;
            }

            switch (alt169) {
                case 1 :
                    // BONSTTreeWalker.g:1589:17: 'delta'
                    {
                    match(input,268,FOLLOW_268_in_other_unary28403); 

                    // TEMPLATE REWRITE
                    // 1589:25: -> delta()
                    {
                        retval.st = templateLib.getInstanceOf("delta");
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1590:16: 'old'
                    {
                    match(input,269,FOLLOW_269_in_other_unary28426); 

                    // TEMPLATE REWRITE
                    // 1590:24: -> old()
                    {
                        retval.st = templateLib.getInstanceOf("old");
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:1591:17: 'not'
                    {
                    match(input,270,FOLLOW_270_in_other_unary28452); 

                    // TEMPLATE REWRITE
                    // 1591:25: -> not()
                    {
                        retval.st = templateLib.getInstanceOf("not");
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
        return retval;
    }
    // $ANTLR end other_unary

    public static class binary_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start binary
    // BONSTTreeWalker.g:1594:1: binary : ( add_sub_op -> asIs(x=$add_sub_op.st) | mul_div_op -> asIs(x=$mul_div_op.st) | comparison_op -> asIs(x=$comparison_op.st) | mod_pow_op -> asIs(x=$mod_pow_op.st) | and_or_xor_op -> asIs(x=$and_or_xor_op.st) | '->' -> implies() | '<->' -> equivalent());
    public final binary_return binary() throws RecognitionException {
        binary_return retval = new binary_return();
        retval.start = input.LT(1);

        add_sub_op_return add_sub_op197 = null;

        mul_div_op_return mul_div_op198 = null;

        comparison_op_return comparison_op199 = null;

        mod_pow_op_return mod_pow_op200 = null;

        and_or_xor_op_return and_or_xor_op201 = null;


        try {
            // BONSTTreeWalker.g:1594:9: ( add_sub_op -> asIs(x=$add_sub_op.st) | mul_div_op -> asIs(x=$mul_div_op.st) | comparison_op -> asIs(x=$comparison_op.st) | mod_pow_op -> asIs(x=$mod_pow_op.st) | and_or_xor_op -> asIs(x=$and_or_xor_op.st) | '->' -> implies() | '<->' -> equivalent())
            int alt170=7;
            switch ( input.LA(1) ) {
            case 263:
            case 264:
                {
                alt170=1;
                }
                break;
            case 277:
            case 278:
            case 280:
                {
                alt170=2;
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
                alt170=3;
                }
                break;
            case MOD_POW_OP:
                {
                alt170=4;
                }
                break;
            case 265:
            case 266:
            case 267:
                {
                alt170=5;
                }
                break;
            case 227:
                {
                alt170=6;
                }
                break;
            case 262:
                {
                alt170=7;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("1594:1: binary : ( add_sub_op -> asIs(x=$add_sub_op.st) | mul_div_op -> asIs(x=$mul_div_op.st) | comparison_op -> asIs(x=$comparison_op.st) | mod_pow_op -> asIs(x=$mod_pow_op.st) | and_or_xor_op -> asIs(x=$and_or_xor_op.st) | '->' -> implies() | '<->' -> equivalent());", 170, 0, input);

                throw nvae;
            }

            switch (alt170) {
                case 1 :
                    // BONSTTreeWalker.g:1594:13: add_sub_op
                    {
                    pushFollow(FOLLOW_add_sub_op_in_binary28500);
                    add_sub_op197=add_sub_op();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1594:28: -> asIs(x=$add_sub_op.st)
                    {
                        retval.st = templateLib.getInstanceOf("asIs",
                      new STAttrMap().put("x", add_sub_op197.st));
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1595:13: mul_div_op
                    {
                    pushFollow(FOLLOW_mul_div_op_in_binary28527);
                    mul_div_op198=mul_div_op();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1595:28: -> asIs(x=$mul_div_op.st)
                    {
                        retval.st = templateLib.getInstanceOf("asIs",
                      new STAttrMap().put("x", mul_div_op198.st));
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:1596:13: comparison_op
                    {
                    pushFollow(FOLLOW_comparison_op_in_binary28554);
                    comparison_op199=comparison_op();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1596:28: -> asIs(x=$comparison_op.st)
                    {
                        retval.st = templateLib.getInstanceOf("asIs",
                      new STAttrMap().put("x", comparison_op199.st));
                    }



                    }
                    break;
                case 4 :
                    // BONSTTreeWalker.g:1597:13: mod_pow_op
                    {
                    pushFollow(FOLLOW_mod_pow_op_in_binary28578);
                    mod_pow_op200=mod_pow_op();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1597:28: -> asIs(x=$mod_pow_op.st)
                    {
                        retval.st = templateLib.getInstanceOf("asIs",
                      new STAttrMap().put("x", mod_pow_op200.st));
                    }



                    }
                    break;
                case 5 :
                    // BONSTTreeWalker.g:1598:13: and_or_xor_op
                    {
                    pushFollow(FOLLOW_and_or_xor_op_in_binary28605);
                    and_or_xor_op201=and_or_xor_op();
                    _fsp--;


                    // TEMPLATE REWRITE
                    // 1598:28: -> asIs(x=$and_or_xor_op.st)
                    {
                        retval.st = templateLib.getInstanceOf("asIs",
                      new STAttrMap().put("x", and_or_xor_op201.st));
                    }



                    }
                    break;
                case 6 :
                    // BONSTTreeWalker.g:1599:13: '->'
                    {
                    match(input,227,FOLLOW_227_in_binary28629); 

                    // TEMPLATE REWRITE
                    // 1599:28: -> implies()
                    {
                        retval.st = templateLib.getInstanceOf("implies");
                    }



                    }
                    break;
                case 7 :
                    // BONSTTreeWalker.g:1600:13: '<->'
                    {
                    match(input,262,FOLLOW_262_in_binary28660); 

                    // TEMPLATE REWRITE
                    // 1600:28: -> equivalent()
                    {
                        retval.st = templateLib.getInstanceOf("equivalent");
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
        return retval;
    }
    // $ANTLR end binary

    public static class comparison_op_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start comparison_op
    // BONSTTreeWalker.g:1603:1: comparison_op : ( '<' -> lessThan() | '>' -> greaterThan() | '<=' -> lessThanOrEqualTo() | '>=' -> greaterThanOrEqualTo() | '=' -> equals() | '/=' -> notEquals() | 'member_of' -> memberOf() | NOT_MEMBER_OF -> notMemberOf() | ':' -> typeChar());
    public final comparison_op_return comparison_op() throws RecognitionException {
        comparison_op_return retval = new comparison_op_return();
        retval.start = input.LT(1);

        try {
            // BONSTTreeWalker.g:1603:16: ( '<' -> lessThan() | '>' -> greaterThan() | '<=' -> lessThanOrEqualTo() | '>=' -> greaterThanOrEqualTo() | '=' -> equals() | '/=' -> notEquals() | 'member_of' -> memberOf() | NOT_MEMBER_OF -> notMemberOf() | ':' -> typeChar())
            int alt171=9;
            switch ( input.LA(1) ) {
            case 271:
                {
                alt171=1;
                }
                break;
            case 272:
                {
                alt171=2;
                }
                break;
            case 273:
                {
                alt171=3;
                }
                break;
            case 274:
                {
                alt171=4;
                }
                break;
            case 275:
                {
                alt171=5;
                }
                break;
            case 276:
                {
                alt171=6;
                }
                break;
            case 246:
                {
                alt171=7;
                }
                break;
            case NOT_MEMBER_OF:
                {
                alt171=8;
                }
                break;
            case 196:
                {
                alt171=9;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("1603:1: comparison_op : ( '<' -> lessThan() | '>' -> greaterThan() | '<=' -> lessThanOrEqualTo() | '>=' -> greaterThanOrEqualTo() | '=' -> equals() | '/=' -> notEquals() | 'member_of' -> memberOf() | NOT_MEMBER_OF -> notMemberOf() | ':' -> typeChar());", 171, 0, input);

                throw nvae;
            }

            switch (alt171) {
                case 1 :
                    // BONSTTreeWalker.g:1603:21: '<'
                    {
                    match(input,271,FOLLOW_271_in_comparison_op28698); 

                    // TEMPLATE REWRITE
                    // 1603:38: -> lessThan()
                    {
                        retval.st = templateLib.getInstanceOf("lessThan");
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1604:21: '>'
                    {
                    match(input,272,FOLLOW_272_in_comparison_op28740); 

                    // TEMPLATE REWRITE
                    // 1604:38: -> greaterThan()
                    {
                        retval.st = templateLib.getInstanceOf("greaterThan");
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:1605:21: '<='
                    {
                    match(input,273,FOLLOW_273_in_comparison_op28781); 

                    // TEMPLATE REWRITE
                    // 1605:38: -> lessThanOrEqualTo()
                    {
                        retval.st = templateLib.getInstanceOf("lessThanOrEqualTo");
                    }



                    }
                    break;
                case 4 :
                    // BONSTTreeWalker.g:1606:21: '>='
                    {
                    match(input,274,FOLLOW_274_in_comparison_op28821); 

                    // TEMPLATE REWRITE
                    // 1606:38: -> greaterThanOrEqualTo()
                    {
                        retval.st = templateLib.getInstanceOf("greaterThanOrEqualTo");
                    }



                    }
                    break;
                case 5 :
                    // BONSTTreeWalker.g:1607:21: '='
                    {
                    match(input,275,FOLLOW_275_in_comparison_op28861); 

                    // TEMPLATE REWRITE
                    // 1607:38: -> equals()
                    {
                        retval.st = templateLib.getInstanceOf("equals");
                    }



                    }
                    break;
                case 6 :
                    // BONSTTreeWalker.g:1608:21: '/='
                    {
                    match(input,276,FOLLOW_276_in_comparison_op28902); 

                    // TEMPLATE REWRITE
                    // 1608:38: -> notEquals()
                    {
                        retval.st = templateLib.getInstanceOf("notEquals");
                    }



                    }
                    break;
                case 7 :
                    // BONSTTreeWalker.g:1609:21: 'member_of'
                    {
                    match(input,246,FOLLOW_246_in_comparison_op28942); 

                    // TEMPLATE REWRITE
                    // 1609:38: -> memberOf()
                    {
                        retval.st = templateLib.getInstanceOf("memberOf");
                    }



                    }
                    break;
                case 8 :
                    // BONSTTreeWalker.g:1610:21: NOT_MEMBER_OF
                    {
                    match(input,NOT_MEMBER_OF,FOLLOW_NOT_MEMBER_OF_in_comparison_op28975); 

                    // TEMPLATE REWRITE
                    // 1610:38: -> notMemberOf()
                    {
                        retval.st = templateLib.getInstanceOf("notMemberOf");
                    }



                    }
                    break;
                case 9 :
                    // BONSTTreeWalker.g:1611:21: ':'
                    {
                    match(input,196,FOLLOW_196_in_comparison_op29006); 

                    // TEMPLATE REWRITE
                    // 1611:38: -> typeChar()
                    {
                        retval.st = templateLib.getInstanceOf("typeChar");
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
        return retval;
    }
    // $ANTLR end comparison_op

    public static class mul_div_op_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start mul_div_op
    // BONSTTreeWalker.g:1615:1: mul_div_op : ( '*' -> multiply() | '/' -> divide() | '//' -> integerDivide());
    public final mul_div_op_return mul_div_op() throws RecognitionException {
        mul_div_op_return retval = new mul_div_op_return();
        retval.start = input.LT(1);

        try {
            // BONSTTreeWalker.g:1615:13: ( '*' -> multiply() | '/' -> divide() | '//' -> integerDivide())
            int alt172=3;
            switch ( input.LA(1) ) {
            case 277:
                {
                alt172=1;
                }
                break;
            case 278:
                {
                alt172=2;
                }
                break;
            case 280:
                {
                alt172=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("1615:1: mul_div_op : ( '*' -> multiply() | '/' -> divide() | '//' -> integerDivide());", 172, 0, input);

                throw nvae;
            }

            switch (alt172) {
                case 1 :
                    // BONSTTreeWalker.g:1615:16: '*'
                    {
                    match(input,277,FOLLOW_277_in_mul_div_op29062); 

                    // TEMPLATE REWRITE
                    // 1615:21: -> multiply()
                    {
                        retval.st = templateLib.getInstanceOf("multiply");
                    }



                    }
                    break;
                case 2 :
                    // BONSTTreeWalker.g:1616:16: '/'
                    {
                    match(input,278,FOLLOW_278_in_mul_div_op29086); 

                    // TEMPLATE REWRITE
                    // 1616:21: -> divide()
                    {
                        retval.st = templateLib.getInstanceOf("divide");
                    }



                    }
                    break;
                case 3 :
                    // BONSTTreeWalker.g:1617:16: '//'
                    {
                    match(input,280,FOLLOW_280_in_mul_div_op29110); 

                    // TEMPLATE REWRITE
                    // 1617:21: -> integerDivide()
                    {
                        retval.st = templateLib.getInstanceOf("integerDivide");
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
        return retval;
    }
    // $ANTLR end mul_div_op

    public static class mod_pow_op_return extends TreeRuleReturnScope {
        public StringTemplate st;
        public Object getTemplate() { return st; }
        public String toString() { return st==null?null:st.toString(); }
    };

    // $ANTLR start mod_pow_op
    // BONSTTreeWalker.g:1620:1: mod_pow_op : MOD_POW_OP -> asIs(x=$MOD_POW_OP.text);
    public final mod_pow_op_return mod_pow_op() throws RecognitionException {
        mod_pow_op_return retval = new mod_pow_op_return();
        retval.start = input.LT(1);

        CommonTree MOD_POW_OP202=null;

        try {
            // BONSTTreeWalker.g:1620:12: ( MOD_POW_OP -> asIs(x=$MOD_POW_OP.text))
            // BONSTTreeWalker.g:1620:14: MOD_POW_OP
            {
            MOD_POW_OP202=(CommonTree)input.LT(1);
            match(input,MOD_POW_OP,FOLLOW_MOD_POW_OP_in_mod_pow_op29137); 

            // TEMPLATE REWRITE
            // 1620:25: -> asIs(x=$MOD_POW_OP.text)
            {
                retval.st = templateLib.getInstanceOf("asIs",
              new STAttrMap().put("x", MOD_POW_OP202.getText()));
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
    // $ANTLR end mod_pow_op


 

    public static final BitSet FOLLOW_PROG_in_prog63 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_bon_specification_in_prog65 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PROG_in_prog99 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_indexing_in_prog101 = new BitSet(new long[]{0x0000004920100160L,0x0000000000000000L,0x0000000000400004L});
    public static final BitSet FOLLOW_bon_specification_in_prog103 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PROG_in_prog141 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_prog143 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_specification_element_in_bon_specification168 = new BitSet(new long[]{0x0000004920100162L,0x0000000000000000L,0x0000000000400004L});
    public static final BitSet FOLLOW_informal_chart_in_specification_element215 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_dictionary_in_specification_element258 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_static_diagram_in_specification_element299 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_dynamic_diagram_in_specification_element342 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_notational_tuning_in_specification_element384 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_system_chart_in_informal_chart433 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cluster_chart_in_informal_chart468 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_class_chart_in_informal_chart502 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_event_chart_in_informal_chart538 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_scenario_chart_in_informal_chart574 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_creation_chart_in_informal_chart607 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CLASS_DICTIONARY_in_class_dictionary668 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_system_name_in_class_dictionary670 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_dictionary_entry_in_class_dictionary699 = new BitSet(new long[]{0x0000000000000088L});
    public static final BitSet FOLLOW_CLASS_DICTIONARY_in_class_dictionary822 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_class_dictionary824 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DICTIONARY_ENTRY_in_dictionary_entry879 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_dictionary_entry881 = new BitSet(new long[]{0x0000000000800000L});
    public static final BitSet FOLLOW_cluster_name_in_dictionary_entry904 = new BitSet(new long[]{0x0000000000001000L});
    public static final BitSet FOLLOW_description_in_dictionary_entry906 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SYSTEM_CHART_in_system_chart1035 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_system_name_in_system_chart1037 = new BitSet(new long[]{0x0000000000002E08L});
    public static final BitSet FOLLOW_indexing_in_system_chart1059 = new BitSet(new long[]{0x0000000000002A08L});
    public static final BitSet FOLLOW_explanation_in_system_chart1083 = new BitSet(new long[]{0x0000000000002808L});
    public static final BitSet FOLLOW_part_in_system_chart1108 = new BitSet(new long[]{0x0000000000002008L});
    public static final BitSet FOLLOW_cluster_entries_in_system_chart1133 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EXPLANATION_in_explanation1241 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_textblock_in_explanation1243 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EXPLANATION_in_explanation1333 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_explanation1335 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDEXING_in_indexing1374 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_index_list_in_indexing1376 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDEXING_in_indexing1452 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_indexing1454 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PART_in_part1486 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_part1488 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PART_in_part1544 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_part1546 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DESCRIPTION_in_description1581 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_textblock_in_description1583 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLUSTER_ENTRIES_in_cluster_entries1686 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cluster_entry_in_cluster_entries1691 = new BitSet(new long[]{0x0000000000004008L});
    public static final BitSet FOLLOW_CLUSTER_ENTRY_in_cluster_entry1825 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_entry1827 = new BitSet(new long[]{0x0000000000001000L});
    public static final BitSet FOLLOW_description_in_cluster_entry1829 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SYSTEM_NAME_in_system_name1952 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_system_name1954 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDEX_LIST_in_index_list2052 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_index_clause_in_index_list2057 = new BitSet(new long[]{0x0000000000020008L});
    public static final BitSet FOLLOW_INDEX_CLAUSE_in_index_clause2164 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_index_clause2166 = new BitSet(new long[]{0x0000000000040000L});
    public static final BitSet FOLLOW_index_term_list_in_index_clause2168 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDEX_CLAUSE_in_index_clause2267 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_index_clause2269 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDEX_TERM_LIST_in_index_term_list2332 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_index_string_in_index_term_list2337 = new BitSet(new long[]{0x0000000000080008L});
    public static final BitSet FOLLOW_INDEX_STRING_in_index_string2469 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_index_string2471 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLUSTER_CHART_in_cluster_chart2576 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_chart2578 = new BitSet(new long[]{0x0000000000202E08L});
    public static final BitSet FOLLOW_indexing_in_cluster_chart2602 = new BitSet(new long[]{0x0000000000202A08L});
    public static final BitSet FOLLOW_explanation_in_cluster_chart2628 = new BitSet(new long[]{0x0000000000202808L});
    public static final BitSet FOLLOW_part_in_cluster_chart2654 = new BitSet(new long[]{0x0000000000202008L});
    public static final BitSet FOLLOW_class_entries_in_cluster_chart2680 = new BitSet(new long[]{0x0000000000002008L});
    public static final BitSet FOLLOW_cluster_entries_in_cluster_chart2706 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLASS_ENTRIES_in_class_entries2834 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_entry_in_class_entries2839 = new BitSet(new long[]{0x0000000000400008L});
    public static final BitSet FOLLOW_CLASS_ENTRY_in_class_entry2962 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_class_entry2964 = new BitSet(new long[]{0x0000000000001000L});
    public static final BitSet FOLLOW_description_in_class_entry2966 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLUSTER_NAME_in_cluster_name3080 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_cluster_name3082 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLASS_CHART_in_class_chart3186 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_class_chart3188 = new BitSet(new long[]{0x0000000000000E08L,0x0000000000000000L,0x0000000780000000L});
    public static final BitSet FOLLOW_indexing_in_class_chart3209 = new BitSet(new long[]{0x0000000000000A08L,0x0000000000000000L,0x0000000780000000L});
    public static final BitSet FOLLOW_explanation_in_class_chart3233 = new BitSet(new long[]{0x0000000000000808L,0x0000000000000000L,0x0000000780000000L});
    public static final BitSet FOLLOW_part_in_class_chart3257 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000780000000L});
    public static final BitSet FOLLOW_inherits_in_class_chart3281 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000700000000L});
    public static final BitSet FOLLOW_queries_in_class_chart3304 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000600000000L});
    public static final BitSet FOLLOW_commands_in_class_chart3328 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000400000000L});
    public static final BitSet FOLLOW_constraints_in_class_chart3352 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INHERITS_in_inherits3438 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_list_in_inherits3440 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INHERITS_in_inherits3480 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_inherits3482 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_QUERIES_in_queries3504 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_query_list_in_queries3506 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_COMMANDS_in_commands3545 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_command_list_in_commands3547 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CONSTRAINTS_in_constraints3578 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_constraint_list_in_constraints3580 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_QUERY_LIST_in_query_list3629 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_textblock_in_query_list3636 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_COMMAND_LIST_in_command_list3746 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_textblock_in_command_list3753 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_CONSTRAINT_LIST_in_constraint_list3876 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_textblock_in_constraint_list3883 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000202000000000L});
    public static final BitSet FOLLOW_CLASS_NAME_LIST_in_class_name_list4004 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_class_name_list4009 = new BitSet(new long[]{0x0000000010000008L});
    public static final BitSet FOLLOW_CLASS_NAME_in_class_name4139 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_class_name4141 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EVENT_CHART_in_event_chart4236 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_system_name_in_event_chart4254 = new BitSet(new long[]{0x0000000040000E08L,0x0000000000000000L,0x0000000000000000L,0x0000000000006000L});
    public static final BitSet FOLLOW_205_in_event_chart4276 = new BitSet(new long[]{0x0000000040000E08L,0x0000000000000000L,0x0000000000000000L,0x0000000000004000L});
    public static final BitSet FOLLOW_206_in_event_chart4283 = new BitSet(new long[]{0x0000000040000E08L});
    public static final BitSet FOLLOW_indexing_in_event_chart4306 = new BitSet(new long[]{0x0000000040000A08L});
    public static final BitSet FOLLOW_explanation_in_event_chart4329 = new BitSet(new long[]{0x0000000040000808L});
    public static final BitSet FOLLOW_part_in_event_chart4352 = new BitSet(new long[]{0x0000000040000008L});
    public static final BitSet FOLLOW_event_entries_in_event_chart4375 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EVENT_ENTRIES_in_event_entries4496 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_event_entry_in_event_entries4519 = new BitSet(new long[]{0x0000000080000008L});
    public static final BitSet FOLLOW_EVENT_ENTRY_in_event_entry4640 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_textblock_in_event_entry4658 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_class_name_list_in_event_entry4676 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EVENT_ENTRY_in_event_entry4769 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_event_entry4771 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SCENARIO_CHART_in_scenario_chart4819 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_system_name_in_scenario_chart4840 = new BitSet(new long[]{0x0000000200000E08L});
    public static final BitSet FOLLOW_indexing_in_scenario_chart4864 = new BitSet(new long[]{0x0000000200000A08L});
    public static final BitSet FOLLOW_explanation_in_scenario_chart4890 = new BitSet(new long[]{0x0000000200000808L});
    public static final BitSet FOLLOW_part_in_scenario_chart4916 = new BitSet(new long[]{0x0000000200000008L});
    public static final BitSet FOLLOW_scenario_entries_in_scenario_chart4942 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SCENARIO_ENTRIES_in_scenario_entries5077 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_scenario_entry_in_scenario_entries5103 = new BitSet(new long[]{0x0000000400000008L});
    public static final BitSet FOLLOW_SCENARIO_ENTRY_in_scenario_entry5265 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_scenario_entry5286 = new BitSet(new long[]{0x0000000000001000L});
    public static final BitSet FOLLOW_description_in_scenario_entry5288 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CREATION_CHART_in_creation_chart5407 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_system_name_in_creation_chart5428 = new BitSet(new long[]{0x0000001000000E08L});
    public static final BitSet FOLLOW_indexing_in_creation_chart5452 = new BitSet(new long[]{0x0000001000000A08L});
    public static final BitSet FOLLOW_explanation_in_creation_chart5478 = new BitSet(new long[]{0x0000001000000808L});
    public static final BitSet FOLLOW_part_in_creation_chart5504 = new BitSet(new long[]{0x0000001000000008L});
    public static final BitSet FOLLOW_creation_entries_in_creation_chart5530 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CREATION_ENTRIES_in_creation_entries5665 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_creation_entry_in_creation_entries5691 = new BitSet(new long[]{0x0000002000000008L});
    public static final BitSet FOLLOW_CREATION_ENTRY_in_creation_entry5830 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_creation_entry5851 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_class_name_list_in_creation_entry5873 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STATIC_DIAGRAM_in_static_diagram5994 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_extended_id_in_static_diagram6018 = new BitSet(new long[]{0x0000010000000008L,0x0000000000000000L,0x0000008000000000L});
    public static final BitSet FOLLOW_COMMENT_in_static_diagram6023 = new BitSet(new long[]{0x0000010000000008L});
    public static final BitSet FOLLOW_static_block_in_static_diagram6051 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EXTENDED_ID_in_extended_id6182 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_extended_id6184 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EXTENDED_ID_in_extended_id6290 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_INTEGER_in_extended_id6292 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STATIC_BLOCK_in_static_block6402 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_static_component_in_static_block6407 = new BitSet(new long[]{0x0000020000000008L});
    public static final BitSet FOLLOW_STATIC_COMPONENT_in_static_component6517 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cluster_in_static_component6519 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STATIC_COMPONENT_in_static_component6661 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_classX_in_static_component6663 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STATIC_COMPONENT_in_static_component6805 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_static_relation_in_static_component6807 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLUSTER_in_cluster6925 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cluster_name_in_cluster6927 = new BitSet(new long[]{0x0000080000000008L,0x0000000000000000L,0x0000008000000000L,0x0000000001000000L});
    public static final BitSet FOLLOW_216_in_cluster6944 = new BitSet(new long[]{0x0000080000000008L,0x0000000000000000L,0x0000008000000000L});
    public static final BitSet FOLLOW_COMMENT_in_cluster6949 = new BitSet(new long[]{0x0000080000000008L});
    public static final BitSet FOLLOW_cluster_components_in_cluster6969 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLUSTER_COMPONENTS_in_cluster_components7075 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_static_block_in_cluster_components7080 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLASS_in_classX7222 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_217_in_classX7238 = new BitSet(new long[]{0x0000000010000000L,0x0000000000000000L,0x0000000000000000L,0x000000000C000000L});
    public static final BitSet FOLLOW_218_in_classX7245 = new BitSet(new long[]{0x0000000010000000L,0x0000000000000000L,0x0000000000000000L,0x0000000008000000L});
    public static final BitSet FOLLOW_219_in_classX7252 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_class_name_in_classX7268 = new BitSet(new long[]{0x0000000000000008L,0x0000000040000080L,0x0000008000000000L,0x0000000031000000L});
    public static final BitSet FOLLOW_formal_generics_in_classX7273 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000080L,0x0000008000000000L,0x0000000031000000L});
    public static final BitSet FOLLOW_216_in_classX7291 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000080L,0x0000008000000000L,0x0000000030000000L});
    public static final BitSet FOLLOW_220_in_classX7298 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000080L,0x0000008000000000L,0x0000000020000000L});
    public static final BitSet FOLLOW_221_in_classX7306 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000080L,0x0000008000000000L});
    public static final BitSet FOLLOW_COMMENT_in_classX7311 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000080L});
    public static final BitSet FOLLOW_class_interface_in_classX7329 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STATIC_RELATION_in_static_relation7441 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_inheritance_relation_in_static_relation7443 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STATIC_RELATION_in_static_relation7553 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_client_relation_in_static_relation7555 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INHERITENCE_RELATION_in_inheritance_relation7659 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_child_in_inheritance_relation7686 = new BitSet(new long[]{0x8000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_multiplicity_in_inheritance_relation7691 = new BitSet(new long[]{0x8000000000000000L});
    public static final BitSet FOLLOW_parent_in_inheritance_relation7721 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000040L});
    public static final BitSet FOLLOW_semantic_label_in_inheritance_relation7726 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_RELATION_in_client_relation7897 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_client_in_client_relation7919 = new BitSet(new long[]{0x1001000000000000L,0x0000000000000002L});
    public static final BitSet FOLLOW_client_entities_in_client_relation7924 = new BitSet(new long[]{0x1000000000000000L,0x0000000000000002L});
    public static final BitSet FOLLOW_type_mark_in_client_relation7931 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000002L});
    public static final BitSet FOLLOW_supplier_in_client_relation7956 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000040L});
    public static final BitSet FOLLOW_semantic_label_in_client_relation7961 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_ENTITIES_in_client_entities8113 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_client_entity_expression_in_client_entities8135 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_ENTITY_EXPRESSION_in_client_entity_expression8277 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_client_entity_list_in_client_entity_expression8279 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_ENTITY_EXPRESSION_in_client_entity_expression8463 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_multiplicity_in_client_entity_expression8465 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_ENTITY_LIST_in_client_entity_list8646 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_client_entity_in_client_entity_list8651 = new BitSet(new long[]{0x0010000000000008L});
    public static final BitSet FOLLOW_CLIENT_ENTITY_in_client_entity8803 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_prefix_in_client_entity8805 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_ENTITY_in_client_entity8936 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_infix_in_client_entity8938 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_ENTITY_in_client_entity9069 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_supplier_indirection_in_client_entity9071 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_ENTITY_in_client_entity9202 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_parent_indirection_in_client_entity9204 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SUPPLIER_INDIRECTION_in_supplier_indirection9338 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_indirection_feature_part_in_supplier_indirection9343 = new BitSet(new long[]{0x0200000000000000L});
    public static final BitSet FOLLOW_generic_indirection_in_supplier_indirection9347 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDIRECTION_FEATURE_PART_in_indirection_feature_part9519 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_feature_name_in_indirection_feature_part9521 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDIRECTION_FEATURE_PART_in_indirection_feature_part9705 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_indirection_feature_list_in_indirection_feature_part9707 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDIRECTION_FEATURE_LIST_in_indirection_feature_list9895 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_feature_name_list_in_indirection_feature_list9897 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PARENT_INDIRECTION_in_parent_indirection10078 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_generic_indirection_in_parent_indirection10080 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_GENERIC_INDIRECTION_in_generic_indirection10244 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_indirection_element_in_generic_indirection10246 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_NAMED_INDIRECTION_in_named_indirection10401 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_named_indirection10403 = new BitSet(new long[]{0x0800000000000000L});
    public static final BitSet FOLLOW_indirection_list_in_named_indirection10405 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_NAMED_INDIRECTION_in_named_indirection10529 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_named_indirection10531 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDIRECTION_LIST_in_indirection_list10602 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_indirection_element_in_indirection_list10607 = new BitSet(new long[]{0x0002000000000008L});
    public static final BitSet FOLLOW_INDIRECTION_ELEMENT_in_indirection_element10753 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_230_in_indirection_element10757 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDIRECTION_ELEMENT_in_indirection_element10917 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_named_indirection_in_indirection_element10919 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INDIRECTION_ELEMENT_in_indirection_element11079 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_indirection_element11081 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_TYPE_MARK_in_type_mark11232 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_196_in_type_mark11236 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_TYPE_MARK_in_type_mark11330 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_231_in_type_mark11334 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_TYPE_MARK_in_type_mark11429 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_shared_mark_in_type_mark11431 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SHARED_MARK_in_shared_mark11530 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_multiplicity_in_shared_mark11532 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CHILD_in_child11625 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_static_ref_in_child11627 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PARENT_in_parent11701 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_static_ref_in_parent11703 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLIENT_in_client11782 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_static_ref_in_client11784 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SUPPLIER_in_supplier11865 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_static_ref_in_supplier11867 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STATIC_REF_in_static_ref11960 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cluster_prefix_in_static_ref11965 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
    public static final BitSet FOLLOW_static_component_name_in_static_ref11969 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLUSTER_PREFIX_in_cluster_prefix12080 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cluster_name_in_cluster_prefix12085 = new BitSet(new long[]{0x0000000000800008L});
    public static final BitSet FOLLOW_STATIC_COMPONENT_NAME_in_static_component_name12207 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_static_component_name12209 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MULTIPLICITY_in_multiplicity12369 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_INTEGER_in_multiplicity12371 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SEMANTIC_LABEL_in_semantic_label12488 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_semantic_label12490 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLASS_INTERFACE_in_class_interface12605 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_indexing_in_class_interface12630 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000600L});
    public static final BitSet FOLLOW_parent_class_list_in_class_interface12657 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000400L});
    public static final BitSet FOLLOW_features_in_class_interface12681 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000100L});
    public static final BitSet FOLLOW_class_invariant_in_class_interface12706 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLASS_INVARIANT_in_class_invariant12852 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_assertion_in_class_invariant12854 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PARENT_CLASS_LIST_in_parent_class_list12989 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_type_in_parent_class_list12994 = new BitSet(new long[]{0x0000000000000008L,0x0000000400000000L});
    public static final BitSet FOLLOW_PARENT_CLASS_LIST_in_parent_class_list13115 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_PARSE_ERROR_in_parent_class_list13117 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FEATURES_in_features13181 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_feature_clause_in_features13186 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000800L});
    public static final BitSet FOLLOW_FEATURE_CLAUSE_in_feature_clause13288 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_selective_export_in_feature_clause13312 = new BitSet(new long[]{0x0000000000000000L,0x0000000000001000L,0x0000008000000000L});
    public static final BitSet FOLLOW_COMMENT_in_feature_clause13337 = new BitSet(new long[]{0x0000000000000000L,0x0000000000001000L});
    public static final BitSet FOLLOW_feature_specifications_in_feature_clause13361 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FEATURE_SPECIFICATIONS_in_feature_specifications13501 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_feature_specification_in_feature_specifications13533 = new BitSet(new long[]{0x0000000000000008L,0x0000000000002000L});
    public static final BitSet FOLLOW_FEATURE_SPECIFICATION_in_feature_specification13710 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_218_in_feature_specification13741 = new BitSet(new long[]{0x0000000000000000L,0x0000000000080000L,0x0000000000000000L,0x0000080008000000L});
    public static final BitSet FOLLOW_219_in_feature_specification13748 = new BitSet(new long[]{0x0000000000000000L,0x0000000000080000L,0x0000000000000000L,0x0000080000000000L});
    public static final BitSet FOLLOW_235_in_feature_specification13755 = new BitSet(new long[]{0x0000000000000000L,0x0000000000080000L});
    public static final BitSet FOLLOW_feature_name_list_in_feature_specification13785 = new BitSet(new long[]{0x0000000000000008L,0x0000000000A04000L,0x0000008800000000L});
    public static final BitSet FOLLOW_has_type_in_feature_specification13790 = new BitSet(new long[]{0x0000000000000008L,0x0000000000A04000L,0x0000008000000000L});
    public static final BitSet FOLLOW_rename_clause_in_feature_specification13823 = new BitSet(new long[]{0x0000000000000008L,0x0000000000804000L,0x0000008000000000L});
    public static final BitSet FOLLOW_COMMENT_in_feature_specification13854 = new BitSet(new long[]{0x0000000000000008L,0x0000000000804000L});
    public static final BitSet FOLLOW_feature_arguments_in_feature_specification13887 = new BitSet(new long[]{0x0000000000000008L,0x0000000000004000L});
    public static final BitSet FOLLOW_contract_clause_in_feature_specification13920 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_HAS_TYPE_in_has_type14055 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_type_mark_in_has_type14057 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_type_in_has_type14059 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CONTRACT_CLAUSE_in_contract_clause14143 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_contracting_conditions_in_contract_clause14145 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CONTRACTING_CONDITIONS_in_contracting_conditions14282 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_precondition_in_contracting_conditions14287 = new BitSet(new long[]{0x0000000000000008L,0x0000000000020000L});
    public static final BitSet FOLLOW_postcondition_in_contracting_conditions14294 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PRECONDITION_in_precondition14446 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_assertion_in_precondition14448 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_POSTCONDITION_in_postcondition14564 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_assertion_in_postcondition14566 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SELECTIVE_EXPORT_in_selective_export14678 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_list_in_selective_export14680 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FEATURE_NAME_LIST_in_feature_name_list14820 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_feature_name_in_feature_name_list14825 = new BitSet(new long[]{0x0000000000000008L,0x0000000000100000L});
    public static final BitSet FOLLOW_FEATURE_NAME_in_feature_name14967 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_feature_name14969 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FEATURE_NAME_in_feature_name15082 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_prefix_in_feature_name15084 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FEATURE_NAME_in_feature_name15197 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_infix_in_feature_name15199 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_RENAME_CLAUSE_in_rename_clause15315 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_renaming_in_rename_clause15317 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_RENAMING_in_renaming15433 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_renaming15435 = new BitSet(new long[]{0x0000000000000000L,0x0000000000100000L});
    public static final BitSet FOLLOW_feature_name_in_renaming15437 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FEATURE_ARGUMENTS_in_feature_arguments15541 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_feature_argument_in_feature_arguments15546 = new BitSet(new long[]{0x0000000000000008L,0x0000000001000000L});
    public static final BitSet FOLLOW_FEATURE_ARGUMENT_in_feature_argument15693 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_identifier_list_in_feature_argument15698 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_type_in_feature_argument15702 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_IDENTIFIER_LIST_in_identifier_list15844 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_identifier_list15849 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000004000000000L});
    public static final BitSet FOLLOW_PREFIX_in_prefix15972 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_prefix_operator_in_prefix15974 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INFIX_in_infix16053 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_infix_operator_in_infix16055 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PREFIX_OPERATOR_in_prefix_operator16138 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_unary_in_prefix_operator16140 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INFIX_OPERATOR_in_infix_operator16271 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_binary_in_infix_operator16273 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FORMAL_GENERICS_in_formal_generics16388 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_formal_generic_list_in_formal_generics16390 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FORMAL_GENERIC_LIST_in_formal_generic_list16527 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_formal_generic_in_formal_generic_list16532 = new BitSet(new long[]{0x0000000000000008L,0x0000000100000000L});
    public static final BitSet FOLLOW_FORMAL_GENERIC_in_formal_generic16686 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_formal_generic_name_in_formal_generic16688 = new BitSet(new long[]{0x0000000000000008L,0x0000000400000000L});
    public static final BitSet FOLLOW_class_type_in_formal_generic16693 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_FORMAL_GENERIC_NAME_in_formal_generic_name16831 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_formal_generic_name16833 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CLASS_TYPE_in_class_type16981 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_class_type16983 = new BitSet(new long[]{0x0000000000000008L,0x0000000800000000L});
    public static final BitSet FOLLOW_actual_generics_in_class_type16988 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_ACTUAL_GENERICS_in_actual_generics17103 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_type_list_in_actual_generics17105 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_TYPE_LIST_in_type_list17233 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_type_in_type_list17238 = new BitSet(new long[]{0x0000000000000008L,0x0000002000000000L});
    public static final BitSet FOLLOW_TYPE_in_type17321 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_type17323 = new BitSet(new long[]{0x0000000000000008L,0x0000000800000000L});
    public static final BitSet FOLLOW_actual_generics_in_type17328 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_ASSERTION_in_assertion17403 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_assertion_clause_in_assertion17408 = new BitSet(new long[]{0x0000000000000008L,0x0000008000000000L});
    public static final BitSet FOLLOW_ASSERTION_CLAUSE_in_assertion_clause17514 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_boolean_expression_in_assertion_clause17516 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_BOOLEAN_EXPRESSION_in_boolean_expression17656 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_expression_in_boolean_expression17658 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_QUANTIFICATION_in_quantification17797 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_quantifier_in_quantification17818 = new BitSet(new long[]{0x0000000000000000L,0x0000080000000000L});
    public static final BitSet FOLLOW_range_expression_in_quantification17841 = new BitSet(new long[]{0x0000000000000000L,0x0000300000000000L});
    public static final BitSet FOLLOW_restriction_in_quantification17866 = new BitSet(new long[]{0x0000000000000000L,0x0000200000000000L});
    public static final BitSet FOLLOW_proposition_in_quantification17890 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_QUANTIFIER_in_quantifier18026 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_242_in_quantifier18030 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_QUANTIFIER_in_quantifier18130 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_243_in_quantifier18134 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_RANGE_EXPRESSION_in_range_expression18243 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_variable_range_in_range_expression18248 = new BitSet(new long[]{0x0000000000000008L,0x0000400000000000L});
    public static final BitSet FOLLOW_RESTRICTION_in_restriction18384 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_boolean_expression_in_restriction18386 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_PROPOSITION_in_proposition18496 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_boolean_expression_in_proposition18498 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_VARIABLE_RANGE_in_variable_range18610 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_member_range_in_variable_range18612 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_VARIABLE_RANGE_in_variable_range18736 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_type_range_in_variable_range18738 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MEMBER_RANGE_in_member_range18863 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_identifier_list_in_member_range18865 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000020000000L});
    public static final BitSet FOLLOW_expression_in_member_range18867 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_TYPE_RANGE_in_type_range18984 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_identifier_list_in_type_range18986 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_type_in_type_range18988 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CALL_CHAIN_in_call_chain19119 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_unqualified_call_in_call_chain19124 = new BitSet(new long[]{0x0000000000000008L,0x0008000000000000L});
    public static final BitSet FOLLOW_UNQUALIFIED_CALL_in_unqualified_call19235 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_unqualified_call19237 = new BitSet(new long[]{0x0000000000000008L,0x0010000000000000L});
    public static final BitSet FOLLOW_actual_arguments_in_unqualified_call19242 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_ACTUAL_ARGUMENTS_in_actual_arguments19366 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ACTUAL_ARGUMENTS_in_actual_arguments19480 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_expression_list_in_actual_arguments19482 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EXPRESSION_LIST_in_expression_list19617 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_expression_in_expression_list19622 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000020000000L});
    public static final BitSet FOLLOW_ENUMERATED_SET_in_enumerated_set19758 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_enumeration_list_in_enumerated_set19760 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_ENUMERATION_LIST_in_enumeration_list19889 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_enumeration_element_in_enumeration_list19894 = new BitSet(new long[]{0x0000000000000008L,0x0100000000000000L});
    public static final BitSet FOLLOW_ENUMERATION_ELEMENT_in_enumeration_element20029 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_expression_in_enumeration_element20031 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_ENUMERATION_ELEMENT_in_enumeration_element20186 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_interval_in_enumeration_element20188 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INTERVAL_in_interval20334 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_integer_interval_in_interval20336 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INTERVAL_in_interval20426 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_character_interval_in_interval20428 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INTEGER_INTERVAL_in_integer_interval20528 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_integer_constant_in_integer_interval20532 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000001L});
    public static final BitSet FOLLOW_integer_constant_in_integer_interval20536 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CHARACTER_INTERVAL_in_character_interval20681 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_CHARACTER_CONSTANT_in_character_interval20685 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000020000000000L});
    public static final BitSet FOLLOW_CHARACTER_CONSTANT_in_character_interval20689 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CONSTANT_in_constant20817 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_constant_in_constant20819 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CONSTANT_in_constant20907 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_248_in_constant20911 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CONSTANT_in_constant20999 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_249_in_constant21003 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MANIFEST_CONSTANT_in_manifest_constant21095 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_boolean_constant_in_manifest_constant21097 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MANIFEST_CONSTANT_in_manifest_constant21246 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_CHARACTER_CONSTANT_in_manifest_constant21248 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MANIFEST_CONSTANT_in_manifest_constant21397 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_integer_constant_in_manifest_constant21399 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MANIFEST_CONSTANT_in_manifest_constant21548 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_real_constant_in_manifest_constant21550 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MANIFEST_CONSTANT_in_manifest_constant21699 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_manifest_constant21701 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MANIFEST_CONSTANT_in_manifest_constant21850 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_enumerated_set_in_manifest_constant21852 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SIGN_in_sign21987 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_add_sub_op_in_sign21989 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_BOOLEAN_CONSTANT_in_boolean_constant22068 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_250_in_boolean_constant22072 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_BOOLEAN_CONSTANT_in_boolean_constant22208 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_251_in_boolean_constant22212 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_INTEGER_CONSTANT_in_integer_constant22353 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_sign_in_integer_constant22379 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_INTEGER_in_integer_constant22383 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_REAL_CONSTANT_in_real_constant22523 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_sign_in_real_constant22546 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000040000000000L});
    public static final BitSet FOLLOW_REAL_in_real_constant22550 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DYNAMIC_DIAGRAM_in_dynamic_diagram22665 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_diagram22690 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000008000000008L});
    public static final BitSet FOLLOW_COMMENT_in_dynamic_diagram22695 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_dynamic_block_in_dynamic_diagram22722 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DYNAMIC_BLOCK_in_dynamic_block22859 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_dynamic_component_in_dynamic_block22882 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000000000010L});
    public static final BitSet FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component23011 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_scenario_description_in_dynamic_component23013 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component23161 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_object_group_in_dynamic_component23163 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component23311 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_object_stack_in_dynamic_component23313 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component23462 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_object_in_dynamic_component23464 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DYNAMIC_COMPONENT_in_dynamic_component23613 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_message_relation_in_dynamic_component23615 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SCENARIO_DESCRIPTION_in_scenario_description23751 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_scenario_name_in_scenario_description23779 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000008000000040L});
    public static final BitSet FOLLOW_COMMENT_in_scenario_description23782 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000040L});
    public static final BitSet FOLLOW_labelled_actions_in_scenario_description23811 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_LABELLED_ACTIONS_in_labelled_actions23975 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_labelled_action_in_labelled_actions23980 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000000000080L});
    public static final BitSet FOLLOW_LABELLED_ACTION_in_labelled_action24120 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_action_label_in_labelled_action24122 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000200L});
    public static final BitSet FOLLOW_action_description_in_labelled_action24124 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_ACTION_LABEL_in_action_label24258 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_action_label24260 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_ACTION_DESCRIPTION_in_action_description24381 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_textblock_in_action_description24383 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_SCENARIO_NAME_in_scenario_name24529 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_manifest_textblock_in_scenario_name24531 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_OBJECT_GROUP_in_object_group24639 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_254_in_object_group24644 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000100000L});
    public static final BitSet FOLLOW_group_name_in_object_group24648 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000008000001000L});
    public static final BitSet FOLLOW_COMMENT_in_object_group24651 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000000001000L});
    public static final BitSet FOLLOW_group_components_in_object_group24658 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_GROUP_COMPONENTS_in_group_components24788 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_dynamic_block_in_group_components24790 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_OBJECT_STACK_in_object_stack24926 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_object_name_in_object_stack24928 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000008000000000L});
    public static final BitSet FOLLOW_COMMENT_in_object_stack24931 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_OBJECT_in_object25042 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_object_name_in_object25044 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000008000000000L});
    public static final BitSet FOLLOW_COMMENT_in_object25047 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MESSAGE_RELATION_in_message_relation25133 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_caller_in_message_relation25135 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000010000L});
    public static final BitSet FOLLOW_receiver_in_message_relation25137 = new BitSet(new long[]{0x0000000000000008L,0x0000000000000000L,0x0000000000200000L});
    public static final BitSet FOLLOW_message_label_in_message_relation25142 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_RECEIVER_in_caller25281 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_dynamic_ref_in_caller25283 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_RECEIVER_in_receiver25364 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_dynamic_ref_in_receiver25366 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DYNAMIC_REF_in_dynamic_ref25460 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_ref25465 = new BitSet(new long[]{0x0000008000000008L});
    public static final BitSet FOLLOW_DYNAMIC_COMPONENT_NAME_in_dynamic_component_name25574 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_IDENTIFIER_in_dynamic_component_name25576 = new BitSet(new long[]{0x0000008000000008L});
    public static final BitSet FOLLOW_extended_id_in_dynamic_component_name25581 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_DYNAMIC_COMPONENT_NAME_in_dynamic_component_name25759 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_INTEGER_in_dynamic_component_name25761 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_OBJECT_NAME_in_object_name25901 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_class_name_in_object_name25903 = new BitSet(new long[]{0x0000008000000008L});
    public static final BitSet FOLLOW_extended_id_in_object_name25908 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_GROUP_NAME_in_group_name26022 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_extended_id_in_group_name26024 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_MESSAGE_LABEL_in_message_label26131 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_message_label26133 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_NOTATIONAL_TUNING_in_notational_tuning26245 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_change_string_marks_in_notational_tuning26247 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_NOTATIONAL_TUNING_in_notational_tuning26389 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_change_concatenator_in_notational_tuning26391 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_NOTATIONAL_TUNING_in_notational_tuning26534 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_change_prefix_in_notational_tuning26536 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CHANGE_STRING_MARKS_in_change_string_marks26683 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_string_marks26687 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000002000000000L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_string_marks26691 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CHANGE_CONCATENATOR_in_change_concatenator26852 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_concatenator26854 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CHANGE_PREFIX_in_change_prefix27005 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_change_prefix27007 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EXPRESSION_in_expression27117 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_equivalence_expression_in_expression27119 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_EXPRESSION_in_expression27220 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_quantification_in_expression27222 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_262_in_equivalence_expression27300 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_equivalence_expression_in_equivalence_expression27304 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000080040000000L,0x0040000A00000010L,0x00000000017FFFC0L});
    public static final BitSet FOLLOW_equivalence_expression_in_equivalence_expression27308 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_implies_expression_in_equivalence_expression27339 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_227_in_implies_expression27385 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_implies_expression_in_implies_expression27389 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000080040000000L,0x0040000A00000010L,0x00000000017FFF80L});
    public static final BitSet FOLLOW_implies_expression_in_implies_expression27393 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_and_or_xor_expression_in_implies_expression27433 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_and_or_xor_op_in_and_or_xor_expression27474 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_and_or_xor_expression_in_and_or_xor_expression27478 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000080040000000L,0x0040000200000010L,0x00000000017FFF80L});
    public static final BitSet FOLLOW_and_or_xor_expression_in_and_or_xor_expression27482 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_comparison_expression_in_and_or_xor_expression27517 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_comparison_op_in_comparison_expression27561 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_comparison_expression_in_comparison_expression27566 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000080040000000L,0x0040000200000010L,0x00000000017FF180L});
    public static final BitSet FOLLOW_comparison_expression_in_comparison_expression27570 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_add_sub_expression_in_comparison_expression27605 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_in_add_sub_expression27649 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_add_sub_expression_in_add_sub_expression27653 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000080000000000L,0x0000000200000000L,0x0000000001607180L});
    public static final BitSet FOLLOW_add_sub_expression_in_add_sub_expression27657 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_mul_div_expression_in_add_sub_expression27690 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_mul_div_op_in_mul_div_expression27731 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_mul_div_expression_in_mul_div_expression27735 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000080000000000L,0x0000000200000000L,0x0000000001607180L});
    public static final BitSet FOLLOW_mul_div_expression_in_mul_div_expression27739 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mul_div_expression27772 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_mod_pow_op_in_mod_pow_expression27814 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mod_pow_expression27818 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000080000000000L,0x0000000200000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_mod_pow_expression_in_mod_pow_expression27822 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_lowest_expression_in_mod_pow_expression27865 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_constant_in_lowest_expression27905 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unary_in_lowest_expression27928 = new BitSet(new long[]{0x0000000000000000L,0x1004000000000000L,0x0000000000000000L,0x0000000200000000L,0x0000000000007180L});
    public static final BitSet FOLLOW_lowest_expression_in_lowest_expression27932 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_225_in_lowest_expression27964 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000020000000L});
    public static final BitSet FOLLOW_expression_in_lowest_expression27966 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000400000000L});
    public static final BitSet FOLLOW_226_in_lowest_expression27968 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000010000000000L});
    public static final BitSet FOLLOW_232_in_lowest_expression27971 = new BitSet(new long[]{0x0000000000000000L,0x0004000000000000L});
    public static final BitSet FOLLOW_call_chain_in_lowest_expression27975 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_call_chain_in_lowest_expression28009 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_STRING_in_manifest_textblock28049 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_START_in_manifest_textblock28075 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000C00000000000L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_MIDDLE_in_manifest_textblock28108 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000C00000000000L});
    public static final BitSet FOLLOW_MANIFEST_TEXTBLOCK_END_in_manifest_textblock28129 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_263_in_add_sub_op28212 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_264_in_add_sub_op28235 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_265_in_and_or_xor_op28264 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_266_in_and_or_xor_op28290 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_267_in_and_or_xor_op28317 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_other_unary_in_unary28352 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_in_unary28375 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_268_in_other_unary28403 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_269_in_other_unary28426 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_270_in_other_unary28452 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_add_sub_op_in_binary28500 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_mul_div_op_in_binary28527 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_comparison_op_in_binary28554 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_mod_pow_op_in_binary28578 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_and_or_xor_op_in_binary28605 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_227_in_binary28629 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_262_in_binary28660 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_271_in_comparison_op28698 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_272_in_comparison_op28740 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_273_in_comparison_op28781 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_274_in_comparison_op28821 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_275_in_comparison_op28861 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_276_in_comparison_op28902 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_246_in_comparison_op28942 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_NOT_MEMBER_OF_in_comparison_op28975 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_196_in_comparison_op29006 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_277_in_mul_div_op29062 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_278_in_mul_div_op29086 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_280_in_mul_div_op29110 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_MOD_POW_OP_in_mod_pow_op29137 = new BitSet(new long[]{0x0000000000000002L});

}