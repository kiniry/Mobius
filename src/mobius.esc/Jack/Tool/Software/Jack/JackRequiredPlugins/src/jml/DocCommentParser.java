// $ANTLR 2.7.1: "doccommentparser.g" -> "DocCommentParser.java"$

// @(#)$Id: doccommentparser.g,v 1.12 2001/08/02 18:36:20 leavens Exp $

// Copyright (C) 1998, 1999 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.


//
// Java Documentation Comment (body) parser
//
// AUTHORS: Gary T. Leavens, Arun Raghavan, Sevtap Karakoy, and Clyde Ruby

package jml;

import java.io.ByteArrayInputStream;
import java.io.File;

import antlr.ASTFactory;
import antlr.ASTPair;
import antlr.NoViableAltException;
import antlr.ParserSharedInputState;
import antlr.RecognitionException;
import antlr.Token;
import antlr.TokenBuffer;
import antlr.TokenStream;
import antlr.TokenStreamException;
import antlr.collections.AST;
import antlr.collections.impl.ASTArray;
import antlr.collections.impl.BitSet;
//import edu.iastate.cs.jml.checker.util.Debug;

public class DocCommentParser extends antlr.LLkParser
       implements DocCommentParserTokenTypes
 {

    // an initializer, to set the tree type
    {
    	if(getASTFactory() == null) {
    		setASTFactory(new ASTFactory());
    	}
        setASTNodeClass("jml.LineAST");
    }
    
    /* package protected */
    File currentFile = null;
    
    static int returnCode = 0;
    
    static int errors = 0;
    static int warnings = 0;
    
    //boolean debugOn = true;
    boolean debugOn = false;
    
    /** Parser error-reporting function can be overridden in subclass */
    public void reportError(RecognitionException ex) {
        errors++;
        try {
            System.err.println(currentFile.getPath() + ":" 
                + LT(1).getLine() + ": " + ex.toString());
        } catch (TokenStreamException tse) {
            System.err.println("TokenStreamException: " + tse.getMessage());
        }
    }
    
    public void reportError(TokenStreamException ex)
    {
        errors++;
        try{
            System.err.println(currentFile.getPath() + ":" 
                + LT(1).getLine() + ": " + ex.toString());
        } catch( TokenStreamException tse) {
            System.err.println("TokenStreamException: " + tse.getMessage());
        }
    }

protected DocCommentParser(TokenBuffer tokenBuf, int k) {
  super(tokenBuf,k);
  tokenNames = _tokenNames;
}

public DocCommentParser(TokenBuffer tokenBuf) {
  this(tokenBuf,1);
}

protected DocCommentParser(TokenStream lexer, int k) {
  super(lexer,k);
  tokenNames = _tokenNames;
}

public DocCommentParser(TokenStream lexer) {
  this(lexer,1);
}

public DocCommentParser(ParserSharedInputState state) {
  super(state,1);
  tokenNames = _tokenNames;
}

	public final void documentationCommentBody() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST documentationCommentBody_AST = null;
		try {      // for error handling
			{
			_loop3:
			do {
				if ((LA(1)==DOC_NON_EMPTY_TEXTLINE)) {
					description();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop3;
				}
				
			} while (true);
			}
			{
			_loop5:
			do {
				if ((_tokenSet_0.member(LA(1)))) {
					taggedParagraph();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop5;
				}
				
			} while (true);
			}
			{
			switch ( LA(1)) {
			case DOC_PRE_JML:
			{
				jml_specs();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case EOF:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			astFactory.create(LT(1));
			match(Token.EOF_TYPE);
			documentationCommentBody_AST = (AST)currentAST.root;
		}
		catch (RecognitionException e) {
			
			System.err.println(currentFile.getPath() + ":" 
			+ LT(1).getLine() + ": " + e.toString());
			
		}
		catch (TokenStreamException err) {
			
			
			System.err.println(currentFile.getPath() + ":" + LT(1).getLine() + ": Error in Documentation Comment");
			
		}
		returnAST = documentationCommentBody_AST;
	}
	
	public final void description() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST description_AST = null;
		Token  dc = null;
		AST dc_AST = null;
		
		//LB    Debug.msg(debugOn, "entering description ");
		
		
		try {      // for error handling
			dc = LT(1);
			dc_AST = (AST)astFactory.create(dc);
			astFactory.addASTChild(currentAST, dc_AST);
			match(DOC_NON_EMPTY_TEXTLINE);
			description_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_1);
		}
		returnAST = description_AST;
	}
	
	public final void taggedParagraph() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST taggedParagraph_AST = null;
		
		//LB Debug.msg(debugOn, "entering tagged paragraph ");
		
		
		try {      // for error handling
			paragraph_tag();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop10:
			do {
				if ((LA(1)==DOC_ATSIGN)) {
					AST tmp2_AST = null;
					tmp2_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp2_AST);
					match(DOC_ATSIGN);
				}
				else {
					break _loop10;
				}
				
			} while (true);
			}
			{
			_loop12:
			do {
				if ((LA(1)==DOC_NON_EMPTY_TEXTLINE)) {
					description();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop12;
				}
				
			} while (true);
			}
			taggedParagraph_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_2);
		}
		returnAST = taggedParagraph_AST;
	}
	
	public final void jml_specs() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST jml_specs_AST = null;
		Token  pjtok = null;
		AST pjtok_AST = null;
		AST d_AST = null;
		Token  jptok = null;
		AST jptok_AST = null;
		
		String r = "";
		//LB Debug.msg(debugOn, "entering jml_spec ");
		
		
		try {      // for error handling
			{
			int _cnt18=0;
			_loop18:
			do {
				if ((LA(1)==DOC_PRE_JML)) {
					pjtok = LT(1);
					pjtok_AST = (AST)astFactory.create(pjtok);
					astFactory.addASTChild(currentAST, pjtok_AST);
					match(DOC_PRE_JML);
					{
					_loop17:
					do {
						if ((LA(1)==DOC_NON_EMPTY_TEXTLINE)) {
							description();
							d_AST = (AST)returnAST;
							astFactory.addASTChild(currentAST, returnAST);
							
							r = r + "\n" + d_AST.getText(); // add NON_NL_WS       
							
						}
						else {
							break _loop17;
						}
						
					} while (true);
					}
					jptok = LT(1);
					jptok_AST = (AST)astFactory.create(jptok);
					astFactory.addASTChild(currentAST, jptok_AST);
					match(DOC_JML_PRE);
					
					if (!pjtok.getText()
					.regionMatches(true,6,jptok.getText(),2,3)) {
					// <JML> ended by </ESC> or vice versa
					reportWarning(pjtok.getText() + " ended by "
					+ jptok.getText());
					}
					
				}
				else {
					if ( _cnt18>=1 ) { break _loop18; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt18++;
			} while (true);
			}
			jml_specs_AST = (AST)currentAST.root;
			
			r = r + "\n void"; // add " void" to end the specification
			//LB Debug.msg(debugOn, "Parsing: ", r);
			
			JmlLexer lexer = new JmlLexer(
			new ByteArrayInputStream(r.getBytes()));
			lexer.setTokenObjectClass("jml.LineToken");
			JmlParser jp = new JmlParser(lexer);
			jp.lexer = lexer;
			lexer.setLine(LT(1).getLine() - (jp.countlines(r) + 2));
			lexer.JML_reading_JML_file = true;
			jp.JML_reading_JML_file = true;
			jp.warnings = 0;
			jp.currentFile = currentFile;
			jp.setASTNodeClass("jml.LineAST");
			LineAST mods = null;
			jp.errors = 0;
			jp.modifiers();
			errors += jp.errors;    
			if (jp.errors == 0) {
			mods = (LineAST)(jp.getAST());
			}
			
			jp.errors = 0;
			jp.method_specification_opt(mods);
			//LB Debug.msg(debugOn, "Parsed documentation: ");
			errors += jp.errors;    
			if (jp.errors > 0) {
			jml_specs_AST = (AST)astFactory.make( (new ASTArray(1)).add((AST)astFactory.create(DOC_JML_SPECS,"#doc_jml_specs#")));
			} else {
			jml_specs_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(DOC_JML_SPECS,"#doc_jml_specs#")).add(jp.getAST()));
			}
			
			warnings += jp.warnings;    
			
			
			currentAST.root = jml_specs_AST;
			currentAST.child = jml_specs_AST!=null &&jml_specs_AST.getFirstChild()!=null ?
				jml_specs_AST.getFirstChild() : jml_specs_AST;
			currentAST.advanceChildToEnd();
			jml_specs_AST = (AST)currentAST.root;
		}
		catch (RecognitionException e) {
			
			System.err.println(currentFile.getPath() + ":" 
			+ e.toString());
			System.err.println("skipping to the end of this documentation comment");        
			
		}
		returnAST = jml_specs_AST;
	}
	
	public final void paragraph_tag() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST paragraph_tag_AST = null;
		
		//LB Debug.msg(debugOn, "entering paragraph_tag ");
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case DOC_AUTHOR:
			{
				AST tmp3_AST = null;
				tmp3_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp3_AST);
				match(DOC_AUTHOR);
				paragraph_tag_AST = (AST)currentAST.root;
				break;
			}
			case DOC_DEPRECATED:
			{
				AST tmp4_AST = null;
				tmp4_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp4_AST);
				match(DOC_DEPRECATED);
				paragraph_tag_AST = (AST)currentAST.root;
				break;
			}
			case DOC_EXCEPTION:
			{
				AST tmp5_AST = null;
				tmp5_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp5_AST);
				match(DOC_EXCEPTION);
				paragraph_tag_AST = (AST)currentAST.root;
				break;
			}
			case DOC_PARAM:
			{
				AST tmp6_AST = null;
				tmp6_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp6_AST);
				match(DOC_PARAM);
				paragraph_tag_AST = (AST)currentAST.root;
				break;
			}
			case DOC_RETURN:
			{
				AST tmp7_AST = null;
				tmp7_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp7_AST);
				match(DOC_RETURN);
				paragraph_tag_AST = (AST)currentAST.root;
				break;
			}
			case DOC_SEE:
			{
				AST tmp8_AST = null;
				tmp8_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp8_AST);
				match(DOC_SEE);
				paragraph_tag_AST = (AST)currentAST.root;
				break;
			}
			case DOC_SERIALDATA:
			{
				AST tmp9_AST = null;
				tmp9_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp9_AST);
				match(DOC_SERIALDATA);
				paragraph_tag_AST = (AST)currentAST.root;
				break;
			}
			case DOC_SERIAL:
			{
				AST tmp10_AST = null;
				tmp10_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp10_AST);
				match(DOC_SERIAL);
				paragraph_tag_AST = (AST)currentAST.root;
				break;
			}
			case DOC_SERIALFIELD:
			{
				AST tmp11_AST = null;
				tmp11_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp11_AST);
				match(DOC_SERIALFIELD);
				paragraph_tag_AST = (AST)currentAST.root;
				break;
			}
			case DOC_SINCE:
			{
				AST tmp12_AST = null;
				tmp12_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp12_AST);
				match(DOC_SINCE);
				paragraph_tag_AST = (AST)currentAST.root;
				break;
			}
			case DOC_THROWS:
			{
				AST tmp13_AST = null;
				tmp13_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp13_AST);
				match(DOC_THROWS);
				paragraph_tag_AST = (AST)currentAST.root;
				break;
			}
			case DOC_VERSION:
			{
				AST tmp14_AST = null;
				tmp14_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp14_AST);
				match(DOC_VERSION);
				paragraph_tag_AST = (AST)currentAST.root;
				break;
			}
			case DOC_UNKNOWN_KEYWORD:
			{
				AST tmp15_AST = null;
				tmp15_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp15_AST);
				match(DOC_UNKNOWN_KEYWORD);
				paragraph_tag_AST = (AST)currentAST.root;
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			consume();
			consumeUntil(_tokenSet_3);
		}
		returnAST = paragraph_tag_AST;
	}
	
	
	public static final String[] _tokenNames = {
		"<0>",
		"EOF",
		"<2>",
		"NULL_TREE_LOOKAHEAD",
		"ADDITIVE_ASSIGNMENT_OP",
		"ADDITIVE_OP",
		"BITWISE_OP",
		"BITWISE_ASSIGNMENT_OP",
		"EQUALITY_OP",
		"LOGICAL_OP",
		"MULTIPLICATIVE_ASSIGNMENT_OP",
		"MULTIPLICATIVE_OP",
		"RELATIONAL_OP",
		"SHIFT_ASSIGNMENT_OP",
		"SHIFT_OP",
		"POST_INCREMENT_OP",
		"PRE_INCREMENT_OP",
		"UNARY_NUMERIC_OP",
		"ACCESSIBLE_KEYWORD",
		"AFFIRM_KEYWORD",
		"ASSIGNABLE_KEYWORD",
		"LABEL_KEYWORD",
		"LOOP_ASSIGNABLE_KEYWORD",
		"ASSUME_KEYWORD",
		"HENCE_BY_KEYWORD",
		"BREAKS_KEYWORD",
		"CALLABLE_KEYWORD",
		"CONSTRAINT_KEYWORD",
		"CONTINUES_KEYWORD",
		"DECREASING_KEYWORD",
		"DEPENDS_KEYWORD",
		"DIVERGES_KEYWORD",
		"ENSURES_KEYWORD",
		"EQUIVALENCE_OP",
		"IMPLICATION_OP",
		"INVARIANT_KEYWORD",
		"JAVA_MODIFIER",
		"JAVA_BUILTIN_TYPE",
		"JML_MODIFIER",
		"LETOLD_KEYWORD",
		"MAINTAINING_KEYWORD",
		"MEASURED_BY_KEYWORD",
		"MODIFIER_SET",
		"PRIVACY_MODIFIER",
		"QUANTIFIER_TOKEN",
		"REPRESENTS_KEYWORD",
		"REQUIRES_KEYWORD",
		"RETURNS_KEYWORD",
		"SIGNALS_KEYWORD",
		"WHEN_KEYWORD",
		"ACCESSIBLE_SEQ",
		"ARRAY_DECLARATOR",
		"ASSERT",
		"ASGNABLE_SEQ",
		"LOOP_ASGNABLE_SEQ",
		"BREAKS_SEQ",
		"CALLABLE_SEQ",
		"CASE",
		"CAST",
		"CONJOINABLE_SPEC",
		"CONSTRUCTOR",
		"CONT_SEQ",
		"DIMS",
		"DIM_EXPRS",
		"DINFORMALLY",
		"DIV_SEQ",
		"DOC_ATSIGN",
		"DOC_ATSIGN_KEYWORD",
		"DOC_AUTHOR",
		"DOC_COMMENT_START",
		"DOC_DEPRECATED",
		"DOC_EXCEPTION",
		"DOC_JML_SPECS",
		"DOC_NL_WS",
		"DOC_NON_EMPTY_TEXTLINE",
		"DOC_NON_NL_WS",
		"DOC_PARAM",
		"DOC_RETURN",
		"DOC_SEE",
		"DOC_SERIAL",
		"DOC_SERIALDATA",
		"DOC_SERIALFIELD",
		"DOC_SINCE",
		"DOC_THROWS",
		"DOC_UNKNOWN_KEYWORD",
		"DOC_VERSION",
		"ENS_SEQ",
		"EXT_ALSO",
		"EXT_AND",
		"FOR_INIT",
		"FOR_TEST",
		"FOR_UPDATER",
		"INIT",
		"INSTANCE_INIT",
		"LOOP_INV_SEQ",
		"METH",
		"NESTED_CLASS",
		"PARAM",
		"POST_DEC",
		"POST_INC",
		"QUANTIFIED_EXPR",
		"QUANT_VARS",
		"REPLACE",
		"RETURNS_SEQ",
		"SET_COMPR",
		"SIG_SEQ",
		"LOOP_SIG_SEQ",
		"SPEC_CASE",
		"STAR_ELEMS",
		"VAR_DECL",
		"VF_SEQ",
		"SPEC_STATEMENT",
		"\"package\"",
		"REFINE",
		"MODEL",
		"\"import\"",
		"DOC_COMMENT",
		"SEMI",
		"IDENT",
		"DOT",
		"STAR",
		"T_TYPEOFALLTYPES",
		"\"private\"",
		"\"public\"",
		"\"protected\"",
		"\"static\"",
		"\"transient\"",
		"\"final\"",
		"\"abstract\"",
		"\"native\"",
		"\"synchronized\"",
		"\"const\"",
		"\"volatile\"",
		"\"strictfp\"",
		"\"class\"",
		"\"extends\"",
		"WEAKLY",
		"LCURLY",
		"RCURLY",
		"\"interface\"",
		"\"implements\"",
		"COMMA",
		"STATIC_INITIALIZER",
		"INITIALIZER",
		"LPAREN",
		"RPAREN",
		"\"throws\"",
		"ASSIGN",
		"L_ARROW",
		"STRING_LITERAL",
		"INITIALLY",
		"READABLE_IF",
		"MONITORED_BY",
		"PURE",
		"INSTANCE",
		"SPEC_PUBLIC",
		"SPEC_PROTECTED",
		"MONITORED",
		"UNINITIALIZED",
		"GHOST",
		"NON_NULL",
		"INVARIANT",
		"INVARIANT_REDUNDANTLY",
		"CONSTRAINT",
		"CONSTRAINT_REDUNDANTLY",
		"FOR",
		"T_EVERYTHING",
		"\"super\"",
		"\"this\"",
		"T_OTHER",
		"\"new\"",
		"DEPENDS",
		"DEPENDS_REDUNDANTLY",
		"REPRESENTS",
		"REPRESENTS_REDUNDANTLY",
		"T_SUCH_THAT",
		"AXIOM",
		"\"void\"",
		"ALSO",
		"AND",
		"BEHAVIOR",
		"EXCEPTIONAL_BEHAVIOR",
		"NORMAL_BEHAVIOR",
		"FOR_EXAMPLE",
		"EXAMPLE",
		"EXCEPTIONAL_EXAMPLE",
		"NORMAL_EXAMPLE",
		"IMPLIES_THAT",
		"SUBCLASSING_CONTRACT",
		"ACCESSIBLE",
		"ACCESSIBLE_REDUNDANTLY",
		"LBRACK",
		"RBRACK",
		"CALLABLE",
		"CALLABLE_REDUNDANTLY",
		"LCURLY_VBAR",
		"VBAR_RCURLY",
		"MODEL_PROGRAM",
		"FORALL",
		"LET",
		"OLD",
		"REQUIRES",
		"PRE",
		"REQUIRES_REDUNDANTLY",
		"PRE_REDUNDANTLY",
		"T_NOT_SPECIFIED",
		"WHEN",
		"WHEN_REDUNDANTLY",
		"MEASURED_BY",
		"MEASURED_BY_REDUNDANTLY",
		"\"if\"",
		"COLON",
		"LABEL",
		"LOOP_MODIFIES",
		"ASSIGNABLE",
		"MODIFIABLE",
		"MODIFIES",
		"ASSIGNABLE_REDUNDANTLY",
		"MODIFIABLE_REDUNDANTLY",
		"MODIFIES_REDUNDANTLY",
		"T_FIELDS_OF",
		"T_NOTHING",
		"DOT_DOT",
		"ENSURES",
		"POST",
		"ENSURES_REDUNDANTLY",
		"POST_REDUNDANTLY",
		"LOOP_EXSURES",
		"SIGNALS",
		"SIGNALS_REDUNDANTLY",
		"EXSURES",
		"EXSURES_REDUNDANTLY",
		"DIVERGES",
		"DIVERGES_REDUNDANTLY",
		"\"else\"",
		"\"while\"",
		"\"do\"",
		"\"for\"",
		"\"break\"",
		"\"continue\"",
		"\"return\"",
		"\"throw\"",
		"\"switch\"",
		"\"case\"",
		"\"default\"",
		"\"try\"",
		"\"finally\"",
		"\"catch\"",
		"\"assert\"",
		"HENCE_BY",
		"HENCE_BY_REDUNDANTLY",
		"ASSERT_REDUNDANTLY",
		"ASSUME",
		"ASSUME_REDUNDANTLY",
		"SET",
		"PLUS_ASSIGN",
		"MINUS_ASSIGN",
		"STAR_ASSIGN",
		"DIV_ASSIGN",
		"MOD_ASSIGN",
		"SR_ASSIGN",
		"BSR_ASSIGN",
		"SL_ASSIGN",
		"BAND_ASSIGN",
		"BOR_ASSIGN",
		"BXOR_ASSIGN",
		"UNREACHABLE",
		"CHOOSE",
		"OR",
		"CHOOSE_IF",
		"ELSE",
		"ABRUPT_BEHAVIOR",
		"CONTINUES",
		"CONTINUES_REDUNDANTLY",
		"R_ARROW",
		"BREAKS",
		"BREAKS_REDUNDANTLY",
		"RETURNS",
		"RETURNS_REDUNDANTLY",
		"MAINTAINING",
		"MAINTAINING_REDUNDANTLY",
		"LOOP_INVARIANT",
		"LOOP_INVARIANT_REDUNDANTLY",
		"DECREASING",
		"DECREASING_REDUNDANTLY",
		"DECREASES",
		"DECREASES_REDUNDANTLY",
		"QUESTION",
		"EQUIV",
		"NOT_EQUIV",
		"LIMPLIES",
		"BACKWARD_IMPLIES",
		"LOR",
		"LAND",
		"BOR",
		"BXOR",
		"BAND",
		"NOT_EQUAL",
		"EQUAL",
		"LT",
		"GT",
		"LE",
		"GE",
		"IS_SUBTYPE_OF",
		"\"instanceof\"",
		"SL",
		"SR",
		"BSR",
		"PLUS",
		"MINUS",
		"DIV",
		"MOD",
		"INC",
		"DEC",
		"BNOT",
		"LNOT",
		"\"true\"",
		"\"false\"",
		"\"null\"",
		"T_LBLNEG",
		"T_LBLPOS",
		"T_RESULT",
		"T_OLD",
		"T_NOT_MODIFIED",
		"T_FRESH",
		"T_REACH",
		"T_NONNULLELEMENTS",
		"T_TYPEOF",
		"T_ELEMTYPE",
		"T_TYPE",
		"T_LOCKSET",
		"T_IS_INITIALIZED",
		"T_INVARIANT_FOR",
		"INFORMAL_DESCRIPTION",
		"\"boolean\"",
		"\"byte\"",
		"\"char\"",
		"\"short\"",
		"\"int\"",
		"\"long\"",
		"\"float\"",
		"\"double\"",
		"NUM_INT",
		"CHAR_LITERAL",
		"NUM_FLOAT",
		"T_FORALL",
		"T_EXISTS",
		"T_MAX",
		"T_MIN",
		"T_SUM",
		"T_PRODUCT",
		"T_NUM_OF",
		"SPEC_SL_COMMENT",
		"SL_COMMENT",
		"NON_NL_WS",
		"NL_WS",
		"IGNORED_AT_IN_COMMENT",
		"ML_COMMENT",
		"WS",
		"NOWARN_LABEL",
		"NOWARN_LABEL_LIST",
		"JML_BACKSLASH_SEQUENCE",
		"ESC",
		"HEX_DIGIT",
		"VOCAB",
		"EXPONENT",
		"FLOAT_SUFFIX",
		"BADCHAR",
		"DOC_PRE_JML",
		"DOC_JML_PRE"
	};
	
	private static final long _tokenSet_0_data_[] = { 0L, 4190416L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_0 = new BitSet(_tokenSet_0_data_);
	private static final long _tokenSet_1_data_[] = { 2L, 4191440L, 0L, 0L, 0L, 844424930131968L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_1 = new BitSet(_tokenSet_1_data_);
	private static final long _tokenSet_2_data_[] = { 2L, 4190416L, 0L, 0L, 0L, 281474976710656L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_2 = new BitSet(_tokenSet_2_data_);
	private static final long _tokenSet_3_data_[] = { 2L, 4191444L, 0L, 0L, 0L, 281474976710656L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_3 = new BitSet(_tokenSet_3_data_);
	
	}
