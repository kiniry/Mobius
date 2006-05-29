// $ANTLR 2.7.2: "jml.g" -> "JmlParser.java"$

// @(#)$Id: jml.g,v 1.4 2002/04/24 08:40:53 antoine Exp $


// Copyright (C) 1999-2001 Iowa State University

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

// JML concrete syntax
//
// AUTHORS: Gary T. Leavens, Clyde Ruby, Anand Ganapathy, and Arun Raghavan,
//          with help (long ago) from Albert Baker
// This grammar is based on the example Java grammar that ships with Antlr,
// by John Mitchell, Terence Parr, John Lilley, Scott Stanchfield,
// Markus Mohnen, and Peter Williams.
// It was last synchronized to Version 1.17.

package jml; //LB

import java.io.ByteArrayInputStream;
import java.io.File;
import java.util.Vector;

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

public class JmlParser extends antlr.LLkParser       implements JavaTokenTypes
 {

  // an initializer, to set the tree type
  {
	  if(getASTFactory() == null) {
		  setASTFactory(new ASTFactory());
	  }
      setASTNodeClass("jml.LineAST");
  }

  /* package protected */
  /*LB*/ public final static int TABSIZE = 4;
  /*LB*/ public /*LB*/ File currentFile;

  /*LB*/ public /*LB*/ boolean JML_reading_JML_file = false;

  /*LB*/ public /*LB*/ JmlLexer lexer;

  /* vectors of ErrorMessage. Those vectors should be created by the user
     after creating a JmlParser instance */
  /*AR*/ public Vector errorVector;
  /*AR*/ public Vector warningVector;

  // values for the in_spec variable that tells
  // what kind of expression we are parsing.
  boolean no_side_effects = true;       // i.e., in a specification
  boolean side_effects_allowed = false; // i.e., not in a specification

  // values for the in_model_prog variable that tells
  // whether we are parsing a model program
  boolean with_jml = true;     // i.e., in a model program
  boolean no_jml_stmts = false; // i.e., not in a model program

  /*AR*/ public /*AR*/ int errors = 0;
  /*AR*/ public /*AR*/ int warnings = 0;

  // boolean debugOn = true;
  boolean debugOn = false;

  /** Consume tokens until one matches the given token */
  public void consumeUntil(int tokenType) throws TokenStreamException {
    System.err.print("skipping:\n   ");
    Token lastToken = null;
    int tokenCount = 0;
    int column = 3;
    String tokenLexeme;
    while (LA(1) != Token.EOF_TYPE && LA(1) != tokenType)
    {
        if (tokenCount < 20) {
        tokenLexeme = LT(1).getText();
        column = column + tokenLexeme.length() + 1;
        if (column > 70) {
            column = tokenLexeme.length() + 4;
            System.err.print("\n   ");
        }
        System.err.print(" " + tokenLexeme);
        tokenCount++;
        } else {
        lastToken = LT(1);
        }
        consume();
    }
    if (lastToken != null) {
        System.err.print("\n    ... through ");
        System.err.print(lastToken.getText()
                 + " on line: " + lastToken.getLine());
    }
    System.err.println();
  }

  /** Consume tokens until one matches the given token set */
  public void consumeUntil(BitSet set) throws TokenStreamException {
    System.err.print("skipping:\n   ");
    Token lastToken = null;
    int tokenCount = 0;
    int column = 3;
    String tokenLexeme;
    while (LA(1) != Token.EOF_TYPE && !set.member(LA(1))) 
    {
        if (tokenCount < 20) {
        tokenLexeme = LT(1).getText();
        column = column + tokenLexeme.length() + 1;
        if (column > 70) {
            column = tokenLexeme.length() + 4;
            System.err.print("\n   ");
        }
        System.err.print(" " + tokenLexeme);
        tokenCount++;
        } else {
        lastToken = LT(1);
        }
        consume();
    }
    if (lastToken != null) {
        System.err.print("\n    ... through ");
        System.err.print(lastToken.getText()
                 + " on line: " + lastToken.getLine());
    }
    System.err.println();
  }

  /** Parser error-reporting. */
  public void reportError(RecognitionException ex) {
        String msg = ex.toString();
        reportError(msg.substring(msg.indexOf(':')+2), // delete "line n: "
                    ex.getLine(), ex.getColumn());
  }

  /** Parser error-reporting. */
  public void reportError(String err, int line, int col) {
        errors++;
        printWithLineNum(err, line, col);
	if(errorVector != null) {
		errorVector.add(new ErrorMessage(err, line, col));
	}
  }

  /** Print a warning or error message with line and column number info. */
  public void printWithLineNum(String msg, int line, int col) {
        System.err.println(currentFile.getPath()
            + ":" + line + ":(Col " + col + ")" + ": " + msg);
  }

  /** Parser warning-reporting. */
  public void reportWarning(String msg, int line, int col) {
        //@ assume msg != null;
        warnings++;
        printWithLineNum("warning, " + msg, line, col);
	if(warningVector != null) {
		warningVector.add(new ErrorMessage(msg, line, col));
	}
  }

  public void consumeToJmlSpecKeyword() throws TokenStreamException {
    System.err.print("skipping:\n   ");

    Token lastToken = null;
    int tokenCount = 0;
    int column = 3;
    String tokenLexeme;
    while (LA(1) != EOF && LA(1) != RCURLY && LA(1) != LCURLY
            && LA(1) != VBAR_RCURLY && LA(1) != LCURLY_VBAR
            && LA(1) != ALSO && LA(1) != AND && LA(1) != MODEL
            && LA(1) != REQUIRES && LA(1) != PRE && LA(1) != WHEN
            && LA(1) != ASSIGNABLE && LA(1) != MODIFIABLE && LA(1) != MODIFIES
            && LA(1) != ENSURES && LA(1) != POST
            && LA(1) != SIGNALS && LA(1) != EXSURES
            && LA(1) != MEASURED_BY && LA(1) != LET && LA(1) != OLD
            && LA(1) != IMPLIES_THAT && LA(1) != FOR_EXAMPLE
            && LA(1) != SUBCLASSING_CONTRACT
            && LA(1) != DIVERGES
            && LA(1) != MEASURED_BY_REDUNDANTLY
            && LA(1) != REQUIRES_REDUNDANTLY && LA(1) != PRE_REDUNDANTLY
            && LA(1) != WHEN_REDUNDANTLY
            && LA(1) != ASSIGNABLE_REDUNDANTLY
            && LA(1) != MODIFIABLE_REDUNDANTLY && LA(1) != MODIFIES_REDUNDANTLY
            && LA(1) != ENSURES_REDUNDANTLY && LA(1) != POST_REDUNDANTLY
            && LA(1) != SIGNALS_REDUNDANTLY
            && LA(1) != EXSURES_REDUNDANTLY
            && LA(1) != DIVERGES_REDUNDANTLY
            && LA(1) != CONTINUES && LA(1) != CONTINUES_REDUNDANTLY
            && LA(1) != BREAKS && LA(1) != BREAKS_REDUNDANTLY
            && LA(1) != RETURNS && LA(1) != RETURNS_REDUNDANTLY
            )
    {
        if (tokenCount < 20) {
        tokenLexeme = LT(1).getText();
        column = column + tokenLexeme.length() + 1;
        if (column > 70) {
            column = tokenLexeme.length() + 4;
            System.err.print("\n   ");
        }
        System.err.print(" " + tokenLexeme);
        tokenCount++;
        } else {
        lastToken = LT(1);
        }
        consume();
    }
    if (lastToken != null) {
        System.err.print("\n    ... through ");
        System.err.print(lastToken.getText()
                 + " on line: " + lastToken.getLine());
    }

    System.err.println();
  }

  public void consumeToTopLevelKeyword() throws TokenStreamException {
    System.err.print("skipping:\n   ");

    Token lastToken = null;
    int tokenCount = 0;
    int column = 3;
    String tokenLexeme;
    while (LA(1) != EOF && LA(1) != LCURLY && LA(1) != RCURLY  
        && LA(1) != LITERAL_class && LA(1) != LITERAL_interface
        && LA(1) != LITERAL_import
        && LA(1) != REFINE ) 
    {
        if (tokenCount < 20) {
        tokenLexeme = LT(1).getText();
        column = column + tokenLexeme.length() + 1;
        if (column > 70) {
            column = tokenLexeme.length() + 4;
            System.err.print("\n   ");
        }
        System.err.print(" " + tokenLexeme);
        tokenCount++;
        } else {
        lastToken = LT(1);
        }
        consume();
    }
    if (lastToken != null) {
        System.err.print("\n    ... through ");
        System.err.print(lastToken.getText()
                 + " on line: " + lastToken.getLine());
    }

    System.err.println();
  }

  /*@ normal_behavior
    @   requires s != null;
    @   ensures (* \result is the number of cr/newline sequences in s *);
    @*/
  public int countlines(String s)
  {
        if (s == null) {
       return 0;
    }
    int count = 0;
    int i;
    for (i = 0; i < s.length(); i++) {
      if (s.charAt(i) == '\n') {
         count++;
      } else if (s.charAt(i) == '\r') {
        if (i+1 < s.length() && s.charAt(i+1) == '\n') {
            i++;
        }
        count++;
      }
    }
    return count;
  }

  /*** Trim the leading asterisks and white space, and trailing asterisks. **/
  /*@ requires doc_com_text != null;
    @*/
  public String trim_asterisks(String doc_com_text) {
        int i = 0;
        while (i < doc_com_text.length() && doc_com_text.charAt(i) == '*') {
            i++;
        }
        /*@ assert 0 <= i
          @    && i < doc_com_text.length() ==> doc_com_text.charAt(i) != '*';
          @*/
        while (i < doc_com_text.length() && doc_com_text.charAt(i) == ' ') {
            i++;
        }
        /*@ assert 0 <= i
          @    && i < doc_com_text.length() ==> doc_com_text.charAt(i) != ' ';
          @*/
        int j = doc_com_text.length();
        while (i <= j && doc_com_text.charAt(j-1) == '*') {
             j--;
        }
        /*@ assert 0 <= i
          @    && i < doc_com_text.length() ==> doc_com_text.charAt(i) != ' '
          @    && i <= j ==> doc_com_text.charAt(j-1) != '*';
          @*/
        if (i > j) {
            return "";
        } else {
            return doc_com_text.substring(i,j);
        }
  }

  //@ requires desc_text != null;
  public String remove_ats_after_newlines(String desc_text)
  {
        StringBuffer res = new StringBuffer(desc_text.length());
        boolean seen_newline = false;
        //@ ghost int res_index = 0;
        //@ ghost int num_of_ats_skipped = 0;
        //@ maintaining res_index + num_of_ats_skipped == i;
        for (int i = 0; i < desc_text.length(); i++) {
            char c = desc_text.charAt(i);
            if (seen_newline && c == '@') {
                seen_newline = false;
                //@ set num_of_ats_skipped = num_of_ats_skipped + 1;
                while (i+1 < desc_text.length()
                       && desc_text.charAt(i+1) == '@') {
                    i++;
                    //@ set num_of_ats_skipped = num_of_ats_skipped + 1;
                }
                continue;
            } else if (seen_newline && (c == ' ' || c == '\t')) {
            ;
            } else if (c == '\n' || c == '\r') {
                seen_newline = true;
            } else {
                /*@ assert (* c is not a newline or cr char,
                  @           and if it's a space or tab, then !seen_newline *);
                  @*/
                seen_newline = false;
            }
            res.append(c);
            //@ set res_index = res_index + 1;
        }
        return res.toString();
  }

  //@ requires mods == null || mods instanceof LineAST;
  private LineAST modifiers2privacy(AST mods)
  {
      if (mods == null) {
          return null;
      }
      LineAST lineASTmods = (LineAST)mods;
      Modifiers modifs = (Modifiers)(lineASTmods.type);
      ModifierSet ms = modifs.getModifiers();
      // save column and line information
      int linenum = lineASTmods.line;
      int colnum = lineASTmods.column;
      // create a new special token
      // [[[should warn if some other modifier besides a privacy modifier is used]]]
      ms = Typing.defaultPrivacyModifiers(ms);
      String priv_mod_str = "privacy_modifier (" + ms + ")";
      LineAST lineASTprivacy_opt = 
          (LineAST)(astFactory.create(PRIVACY_MODIFIER, priv_mod_str));
      lineASTprivacy_opt.type = modifs;
      lineASTprivacy_opt.line = linenum;
      lineASTprivacy_opt.column = colnum;
      return lineASTprivacy_opt;
  }

  private void checkForMissingCommentEnd() {
    if (lexer.ML_Jml_state) {
      System.err.println(currentFile.getPath() + ":" 
        + lexer.annotStartLine + ": "
        + "Multi-line annotation '/*@' (or '/*+@') without closing '*/'");
      System.err.println();
      errors++;
    }
  }

protected JmlParser(TokenBuffer tokenBuf, int k) {
  super(tokenBuf,k);
  tokenNames = _tokenNames;
  buildTokenTypeASTClassMap();
  astFactory = new ASTFactory(getTokenTypeToASTClassMap());
  setASTNodeClass("jml.LineAST");
}

public JmlParser(TokenBuffer tokenBuf) {
  this(tokenBuf,2);
}

protected JmlParser(TokenStream lexer, int k) {
  super(lexer,k);
  tokenNames = _tokenNames;
  buildTokenTypeASTClassMap();
  astFactory = new ASTFactory(getTokenTypeToASTClassMap());
  setASTNodeClass("jml.LineAST");
}

public JmlParser(TokenStream lexer) {
  this(lexer,2);
}

public JmlParser(ParserSharedInputState state) {
  super(state,2);
  tokenNames = _tokenNames;
  buildTokenTypeASTClassMap();
  astFactory = new ASTFactory(getTokenTypeToASTClassMap());
  setASTNodeClass("jml.LineAST");
}

	public final void compilation_unit() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST compilation_unit_AST = null;
		
		try {      // for error handling
			{
			if ((LA(1)==LITERAL_package||LA(1)==DOC_COMMENT) && (_tokenSet_0.member(LA(2)))) {
				{
				switch ( LA(1)) {
				case DOC_COMMENT:
				{
					ignored_doc_comments();
					break;
				}
				case LITERAL_package:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				package_definition();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else if ((_tokenSet_1.member(LA(1))) && (_tokenSet_2.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			{
			if ((LA(1)==REFINE||LA(1)==DOC_COMMENT) && (_tokenSet_3.member(LA(2)))) {
				{
				switch ( LA(1)) {
				case DOC_COMMENT:
				{
					ignored_doc_comments();
					break;
				}
				case REFINE:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				refine_prefix();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else if ((_tokenSet_4.member(LA(1))) && (_tokenSet_5.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			{
			_loop15:
			do {
				if (((LA(1) >= MODEL && LA(1) <= DOC_COMMENT)) && (_tokenSet_6.member(LA(2)))) {
					{
					switch ( LA(1)) {
					case DOC_COMMENT:
					{
						ignored_doc_comments();
						break;
					}
					case MODEL:
					case LITERAL_import:
					{
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					import_definition();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop15;
				}
				
			} while (true);
			}
			{
			_loop17:
			do {
				if ((_tokenSet_7.member(LA(1)))) {
					type_definition();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop17;
				}
				
			} while (true);
			}
			AST tmp1_AST = null;
			tmp1_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp1_AST);
			match(Token.EOF_TYPE);
			if ( inputState.guessing==0 ) {
				checkForMissingCommentEnd();
			}
			compilation_unit_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				System.err.print("skipping:\n   ");
				Token lastToken = null;
				int tokenCount = 0;
				int column = 3;
				String tokenLexeme;
				
				while (LA(1) != EOF)
				{
				if (tokenCount < 20) {
				tokenLexeme = LT(1).getText();
				column = column + tokenLexeme.length() + 1;
				if (column > 70) {
				column = tokenLexeme.length() + 4;
				System.err.print("\n   ");
				}
				System.err.print(" " + tokenLexeme);
				tokenCount++;
				} else {
				lastToken = LT(1);
				}
				consume();
				}
				if (lastToken != null) {
				System.err.print("\n    ... through ");
				System.err.print(lastToken.getText()
				+ " on line: " + lastToken.getLine());
				}
				
				System.err.println();
				
			} else {
				throw err;
			}
		}
		returnAST = compilation_unit_AST;
	}
	
	public final void ignored_doc_comments() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST ignored_doc_comments_AST = null;
		Token  d = null;
		AST d_AST = null;
		
		int line = 0, col = 0;
		
		
		{
		int _cnt22=0;
		_loop22:
		do {
			if ((LA(1)==DOC_COMMENT)) {
				d = LT(1);
				d_AST = astFactory.create(d);
				astFactory.addASTChild(currentAST, d_AST);
				match(DOC_COMMENT);
				if ( inputState.guessing==0 ) {
					line = ((LineAST)d_AST).line;
					col = ((LineAST)d_AST).column;
					
				}
			}
			else {
				if ( _cnt22>=1 ) { break _loop22; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt22++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
			reportWarning("doc comment appears before "
			+ "'package', 'refine', or 'import', ignored",
			line, col);
			
		}
		ignored_doc_comments_AST = (AST)currentAST.root;
		returnAST = ignored_doc_comments_AST;
	}
	
	public final void package_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST package_definition_AST = null;
		
		try {      // for error handling
			AST tmp2_AST = null;
			tmp2_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp2_AST);
			match(LITERAL_package);
			name();
			astFactory.addASTChild(currentAST, returnAST);
			match(SEMI);
			package_definition_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToTopLevelKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = package_definition_AST;
	}
	
	public final void refine_prefix() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST refine_prefix_AST = null;
		
		try {      // for error handling
			AST tmp4_AST = null;
			tmp4_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp4_AST);
			match(REFINE);
			ident_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp5_AST = null;
			tmp5_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp5_AST);
			match(L_ARROW);
			AST tmp6_AST = null;
			tmp6_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp6_AST);
			match(STRING_LITERAL);
			match(SEMI);
			refine_prefix_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToTopLevelKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = refine_prefix_AST;
	}
	
	public final void import_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST import_definition_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case LITERAL_import:
			{
				AST tmp8_AST = null;
				tmp8_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp8_AST);
				match(LITERAL_import);
				name_star();
				astFactory.addASTChild(currentAST, returnAST);
				match(SEMI);
				import_definition_AST = (AST)currentAST.root;
				break;
			}
			case MODEL:
			{
				AST tmp10_AST = null;
				tmp10_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp10_AST);
				match(MODEL);
				AST tmp11_AST = null;
				tmp11_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp11_AST);
				match(LITERAL_import);
				name_star();
				astFactory.addASTChild(currentAST, returnAST);
				match(SEMI);
				import_definition_AST = (AST)currentAST.root;
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToTopLevelKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = import_definition_AST;
	}
	
	public final void type_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST type_definition_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case MODEL:
			case DOC_COMMENT:
			case LITERAL_private:
			case LITERAL_public:
			case LITERAL_protected:
			case LITERAL_static:
			case LITERAL_transient:
			case LITERAL_final:
			case LITERAL_abstract:
			case LITERAL_native:
			case LITERAL_synchronized:
			case LITERAL_const:
			case LITERAL_volatile:
			case LITERAL_strictfp:
			case LITERAL_class:
			case LITERAL_interface:
			case PURE:
			case INSTANCE:
			case SPEC_PUBLIC:
			case SPEC_PROTECTED:
			case MONITORED:
			case UNINITIALIZED:
			case GHOST:
			case NON_NULL:
			{
				{
				switch ( LA(1)) {
				case DOC_COMMENT:
				{
					doc_comment();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				case MODEL:
				case LITERAL_private:
				case LITERAL_public:
				case LITERAL_protected:
				case LITERAL_static:
				case LITERAL_transient:
				case LITERAL_final:
				case LITERAL_abstract:
				case LITERAL_native:
				case LITERAL_synchronized:
				case LITERAL_const:
				case LITERAL_volatile:
				case LITERAL_strictfp:
				case LITERAL_class:
				case LITERAL_interface:
				case PURE:
				case INSTANCE:
				case SPEC_PUBLIC:
				case SPEC_PROTECTED:
				case MONITORED:
				case UNINITIALIZED:
				case GHOST:
				case NON_NULL:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				modifiers();
				astFactory.addASTChild(currentAST, returnAST);
				class_or_interface_def();
				astFactory.addASTChild(currentAST, returnAST);
				type_definition_AST = (AST)currentAST.root;
				break;
			}
			case SEMI:
			{
				AST tmp13_AST = null;
				tmp13_AST = astFactory.create(LT(1));
				match(SEMI);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToTopLevelKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = type_definition_AST;
	}
	
	public final void start_predicate() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST start_predicate_AST = null;
		
		predicate();
		astFactory.addASTChild(currentAST, returnAST);
		start_predicate_AST = (AST)currentAST.root;
		returnAST = start_predicate_AST;
	}
	
	public final void predicate() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST predicate_AST = null;
		
		spec_expression();
		astFactory.addASTChild(currentAST, returnAST);
		predicate_AST = (AST)currentAST.root;
		returnAST = predicate_AST;
	}
	
	public final void start_signals() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST start_signals_AST = null;
		
		signals_clause();
		astFactory.addASTChild(currentAST, returnAST);
		start_signals_AST = (AST)currentAST.root;
		returnAST = start_signals_AST;
	}
	
	public final void signals_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST signals_clause_AST = null;
		
		String kw = "";
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case SIGNALS:
			{
				AST tmp14_AST = null;
				tmp14_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp14_AST);
				match(SIGNALS);
				break;
			}
			case SIGNALS_REDUNDANTLY:
			{
				AST tmp15_AST = null;
				tmp15_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp15_AST);
				match(SIGNALS_REDUNDANTLY);
				break;
			}
			case EXSURES:
			{
				AST tmp16_AST = null;
				tmp16_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp16_AST);
				match(EXSURES);
				break;
			}
			case EXSURES_REDUNDANTLY:
			{
				AST tmp17_AST = null;
				tmp17_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp17_AST);
				match(EXSURES_REDUNDANTLY);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			AST tmp18_AST = null;
			tmp18_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp18_AST);
			match(LPAREN);
			reference_type();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case IDENT:
			{
				AST tmp19_AST = null;
				tmp19_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp19_AST);
				match(IDENT);
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			AST tmp20_AST = null;
			tmp20_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp20_AST);
			match(RPAREN);
			{
			switch ( LA(1)) {
			case T_NOT_SPECIFIED:
			{
				AST tmp21_AST = null;
				tmp21_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp21_AST);
				match(T_NOT_SPECIFIED);
				break;
			}
			case IDENT:
			case LPAREN:
			case STRING_LITERAL:
			case LITERAL_super:
			case LITERAL_this:
			case LITERAL_new:
			case LITERAL_void:
			case PLUS:
			case MINUS:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case T_RESULT:
			case T_OLD:
			case T_NOT_MODIFIED:
			case T_FRESH:
			case T_REACH:
			case T_NONNULLELEMENTS:
			case T_TYPEOF:
			case T_ELEMTYPE:
			case T_TYPE:
			case T_LOCKSET:
			case T_IS_INITIALIZED:
			case T_INVARIANT_FOR:
			case INFORMAL_DESCRIPTION:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			case NUM_INT:
			case CHAR_LITERAL:
			case NUM_FLOAT:
			{
				predicate();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
			if ( inputState.guessing==0 ) {
				signals_clause_AST = (AST)currentAST.root;
				signals_clause_AST.setType(SIGNALS_KEYWORD);
			}
			signals_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToJmlSpecKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = signals_clause_AST;
	}
	
	public final void name() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST name_AST = null;
		
		AST tmp23_AST = null;
		tmp23_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp23_AST);
		match(IDENT);
		{
		_loop27:
		do {
			if ((LA(1)==DOT)) {
				AST tmp24_AST = null;
				tmp24_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp24_AST);
				match(DOT);
				AST tmp25_AST = null;
				tmp25_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp25_AST);
				match(IDENT);
			}
			else {
				break _loop27;
			}
			
		} while (true);
		}
		name_AST = (AST)currentAST.root;
		returnAST = name_AST;
	}
	
	public final void name_star() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST name_star_AST = null;
		
		AST tmp26_AST = null;
		tmp26_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp26_AST);
		match(IDENT);
		{
		_loop30:
		do {
			if ((LA(1)==DOT) && (LA(2)==IDENT)) {
				AST tmp27_AST = null;
				tmp27_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp27_AST);
				match(DOT);
				AST tmp28_AST = null;
				tmp28_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp28_AST);
				match(IDENT);
			}
			else {
				break _loop30;
			}
			
		} while (true);
		}
		{
		switch ( LA(1)) {
		case DOT:
		{
			AST tmp29_AST = null;
			tmp29_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp29_AST);
			match(DOT);
			AST tmp30_AST = null;
			tmp30_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp30_AST);
			match(STAR);
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		name_star_AST = (AST)currentAST.root;
		returnAST = name_star_AST;
	}
	
	public final void doc_comment() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST doc_comment_AST = null;
		Token  d = null;
		AST d_AST = null;
		
		d = LT(1);
		d_AST = astFactory.create(d);
		astFactory.addASTChild(currentAST, d_AST);
		match(DOC_COMMENT);
		if ( inputState.guessing==0 ) {
			doc_comment_AST = (AST)currentAST.root;
			
			DocCommentLexer dl = new DocCommentLexer(
			new ByteArrayInputStream(trim_asterisks(d.getText()).getBytes()));
			dl.setLine(d.getLine() - (countlines(d.getText() + 2)));
			DocCommentParser dp = new DocCommentParser(dl);
			dp.errors = 0;
			dp.warnings = 0;
			dp.currentFile = currentFile;
			dp.documentationCommentBody();
			if (dp.errors > 0) {
			reportWarning("Skipping to end of this"
			+ " documentation comment",
			dl.getLine(), dl.getColumn());
			doc_comment_AST = (AST)astFactory.make( (new ASTArray(1)).add(astFactory.create(DOC_COMMENT_START,"doc_comment_start")));
			} else {
			doc_comment_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(DOC_COMMENT_START,"doc_comment_start")).add(dp.getAST()));
			}
			
			currentAST.root = doc_comment_AST;
			currentAST.child = doc_comment_AST!=null &&doc_comment_AST.getFirstChild()!=null ?
				doc_comment_AST.getFirstChild() : doc_comment_AST;
			currentAST.advanceChildToEnd();
		}
		doc_comment_AST = (AST)currentAST.root;
		returnAST = doc_comment_AST;
	}
	
	public final void modifiers() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST modifiers_AST = null;
		AST mod_AST = null;
		
		ModifierSet ms = new ModifierSet();
		int linenum = 0;
		int colnum = 0;
		
		
		{
		_loop43:
		do {
			if ((_tokenSet_8.member(LA(1)))) {
				modifier();
				mod_AST = (AST)returnAST;
				if ( inputState.guessing==0 ) {
					LineAST lineASTmod = (LineAST)mod_AST;
					linenum = lineASTmod.line;
					colnum = lineASTmod.column;
					ModifierSet m
					= ((Modifiers)(lineASTmod.type)).getModifiers();
					if (ms.intersects(m)) {
					reportWarning("duplicate modifier, '"
					+ m.toString() + "'",
					linenum, colnum);
					}
					ms = ms.union(m);
					
				}
			}
			else {
				break _loop43;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			modifiers_AST = (AST)currentAST.root;
			
			ms = Typing.defaultPrivacyModifiers(ms);
			String mod_set_string = "modifier_set (" + ms + ")";
			modifiers_AST = astFactory.create(MODIFIER_SET,mod_set_string);
			LineAST lineASTmodifiers = (LineAST)modifiers_AST;
			lineASTmodifiers.type = new Modifiers(ms);
			lineASTmodifiers.line = linenum;
			lineASTmodifiers.column = colnum;
			
			currentAST.root = modifiers_AST;
			currentAST.child = modifiers_AST!=null &&modifiers_AST.getFirstChild()!=null ?
				modifiers_AST.getFirstChild() : modifiers_AST;
			currentAST.advanceChildToEnd();
		}
		returnAST = modifiers_AST;
	}
	
	public final void class_or_interface_def() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST class_or_interface_def_AST = null;
		
		switch ( LA(1)) {
		case LITERAL_class:
		{
			class_definition(no_jml_stmts);
			astFactory.addASTChild(currentAST, returnAST);
			class_or_interface_def_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_interface:
		{
			interface_definition();
			astFactory.addASTChild(currentAST, returnAST);
			class_or_interface_def_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = class_or_interface_def_AST;
	}
	
	public final void class_definition(
		boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST class_definition_AST = null;
		
		AST tmp31_AST = null;
		tmp31_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp31_AST);
		match(LITERAL_class);
		AST tmp32_AST = null;
		tmp32_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp32_AST);
		match(IDENT);
		{
		switch ( LA(1)) {
		case LITERAL_extends:
		{
			AST tmp33_AST = null;
			tmp33_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp33_AST);
			match(LITERAL_extends);
			name();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case WEAKLY:
			{
				AST tmp34_AST = null;
				tmp34_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp34_AST);
				match(WEAKLY);
				break;
			}
			case LCURLY:
			case LITERAL_implements:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		case LCURLY:
		case LITERAL_implements:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_implements:
		{
			implements_clause();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case LCURLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		class_block(side_effects_allowed, in_model_prog);
		astFactory.addASTChild(currentAST, returnAST);
		class_definition_AST = (AST)currentAST.root;
		returnAST = class_definition_AST;
	}
	
	public final void interface_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST interface_definition_AST = null;
		
		AST tmp35_AST = null;
		tmp35_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp35_AST);
		match(LITERAL_interface);
		AST tmp36_AST = null;
		tmp36_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp36_AST);
		match(IDENT);
		{
		switch ( LA(1)) {
		case LITERAL_extends:
		{
			interface_extends();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case LCURLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		class_block(side_effects_allowed, no_jml_stmts);
		astFactory.addASTChild(currentAST, returnAST);
		interface_definition_AST = (AST)currentAST.root;
		returnAST = interface_definition_AST;
	}
	
	public final void type_spec() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST type_spec_AST = null;
		
		{
		switch ( LA(1)) {
		case IDENT:
		case LITERAL_void:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_short:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_float:
		case LITERAL_double:
		{
			type();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case T_TYPEOFALLTYPES:
		{
			AST tmp37_AST = null;
			tmp37_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp37_AST);
			match(T_TYPEOFALLTYPES);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LBRACK:
		{
			dims();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case EOF:
		case SEMI:
		case IDENT:
		case RCURLY:
		case COMMA:
		case RPAREN:
		case ASSIGN:
		case INITIALLY:
		case READABLE_IF:
		case MONITORED_BY:
		case FOR:
		case RBRACK:
		case LITERAL_if:
		case COLON:
		case DOT_DOT:
		case PLUS_ASSIGN:
		case MINUS_ASSIGN:
		case STAR_ASSIGN:
		case DIV_ASSIGN:
		case MOD_ASSIGN:
		case SR_ASSIGN:
		case BSR_ASSIGN:
		case SL_ASSIGN:
		case BAND_ASSIGN:
		case BOR_ASSIGN:
		case BXOR_ASSIGN:
		case QUESTION:
		case EQUIV:
		case NOT_EQUIV:
		case LIMPLIES:
		case BACKWARD_IMPLIES:
		case LOR:
		case LAND:
		case BOR:
		case BXOR:
		case BAND:
		case NOT_EQUAL:
		case EQUAL:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		type_spec_AST = (AST)currentAST.root;
		returnAST = type_spec_AST;
	}
	
	public final void type() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST type_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		{
			reference_type();
			astFactory.addASTChild(currentAST, returnAST);
			type_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_void:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_short:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_float:
		case LITERAL_double:
		{
			builtInType();
			astFactory.addASTChild(currentAST, returnAST);
			type_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = type_AST;
	}
	
	public final void dims() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST dims_AST = null;
		
		{
		int _cnt642=0;
		_loop642:
		do {
			if ((LA(1)==LBRACK) && (LA(2)==RBRACK)) {
				AST tmp38_AST = null;
				tmp38_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp38_AST);
				match(LBRACK);
				match(RBRACK);
			}
			else {
				if ( _cnt642>=1 ) { break _loop642; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt642++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			dims_AST = (AST)currentAST.root;
			dims_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(DIMS,"#dims#")).add(dims_AST));
			currentAST.root = dims_AST;
			currentAST.child = dims_AST!=null &&dims_AST.getFirstChild()!=null ?
				dims_AST.getFirstChild() : dims_AST;
			currentAST.advanceChildToEnd();
		}
		dims_AST = (AST)currentAST.root;
		returnAST = dims_AST;
	}
	
	public final void reference_type() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST reference_type_AST = null;
		
		name();
		astFactory.addASTChild(currentAST, returnAST);
		reference_type_AST = (AST)currentAST.root;
		returnAST = reference_type_AST;
	}
	
	public final void builtInType() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST builtInType_AST = null;
		
		{
		switch ( LA(1)) {
		case LITERAL_void:
		{
			AST tmp40_AST = null;
			tmp40_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp40_AST);
			match(LITERAL_void);
			break;
		}
		case LITERAL_boolean:
		{
			AST tmp41_AST = null;
			tmp41_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp41_AST);
			match(LITERAL_boolean);
			break;
		}
		case LITERAL_byte:
		{
			AST tmp42_AST = null;
			tmp42_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp42_AST);
			match(LITERAL_byte);
			break;
		}
		case LITERAL_char:
		{
			AST tmp43_AST = null;
			tmp43_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp43_AST);
			match(LITERAL_char);
			break;
		}
		case LITERAL_short:
		{
			AST tmp44_AST = null;
			tmp44_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp44_AST);
			match(LITERAL_short);
			break;
		}
		case LITERAL_int:
		{
			AST tmp45_AST = null;
			tmp45_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp45_AST);
			match(LITERAL_int);
			break;
		}
		case LITERAL_long:
		{
			AST tmp46_AST = null;
			tmp46_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp46_AST);
			match(LITERAL_long);
			break;
		}
		case LITERAL_float:
		{
			AST tmp47_AST = null;
			tmp47_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp47_AST);
			match(LITERAL_float);
			break;
		}
		case LITERAL_double:
		{
			AST tmp48_AST = null;
			tmp48_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp48_AST);
			match(LITERAL_double);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			builtInType_AST = (AST)currentAST.root;
			builtInType_AST.setType(JAVA_BUILTIN_TYPE);
		}
		builtInType_AST = (AST)currentAST.root;
		returnAST = builtInType_AST;
	}
	
	public final void modifier() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST modifier_AST = null;
		
		Modifier r = Modifier.NONE;
		
		
		switch ( LA(1)) {
		case LITERAL_private:
		case LITERAL_public:
		case LITERAL_protected:
		case LITERAL_static:
		case LITERAL_transient:
		case LITERAL_final:
		case LITERAL_abstract:
		case LITERAL_native:
		case LITERAL_synchronized:
		case LITERAL_const:
		case LITERAL_volatile:
		case LITERAL_strictfp:
		{
			{
			switch ( LA(1)) {
			case LITERAL_private:
			{
				AST tmp49_AST = null;
				tmp49_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp49_AST);
				match(LITERAL_private);
				break;
			}
			case LITERAL_public:
			{
				AST tmp50_AST = null;
				tmp50_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp50_AST);
				match(LITERAL_public);
				break;
			}
			case LITERAL_protected:
			{
				AST tmp51_AST = null;
				tmp51_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp51_AST);
				match(LITERAL_protected);
				break;
			}
			case LITERAL_static:
			{
				AST tmp52_AST = null;
				tmp52_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp52_AST);
				match(LITERAL_static);
				break;
			}
			case LITERAL_transient:
			{
				AST tmp53_AST = null;
				tmp53_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp53_AST);
				match(LITERAL_transient);
				break;
			}
			case LITERAL_final:
			{
				AST tmp54_AST = null;
				tmp54_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp54_AST);
				match(LITERAL_final);
				break;
			}
			case LITERAL_abstract:
			{
				AST tmp55_AST = null;
				tmp55_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp55_AST);
				match(LITERAL_abstract);
				break;
			}
			case LITERAL_native:
			{
				AST tmp56_AST = null;
				tmp56_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp56_AST);
				match(LITERAL_native);
				break;
			}
			case LITERAL_synchronized:
			{
				AST tmp57_AST = null;
				tmp57_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp57_AST);
				match(LITERAL_synchronized);
				break;
			}
			case LITERAL_const:
			{
				AST tmp58_AST = null;
				tmp58_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp58_AST);
				match(LITERAL_const);
				break;
			}
			case LITERAL_volatile:
			{
				AST tmp59_AST = null;
				tmp59_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp59_AST);
				match(LITERAL_volatile);
				break;
			}
			case LITERAL_strictfp:
			{
				AST tmp60_AST = null;
				tmp60_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp60_AST);
				match(LITERAL_strictfp);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				modifier_AST = (AST)currentAST.root;
				modifier_AST.setType(JAVA_MODIFIER);
				r = new Modifier(modifier_AST.getText());
//				System.out.println(modifier_AST.getClass());
				((LineAST)modifier_AST).type = new Modifiers(r);
				
			}
			modifier_AST = (AST)currentAST.root;
			break;
		}
		case MODEL:
		case PURE:
		case INSTANCE:
		case SPEC_PUBLIC:
		case SPEC_PROTECTED:
		case MONITORED:
		case UNINITIALIZED:
		case GHOST:
		case NON_NULL:
		{
			jml_modifier();
			astFactory.addASTChild(currentAST, returnAST);
			modifier_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = modifier_AST;
	}
	
	public final void jml_modifier() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST jml_modifier_AST = null;
		
		Modifier r = Modifier.NONE;
		
		
		{
		switch ( LA(1)) {
		case MODEL:
		{
			AST tmp61_AST = null;
			tmp61_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp61_AST);
			match(MODEL);
			break;
		}
		case PURE:
		{
			AST tmp62_AST = null;
			tmp62_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp62_AST);
			match(PURE);
			break;
		}
		case INSTANCE:
		{
			AST tmp63_AST = null;
			tmp63_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp63_AST);
			match(INSTANCE);
			break;
		}
		case SPEC_PUBLIC:
		{
			AST tmp64_AST = null;
			tmp64_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp64_AST);
			match(SPEC_PUBLIC);
			break;
		}
		case SPEC_PROTECTED:
		{
			AST tmp65_AST = null;
			tmp65_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp65_AST);
			match(SPEC_PROTECTED);
			break;
		}
		case MONITORED:
		{
			AST tmp66_AST = null;
			tmp66_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp66_AST);
			match(MONITORED);
			break;
		}
		case UNINITIALIZED:
		{
			AST tmp67_AST = null;
			tmp67_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp67_AST);
			match(UNINITIALIZED);
			break;
		}
		case GHOST:
		{
			AST tmp68_AST = null;
			tmp68_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp68_AST);
			match(GHOST);
			break;
		}
		case NON_NULL:
		{
			AST tmp69_AST = null;
			tmp69_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp69_AST);
			match(NON_NULL);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			jml_modifier_AST = (AST)currentAST.root;
			jml_modifier_AST.setType(JML_MODIFIER);
			r = new Modifier(jml_modifier_AST.getText());
			((LineAST)jml_modifier_AST).type = new Modifiers(r);
			
		}
		jml_modifier_AST = (AST)currentAST.root;
		returnAST = jml_modifier_AST;
	}
	
	public final void implements_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST implements_clause_AST = null;
		
		AST tmp70_AST = null;
		tmp70_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp70_AST);
		match(LITERAL_implements);
		name_weakly_list();
		astFactory.addASTChild(currentAST, returnAST);
		implements_clause_AST = (AST)currentAST.root;
		returnAST = implements_clause_AST;
	}
	
	public final void class_block(
		boolean in_spec, boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST class_block_AST = null;
		
		AST tmp71_AST = null;
		tmp71_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp71_AST);
		match(LCURLY);
		{
		_loop52:
		do {
			if ((_tokenSet_9.member(LA(1)))) {
				field(in_spec, in_model_prog);
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop52;
			}
			
		} while (true);
		}
		AST tmp72_AST = null;
		tmp72_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp72_AST);
		match(RCURLY);
		class_block_AST = (AST)currentAST.root;
		returnAST = class_block_AST;
	}
	
	public final void field(
		boolean in_spec, boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST field_AST = null;
		AST d_AST = null;
		Token  st = null;
		AST st_AST = null;
		AST ii_AST = null;
		AST mods_AST = null;
		AST msfd_AST = null;
		
		ModifierSet ms = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case MODEL:
			case DOC_COMMENT:
			case IDENT:
			case T_TYPEOFALLTYPES:
			case LITERAL_private:
			case LITERAL_public:
			case LITERAL_protected:
			case LITERAL_static:
			case LITERAL_transient:
			case LITERAL_final:
			case LITERAL_abstract:
			case LITERAL_native:
			case LITERAL_synchronized:
			case LITERAL_const:
			case LITERAL_volatile:
			case LITERAL_strictfp:
			case LITERAL_class:
			case LCURLY:
			case LITERAL_interface:
			case PURE:
			case INSTANCE:
			case SPEC_PUBLIC:
			case SPEC_PROTECTED:
			case MONITORED:
			case UNINITIALIZED:
			case GHOST:
			case NON_NULL:
			case INVARIANT:
			case INVARIANT_REDUNDANTLY:
			case CONSTRAINT:
			case CONSTRAINT_REDUNDANTLY:
			case DEPENDS:
			case DEPENDS_REDUNDANTLY:
			case REPRESENTS:
			case REPRESENTS_REDUNDANTLY:
			case LITERAL_void:
			case ALSO:
			case AND:
			case BEHAVIOR:
			case EXCEPTIONAL_BEHAVIOR:
			case NORMAL_BEHAVIOR:
			case FOR_EXAMPLE:
			case IMPLIES_THAT:
			case SUBCLASSING_CONTRACT:
			case LCURLY_VBAR:
			case MODEL_PROGRAM:
			case FORALL:
			case LET:
			case OLD:
			case REQUIRES:
			case PRE:
			case REQUIRES_REDUNDANTLY:
			case PRE_REDUNDANTLY:
			case WHEN:
			case WHEN_REDUNDANTLY:
			case MEASURED_BY:
			case MEASURED_BY_REDUNDANTLY:
			case ASSIGNABLE:
			case MODIFIABLE:
			case MODIFIES:
			case ASSIGNABLE_REDUNDANTLY:
			case MODIFIABLE_REDUNDANTLY:
			case MODIFIES_REDUNDANTLY:
			case ENSURES:
			case POST:
			case ENSURES_REDUNDANTLY:
			case POST_REDUNDANTLY:
			case SIGNALS:
			case SIGNALS_REDUNDANTLY:
			case EXSURES:
			case EXSURES_REDUNDANTLY:
			case DIVERGES:
			case DIVERGES_REDUNDANTLY:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			{
				doc_comments();
				d_AST = (AST)returnAST;
				astFactory.addASTChild(currentAST, returnAST);
				{
				if ((LA(1)==LITERAL_static) && (LA(2)==LCURLY)) {
					st = LT(1);
					st_AST = astFactory.create(st);
					astFactory.addASTChild(currentAST, st_AST);
					match(LITERAL_static);
					compound_statement(in_model_prog);
					astFactory.addASTChild(currentAST, returnAST);
					if ( inputState.guessing==0 ) {
						field_AST = (AST)currentAST.root;
						field_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(INIT,"class-init")).add(field_AST));
						if (in_spec) {
						reportError("static initializers are not allowed in JML specification expressions",
						st.getLine(), st.getColumn());
						}
						
						currentAST.root = field_AST;
						currentAST.child = field_AST!=null &&field_AST.getFirstChild()!=null ?
							field_AST.getFirstChild() : field_AST;
						currentAST.advanceChildToEnd();
					}
				}
				else if ((LA(1)==LCURLY)) {
					compound_statement(in_model_prog);
					ii_AST = (AST)returnAST;
					astFactory.addASTChild(currentAST, returnAST);
					if ( inputState.guessing==0 ) {
						field_AST = (AST)currentAST.root;
						field_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(INSTANCE_INIT,"instance-init")).add(field_AST));
						if (in_spec) {
						reportError("instance initializers are not allowed in JML specification expressions",
						((LineAST)ii_AST).line, ((LineAST)ii_AST).column);
						}
						
						currentAST.root = field_AST;
						currentAST.child = field_AST!=null &&field_AST.getFirstChild()!=null ?
							field_AST.getFirstChild() : field_AST;
						currentAST.advanceChildToEnd();
					}
				}
				else if ((_tokenSet_10.member(LA(1))) && (_tokenSet_11.member(LA(2)))) {
					modifiers();
					mods_AST = (AST)returnAST;
					astFactory.addASTChild(currentAST, returnAST);
					if ( inputState.guessing==0 ) {
						
						if (mods_AST instanceof LineAST) {
						ms = ((MTypeAttrib)((LineAST)mods_AST).type).getModifiers();
						in_spec = in_spec || ms.has(Modifier.MODEL)
						|| ms.has(Modifier.GHOST);
						}
						
					}
					{
					if ((_tokenSet_12.member(LA(1))) && (_tokenSet_13.member(LA(2)))) {
						member_decl(in_spec, in_model_prog);
						astFactory.addASTChild(currentAST, returnAST);
					}
					else if ((_tokenSet_14.member(LA(1))) && (_tokenSet_15.member(LA(2)))) {
						method_spec_first_decl(mods_AST, in_model_prog);
						msfd_AST = (AST)returnAST;
						astFactory.addASTChild(currentAST, returnAST);
						if ( inputState.guessing==0 ) {
							field_AST = (AST)currentAST.root;
							
							if (d_AST != null) {
							field_AST = d_AST;
							field_AST.setNextSibling(msfd_AST);
							} else {
							field_AST = msfd_AST;
							}
							
							currentAST.root = field_AST;
							currentAST.child = field_AST!=null &&field_AST.getFirstChild()!=null ?
								field_AST.getFirstChild() : field_AST;
							currentAST.advanceChildToEnd();
						}
					}
					else if ((_tokenSet_16.member(LA(1)))) {
						jml_declaration();
						astFactory.addASTChild(currentAST, returnAST);
					}
					else {
						throw new NoViableAltException(LT(1), getFilename());
					}
					
					}
				}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				
				}
				break;
			}
			case AXIOM:
			{
				axiom_pragma();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case SEMI:
			{
				AST tmp73_AST = null;
				tmp73_AST = astFactory.create(LT(1));
				match(SEMI);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				
				/*LB
					    JmlTreeSurgery ts = new JmlTreeSurgery();
				ts.currentFile = currentFile;
				ts.mergeJmlDocSpecs((LineAST) #field);
					LB*/
				
			}
			field_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				System.err.print("skipping:\n   ");
				Token lastToken = null;
				int tokenCount = 0;
				int column = 3;
				String tokenLexeme;
				
				while (LA(1) != EOF && LA(1) != LCURLY && LA(1) != RCURLY  
				&& LA(1) != LITERAL_class && LA(1) != LITERAL_interface
				&& LA(1) != INVARIANT && LA(1) != CONSTRAINT
				&& LA(1) != DEPENDS && LA(1) != REPRESENTS
				&& LA(1) != INVARIANT_REDUNDANTLY
				&& LA(1) != CONSTRAINT_REDUNDANTLY
				&& LA(1) != DEPENDS_REDUNDANTLY
				&& LA(1) != REPRESENTS_REDUNDANTLY
				) 
				{
				if (tokenCount < 20) {
				tokenLexeme = LT(1).getText();
				column = column + tokenLexeme.length() + 1;
				if (column > 70) {
				column = tokenLexeme.length() + 4;
				System.err.print("\n   ");
				}
				System.err.print(" " + tokenLexeme);
				tokenCount++;
				} else {
				lastToken = LT(1);
				}
				consume();
				}
				if (lastToken != null) {
				System.err.print("\n    ... through ");
				System.err.print(lastToken.getText()
				+ " on line: " + lastToken.getLine());
				}
				
				System.err.println();
				
			} else {
				throw err;
			}
		}
		returnAST = field_AST;
	}
	
	public final void interface_extends() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST interface_extends_AST = null;
		
		AST tmp74_AST = null;
		tmp74_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp74_AST);
		match(LITERAL_extends);
		name_weakly_list();
		astFactory.addASTChild(currentAST, returnAST);
		interface_extends_AST = (AST)currentAST.root;
		returnAST = interface_extends_AST;
	}
	
	public final void name_weakly_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST name_weakly_list_AST = null;
		
		name();
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case WEAKLY:
		{
			AST tmp75_AST = null;
			tmp75_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp75_AST);
			match(WEAKLY);
			break;
		}
		case LCURLY:
		case COMMA:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		_loop61:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp76_AST = null;
				tmp76_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp76_AST);
				match(COMMA);
				name();
				astFactory.addASTChild(currentAST, returnAST);
				{
				switch ( LA(1)) {
				case WEAKLY:
				{
					AST tmp77_AST = null;
					tmp77_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp77_AST);
					match(WEAKLY);
					break;
				}
				case LCURLY:
				case COMMA:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
			}
			else {
				break _loop61;
			}
			
		} while (true);
		}
		name_weakly_list_AST = (AST)currentAST.root;
		returnAST = name_weakly_list_AST;
	}
	
	public final void doc_comments() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST doc_comments_AST = null;
		
		{
		_loop64:
		do {
			if ((LA(1)==DOC_COMMENT)) {
				doc_comment();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop64;
			}
			
		} while (true);
		}
		doc_comments_AST = (AST)currentAST.root;
		returnAST = doc_comments_AST;
	}
	
	public final void compound_statement(
		boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST compound_statement_AST = null;
		
		AST tmp78_AST = null;
		tmp78_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp78_AST);
		match(LCURLY);
		{
		_loop413:
		do {
			if ((_tokenSet_17.member(LA(1)))) {
				statement(in_model_prog);
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop413;
			}
			
		} while (true);
		}
		AST tmp79_AST = null;
		tmp79_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp79_AST);
		match(RCURLY);
		compound_statement_AST = (AST)currentAST.root;
		returnAST = compound_statement_AST;
	}
	
	public final void member_decl(
		boolean in_spec, boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST member_decl_AST = null;
		
		switch ( LA(1)) {
		case LITERAL_class:
		{
			class_definition(in_model_prog);
			astFactory.addASTChild(currentAST, returnAST);
			member_decl_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_interface:
		{
			interface_definition();
			astFactory.addASTChild(currentAST, returnAST);
			member_decl_AST = (AST)currentAST.root;
			break;
		}
		default:
			boolean synPredMatched71 = false;
			if (((_tokenSet_18.member(LA(1))) && (_tokenSet_19.member(LA(2))))) {
				int _m71 = mark();
				synPredMatched71 = true;
				inputState.guessing++;
				try {
					{
					variable_decls(in_spec);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched71 = false;
				}
				rewind(_m71);
				inputState.guessing--;
			}
			if ( synPredMatched71 ) {
				variable_decls(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
				match(SEMI);
				member_decl_AST = (AST)currentAST.root;
			}
			else if ((_tokenSet_18.member(LA(1))) && (_tokenSet_13.member(LA(2)))) {
				method_decl(in_model_prog);
				astFactory.addASTChild(currentAST, returnAST);
				member_decl_AST = (AST)currentAST.root;
			}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = member_decl_AST;
	}
	
	public final void method_spec_first_decl(
		AST m, boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST method_spec_first_decl_AST = null;
		AST ms_AST = null;
		Token  si = null;
		AST si_AST = null;
		Token  init = null;
		AST init_AST = null;
		AST c1_AST = null;
		AST c2_AST = null;
		AST mods_AST = null;
		AST ts_AST = null;
		AST mh_AST = null;
		AST mb_AST = null;
		AST cmh_AST = null;
		AST cmb_AST = null;
		
		method_specification(m);
		ms_AST = (AST)returnAST;
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case STATIC_INITIALIZER:
		{
			si = LT(1);
			si_AST = astFactory.create(si);
			astFactory.addASTChild(currentAST, si_AST);
			match(STATIC_INITIALIZER);
			if ( inputState.guessing==0 ) {
				method_spec_first_decl_AST = (AST)currentAST.root;
				method_spec_first_decl_AST = (AST)astFactory.make( (new ASTArray(2)).add(si_AST).add(ms_AST));
				currentAST.root = method_spec_first_decl_AST;
				currentAST.child = method_spec_first_decl_AST!=null &&method_spec_first_decl_AST.getFirstChild()!=null ?
					method_spec_first_decl_AST.getFirstChild() : method_spec_first_decl_AST;
				currentAST.advanceChildToEnd();
			}
			break;
		}
		case INITIALIZER:
		{
			init = LT(1);
			init_AST = astFactory.create(init);
			astFactory.addASTChild(currentAST, init_AST);
			match(INITIALIZER);
			if ( inputState.guessing==0 ) {
				method_spec_first_decl_AST = (AST)currentAST.root;
				method_spec_first_decl_AST = (AST)astFactory.make( (new ASTArray(2)).add(init_AST).add(ms_AST));
				currentAST.root = method_spec_first_decl_AST;
				currentAST.child = method_spec_first_decl_AST!=null &&method_spec_first_decl_AST.getFirstChild()!=null ?
					method_spec_first_decl_AST.getFirstChild() : method_spec_first_decl_AST;
				currentAST.advanceChildToEnd();
			}
			break;
		}
		case LCURLY:
		{
			compound_statement(in_model_prog);
			c2_AST = (AST)returnAST;
			if ( inputState.guessing==0 ) {
				method_spec_first_decl_AST = (AST)currentAST.root;
				method_spec_first_decl_AST =
				(AST)astFactory.make( (new ASTArray(3)).add(astFactory.create(INSTANCE_INIT,"instance-init")).add(ms_AST).add(c2_AST));
				
				currentAST.root = method_spec_first_decl_AST;
				currentAST.child = method_spec_first_decl_AST!=null &&method_spec_first_decl_AST.getFirstChild()!=null ?
					method_spec_first_decl_AST.getFirstChild() : method_spec_first_decl_AST;
				currentAST.advanceChildToEnd();
			}
			break;
		}
		default:
			if ((LA(1)==LITERAL_static) && (LA(2)==LCURLY)) {
				match(LITERAL_static);
				compound_statement(in_model_prog);
				c1_AST = (AST)returnAST;
				if ( inputState.guessing==0 ) {
					method_spec_first_decl_AST = (AST)currentAST.root;
					method_spec_first_decl_AST =
					(AST)astFactory.make( (new ASTArray(4)).add(astFactory.create(INIT,"class-init")).add(ms_AST).add(astFactory.create(LITERAL_static,"static")).add(c1_AST));
					
					currentAST.root = method_spec_first_decl_AST;
					currentAST.child = method_spec_first_decl_AST!=null &&method_spec_first_decl_AST.getFirstChild()!=null ?
						method_spec_first_decl_AST.getFirstChild() : method_spec_first_decl_AST;
					currentAST.advanceChildToEnd();
				}
			}
			else if ((_tokenSet_20.member(LA(1))) && (_tokenSet_21.member(LA(2)))) {
				modifiers();
				mods_AST = (AST)returnAST;
				{
				if ((_tokenSet_18.member(LA(1))) && (_tokenSet_19.member(LA(2)))) {
					type_spec();
					ts_AST = (AST)returnAST;
					method_head();
					mh_AST = (AST)returnAST;
					method_body(in_model_prog);
					mb_AST = (AST)returnAST;
					if ( inputState.guessing==0 ) {
						method_spec_first_decl_AST = (AST)currentAST.root;
						
						if( mods_AST != null )
						{
						method_spec_first_decl_AST = mods_AST;
						method_spec_first_decl_AST.setNextSibling(
						(AST)astFactory.make( (new ASTArray(5)).add(astFactory.create(METH,"#meth#")).add(ts_AST).add(mh_AST).add(ms_AST).add(mb_AST)) );
						} else {
						method_spec_first_decl_AST =
						(AST)astFactory.make( (new ASTArray(5)).add(astFactory.create(METH,"#meth#")).add(ts_AST).add(mh_AST).add(ms_AST).add(mb_AST));
						}
						
						currentAST.root = method_spec_first_decl_AST;
						currentAST.child = method_spec_first_decl_AST!=null &&method_spec_first_decl_AST.getFirstChild()!=null ?
							method_spec_first_decl_AST.getFirstChild() : method_spec_first_decl_AST;
						currentAST.advanceChildToEnd();
					}
				}
				else if ((LA(1)==IDENT) && (LA(2)==LPAREN)) {
					method_head();
					cmh_AST = (AST)returnAST;
					method_body(in_model_prog);
					cmb_AST = (AST)returnAST;
					if ( inputState.guessing==0 ) {
						method_spec_first_decl_AST = (AST)currentAST.root;
						
						if( mods_AST != null )
						{
						method_spec_first_decl_AST = mods_AST;
						method_spec_first_decl_AST.setNextSibling(
						(AST)astFactory.make( (new ASTArray(4)).add(astFactory.create(CONSTRUCTOR,"#constr#")).add(cmh_AST).add(ms_AST).add(cmb_AST)) );
						} else {
						method_spec_first_decl_AST =
						(AST)astFactory.make( (new ASTArray(4)).add(astFactory.create(CONSTRUCTOR,"#constr#")).add(cmh_AST).add(ms_AST).add(cmb_AST));
						}
						
						currentAST.root = method_spec_first_decl_AST;
						currentAST.child = method_spec_first_decl_AST!=null &&method_spec_first_decl_AST.getFirstChild()!=null ?
							method_spec_first_decl_AST.getFirstChild() : method_spec_first_decl_AST;
						currentAST.advanceChildToEnd();
					}
				}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				
				}
			}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		method_spec_first_decl_AST = (AST)currentAST.root;
		returnAST = method_spec_first_decl_AST;
	}
	
	public final void jml_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST jml_declaration_AST = null;
		
		switch ( LA(1)) {
		case INVARIANT:
		case INVARIANT_REDUNDANTLY:
		{
			invariant();
			astFactory.addASTChild(currentAST, returnAST);
			jml_declaration_AST = (AST)currentAST.root;
			break;
		}
		case CONSTRAINT:
		case CONSTRAINT_REDUNDANTLY:
		{
			history_constraint();
			astFactory.addASTChild(currentAST, returnAST);
			jml_declaration_AST = (AST)currentAST.root;
			break;
		}
		case DEPENDS:
		case DEPENDS_REDUNDANTLY:
		{
			depends_decl();
			astFactory.addASTChild(currentAST, returnAST);
			jml_declaration_AST = (AST)currentAST.root;
			break;
		}
		case REPRESENTS:
		case REPRESENTS_REDUNDANTLY:
		{
			represents_decl();
			astFactory.addASTChild(currentAST, returnAST);
			jml_declaration_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = jml_declaration_AST;
	}
	
	public final void axiom_pragma() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST axiom_pragma_AST = null;
		
		AST tmp82_AST = null;
		tmp82_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp82_AST);
		match(AXIOM);
		predicate();
		astFactory.addASTChild(currentAST, returnAST);
		match(SEMI);
		axiom_pragma_AST = (AST)currentAST.root;
		returnAST = axiom_pragma_AST;
	}
	
	public final void variable_decls(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST variable_decls_AST = null;
		
		type_spec();
		astFactory.addASTChild(currentAST, returnAST);
		variable_declarators(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case INITIALLY:
		case READABLE_IF:
		case MONITORED_BY:
		{
			jml_var_assertion();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			variable_decls_AST = (AST)currentAST.root;
			variable_decls_AST = 
			(AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(VAR_DECL,"#vardecl#")).add(variable_decls_AST));
			currentAST.root = variable_decls_AST;
			currentAST.child = variable_decls_AST!=null &&variable_decls_AST.getFirstChild()!=null ?
				variable_decls_AST.getFirstChild() : variable_decls_AST;
			currentAST.advanceChildToEnd();
		}
		variable_decls_AST = (AST)currentAST.root;
		returnAST = variable_decls_AST;
	}
	
	public final void method_decl(
		boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST method_decl_AST = null;
		AST ts_AST = null;
		AST mh_AST = null;
		AST mods_AST = null;
		AST ms_AST = null;
		AST mb_AST = null;
		AST ch_AST = null;
		AST cm_AST = null;
		AST cms_AST = null;
		AST cmb_AST = null;
		
		if ((_tokenSet_18.member(LA(1))) && (_tokenSet_19.member(LA(2)))) {
			type_spec();
			ts_AST = (AST)returnAST;
			method_head();
			mh_AST = (AST)returnAST;
			{
			switch ( LA(1)) {
			case MODEL:
			case IDENT:
			case LITERAL_private:
			case LITERAL_public:
			case LITERAL_protected:
			case LITERAL_static:
			case LITERAL_transient:
			case LITERAL_final:
			case LITERAL_abstract:
			case LITERAL_native:
			case LITERAL_synchronized:
			case LITERAL_const:
			case LITERAL_volatile:
			case LITERAL_strictfp:
			case PURE:
			case INSTANCE:
			case SPEC_PUBLIC:
			case SPEC_PROTECTED:
			case MONITORED:
			case UNINITIALIZED:
			case GHOST:
			case NON_NULL:
			case ALSO:
			case AND:
			case BEHAVIOR:
			case EXCEPTIONAL_BEHAVIOR:
			case NORMAL_BEHAVIOR:
			case FOR_EXAMPLE:
			case IMPLIES_THAT:
			case SUBCLASSING_CONTRACT:
			case LCURLY_VBAR:
			case MODEL_PROGRAM:
			case FORALL:
			case LET:
			case OLD:
			case REQUIRES:
			case PRE:
			case REQUIRES_REDUNDANTLY:
			case PRE_REDUNDANTLY:
			case WHEN:
			case WHEN_REDUNDANTLY:
			case MEASURED_BY:
			case MEASURED_BY_REDUNDANTLY:
			case ASSIGNABLE:
			case MODIFIABLE:
			case MODIFIES:
			case ASSIGNABLE_REDUNDANTLY:
			case MODIFIABLE_REDUNDANTLY:
			case MODIFIES_REDUNDANTLY:
			case ENSURES:
			case POST:
			case ENSURES_REDUNDANTLY:
			case POST_REDUNDANTLY:
			case SIGNALS:
			case SIGNALS_REDUNDANTLY:
			case EXSURES:
			case EXSURES_REDUNDANTLY:
			case DIVERGES:
			case DIVERGES_REDUNDANTLY:
			{
				modifiers();
				mods_AST = (AST)returnAST;
				method_specification(mods_AST);
				ms_AST = (AST)returnAST;
				break;
			}
			case SEMI:
			case LCURLY:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			method_body(in_model_prog);
			mb_AST = (AST)returnAST;
			if ( inputState.guessing==0 ) {
				method_decl_AST = (AST)currentAST.root;
				
				method_decl_AST =
				(AST)astFactory.make( (new ASTArray(5)).add(astFactory.create(METH,"#meth#")).add(ts_AST).add(mh_AST).add(ms_AST).add(mb_AST));
				
				currentAST.root = method_decl_AST;
				currentAST.child = method_decl_AST!=null &&method_decl_AST.getFirstChild()!=null ?
					method_decl_AST.getFirstChild() : method_decl_AST;
				currentAST.advanceChildToEnd();
			}
		}
		else if ((LA(1)==IDENT) && (LA(2)==LPAREN)) {
			method_head();
			ch_AST = (AST)returnAST;
			{
			switch ( LA(1)) {
			case MODEL:
			case IDENT:
			case LITERAL_private:
			case LITERAL_public:
			case LITERAL_protected:
			case LITERAL_static:
			case LITERAL_transient:
			case LITERAL_final:
			case LITERAL_abstract:
			case LITERAL_native:
			case LITERAL_synchronized:
			case LITERAL_const:
			case LITERAL_volatile:
			case LITERAL_strictfp:
			case PURE:
			case INSTANCE:
			case SPEC_PUBLIC:
			case SPEC_PROTECTED:
			case MONITORED:
			case UNINITIALIZED:
			case GHOST:
			case NON_NULL:
			case ALSO:
			case AND:
			case BEHAVIOR:
			case EXCEPTIONAL_BEHAVIOR:
			case NORMAL_BEHAVIOR:
			case FOR_EXAMPLE:
			case IMPLIES_THAT:
			case SUBCLASSING_CONTRACT:
			case LCURLY_VBAR:
			case MODEL_PROGRAM:
			case FORALL:
			case LET:
			case OLD:
			case REQUIRES:
			case PRE:
			case REQUIRES_REDUNDANTLY:
			case PRE_REDUNDANTLY:
			case WHEN:
			case WHEN_REDUNDANTLY:
			case MEASURED_BY:
			case MEASURED_BY_REDUNDANTLY:
			case ASSIGNABLE:
			case MODIFIABLE:
			case MODIFIES:
			case ASSIGNABLE_REDUNDANTLY:
			case MODIFIABLE_REDUNDANTLY:
			case MODIFIES_REDUNDANTLY:
			case ENSURES:
			case POST:
			case ENSURES_REDUNDANTLY:
			case POST_REDUNDANTLY:
			case SIGNALS:
			case SIGNALS_REDUNDANTLY:
			case EXSURES:
			case EXSURES_REDUNDANTLY:
			case DIVERGES:
			case DIVERGES_REDUNDANTLY:
			{
				modifiers();
				cm_AST = (AST)returnAST;
				method_specification(cm_AST);
				cms_AST = (AST)returnAST;
				break;
			}
			case SEMI:
			case LCURLY:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			method_body(in_model_prog);
			cmb_AST = (AST)returnAST;
			if ( inputState.guessing==0 ) {
				method_decl_AST = (AST)currentAST.root;
				
				method_decl_AST =
				(AST)astFactory.make( (new ASTArray(4)).add(astFactory.create(CONSTRUCTOR,"#constr#")).add(ch_AST).add(cms_AST).add(cmb_AST));
				
				currentAST.root = method_decl_AST;
				currentAST.child = method_decl_AST!=null &&method_decl_AST.getFirstChild()!=null ?
					method_decl_AST.getFirstChild() : method_decl_AST;
				currentAST.advanceChildToEnd();
			}
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		returnAST = method_decl_AST;
	}
	
	public final void variable_declarators(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST variable_declarators_AST = null;
		
		variable_declarator(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop97:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp84_AST = null;
				tmp84_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp84_AST);
				match(COMMA);
				variable_declarator(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop97;
			}
			
		} while (true);
		}
		variable_declarators_AST = (AST)currentAST.root;
		returnAST = variable_declarators_AST;
	}
	
	public final void jml_var_assertion() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST jml_var_assertion_AST = null;
		
		switch ( LA(1)) {
		case INITIALLY:
		case READABLE_IF:
		{
			{
			switch ( LA(1)) {
			case INITIALLY:
			{
				AST tmp85_AST = null;
				tmp85_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp85_AST);
				match(INITIALLY);
				break;
			}
			case READABLE_IF:
			{
				AST tmp86_AST = null;
				tmp86_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp86_AST);
				match(READABLE_IF);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			predicate();
			astFactory.addASTChild(currentAST, returnAST);
			jml_var_assertion_AST = (AST)currentAST.root;
			break;
		}
		case MONITORED_BY:
		{
			monitored_by_clause();
			astFactory.addASTChild(currentAST, returnAST);
			jml_var_assertion_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = jml_var_assertion_AST;
	}
	
	public final void method_head() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST method_head_AST = null;
		
		AST tmp87_AST = null;
		tmp87_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp87_AST);
		match(IDENT);
		match(LPAREN);
		{
		switch ( LA(1)) {
		case IDENT:
		case T_TYPEOFALLTYPES:
		case LITERAL_final:
		case LITERAL_void:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_short:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_float:
		case LITERAL_double:
		{
			param_declaration_list();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case RPAREN:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(RPAREN);
		{
		switch ( LA(1)) {
		case LBRACK:
		{
			dims();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case MODEL:
		case SEMI:
		case IDENT:
		case LITERAL_private:
		case LITERAL_public:
		case LITERAL_protected:
		case LITERAL_static:
		case LITERAL_transient:
		case LITERAL_final:
		case LITERAL_abstract:
		case LITERAL_native:
		case LITERAL_synchronized:
		case LITERAL_const:
		case LITERAL_volatile:
		case LITERAL_strictfp:
		case LCURLY:
		case LITERAL_throws:
		case PURE:
		case INSTANCE:
		case SPEC_PUBLIC:
		case SPEC_PROTECTED:
		case MONITORED:
		case UNINITIALIZED:
		case GHOST:
		case NON_NULL:
		case ALSO:
		case AND:
		case BEHAVIOR:
		case EXCEPTIONAL_BEHAVIOR:
		case NORMAL_BEHAVIOR:
		case FOR_EXAMPLE:
		case IMPLIES_THAT:
		case SUBCLASSING_CONTRACT:
		case LCURLY_VBAR:
		case MODEL_PROGRAM:
		case FORALL:
		case LET:
		case OLD:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case WHEN:
		case WHEN_REDUNDANTLY:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case LITERAL_throws:
		{
			throws_clause();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case MODEL:
		case SEMI:
		case IDENT:
		case LITERAL_private:
		case LITERAL_public:
		case LITERAL_protected:
		case LITERAL_static:
		case LITERAL_transient:
		case LITERAL_final:
		case LITERAL_abstract:
		case LITERAL_native:
		case LITERAL_synchronized:
		case LITERAL_const:
		case LITERAL_volatile:
		case LITERAL_strictfp:
		case LCURLY:
		case PURE:
		case INSTANCE:
		case SPEC_PUBLIC:
		case SPEC_PROTECTED:
		case MONITORED:
		case UNINITIALIZED:
		case GHOST:
		case NON_NULL:
		case ALSO:
		case AND:
		case BEHAVIOR:
		case EXCEPTIONAL_BEHAVIOR:
		case NORMAL_BEHAVIOR:
		case FOR_EXAMPLE:
		case IMPLIES_THAT:
		case SUBCLASSING_CONTRACT:
		case LCURLY_VBAR:
		case MODEL_PROGRAM:
		case FORALL:
		case LET:
		case OLD:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case WHEN:
		case WHEN_REDUNDANTLY:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		method_head_AST = (AST)currentAST.root;
		returnAST = method_head_AST;
	}
	
	public final void method_specification(
		AST mods
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST method_specification_AST = null;
		//line = annotStartLine;
		
		switch ( LA(1)) {
		case IDENT:
		case BEHAVIOR:
		case EXCEPTIONAL_BEHAVIOR:
		case NORMAL_BEHAVIOR:
		case FOR_EXAMPLE:
		case IMPLIES_THAT:
		case SUBCLASSING_CONTRACT:
		case LCURLY_VBAR:
		case MODEL_PROGRAM:
		case FORALL:
		case LET:
		case OLD:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case WHEN:
		case WHEN_REDUNDANTLY:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			specification(mods);
			astFactory.addASTChild(currentAST, returnAST);
			method_specification_AST = (AST)currentAST.root;
			break;
		}
		case ALSO:
		case AND:
		{
			extending_specification();
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				
				if (!(mods == null
				|| ((MTypeAttrib)((LineAST) mods).type)
				.getModifiers().printsEmpty())) {
				reportWarning("can't use a modifier before 'also' or 'and'"
				+ ": " + mods,
				((LineAST)mods).line, ((LineAST)mods).column);
				}
				
			}
			method_specification_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = method_specification_AST;
	}
	
	public final void method_body(
		boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST method_body_AST = null;
		
		switch ( LA(1)) {
		case LCURLY:
		{
			compound_statement(in_model_prog);
			astFactory.addASTChild(currentAST, returnAST);
			method_body_AST = (AST)currentAST.root;
			break;
		}
		case SEMI:
		{
			AST tmp90_AST = null;
			tmp90_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp90_AST);
			match(SEMI);
			method_body_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = method_body_AST;
	}
	
	public final void param_declaration_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST param_declaration_list_AST = null;
		
		param_declaration();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop91:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp91_AST = null;
				tmp91_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp91_AST);
				match(COMMA);
				param_declaration();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop91;
			}
			
		} while (true);
		}
		param_declaration_list_AST = (AST)currentAST.root;
		returnAST = param_declaration_list_AST;
	}
	
	public final void throws_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST throws_clause_AST = null;
		
		AST tmp92_AST = null;
		tmp92_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp92_AST);
		match(LITERAL_throws);
		name_list();
		astFactory.addASTChild(currentAST, returnAST);
		throws_clause_AST = (AST)currentAST.root;
		returnAST = throws_clause_AST;
	}
	
	public final void name_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST name_list_AST = null;
		
		name();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop88:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp93_AST = null;
				tmp93_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp93_AST);
				match(COMMA);
				name();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop88;
			}
			
		} while (true);
		}
		name_list_AST = (AST)currentAST.root;
		returnAST = name_list_AST;
	}
	
	public final void param_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST param_declaration_AST = null;
		
		{
		switch ( LA(1)) {
		case LITERAL_final:
		{
			AST tmp94_AST = null;
			tmp94_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp94_AST);
			match(LITERAL_final);
			break;
		}
		case IDENT:
		case T_TYPEOFALLTYPES:
		case LITERAL_void:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_short:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_float:
		case LITERAL_double:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		type_spec();
		astFactory.addASTChild(currentAST, returnAST);
		AST tmp95_AST = null;
		tmp95_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp95_AST);
		match(IDENT);
		{
		switch ( LA(1)) {
		case LBRACK:
		{
			dims();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case COMMA:
		case RPAREN:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			param_declaration_AST = (AST)currentAST.root;
			param_declaration_AST =
			(AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(PARAM)).add(param_declaration_AST));
			currentAST.root = param_declaration_AST;
			currentAST.child = param_declaration_AST!=null &&param_declaration_AST.getFirstChild()!=null ?
				param_declaration_AST.getFirstChild() : param_declaration_AST;
			currentAST.advanceChildToEnd();
		}
		param_declaration_AST = (AST)currentAST.root;
		returnAST = param_declaration_AST;
	}
	
	public final void variable_declarator(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST variable_declarator_AST = null;
		
		AST tmp96_AST = null;
		tmp96_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp96_AST);
		match(IDENT);
		{
		switch ( LA(1)) {
		case LBRACK:
		{
			dims();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case SEMI:
		case COMMA:
		case ASSIGN:
		case INITIALLY:
		case READABLE_IF:
		case MONITORED_BY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case ASSIGN:
		{
			AST tmp97_AST = null;
			tmp97_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp97_AST);
			match(ASSIGN);
			initializer(in_spec);
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case SEMI:
		case COMMA:
		case INITIALLY:
		case READABLE_IF:
		case MONITORED_BY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		variable_declarator_AST = (AST)currentAST.root;
		returnAST = variable_declarator_AST;
	}
	
	public final void initializer(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST initializer_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		case LPAREN:
		case STRING_LITERAL:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_new:
		case LITERAL_void:
		case PLUS:
		case MINUS:
		case INC:
		case DEC:
		case BNOT:
		case LNOT:
		case LITERAL_true:
		case LITERAL_false:
		case LITERAL_null:
		case T_RESULT:
		case T_OLD:
		case T_NOT_MODIFIED:
		case T_FRESH:
		case T_REACH:
		case T_NONNULLELEMENTS:
		case T_TYPEOF:
		case T_ELEMTYPE:
		case T_TYPE:
		case T_LOCKSET:
		case T_IS_INITIALIZED:
		case T_INVARIANT_FOR:
		case INFORMAL_DESCRIPTION:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_short:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_float:
		case LITERAL_double:
		case NUM_INT:
		case CHAR_LITERAL:
		case NUM_FLOAT:
		{
			expression(in_spec);
			astFactory.addASTChild(currentAST, returnAST);
			initializer_AST = (AST)currentAST.root;
			break;
		}
		case LCURLY:
		{
			array_initializer(in_spec);
			astFactory.addASTChild(currentAST, returnAST);
			initializer_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = initializer_AST;
	}
	
	public final void expression(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST expression_AST = null;
		
		assignment_expr(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		expression_AST = (AST)currentAST.root;
		returnAST = expression_AST;
	}
	
	public final void array_initializer(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST array_initializer_AST = null;
		
		AST tmp98_AST = null;
		tmp98_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp98_AST);
		match(LCURLY);
		{
		switch ( LA(1)) {
		case IDENT:
		case LCURLY:
		case LPAREN:
		case STRING_LITERAL:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_new:
		case LITERAL_void:
		case PLUS:
		case MINUS:
		case INC:
		case DEC:
		case BNOT:
		case LNOT:
		case LITERAL_true:
		case LITERAL_false:
		case LITERAL_null:
		case T_RESULT:
		case T_OLD:
		case T_NOT_MODIFIED:
		case T_FRESH:
		case T_REACH:
		case T_NONNULLELEMENTS:
		case T_TYPEOF:
		case T_ELEMTYPE:
		case T_TYPE:
		case T_LOCKSET:
		case T_IS_INITIALIZED:
		case T_INVARIANT_FOR:
		case INFORMAL_DESCRIPTION:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_short:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_float:
		case LITERAL_double:
		case NUM_INT:
		case CHAR_LITERAL:
		case NUM_FLOAT:
		{
			initializer_list(in_spec);
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case RCURLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		AST tmp99_AST = null;
		tmp99_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp99_AST);
		match(RCURLY);
		array_initializer_AST = (AST)currentAST.root;
		returnAST = array_initializer_AST;
	}
	
	public final void initializer_list(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST initializer_list_AST = null;
		
		initializer(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop107:
		do {
			if ((LA(1)==COMMA) && (_tokenSet_22.member(LA(2)))) {
				{
				match(COMMA);
				}
				initializer(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop107;
			}
			
		} while (true);
		}
		{
		switch ( LA(1)) {
		case COMMA:
		{
			match(COMMA);
			break;
		}
		case RCURLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		initializer_list_AST = (AST)currentAST.root;
		returnAST = initializer_list_AST;
	}
	
	public final void ident_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST ident_list_AST = null;
		
		AST tmp102_AST = null;
		tmp102_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp102_AST);
		match(IDENT);
		{
		_loop112:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp103_AST = null;
				tmp103_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp103_AST);
				match(COMMA);
				AST tmp104_AST = null;
				tmp104_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp104_AST);
				match(IDENT);
			}
			else {
				break _loop112;
			}
			
		} while (true);
		}
		ident_list_AST = (AST)currentAST.root;
		returnAST = ident_list_AST;
	}
	
	public final void monitored_by_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST monitored_by_clause_AST = null;
		
		AST tmp105_AST = null;
		tmp105_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp105_AST);
		match(MONITORED_BY);
		expression_list(no_side_effects);
		astFactory.addASTChild(currentAST, returnAST);
		monitored_by_clause_AST = (AST)currentAST.root;
		returnAST = monitored_by_clause_AST;
	}
	
	public final void expression_list(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST expression_list_AST = null;
		
		expression(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop540:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp106_AST = null;
				tmp106_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp106_AST);
				match(COMMA);
				expression(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop540;
			}
			
		} while (true);
		}
		expression_list_AST = (AST)currentAST.root;
		returnAST = expression_list_AST;
	}
	
	public final void invariant() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST invariant_AST = null;
		
		{
		switch ( LA(1)) {
		case INVARIANT:
		{
			AST tmp107_AST = null;
			tmp107_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp107_AST);
			match(INVARIANT);
			break;
		}
		case INVARIANT_REDUNDANTLY:
		{
			AST tmp108_AST = null;
			tmp108_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp108_AST);
			match(INVARIANT_REDUNDANTLY);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		predicate();
		astFactory.addASTChild(currentAST, returnAST);
		match(SEMI);
		if ( inputState.guessing==0 ) {
			invariant_AST = (AST)currentAST.root;
			invariant_AST.setType(INVARIANT_KEYWORD);
		}
		invariant_AST = (AST)currentAST.root;
		returnAST = invariant_AST;
	}
	
	public final void history_constraint() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST history_constraint_AST = null;
		
		{
		switch ( LA(1)) {
		case CONSTRAINT:
		{
			AST tmp110_AST = null;
			tmp110_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp110_AST);
			match(CONSTRAINT);
			break;
		}
		case CONSTRAINT_REDUNDANTLY:
		{
			AST tmp111_AST = null;
			tmp111_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp111_AST);
			match(CONSTRAINT_REDUNDANTLY);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		predicate();
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case FOR:
		{
			AST tmp112_AST = null;
			tmp112_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp112_AST);
			match(FOR);
			constrained_list();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			history_constraint_AST = (AST)currentAST.root;
			history_constraint_AST.setType(CONSTRAINT_KEYWORD);
		}
		history_constraint_AST = (AST)currentAST.root;
		returnAST = history_constraint_AST;
	}
	
	public final void depends_decl() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST depends_decl_AST = null;
		
		{
		switch ( LA(1)) {
		case DEPENDS:
		{
			AST tmp114_AST = null;
			tmp114_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp114_AST);
			match(DEPENDS);
			break;
		}
		case DEPENDS_REDUNDANTLY:
		{
			AST tmp115_AST = null;
			tmp115_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp115_AST);
			match(DEPENDS_REDUNDANTLY);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		store_ref();
		astFactory.addASTChild(currentAST, returnAST);
		match(L_ARROW);
		store_references();
		astFactory.addASTChild(currentAST, returnAST);
		match(SEMI);
		if ( inputState.guessing==0 ) {
			depends_decl_AST = (AST)currentAST.root;
			depends_decl_AST.setType(DEPENDS_KEYWORD);
		}
		depends_decl_AST = (AST)currentAST.root;
		returnAST = depends_decl_AST;
	}
	
	public final void represents_decl() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST represents_decl_AST = null;
		
		{
		switch ( LA(1)) {
		case REPRESENTS:
		{
			AST tmp118_AST = null;
			tmp118_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp118_AST);
			match(REPRESENTS);
			break;
		}
		case REPRESENTS_REDUNDANTLY:
		{
			AST tmp119_AST = null;
			tmp119_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp119_AST);
			match(REPRESENTS_REDUNDANTLY);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		represents_expr();
		astFactory.addASTChild(currentAST, returnAST);
		match(SEMI);
		if ( inputState.guessing==0 ) {
			represents_decl_AST = (AST)currentAST.root;
			represents_decl_AST.setType(REPRESENTS_KEYWORD);
		}
		represents_decl_AST = (AST)currentAST.root;
		returnAST = represents_decl_AST;
	}
	
	public final void constrained_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST constrained_list_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		case LITERAL_super:
		case LITERAL_this:
		case T_OTHER:
		case LITERAL_new:
		{
			method_name_list();
			astFactory.addASTChild(currentAST, returnAST);
			constrained_list_AST = (AST)currentAST.root;
			break;
		}
		case T_EVERYTHING:
		{
			AST tmp121_AST = null;
			tmp121_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp121_AST);
			match(T_EVERYTHING);
			constrained_list_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = constrained_list_AST;
	}
	
	public final void method_name_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST method_name_list_AST = null;
		
		method_name();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop127:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp122_AST = null;
				tmp122_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp122_AST);
				match(COMMA);
				method_name();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop127;
			}
			
		} while (true);
		}
		method_name_list_AST = (AST)currentAST.root;
		returnAST = method_name_list_AST;
	}
	
	public final void method_name() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST method_name_AST = null;
		
		method_ref();
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case LPAREN:
		{
			AST tmp123_AST = null;
			tmp123_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp123_AST);
			match(LPAREN);
			{
			switch ( LA(1)) {
			case IDENT:
			case T_TYPEOFALLTYPES:
			case LITERAL_void:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			{
				param_disambig_list();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RPAREN);
			break;
		}
		case SEMI:
		case COMMA:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		method_name_AST = (AST)currentAST.root;
		returnAST = method_name_AST;
	}
	
	public final void method_ref() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST method_ref_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		case LITERAL_super:
		case LITERAL_this:
		case T_OTHER:
		{
			{
			switch ( LA(1)) {
			case LITERAL_super:
			{
				AST tmp125_AST = null;
				tmp125_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp125_AST);
				match(LITERAL_super);
				break;
			}
			case LITERAL_this:
			{
				AST tmp126_AST = null;
				tmp126_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp126_AST);
				match(LITERAL_this);
				break;
			}
			case IDENT:
			{
				AST tmp127_AST = null;
				tmp127_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp127_AST);
				match(IDENT);
				break;
			}
			case T_OTHER:
			{
				AST tmp128_AST = null;
				tmp128_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp128_AST);
				match(T_OTHER);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			_loop134:
			do {
				if ((LA(1)==DOT)) {
					AST tmp129_AST = null;
					tmp129_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp129_AST);
					match(DOT);
					AST tmp130_AST = null;
					tmp130_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp130_AST);
					match(IDENT);
				}
				else {
					break _loop134;
				}
				
			} while (true);
			}
			method_ref_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_new:
		{
			constructor_ref();
			astFactory.addASTChild(currentAST, returnAST);
			method_ref_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = method_ref_AST;
	}
	
	public final void param_disambig_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST param_disambig_list_AST = null;
		
		param_disambig();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop138:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp131_AST = null;
				tmp131_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp131_AST);
				match(COMMA);
				param_disambig();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop138;
			}
			
		} while (true);
		}
		param_disambig_list_AST = (AST)currentAST.root;
		returnAST = param_disambig_list_AST;
	}
	
	public final void constructor_ref() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST constructor_ref_AST = null;
		
		AST tmp132_AST = null;
		tmp132_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp132_AST);
		match(LITERAL_new);
		reference_type();
		astFactory.addASTChild(currentAST, returnAST);
		constructor_ref_AST = (AST)currentAST.root;
		returnAST = constructor_ref_AST;
	}
	
	public final void param_disambig() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST param_disambig_AST = null;
		
		type_spec();
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case IDENT:
		{
			AST tmp133_AST = null;
			tmp133_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp133_AST);
			match(IDENT);
			{
			switch ( LA(1)) {
			case LBRACK:
			{
				dims();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case COMMA:
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		case COMMA:
		case RPAREN:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			param_disambig_AST = (AST)currentAST.root;
			param_disambig_AST = 
			(AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(PARAM)).add(param_disambig_AST));
			currentAST.root = param_disambig_AST;
			currentAST.child = param_disambig_AST!=null &&param_disambig_AST.getFirstChild()!=null ?
				param_disambig_AST.getFirstChild() : param_disambig_AST;
			currentAST.advanceChildToEnd();
		}
		param_disambig_AST = (AST)currentAST.root;
		returnAST = param_disambig_AST;
	}
	
	public final void store_ref() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST store_ref_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		case LITERAL_super:
		case LITERAL_this:
		{
			store_ref_expression();
			astFactory.addASTChild(currentAST, returnAST);
			store_ref_AST = (AST)currentAST.root;
			break;
		}
		case T_FIELDS_OF:
		{
			AST tmp134_AST = null;
			tmp134_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp134_AST);
			match(T_FIELDS_OF);
			match(LPAREN);
			spec_expression();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case COMMA:
			{
				match(COMMA);
				reference_type();
				astFactory.addASTChild(currentAST, returnAST);
				{
				switch ( LA(1)) {
				case COMMA:
				{
					match(COMMA);
					store_ref_expression();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				case RPAREN:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RPAREN);
			store_ref_AST = (AST)currentAST.root;
			break;
		}
		case INFORMAL_DESCRIPTION:
		{
			informal_desc();
			astFactory.addASTChild(currentAST, returnAST);
			store_ref_AST = (AST)currentAST.root;
			break;
		}
		case T_EVERYTHING:
		case T_NOT_SPECIFIED:
		case T_NOTHING:
		{
			store_ref_keyword();
			astFactory.addASTChild(currentAST, returnAST);
			store_ref_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = store_ref_AST;
	}
	
	public final void store_references() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST store_references_AST = null;
		
		store_ref_list();
		astFactory.addASTChild(currentAST, returnAST);
		store_references_AST = (AST)currentAST.root;
		returnAST = store_references_AST;
	}
	
	public final void represents_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST represents_expr_AST = null;
		
		store_ref();
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case T_SUCH_THAT:
		{
			AST tmp139_AST = null;
			tmp139_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp139_AST);
			match(T_SUCH_THAT);
			predicate();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case L_ARROW:
		{
			AST tmp140_AST = null;
			tmp140_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp140_AST);
			match(L_ARROW);
			spec_expression();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		represents_expr_AST = (AST)currentAST.root;
		returnAST = represents_expr_AST;
	}
	
	public final void spec_expression() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST spec_expression_AST = null;
		
		expression(no_side_effects);
		astFactory.addASTChild(currentAST, returnAST);
		spec_expression_AST = (AST)currentAST.root;
		returnAST = spec_expression_AST;
	}
	
	public final void method_specification_opt(
		AST mods
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST method_specification_opt_AST = null;
		
		switch ( LA(1)) {
		case LITERAL_void:
		{
			match(LITERAL_void);
			if ( inputState.guessing==0 ) {
				method_specification_opt_AST = (AST)currentAST.root;
				method_specification_opt_AST = null;
				currentAST.root = method_specification_opt_AST;
				currentAST.child = method_specification_opt_AST!=null &&method_specification_opt_AST.getFirstChild()!=null ?
					method_specification_opt_AST.getFirstChild() : method_specification_opt_AST;
				currentAST.advanceChildToEnd();
			}
			break;
		}
		case IDENT:
		case ALSO:
		case AND:
		case BEHAVIOR:
		case EXCEPTIONAL_BEHAVIOR:
		case NORMAL_BEHAVIOR:
		case FOR_EXAMPLE:
		case IMPLIES_THAT:
		case SUBCLASSING_CONTRACT:
		case LCURLY_VBAR:
		case MODEL_PROGRAM:
		case FORALL:
		case LET:
		case OLD:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case WHEN:
		case WHEN_REDUNDANTLY:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			method_specification(mods);
			astFactory.addASTChild(currentAST, returnAST);
			method_specification_opt_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = method_specification_opt_AST;
	}
	
	public final void specification(
		AST mods
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST specification_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		case BEHAVIOR:
		case EXCEPTIONAL_BEHAVIOR:
		case NORMAL_BEHAVIOR:
		case LCURLY_VBAR:
		case MODEL_PROGRAM:
		case FORALL:
		case LET:
		case OLD:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case WHEN:
		case WHEN_REDUNDANTLY:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			initial_spec_case_seq(mods);
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case SUBCLASSING_CONTRACT:
			{
				subclassing_contract();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case EOF:
			case MODEL:
			case SEMI:
			case IDENT:
			case T_TYPEOFALLTYPES:
			case LITERAL_private:
			case LITERAL_public:
			case LITERAL_protected:
			case LITERAL_static:
			case LITERAL_transient:
			case LITERAL_final:
			case LITERAL_abstract:
			case LITERAL_native:
			case LITERAL_synchronized:
			case LITERAL_const:
			case LITERAL_volatile:
			case LITERAL_strictfp:
			case LCURLY:
			case STATIC_INITIALIZER:
			case INITIALIZER:
			case PURE:
			case INSTANCE:
			case SPEC_PUBLIC:
			case SPEC_PROTECTED:
			case MONITORED:
			case UNINITIALIZED:
			case GHOST:
			case NON_NULL:
			case LITERAL_void:
			case FOR_EXAMPLE:
			case IMPLIES_THAT:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case FOR_EXAMPLE:
			case IMPLIES_THAT:
			{
				redundant_spec();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case EOF:
			case MODEL:
			case SEMI:
			case IDENT:
			case T_TYPEOFALLTYPES:
			case LITERAL_private:
			case LITERAL_public:
			case LITERAL_protected:
			case LITERAL_static:
			case LITERAL_transient:
			case LITERAL_final:
			case LITERAL_abstract:
			case LITERAL_native:
			case LITERAL_synchronized:
			case LITERAL_const:
			case LITERAL_volatile:
			case LITERAL_strictfp:
			case LCURLY:
			case STATIC_INITIALIZER:
			case INITIALIZER:
			case PURE:
			case INSTANCE:
			case SPEC_PUBLIC:
			case SPEC_PROTECTED:
			case MONITORED:
			case UNINITIALIZED:
			case GHOST:
			case NON_NULL:
			case LITERAL_void:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			specification_AST = (AST)currentAST.root;
			break;
		}
		case SUBCLASSING_CONTRACT:
		{
			subclassing_contract();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case FOR_EXAMPLE:
			case IMPLIES_THAT:
			{
				redundant_spec();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case EOF:
			case MODEL:
			case SEMI:
			case IDENT:
			case T_TYPEOFALLTYPES:
			case LITERAL_private:
			case LITERAL_public:
			case LITERAL_protected:
			case LITERAL_static:
			case LITERAL_transient:
			case LITERAL_final:
			case LITERAL_abstract:
			case LITERAL_native:
			case LITERAL_synchronized:
			case LITERAL_const:
			case LITERAL_volatile:
			case LITERAL_strictfp:
			case LCURLY:
			case STATIC_INITIALIZER:
			case INITIALIZER:
			case PURE:
			case INSTANCE:
			case SPEC_PUBLIC:
			case SPEC_PROTECTED:
			case MONITORED:
			case UNINITIALIZED:
			case GHOST:
			case NON_NULL:
			case LITERAL_void:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				
				if (!(mods == null
				|| ((MTypeAttrib)((LineAST) mods).type)
				.getModifiers().printsEmpty())) {
				reportWarning("can't use a modifier before 'subclassing_contract'"
				+ ": " + mods,
				((LineAST)mods).line, ((LineAST)mods).column);
				}
				
			}
			specification_AST = (AST)currentAST.root;
			break;
		}
		case FOR_EXAMPLE:
		case IMPLIES_THAT:
		{
			redundant_spec();
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				
				if (!(mods == null
				|| ((MTypeAttrib)((LineAST) mods).type)
				.getModifiers().printsEmpty())) {
				reportWarning("can't use a modifier before 'implies_that'"
				+ ": " + mods,
				((LineAST)mods).line, ((LineAST)mods).column);
				}
				
			}
			specification_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = specification_AST;
	}
	
	public final void extending_specification() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST extending_specification_AST = null;
		AST m_AST = null;
		AST sp_AST = null;
		
		switch ( LA(1)) {
		case ALSO:
		{
			AST tmp142_AST = null;
			tmp142_AST = astFactory.create(LT(1));
			match(ALSO);
			modifiers();
			m_AST = (AST)returnAST;
			specification(m_AST);
			sp_AST = (AST)returnAST;
			if ( inputState.guessing==0 ) {
				extending_specification_AST = (AST)currentAST.root;
				extending_specification_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(EXT_ALSO,"EXT_also")).add(sp_AST));
				currentAST.root = extending_specification_AST;
				currentAST.child = extending_specification_AST!=null &&extending_specification_AST.getFirstChild()!=null ?
					extending_specification_AST.getFirstChild() : extending_specification_AST;
				currentAST.advanceChildToEnd();
			}
			break;
		}
		case AND:
		{
			match(AND);
			conjoinable_spec_seq();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case ALSO:
			{
				AST tmp144_AST = null;
				tmp144_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp144_AST);
				match(ALSO);
				spec_case_seq();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case EOF:
			case MODEL:
			case SEMI:
			case IDENT:
			case T_TYPEOFALLTYPES:
			case LITERAL_private:
			case LITERAL_public:
			case LITERAL_protected:
			case LITERAL_static:
			case LITERAL_transient:
			case LITERAL_final:
			case LITERAL_abstract:
			case LITERAL_native:
			case LITERAL_synchronized:
			case LITERAL_const:
			case LITERAL_volatile:
			case LITERAL_strictfp:
			case LCURLY:
			case STATIC_INITIALIZER:
			case INITIALIZER:
			case PURE:
			case INSTANCE:
			case SPEC_PUBLIC:
			case SPEC_PROTECTED:
			case MONITORED:
			case UNINITIALIZED:
			case GHOST:
			case NON_NULL:
			case LITERAL_void:
			case FOR_EXAMPLE:
			case IMPLIES_THAT:
			case SUBCLASSING_CONTRACT:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case SUBCLASSING_CONTRACT:
			{
				subclassing_contract();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case EOF:
			case MODEL:
			case SEMI:
			case IDENT:
			case T_TYPEOFALLTYPES:
			case LITERAL_private:
			case LITERAL_public:
			case LITERAL_protected:
			case LITERAL_static:
			case LITERAL_transient:
			case LITERAL_final:
			case LITERAL_abstract:
			case LITERAL_native:
			case LITERAL_synchronized:
			case LITERAL_const:
			case LITERAL_volatile:
			case LITERAL_strictfp:
			case LCURLY:
			case STATIC_INITIALIZER:
			case INITIALIZER:
			case PURE:
			case INSTANCE:
			case SPEC_PUBLIC:
			case SPEC_PROTECTED:
			case MONITORED:
			case UNINITIALIZED:
			case GHOST:
			case NON_NULL:
			case LITERAL_void:
			case FOR_EXAMPLE:
			case IMPLIES_THAT:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case FOR_EXAMPLE:
			case IMPLIES_THAT:
			{
				redundant_spec();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case EOF:
			case MODEL:
			case SEMI:
			case IDENT:
			case T_TYPEOFALLTYPES:
			case LITERAL_private:
			case LITERAL_public:
			case LITERAL_protected:
			case LITERAL_static:
			case LITERAL_transient:
			case LITERAL_final:
			case LITERAL_abstract:
			case LITERAL_native:
			case LITERAL_synchronized:
			case LITERAL_const:
			case LITERAL_volatile:
			case LITERAL_strictfp:
			case LCURLY:
			case STATIC_INITIALIZER:
			case INITIALIZER:
			case PURE:
			case INSTANCE:
			case SPEC_PUBLIC:
			case SPEC_PROTECTED:
			case MONITORED:
			case UNINITIALIZED:
			case GHOST:
			case NON_NULL:
			case LITERAL_void:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				extending_specification_AST = (AST)currentAST.root;
				extending_specification_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(EXT_AND,"EXT_and")).add(extending_specification_AST));
				currentAST.root = extending_specification_AST;
				currentAST.child = extending_specification_AST!=null &&extending_specification_AST.getFirstChild()!=null ?
					extending_specification_AST.getFirstChild() : extending_specification_AST;
				currentAST.advanceChildToEnd();
			}
			extending_specification_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = extending_specification_AST;
	}
	
	public final void initial_spec_case_seq(
		AST mods
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST initial_spec_case_seq_AST = null;
		
		initial_spec_case(mods);
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop216:
		do {
			if ((LA(1)==ALSO)) {
				AST tmp145_AST = null;
				tmp145_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp145_AST);
				match(ALSO);
				spec_case();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop216;
			}
			
		} while (true);
		}
		initial_spec_case_seq_AST = (AST)currentAST.root;
		returnAST = initial_spec_case_seq_AST;
	}
	
	public final void subclassing_contract() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST subclassing_contract_AST = null;
		
		if ((LA(1)==SUBCLASSING_CONTRACT) && (LA(2)==ACCESSIBLE||LA(2)==ACCESSIBLE_REDUNDANTLY)) {
			AST tmp146_AST = null;
			tmp146_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp146_AST);
			match(SUBCLASSING_CONTRACT);
			accessible_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			callable_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			subclassing_contract_AST = (AST)currentAST.root;
		}
		else if ((LA(1)==SUBCLASSING_CONTRACT) && (LA(2)==CALLABLE||LA(2)==CALLABLE_REDUNDANTLY)) {
			AST tmp147_AST = null;
			tmp147_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp147_AST);
			match(SUBCLASSING_CONTRACT);
			callable_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			subclassing_contract_AST = (AST)currentAST.root;
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		returnAST = subclassing_contract_AST;
	}
	
	public final void redundant_spec() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST redundant_spec_AST = null;
		
		switch ( LA(1)) {
		case IMPLIES_THAT:
		{
			implications();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case FOR_EXAMPLE:
			{
				examples();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case EOF:
			case MODEL:
			case SEMI:
			case IDENT:
			case T_TYPEOFALLTYPES:
			case LITERAL_private:
			case LITERAL_public:
			case LITERAL_protected:
			case LITERAL_static:
			case LITERAL_transient:
			case LITERAL_final:
			case LITERAL_abstract:
			case LITERAL_native:
			case LITERAL_synchronized:
			case LITERAL_const:
			case LITERAL_volatile:
			case LITERAL_strictfp:
			case LCURLY:
			case STATIC_INITIALIZER:
			case INITIALIZER:
			case PURE:
			case INSTANCE:
			case SPEC_PUBLIC:
			case SPEC_PROTECTED:
			case MONITORED:
			case UNINITIALIZED:
			case GHOST:
			case NON_NULL:
			case LITERAL_void:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			redundant_spec_AST = (AST)currentAST.root;
			break;
		}
		case FOR_EXAMPLE:
		{
			examples();
			astFactory.addASTChild(currentAST, returnAST);
			redundant_spec_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = redundant_spec_AST;
	}
	
	public final void conjoinable_spec_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST conjoinable_spec_seq_AST = null;
		
		conjoinable_spec();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop161:
		do {
			if ((LA(1)==AND)) {
				AST tmp148_AST = null;
				tmp148_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp148_AST);
				match(AND);
				conjoinable_spec();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop161;
			}
			
		} while (true);
		}
		conjoinable_spec_seq_AST = (AST)currentAST.root;
		returnAST = conjoinable_spec_seq_AST;
	}
	
	public final void spec_case_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST spec_case_seq_AST = null;
		
		spec_case();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop221:
		do {
			if ((LA(1)==ALSO)) {
				AST tmp149_AST = null;
				tmp149_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp149_AST);
				match(ALSO);
				spec_case();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop221;
			}
			
		} while (true);
		}
		spec_case_seq_AST = (AST)currentAST.root;
		returnAST = spec_case_seq_AST;
	}
	
	public final void conjoinable_spec() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST conjoinable_spec_AST = null;
		
		switch ( LA(1)) {
		case FORALL:
		case LET:
		case OLD:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			generic_conjoinable_spec();
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				conjoinable_spec_AST = (AST)currentAST.root;
				
				conjoinable_spec_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(CONJOINABLE_SPEC,"conjoinable_spec")).add(conjoinable_spec_AST));
				
				currentAST.root = conjoinable_spec_AST;
				currentAST.child = conjoinable_spec_AST!=null &&conjoinable_spec_AST.getFirstChild()!=null ?
					conjoinable_spec_AST.getFirstChild() : conjoinable_spec_AST;
				currentAST.advanceChildToEnd();
			}
			conjoinable_spec_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_private:
		case LITERAL_public:
		case LITERAL_protected:
		case BEHAVIOR:
		case EXCEPTIONAL_BEHAVIOR:
		case NORMAL_BEHAVIOR:
		{
			privacy_opt();
			astFactory.addASTChild(currentAST, returnAST);
			behavior_conjoinable_spec();
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				conjoinable_spec_AST = (AST)currentAST.root;
				
				conjoinable_spec_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(CONJOINABLE_SPEC,"conjoinable_spec")).add(conjoinable_spec_AST));
				
				currentAST.root = conjoinable_spec_AST;
				currentAST.child = conjoinable_spec_AST!=null &&conjoinable_spec_AST.getFirstChild()!=null ?
					conjoinable_spec_AST.getFirstChild() : conjoinable_spec_AST;
				currentAST.advanceChildToEnd();
			}
			conjoinable_spec_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = conjoinable_spec_AST;
	}
	
	public final void generic_conjoinable_spec() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST generic_conjoinable_spec_AST = null;
		
		{
		switch ( LA(1)) {
		case FORALL:
		case LET:
		case OLD:
		{
			spec_var_decls();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		simple_spec_body();
		astFactory.addASTChild(currentAST, returnAST);
		if ( inputState.guessing==0 ) {
			generic_conjoinable_spec_AST = (AST)currentAST.root;
			generic_conjoinable_spec_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(CONJOINABLE_SPEC,"conjoinable_spec")).add(generic_conjoinable_spec_AST));
			currentAST.root = generic_conjoinable_spec_AST;
			currentAST.child = generic_conjoinable_spec_AST!=null &&generic_conjoinable_spec_AST.getFirstChild()!=null ?
				generic_conjoinable_spec_AST.getFirstChild() : generic_conjoinable_spec_AST;
			currentAST.advanceChildToEnd();
		}
		generic_conjoinable_spec_AST = (AST)currentAST.root;
		returnAST = generic_conjoinable_spec_AST;
	}
	
	public final void privacy_opt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST privacy_opt_AST = null;
		
		Modifier r = Modifier.NONE;
		
		
		switch ( LA(1)) {
		case BEHAVIOR:
		case EXCEPTIONAL_BEHAVIOR:
		case NORMAL_BEHAVIOR:
		case EXAMPLE:
		case EXCEPTIONAL_EXAMPLE:
		case NORMAL_EXAMPLE:
		case MODEL_PROGRAM:
		{
			privacy_opt_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_private:
		case LITERAL_public:
		case LITERAL_protected:
		{
			{
			switch ( LA(1)) {
			case LITERAL_public:
			{
				AST tmp150_AST = null;
				tmp150_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp150_AST);
				match(LITERAL_public);
				break;
			}
			case LITERAL_private:
			{
				AST tmp151_AST = null;
				tmp151_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp151_AST);
				match(LITERAL_private);
				break;
			}
			case LITERAL_protected:
			{
				AST tmp152_AST = null;
				tmp152_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp152_AST);
				match(LITERAL_protected);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				privacy_opt_AST = (AST)currentAST.root;
				r = new Modifier(privacy_opt_AST.getText());
				ModifierSet ms = new ModifierSet(r);
				// save column and line information
				LineAST lineASTprivacy_opt = (LineAST)privacy_opt_AST;
				int linenum = lineASTprivacy_opt.line;
				int colnum = lineASTprivacy_opt.column;
				// create a new special token
				ms = Typing.defaultPrivacyModifiers(ms);
				String priv_mod_str = "privacy_modifier (" + ms + ")";
				privacy_opt_AST = astFactory.create(PRIVACY_MODIFIER,priv_mod_str);
				lineASTprivacy_opt = (LineAST)privacy_opt_AST;
				lineASTprivacy_opt.type = new Modifiers(ms);
				lineASTprivacy_opt.line = linenum;
				lineASTprivacy_opt.column = colnum;
				
				currentAST.root = privacy_opt_AST;
				currentAST.child = privacy_opt_AST!=null &&privacy_opt_AST.getFirstChild()!=null ?
					privacy_opt_AST.getFirstChild() : privacy_opt_AST;
				currentAST.advanceChildToEnd();
			}
			privacy_opt_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = privacy_opt_AST;
	}
	
	public final void behavior_conjoinable_spec() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST behavior_conjoinable_spec_AST = null;
		
		switch ( LA(1)) {
		case BEHAVIOR:
		{
			AST tmp153_AST = null;
			tmp153_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp153_AST);
			match(BEHAVIOR);
			{
			switch ( LA(1)) {
			case FORALL:
			case LET:
			case OLD:
			{
				spec_var_decls();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case ASSIGNABLE:
			case MODIFIABLE:
			case MODIFIES:
			case ASSIGNABLE_REDUNDANTLY:
			case MODIFIABLE_REDUNDANTLY:
			case MODIFIES_REDUNDANTLY:
			case ENSURES:
			case POST:
			case ENSURES_REDUNDANTLY:
			case POST_REDUNDANTLY:
			case SIGNALS:
			case SIGNALS_REDUNDANTLY:
			case EXSURES:
			case EXSURES_REDUNDANTLY:
			case DIVERGES:
			case DIVERGES_REDUNDANTLY:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			simple_spec_body();
			astFactory.addASTChild(currentAST, returnAST);
			behavior_conjoinable_spec_AST = (AST)currentAST.root;
			break;
		}
		case EXCEPTIONAL_BEHAVIOR:
		{
			AST tmp154_AST = null;
			tmp154_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp154_AST);
			match(EXCEPTIONAL_BEHAVIOR);
			{
			switch ( LA(1)) {
			case FORALL:
			case LET:
			case OLD:
			{
				spec_var_decls();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case ASSIGNABLE:
			case MODIFIABLE:
			case MODIFIES:
			case ASSIGNABLE_REDUNDANTLY:
			case MODIFIABLE_REDUNDANTLY:
			case MODIFIES_REDUNDANTLY:
			case SIGNALS:
			case SIGNALS_REDUNDANTLY:
			case EXSURES:
			case EXSURES_REDUNDANTLY:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			exceptional_simple_spec_body();
			astFactory.addASTChild(currentAST, returnAST);
			behavior_conjoinable_spec_AST = (AST)currentAST.root;
			break;
		}
		case NORMAL_BEHAVIOR:
		{
			AST tmp155_AST = null;
			tmp155_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp155_AST);
			match(NORMAL_BEHAVIOR);
			{
			switch ( LA(1)) {
			case FORALL:
			case LET:
			case OLD:
			{
				spec_var_decls();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case ASSIGNABLE:
			case MODIFIABLE:
			case MODIFIES:
			case ASSIGNABLE_REDUNDANTLY:
			case MODIFIABLE_REDUNDANTLY:
			case MODIFIES_REDUNDANTLY:
			case ENSURES:
			case POST:
			case ENSURES_REDUNDANTLY:
			case POST_REDUNDANTLY:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			normal_simple_spec_body();
			astFactory.addASTChild(currentAST, returnAST);
			behavior_conjoinable_spec_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = behavior_conjoinable_spec_AST;
	}
	
	public final void spec_var_decls() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST spec_var_decls_AST = null;
		
		switch ( LA(1)) {
		case FORALL:
		{
			{
			int _cnt296=0;
			_loop296:
			do {
				if ((LA(1)==FORALL)) {
					forall_var_decl();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					if ( _cnt296>=1 ) { break _loop296; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt296++;
			} while (true);
			}
			{
			switch ( LA(1)) {
			case LET:
			case OLD:
			{
				let_var_decls();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case IDENT:
			case LCURLY_VBAR:
			case REQUIRES:
			case PRE:
			case REQUIRES_REDUNDANTLY:
			case PRE_REDUNDANTLY:
			case WHEN:
			case WHEN_REDUNDANTLY:
			case MEASURED_BY:
			case MEASURED_BY_REDUNDANTLY:
			case ASSIGNABLE:
			case MODIFIABLE:
			case MODIFIES:
			case ASSIGNABLE_REDUNDANTLY:
			case MODIFIABLE_REDUNDANTLY:
			case MODIFIES_REDUNDANTLY:
			case ENSURES:
			case POST:
			case ENSURES_REDUNDANTLY:
			case POST_REDUNDANTLY:
			case SIGNALS:
			case SIGNALS_REDUNDANTLY:
			case EXSURES:
			case EXSURES_REDUNDANTLY:
			case DIVERGES:
			case DIVERGES_REDUNDANTLY:
			case CONTINUES:
			case CONTINUES_REDUNDANTLY:
			case BREAKS:
			case BREAKS_REDUNDANTLY:
			case RETURNS:
			case RETURNS_REDUNDANTLY:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			spec_var_decls_AST = (AST)currentAST.root;
			break;
		}
		case LET:
		case OLD:
		{
			let_var_decls();
			astFactory.addASTChild(currentAST, returnAST);
			spec_var_decls_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = spec_var_decls_AST;
	}
	
	public final void simple_spec_body() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST simple_spec_body_AST = null;
		
		switch ( LA(1)) {
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		{
			assignable_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			ensures_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			signals_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			diverges_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			simple_spec_body_AST = (AST)currentAST.root;
			break;
		}
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		{
			ensures_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			signals_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			diverges_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			simple_spec_body_AST = (AST)currentAST.root;
			break;
		}
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		{
			signals_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			diverges_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			simple_spec_body_AST = (AST)currentAST.root;
			break;
		}
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			diverges_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			simple_spec_body_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = simple_spec_body_AST;
	}
	
	public final void exceptional_simple_spec_body() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST exceptional_simple_spec_body_AST = null;
		
		switch ( LA(1)) {
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		{
			assignable_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			signals_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			diverges_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			exceptional_simple_spec_body_AST = (AST)currentAST.root;
			break;
		}
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		{
			signals_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			diverges_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			exceptional_simple_spec_body_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = exceptional_simple_spec_body_AST;
	}
	
	public final void normal_simple_spec_body() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST normal_simple_spec_body_AST = null;
		
		switch ( LA(1)) {
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		{
			assignable_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			ensures_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			diverges_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			normal_simple_spec_body_AST = (AST)currentAST.root;
			break;
		}
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		{
			ensures_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			diverges_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			normal_simple_spec_body_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = normal_simple_spec_body_AST;
	}
	
	public final void assignable_clause_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST assignable_clause_seq_AST = null;
		
		{
		int _cnt343=0;
		_loop343:
		do {
			if (((LA(1) >= ASSIGNABLE && LA(1) <= MODIFIES_REDUNDANTLY)) && (_tokenSet_23.member(LA(2)))) {
				assignable_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt343>=1 ) { break _loop343; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt343++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			assignable_clause_seq_AST = (AST)currentAST.root;
			assignable_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(ASGNABLE_SEQ,"assignable_seq")).add(assignable_clause_seq_AST)); 
			
			currentAST.root = assignable_clause_seq_AST;
			currentAST.child = assignable_clause_seq_AST!=null &&assignable_clause_seq_AST.getFirstChild()!=null ?
				assignable_clause_seq_AST.getFirstChild() : assignable_clause_seq_AST;
			currentAST.advanceChildToEnd();
		}
		assignable_clause_seq_AST = (AST)currentAST.root;
		returnAST = assignable_clause_seq_AST;
	}
	
	public final void signals_clause_seq_opt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST signals_clause_seq_opt_AST = null;
		
		{
		_loop389:
		do {
			if (((LA(1) >= SIGNALS && LA(1) <= EXSURES_REDUNDANTLY)) && (LA(2)==LPAREN)) {
				signals_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop389;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			signals_clause_seq_opt_AST = (AST)currentAST.root;
			
			signals_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(SIG_SEQ,"signals_seq")).add(signals_clause_seq_opt_AST));
			
			currentAST.root = signals_clause_seq_opt_AST;
			currentAST.child = signals_clause_seq_opt_AST!=null &&signals_clause_seq_opt_AST.getFirstChild()!=null ?
				signals_clause_seq_opt_AST.getFirstChild() : signals_clause_seq_opt_AST;
			currentAST.advanceChildToEnd();
		}
		signals_clause_seq_opt_AST = (AST)currentAST.root;
		returnAST = signals_clause_seq_opt_AST;
	}
	
	public final void diverges_clause_seq_opt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST diverges_clause_seq_opt_AST = null;
		
		{
		_loop399:
		do {
			if ((LA(1)==DIVERGES||LA(1)==DIVERGES_REDUNDANTLY)) {
				diverges_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop399;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			diverges_clause_seq_opt_AST = (AST)currentAST.root;
			
			diverges_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(DIV_SEQ,"diverges_seq")).add(diverges_clause_seq_opt_AST));
			
			currentAST.root = diverges_clause_seq_opt_AST;
			currentAST.child = diverges_clause_seq_opt_AST!=null &&diverges_clause_seq_opt_AST.getFirstChild()!=null ?
				diverges_clause_seq_opt_AST.getFirstChild() : diverges_clause_seq_opt_AST;
			currentAST.advanceChildToEnd();
		}
		diverges_clause_seq_opt_AST = (AST)currentAST.root;
		returnAST = diverges_clause_seq_opt_AST;
	}
	
	public final void signals_clause_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST signals_clause_seq_AST = null;
		
		{
		int _cnt392=0;
		_loop392:
		do {
			if (((LA(1) >= SIGNALS && LA(1) <= EXSURES_REDUNDANTLY)) && (LA(2)==LPAREN)) {
				signals_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt392>=1 ) { break _loop392; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt392++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			signals_clause_seq_AST = (AST)currentAST.root;
			
			signals_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(SIG_SEQ,"signals_seq")).add(signals_clause_seq_AST));
			
			currentAST.root = signals_clause_seq_AST;
			currentAST.child = signals_clause_seq_AST!=null &&signals_clause_seq_AST.getFirstChild()!=null ?
				signals_clause_seq_AST.getFirstChild() : signals_clause_seq_AST;
			currentAST.advanceChildToEnd();
		}
		signals_clause_seq_AST = (AST)currentAST.root;
		returnAST = signals_clause_seq_AST;
	}
	
	public final void ensures_clause_seq_opt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST ensures_clause_seq_opt_AST = null;
		
		{
		_loop369:
		do {
			if (((LA(1) >= ENSURES && LA(1) <= POST_REDUNDANTLY)) && (_tokenSet_24.member(LA(2)))) {
				ensures_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop369;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			ensures_clause_seq_opt_AST = (AST)currentAST.root;
			
			ensures_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(ENS_SEQ,"ensures_seq")).add(ensures_clause_seq_opt_AST)); 
			
			currentAST.root = ensures_clause_seq_opt_AST;
			currentAST.child = ensures_clause_seq_opt_AST!=null &&ensures_clause_seq_opt_AST.getFirstChild()!=null ?
				ensures_clause_seq_opt_AST.getFirstChild() : ensures_clause_seq_opt_AST;
			currentAST.advanceChildToEnd();
		}
		ensures_clause_seq_opt_AST = (AST)currentAST.root;
		returnAST = ensures_clause_seq_opt_AST;
	}
	
	public final void ensures_clause_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST ensures_clause_seq_AST = null;
		
		{
		int _cnt372=0;
		_loop372:
		do {
			if (((LA(1) >= ENSURES && LA(1) <= POST_REDUNDANTLY)) && (_tokenSet_24.member(LA(2)))) {
				ensures_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt372>=1 ) { break _loop372; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt372++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			ensures_clause_seq_AST = (AST)currentAST.root;
			
			ensures_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(ENS_SEQ,"ensures_seq")).add(ensures_clause_seq_AST)); 
			
			currentAST.root = ensures_clause_seq_AST;
			currentAST.child = ensures_clause_seq_AST!=null &&ensures_clause_seq_AST.getFirstChild()!=null ?
				ensures_clause_seq_AST.getFirstChild() : ensures_clause_seq_AST;
			currentAST.advanceChildToEnd();
		}
		ensures_clause_seq_AST = (AST)currentAST.root;
		returnAST = ensures_clause_seq_AST;
	}
	
	public final void implications() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST implications_AST = null;
		
		AST tmp156_AST = null;
		tmp156_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp156_AST);
		match(IMPLIES_THAT);
		spec_case_seq();
		astFactory.addASTChild(currentAST, returnAST);
		implications_AST = (AST)currentAST.root;
		returnAST = implications_AST;
	}
	
	public final void examples() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST examples_AST = null;
		
		AST tmp157_AST = null;
		tmp157_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp157_AST);
		match(FOR_EXAMPLE);
		example_seq();
		astFactory.addASTChild(currentAST, returnAST);
		examples_AST = (AST)currentAST.root;
		returnAST = examples_AST;
	}
	
	public final void example_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST example_seq_AST = null;
		
		example();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop178:
		do {
			if ((LA(1)==ALSO)) {
				AST tmp158_AST = null;
				tmp158_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp158_AST);
				match(ALSO);
				example();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop178;
			}
			
		} while (true);
		}
		example_seq_AST = (AST)currentAST.root;
		returnAST = example_seq_AST;
	}
	
	public final void example() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST example_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		case FORALL:
		case LET:
		case OLD:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case WHEN:
		case WHEN_REDUNDANTLY:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			{
			switch ( LA(1)) {
			case FORALL:
			case LET:
			case OLD:
			{
				spec_var_decls();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case IDENT:
			case REQUIRES:
			case PRE:
			case REQUIRES_REDUNDANTLY:
			case PRE_REDUNDANTLY:
			case WHEN:
			case WHEN_REDUNDANTLY:
			case MEASURED_BY:
			case MEASURED_BY_REDUNDANTLY:
			case ASSIGNABLE:
			case MODIFIABLE:
			case MODIFIES:
			case ASSIGNABLE_REDUNDANTLY:
			case MODIFIABLE_REDUNDANTLY:
			case MODIFIES_REDUNDANTLY:
			case ENSURES:
			case POST:
			case ENSURES_REDUNDANTLY:
			case POST_REDUNDANTLY:
			case SIGNALS:
			case SIGNALS_REDUNDANTLY:
			case EXSURES:
			case EXSURES_REDUNDANTLY:
			case DIVERGES:
			case DIVERGES_REDUNDANTLY:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case IDENT:
			case REQUIRES:
			case PRE:
			case REQUIRES_REDUNDANTLY:
			case PRE_REDUNDANTLY:
			case WHEN:
			case WHEN_REDUNDANTLY:
			case MEASURED_BY:
			case MEASURED_BY_REDUNDANTLY:
			{
				spec_header();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case ASSIGNABLE:
			case MODIFIABLE:
			case MODIFIES:
			case ASSIGNABLE_REDUNDANTLY:
			case MODIFIABLE_REDUNDANTLY:
			case MODIFIES_REDUNDANTLY:
			case ENSURES:
			case POST:
			case ENSURES_REDUNDANTLY:
			case POST_REDUNDANTLY:
			case SIGNALS:
			case SIGNALS_REDUNDANTLY:
			case EXSURES:
			case EXSURES_REDUNDANTLY:
			case DIVERGES:
			case DIVERGES_REDUNDANTLY:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			simple_spec_body();
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				example_AST = (AST)currentAST.root;
				example_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(SPEC_CASE,"generic_example")).add(example_AST));
				currentAST.root = example_AST;
				currentAST.child = example_AST!=null &&example_AST.getFirstChild()!=null ?
					example_AST.getFirstChild() : example_AST;
				currentAST.advanceChildToEnd();
			}
			example_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_private:
		case LITERAL_public:
		case LITERAL_protected:
		case EXAMPLE:
		case EXCEPTIONAL_EXAMPLE:
		case NORMAL_EXAMPLE:
		{
			privacy_opt();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case EXAMPLE:
			{
				AST tmp159_AST = null;
				tmp159_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp159_AST);
				match(EXAMPLE);
				{
				switch ( LA(1)) {
				case FORALL:
				case LET:
				case OLD:
				{
					spec_var_decls();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				case IDENT:
				case REQUIRES:
				case PRE:
				case REQUIRES_REDUNDANTLY:
				case PRE_REDUNDANTLY:
				case WHEN:
				case WHEN_REDUNDANTLY:
				case MEASURED_BY:
				case MEASURED_BY_REDUNDANTLY:
				case ASSIGNABLE:
				case MODIFIABLE:
				case MODIFIES:
				case ASSIGNABLE_REDUNDANTLY:
				case MODIFIABLE_REDUNDANTLY:
				case MODIFIES_REDUNDANTLY:
				case ENSURES:
				case POST:
				case ENSURES_REDUNDANTLY:
				case POST_REDUNDANTLY:
				case SIGNALS:
				case SIGNALS_REDUNDANTLY:
				case EXSURES:
				case EXSURES_REDUNDANTLY:
				case DIVERGES:
				case DIVERGES_REDUNDANTLY:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				{
				switch ( LA(1)) {
				case IDENT:
				case REQUIRES:
				case PRE:
				case REQUIRES_REDUNDANTLY:
				case PRE_REDUNDANTLY:
				case WHEN:
				case WHEN_REDUNDANTLY:
				case MEASURED_BY:
				case MEASURED_BY_REDUNDANTLY:
				{
					spec_header();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				case ASSIGNABLE:
				case MODIFIABLE:
				case MODIFIES:
				case ASSIGNABLE_REDUNDANTLY:
				case MODIFIABLE_REDUNDANTLY:
				case MODIFIES_REDUNDANTLY:
				case ENSURES:
				case POST:
				case ENSURES_REDUNDANTLY:
				case POST_REDUNDANTLY:
				case SIGNALS:
				case SIGNALS_REDUNDANTLY:
				case EXSURES:
				case EXSURES_REDUNDANTLY:
				case DIVERGES:
				case DIVERGES_REDUNDANTLY:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				simple_spec_body();
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					example_AST = (AST)currentAST.root;
					example_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(SPEC_CASE,"example")).add(example_AST));
					currentAST.root = example_AST;
					currentAST.child = example_AST!=null &&example_AST.getFirstChild()!=null ?
						example_AST.getFirstChild() : example_AST;
					currentAST.advanceChildToEnd();
				}
				break;
			}
			case EXCEPTIONAL_EXAMPLE:
			{
				AST tmp160_AST = null;
				tmp160_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp160_AST);
				match(EXCEPTIONAL_EXAMPLE);
				{
				switch ( LA(1)) {
				case FORALL:
				case LET:
				case OLD:
				{
					spec_var_decls();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				case IDENT:
				case REQUIRES:
				case PRE:
				case REQUIRES_REDUNDANTLY:
				case PRE_REDUNDANTLY:
				case WHEN:
				case WHEN_REDUNDANTLY:
				case MEASURED_BY:
				case MEASURED_BY_REDUNDANTLY:
				case ASSIGNABLE:
				case MODIFIABLE:
				case MODIFIES:
				case ASSIGNABLE_REDUNDANTLY:
				case MODIFIABLE_REDUNDANTLY:
				case MODIFIES_REDUNDANTLY:
				case SIGNALS:
				case SIGNALS_REDUNDANTLY:
				case EXSURES:
				case EXSURES_REDUNDANTLY:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				{
				switch ( LA(1)) {
				case IDENT:
				case REQUIRES:
				case PRE:
				case REQUIRES_REDUNDANTLY:
				case PRE_REDUNDANTLY:
				case WHEN:
				case WHEN_REDUNDANTLY:
				case MEASURED_BY:
				case MEASURED_BY_REDUNDANTLY:
				{
					spec_header();
					astFactory.addASTChild(currentAST, returnAST);
					{
					switch ( LA(1)) {
					case ASSIGNABLE:
					case MODIFIABLE:
					case MODIFIES:
					case ASSIGNABLE_REDUNDANTLY:
					case MODIFIABLE_REDUNDANTLY:
					case MODIFIES_REDUNDANTLY:
					case SIGNALS:
					case SIGNALS_REDUNDANTLY:
					case EXSURES:
					case EXSURES_REDUNDANTLY:
					{
						exceptional_example_body();
						astFactory.addASTChild(currentAST, returnAST);
						break;
					}
					case EOF:
					case MODEL:
					case SEMI:
					case IDENT:
					case T_TYPEOFALLTYPES:
					case LITERAL_private:
					case LITERAL_public:
					case LITERAL_protected:
					case LITERAL_static:
					case LITERAL_transient:
					case LITERAL_final:
					case LITERAL_abstract:
					case LITERAL_native:
					case LITERAL_synchronized:
					case LITERAL_const:
					case LITERAL_volatile:
					case LITERAL_strictfp:
					case LCURLY:
					case STATIC_INITIALIZER:
					case INITIALIZER:
					case PURE:
					case INSTANCE:
					case SPEC_PUBLIC:
					case SPEC_PROTECTED:
					case MONITORED:
					case UNINITIALIZED:
					case GHOST:
					case NON_NULL:
					case LITERAL_void:
					case ALSO:
					case LITERAL_boolean:
					case LITERAL_byte:
					case LITERAL_char:
					case LITERAL_short:
					case LITERAL_int:
					case LITERAL_long:
					case LITERAL_float:
					case LITERAL_double:
					{
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					break;
				}
				case ASSIGNABLE:
				case MODIFIABLE:
				case MODIFIES:
				case ASSIGNABLE_REDUNDANTLY:
				case MODIFIABLE_REDUNDANTLY:
				case MODIFIES_REDUNDANTLY:
				case SIGNALS:
				case SIGNALS_REDUNDANTLY:
				case EXSURES:
				case EXSURES_REDUNDANTLY:
				{
					exceptional_example_body();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					example_AST = (AST)currentAST.root;
					example_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(SPEC_CASE,"example")).add(example_AST));
					currentAST.root = example_AST;
					currentAST.child = example_AST!=null &&example_AST.getFirstChild()!=null ?
						example_AST.getFirstChild() : example_AST;
					currentAST.advanceChildToEnd();
				}
				break;
			}
			case NORMAL_EXAMPLE:
			{
				AST tmp161_AST = null;
				tmp161_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp161_AST);
				match(NORMAL_EXAMPLE);
				{
				switch ( LA(1)) {
				case FORALL:
				case LET:
				case OLD:
				{
					spec_var_decls();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				case IDENT:
				case REQUIRES:
				case PRE:
				case REQUIRES_REDUNDANTLY:
				case PRE_REDUNDANTLY:
				case WHEN:
				case WHEN_REDUNDANTLY:
				case MEASURED_BY:
				case MEASURED_BY_REDUNDANTLY:
				case ASSIGNABLE:
				case MODIFIABLE:
				case MODIFIES:
				case ASSIGNABLE_REDUNDANTLY:
				case MODIFIABLE_REDUNDANTLY:
				case MODIFIES_REDUNDANTLY:
				case ENSURES:
				case POST:
				case ENSURES_REDUNDANTLY:
				case POST_REDUNDANTLY:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				{
				switch ( LA(1)) {
				case IDENT:
				case REQUIRES:
				case PRE:
				case REQUIRES_REDUNDANTLY:
				case PRE_REDUNDANTLY:
				case WHEN:
				case WHEN_REDUNDANTLY:
				case MEASURED_BY:
				case MEASURED_BY_REDUNDANTLY:
				{
					spec_header();
					astFactory.addASTChild(currentAST, returnAST);
					{
					switch ( LA(1)) {
					case ASSIGNABLE:
					case MODIFIABLE:
					case MODIFIES:
					case ASSIGNABLE_REDUNDANTLY:
					case MODIFIABLE_REDUNDANTLY:
					case MODIFIES_REDUNDANTLY:
					case ENSURES:
					case POST:
					case ENSURES_REDUNDANTLY:
					case POST_REDUNDANTLY:
					{
						normal_example_body();
						astFactory.addASTChild(currentAST, returnAST);
						break;
					}
					case EOF:
					case MODEL:
					case SEMI:
					case IDENT:
					case T_TYPEOFALLTYPES:
					case LITERAL_private:
					case LITERAL_public:
					case LITERAL_protected:
					case LITERAL_static:
					case LITERAL_transient:
					case LITERAL_final:
					case LITERAL_abstract:
					case LITERAL_native:
					case LITERAL_synchronized:
					case LITERAL_const:
					case LITERAL_volatile:
					case LITERAL_strictfp:
					case LCURLY:
					case STATIC_INITIALIZER:
					case INITIALIZER:
					case PURE:
					case INSTANCE:
					case SPEC_PUBLIC:
					case SPEC_PROTECTED:
					case MONITORED:
					case UNINITIALIZED:
					case GHOST:
					case NON_NULL:
					case LITERAL_void:
					case ALSO:
					case LITERAL_boolean:
					case LITERAL_byte:
					case LITERAL_char:
					case LITERAL_short:
					case LITERAL_int:
					case LITERAL_long:
					case LITERAL_float:
					case LITERAL_double:
					{
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					break;
				}
				case ASSIGNABLE:
				case MODIFIABLE:
				case MODIFIES:
				case ASSIGNABLE_REDUNDANTLY:
				case MODIFIABLE_REDUNDANTLY:
				case MODIFIES_REDUNDANTLY:
				case ENSURES:
				case POST:
				case ENSURES_REDUNDANTLY:
				case POST_REDUNDANTLY:
				{
					normal_example_body();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					example_AST = (AST)currentAST.root;
					example_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(SPEC_CASE,"example")).add(example_AST));
					currentAST.root = example_AST;
					currentAST.child = example_AST!=null &&example_AST.getFirstChild()!=null ?
						example_AST.getFirstChild() : example_AST;
					currentAST.advanceChildToEnd();
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			example_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = example_AST;
	}
	
	public final void spec_header() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST spec_header_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		{
			{
			int _cnt252=0;
			_loop252:
			do {
				if ((LA(1)==IDENT) && (LA(2)==COLON)) {
					label_decl();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					if ( _cnt252>=1 ) { break _loop252; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt252++;
			} while (true);
			}
			{
			_loop254:
			do {
				if (((LA(1) >= REQUIRES && LA(1) <= PRE_REDUNDANTLY)) && (_tokenSet_24.member(LA(2)))) {
					requires_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop254;
				}
				
			} while (true);
			}
			{
			_loop256:
			do {
				if ((LA(1)==WHEN||LA(1)==WHEN_REDUNDANTLY)) {
					when_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop256;
				}
				
			} while (true);
			}
			{
			_loop258:
			do {
				if ((LA(1)==MEASURED_BY||LA(1)==MEASURED_BY_REDUNDANTLY)) {
					measured_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop258;
				}
				
			} while (true);
			}
			spec_header_AST = (AST)currentAST.root;
			break;
		}
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		{
			{
			int _cnt260=0;
			_loop260:
			do {
				if (((LA(1) >= REQUIRES && LA(1) <= PRE_REDUNDANTLY)) && (_tokenSet_24.member(LA(2)))) {
					requires_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					if ( _cnt260>=1 ) { break _loop260; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt260++;
			} while (true);
			}
			{
			_loop262:
			do {
				if ((LA(1)==WHEN||LA(1)==WHEN_REDUNDANTLY)) {
					when_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop262;
				}
				
			} while (true);
			}
			{
			_loop264:
			do {
				if ((LA(1)==MEASURED_BY||LA(1)==MEASURED_BY_REDUNDANTLY)) {
					measured_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop264;
				}
				
			} while (true);
			}
			spec_header_AST = (AST)currentAST.root;
			break;
		}
		case WHEN:
		case WHEN_REDUNDANTLY:
		{
			{
			int _cnt266=0;
			_loop266:
			do {
				if ((LA(1)==WHEN||LA(1)==WHEN_REDUNDANTLY)) {
					when_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					if ( _cnt266>=1 ) { break _loop266; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt266++;
			} while (true);
			}
			{
			_loop268:
			do {
				if ((LA(1)==MEASURED_BY||LA(1)==MEASURED_BY_REDUNDANTLY)) {
					measured_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop268;
				}
				
			} while (true);
			}
			spec_header_AST = (AST)currentAST.root;
			break;
		}
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		{
			{
			int _cnt270=0;
			_loop270:
			do {
				if ((LA(1)==MEASURED_BY||LA(1)==MEASURED_BY_REDUNDANTLY)) {
					measured_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					if ( _cnt270>=1 ) { break _loop270; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt270++;
			} while (true);
			}
			spec_header_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = spec_header_AST;
	}
	
	public final void exceptional_example_body() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST exceptional_example_body_AST = null;
		
		switch ( LA(1)) {
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		{
			{
			int _cnt193=0;
			_loop193:
			do {
				if (((LA(1) >= ASSIGNABLE && LA(1) <= MODIFIES_REDUNDANTLY))) {
					assignable_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					if ( _cnt193>=1 ) { break _loop193; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt193++;
			} while (true);
			}
			{
			_loop195:
			do {
				if (((LA(1) >= SIGNALS && LA(1) <= EXSURES_REDUNDANTLY))) {
					signals_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop195;
				}
				
			} while (true);
			}
			{
			_loop197:
			do {
				if ((LA(1)==DIVERGES||LA(1)==DIVERGES_REDUNDANTLY)) {
					diverges_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop197;
				}
				
			} while (true);
			}
			exceptional_example_body_AST = (AST)currentAST.root;
			break;
		}
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		{
			{
			int _cnt199=0;
			_loop199:
			do {
				if (((LA(1) >= SIGNALS && LA(1) <= EXSURES_REDUNDANTLY))) {
					signals_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					if ( _cnt199>=1 ) { break _loop199; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt199++;
			} while (true);
			}
			{
			_loop201:
			do {
				if ((LA(1)==DIVERGES||LA(1)==DIVERGES_REDUNDANTLY)) {
					diverges_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop201;
				}
				
			} while (true);
			}
			exceptional_example_body_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = exceptional_example_body_AST;
	}
	
	public final void normal_example_body() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST normal_example_body_AST = null;
		
		switch ( LA(1)) {
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		{
			{
			int _cnt204=0;
			_loop204:
			do {
				if (((LA(1) >= ASSIGNABLE && LA(1) <= MODIFIES_REDUNDANTLY))) {
					assignable_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					if ( _cnt204>=1 ) { break _loop204; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt204++;
			} while (true);
			}
			{
			_loop206:
			do {
				if (((LA(1) >= ENSURES && LA(1) <= POST_REDUNDANTLY))) {
					ensures_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop206;
				}
				
			} while (true);
			}
			{
			_loop208:
			do {
				if ((LA(1)==DIVERGES||LA(1)==DIVERGES_REDUNDANTLY)) {
					diverges_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop208;
				}
				
			} while (true);
			}
			normal_example_body_AST = (AST)currentAST.root;
			break;
		}
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		{
			{
			int _cnt210=0;
			_loop210:
			do {
				if (((LA(1) >= ENSURES && LA(1) <= POST_REDUNDANTLY))) {
					ensures_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					if ( _cnt210>=1 ) { break _loop210; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt210++;
			} while (true);
			}
			{
			_loop212:
			do {
				if ((LA(1)==DIVERGES||LA(1)==DIVERGES_REDUNDANTLY)) {
					diverges_clause();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop212;
				}
				
			} while (true);
			}
			normal_example_body_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = normal_example_body_AST;
	}
	
	public final void assignable_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST assignable_clause_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case ASSIGNABLE:
			{
				AST tmp162_AST = null;
				tmp162_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp162_AST);
				match(ASSIGNABLE);
				break;
			}
			case MODIFIABLE:
			{
				AST tmp163_AST = null;
				tmp163_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp163_AST);
				match(MODIFIABLE);
				break;
			}
			case MODIFIES:
			{
				AST tmp164_AST = null;
				tmp164_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp164_AST);
				match(MODIFIES);
				break;
			}
			case ASSIGNABLE_REDUNDANTLY:
			{
				AST tmp165_AST = null;
				tmp165_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp165_AST);
				match(ASSIGNABLE_REDUNDANTLY);
				break;
			}
			case MODIFIABLE_REDUNDANTLY:
			{
				AST tmp166_AST = null;
				tmp166_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp166_AST);
				match(MODIFIABLE_REDUNDANTLY);
				break;
			}
			case MODIFIES_REDUNDANTLY:
			{
				AST tmp167_AST = null;
				tmp167_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp167_AST);
				match(MODIFIES_REDUNDANTLY);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			conditional_store_references();
			astFactory.addASTChild(currentAST, returnAST);
			match(SEMI);
			if ( inputState.guessing==0 ) {
				assignable_clause_AST = (AST)currentAST.root;
				assignable_clause_AST.setType(ASSIGNABLE_KEYWORD);
			}
			assignable_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToJmlSpecKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = assignable_clause_AST;
	}
	
	public final void diverges_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST diverges_clause_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case DIVERGES:
			{
				AST tmp169_AST = null;
				tmp169_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp169_AST);
				match(DIVERGES);
				break;
			}
			case DIVERGES_REDUNDANTLY:
			{
				AST tmp170_AST = null;
				tmp170_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp170_AST);
				match(DIVERGES_REDUNDANTLY);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case T_NOT_SPECIFIED:
			{
				AST tmp171_AST = null;
				tmp171_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp171_AST);
				match(T_NOT_SPECIFIED);
				break;
			}
			case IDENT:
			case LPAREN:
			case STRING_LITERAL:
			case LITERAL_super:
			case LITERAL_this:
			case LITERAL_new:
			case LITERAL_void:
			case PLUS:
			case MINUS:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case T_RESULT:
			case T_OLD:
			case T_NOT_MODIFIED:
			case T_FRESH:
			case T_REACH:
			case T_NONNULLELEMENTS:
			case T_TYPEOF:
			case T_ELEMTYPE:
			case T_TYPE:
			case T_LOCKSET:
			case T_IS_INITIALIZED:
			case T_INVARIANT_FOR:
			case INFORMAL_DESCRIPTION:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			case NUM_INT:
			case CHAR_LITERAL:
			case NUM_FLOAT:
			{
				predicate();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
			if ( inputState.guessing==0 ) {
				diverges_clause_AST = (AST)currentAST.root;
				diverges_clause_AST.setType(DIVERGES_KEYWORD);
			}
			diverges_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToJmlSpecKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = diverges_clause_AST;
	}
	
	public final void ensures_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST ensures_clause_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case ENSURES:
			{
				AST tmp173_AST = null;
				tmp173_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp173_AST);
				match(ENSURES);
				break;
			}
			case POST:
			{
				AST tmp174_AST = null;
				tmp174_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp174_AST);
				match(POST);
				break;
			}
			case ENSURES_REDUNDANTLY:
			{
				AST tmp175_AST = null;
				tmp175_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp175_AST);
				match(ENSURES_REDUNDANTLY);
				break;
			}
			case POST_REDUNDANTLY:
			{
				AST tmp176_AST = null;
				tmp176_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp176_AST);
				match(POST_REDUNDANTLY);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case T_NOT_SPECIFIED:
			{
				AST tmp177_AST = null;
				tmp177_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp177_AST);
				match(T_NOT_SPECIFIED);
				break;
			}
			case IDENT:
			case LPAREN:
			case STRING_LITERAL:
			case LITERAL_super:
			case LITERAL_this:
			case LITERAL_new:
			case LITERAL_void:
			case PLUS:
			case MINUS:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case T_RESULT:
			case T_OLD:
			case T_NOT_MODIFIED:
			case T_FRESH:
			case T_REACH:
			case T_NONNULLELEMENTS:
			case T_TYPEOF:
			case T_ELEMTYPE:
			case T_TYPE:
			case T_LOCKSET:
			case T_IS_INITIALIZED:
			case T_INVARIANT_FOR:
			case INFORMAL_DESCRIPTION:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			case NUM_INT:
			case CHAR_LITERAL:
			case NUM_FLOAT:
			{
				post_cond();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
			if ( inputState.guessing==0 ) {
				ensures_clause_AST = (AST)currentAST.root;
				ensures_clause_AST.setType(ENSURES_KEYWORD);
			}
			ensures_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToJmlSpecKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = ensures_clause_AST;
	}
	
	public final void initial_spec_case(
		AST mods
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST initial_spec_case_AST = null;
		
		LineAST privs = modifiers2privacy(mods);
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case IDENT:
			case LCURLY_VBAR:
			case FORALL:
			case LET:
			case OLD:
			case REQUIRES:
			case PRE:
			case REQUIRES_REDUNDANTLY:
			case PRE_REDUNDANTLY:
			case WHEN:
			case WHEN_REDUNDANTLY:
			case MEASURED_BY:
			case MEASURED_BY_REDUNDANTLY:
			case ASSIGNABLE:
			case MODIFIABLE:
			case MODIFIES:
			case ASSIGNABLE_REDUNDANTLY:
			case MODIFIABLE_REDUNDANTLY:
			case MODIFIES_REDUNDANTLY:
			case ENSURES:
			case POST:
			case ENSURES_REDUNDANTLY:
			case POST_REDUNDANTLY:
			case SIGNALS:
			case SIGNALS_REDUNDANTLY:
			case EXSURES:
			case EXSURES_REDUNDANTLY:
			case DIVERGES:
			case DIVERGES_REDUNDANTLY:
			{
				generic_spec_case();
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					initial_spec_case_AST = (AST)currentAST.root;
					
					initial_spec_case_AST =
					(AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(SPEC_CASE,"generic_spec_case")).add(initial_spec_case_AST));
					
					currentAST.root = initial_spec_case_AST;
					currentAST.child = initial_spec_case_AST!=null &&initial_spec_case_AST.getFirstChild()!=null ?
						initial_spec_case_AST.getFirstChild() : initial_spec_case_AST;
					currentAST.advanceChildToEnd();
				}
				initial_spec_case_AST = (AST)currentAST.root;
				break;
			}
			case BEHAVIOR:
			case EXCEPTIONAL_BEHAVIOR:
			case NORMAL_BEHAVIOR:
			case MODEL_PROGRAM:
			{
				{
				switch ( LA(1)) {
				case BEHAVIOR:
				case EXCEPTIONAL_BEHAVIOR:
				case NORMAL_BEHAVIOR:
				{
					behavior_spec();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				case MODEL_PROGRAM:
				{
					model_program();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					initial_spec_case_AST = (AST)currentAST.root;
					
					initial_spec_case_AST =
					(AST)astFactory.make( (new ASTArray(3)).add(astFactory.create(SPEC_CASE,"spec_case")).add(privs).add(initial_spec_case_AST));
					
					currentAST.root = initial_spec_case_AST;
					currentAST.child = initial_spec_case_AST!=null &&initial_spec_case_AST.getFirstChild()!=null ?
						initial_spec_case_AST.getFirstChild() : initial_spec_case_AST;
					currentAST.advanceChildToEnd();
				}
				initial_spec_case_AST = (AST)currentAST.root;
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				System.err.print("skipping:\n   ");
				Token lastToken = null;
				int tokenCount = 0;
				int column = 3;
				String tokenLexeme;
				
				while (LA(1) != EOF && LA(1) != VBAR_RCURLY
				&& LA(1) != RCURLY && LA(1) != AND
				&& LA(1) != ALSO && LA(1) != ALSO
				&& LA(1) != SUBCLASSING_CONTRACT && LA(1) != IMPLIES_THAT
				&& LA(1) != FOR_EXAMPLE) {
				if (tokenCount < 20) {
				tokenLexeme = LT(1).getText();
				column = column + tokenLexeme.length() + 1;
				if (column > 70) {
				column = tokenLexeme.length() + 4;
				System.err.print("\n   ");
				}
				System.err.print(" " + tokenLexeme);
				tokenCount++;
				
				} else {
				lastToken = LT(1);
				}
				consume();
				}
				if (lastToken != null) {
				System.err.print("\n    ... through ");
				System.err.print(lastToken.getText()
				+ " on line: " + lastToken.getLine());
				}
				
				System.err.println();
				
			} else {
				throw err;
			}
		}
		returnAST = initial_spec_case_AST;
	}
	
	public final void spec_case() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST spec_case_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case IDENT:
			case LCURLY_VBAR:
			case FORALL:
			case LET:
			case OLD:
			case REQUIRES:
			case PRE:
			case REQUIRES_REDUNDANTLY:
			case PRE_REDUNDANTLY:
			case WHEN:
			case WHEN_REDUNDANTLY:
			case MEASURED_BY:
			case MEASURED_BY_REDUNDANTLY:
			case ASSIGNABLE:
			case MODIFIABLE:
			case MODIFIES:
			case ASSIGNABLE_REDUNDANTLY:
			case MODIFIABLE_REDUNDANTLY:
			case MODIFIES_REDUNDANTLY:
			case ENSURES:
			case POST:
			case ENSURES_REDUNDANTLY:
			case POST_REDUNDANTLY:
			case SIGNALS:
			case SIGNALS_REDUNDANTLY:
			case EXSURES:
			case EXSURES_REDUNDANTLY:
			case DIVERGES:
			case DIVERGES_REDUNDANTLY:
			{
				generic_spec_case();
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					spec_case_AST = (AST)currentAST.root;
					
					spec_case_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(SPEC_CASE,"generic_spec_case")).add(spec_case_AST)); 
					
					currentAST.root = spec_case_AST;
					currentAST.child = spec_case_AST!=null &&spec_case_AST.getFirstChild()!=null ?
						spec_case_AST.getFirstChild() : spec_case_AST;
					currentAST.advanceChildToEnd();
				}
				spec_case_AST = (AST)currentAST.root;
				break;
			}
			case LITERAL_private:
			case LITERAL_public:
			case LITERAL_protected:
			case BEHAVIOR:
			case EXCEPTIONAL_BEHAVIOR:
			case NORMAL_BEHAVIOR:
			case MODEL_PROGRAM:
			{
				{
				privacy_opt();
				astFactory.addASTChild(currentAST, returnAST);
				{
				switch ( LA(1)) {
				case BEHAVIOR:
				case EXCEPTIONAL_BEHAVIOR:
				case NORMAL_BEHAVIOR:
				{
					behavior_spec();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				case MODEL_PROGRAM:
				{
					model_program();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					spec_case_AST = (AST)currentAST.root;
					
					spec_case_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(SPEC_CASE,"spec_case")).add(spec_case_AST)); 
					
					currentAST.root = spec_case_AST;
					currentAST.child = spec_case_AST!=null &&spec_case_AST.getFirstChild()!=null ?
						spec_case_AST.getFirstChild() : spec_case_AST;
					currentAST.advanceChildToEnd();
				}
				}
				spec_case_AST = (AST)currentAST.root;
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				System.err.print("skipping:\n   ");
				int column = 3;  // because of the blanks in the message above
				Token lastToken = null;
				int tokenCount = 0;
				String tokenLexeme;
				
				while (LA(1) != EOF && LA(1) != VBAR_RCURLY
				&& LA(1) != RCURLY && LA(1) != AND
				&& LA(1) != ALSO && LA(1) != ALSO
				&& LA(1) != SUBCLASSING_CONTRACT && LA(1) != IMPLIES_THAT
				&& LA(1) != FOR_EXAMPLE) {
				if (tokenCount < 20) {
				tokenLexeme = LT(1).getText();
				column = column + tokenLexeme.length() + 1;
				if (column > 70) {
				column = tokenLexeme.length() + 4;
				System.err.print("\n   ");
				}
				System.err.print(" " + tokenLexeme);
				tokenCount++;
				
				} else {
				lastToken = LT(1);
				}
				consume();
				}
				if (lastToken != null) {
				System.err.print("\n    ... through ");
				System.err.print(lastToken.getText()
				+ " on line: " + lastToken.getLine());
				}
				
				System.err.println();
				
			} else {
				throw err;
			}
		}
		returnAST = spec_case_AST;
	}
	
	public final void generic_spec_case() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST generic_spec_case_AST = null;
		
		{
		switch ( LA(1)) {
		case FORALL:
		case LET:
		case OLD:
		{
			spec_var_decls();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case IDENT:
		case LCURLY_VBAR:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case WHEN:
		case WHEN_REDUNDANTLY:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case IDENT:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case WHEN:
		case WHEN_REDUNDANTLY:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		{
			spec_header();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case LCURLY_VBAR:
			case ASSIGNABLE:
			case MODIFIABLE:
			case MODIFIES:
			case ASSIGNABLE_REDUNDANTLY:
			case MODIFIABLE_REDUNDANTLY:
			case MODIFIES_REDUNDANTLY:
			case ENSURES:
			case POST:
			case ENSURES_REDUNDANTLY:
			case POST_REDUNDANTLY:
			case SIGNALS:
			case SIGNALS_REDUNDANTLY:
			case EXSURES:
			case EXSURES_REDUNDANTLY:
			case DIVERGES:
			case DIVERGES_REDUNDANTLY:
			{
				generic_spec_body();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case EOF:
			case MODEL:
			case SEMI:
			case IDENT:
			case T_TYPEOFALLTYPES:
			case LITERAL_private:
			case LITERAL_public:
			case LITERAL_protected:
			case LITERAL_static:
			case LITERAL_transient:
			case LITERAL_final:
			case LITERAL_abstract:
			case LITERAL_native:
			case LITERAL_synchronized:
			case LITERAL_const:
			case LITERAL_volatile:
			case LITERAL_strictfp:
			case LCURLY:
			case STATIC_INITIALIZER:
			case INITIALIZER:
			case PURE:
			case INSTANCE:
			case SPEC_PUBLIC:
			case SPEC_PROTECTED:
			case MONITORED:
			case UNINITIALIZED:
			case GHOST:
			case NON_NULL:
			case LITERAL_void:
			case ALSO:
			case FOR_EXAMPLE:
			case IMPLIES_THAT:
			case SUBCLASSING_CONTRACT:
			case VBAR_RCURLY:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		case LCURLY_VBAR:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			generic_spec_body();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			generic_spec_case_AST = (AST)currentAST.root;
			generic_spec_case_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(SPEC_CASE,"generic_spec_case")).add(generic_spec_case_AST));
			currentAST.root = generic_spec_case_AST;
			currentAST.child = generic_spec_case_AST!=null &&generic_spec_case_AST.getFirstChild()!=null ?
				generic_spec_case_AST.getFirstChild() : generic_spec_case_AST;
			currentAST.advanceChildToEnd();
		}
		generic_spec_case_AST = (AST)currentAST.root;
		returnAST = generic_spec_case_AST;
	}
	
	public final void behavior_spec() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST behavior_spec_AST = null;
		
		switch ( LA(1)) {
		case BEHAVIOR:
		{
			AST tmp179_AST = null;
			tmp179_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp179_AST);
			match(BEHAVIOR);
			generic_spec_case();
			astFactory.addASTChild(currentAST, returnAST);
			behavior_spec_AST = (AST)currentAST.root;
			break;
		}
		case EXCEPTIONAL_BEHAVIOR:
		{
			AST tmp180_AST = null;
			tmp180_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp180_AST);
			match(EXCEPTIONAL_BEHAVIOR);
			exceptional_spec_case();
			astFactory.addASTChild(currentAST, returnAST);
			behavior_spec_AST = (AST)currentAST.root;
			break;
		}
		case NORMAL_BEHAVIOR:
		{
			AST tmp181_AST = null;
			tmp181_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp181_AST);
			match(NORMAL_BEHAVIOR);
			normal_spec_case();
			astFactory.addASTChild(currentAST, returnAST);
			behavior_spec_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = behavior_spec_AST;
	}
	
	public final void model_program() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST model_program_AST = null;
		
		AST tmp182_AST = null;
		tmp182_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp182_AST);
		match(MODEL_PROGRAM);
		compound_statement(with_jml);
		astFactory.addASTChild(currentAST, returnAST);
		model_program_AST = (AST)currentAST.root;
		returnAST = model_program_AST;
	}
	
	public final void accessible_clause_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST accessible_clause_seq_AST = null;
		
		{
		int _cnt228=0;
		_loop228:
		do {
			if ((LA(1)==ACCESSIBLE||LA(1)==ACCESSIBLE_REDUNDANTLY)) {
				accessible_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt228>=1 ) { break _loop228; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt228++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			accessible_clause_seq_AST = (AST)currentAST.root;
			accessible_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(ACCESSIBLE_SEQ,"accessible_seq")).add(accessible_clause_seq_AST));
			currentAST.root = accessible_clause_seq_AST;
			currentAST.child = accessible_clause_seq_AST!=null &&accessible_clause_seq_AST.getFirstChild()!=null ?
				accessible_clause_seq_AST.getFirstChild() : accessible_clause_seq_AST;
			currentAST.advanceChildToEnd();
		}
		accessible_clause_seq_AST = (AST)currentAST.root;
		returnAST = accessible_clause_seq_AST;
	}
	
	public final void callable_clause_seq_opt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST callable_clause_seq_opt_AST = null;
		
		{
		_loop242:
		do {
			if ((LA(1)==CALLABLE||LA(1)==CALLABLE_REDUNDANTLY)) {
				callable_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop242;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			callable_clause_seq_opt_AST = (AST)currentAST.root;
			callable_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(CALLABLE_SEQ,"callable_seq")).add(callable_clause_seq_opt_AST));
			currentAST.root = callable_clause_seq_opt_AST;
			currentAST.child = callable_clause_seq_opt_AST!=null &&callable_clause_seq_opt_AST.getFirstChild()!=null ?
				callable_clause_seq_opt_AST.getFirstChild() : callable_clause_seq_opt_AST;
			currentAST.advanceChildToEnd();
		}
		callable_clause_seq_opt_AST = (AST)currentAST.root;
		returnAST = callable_clause_seq_opt_AST;
	}
	
	public final void callable_clause_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST callable_clause_seq_AST = null;
		
		{
		int _cnt239=0;
		_loop239:
		do {
			if ((LA(1)==CALLABLE||LA(1)==CALLABLE_REDUNDANTLY)) {
				callable_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt239>=1 ) { break _loop239; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt239++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			callable_clause_seq_AST = (AST)currentAST.root;
			callable_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(CALLABLE_SEQ,"callable_seq")).add(callable_clause_seq_AST));
			currentAST.root = callable_clause_seq_AST;
			currentAST.child = callable_clause_seq_AST!=null &&callable_clause_seq_AST.getFirstChild()!=null ?
				callable_clause_seq_AST.getFirstChild() : callable_clause_seq_AST;
			currentAST.advanceChildToEnd();
		}
		callable_clause_seq_AST = (AST)currentAST.root;
		returnAST = callable_clause_seq_AST;
	}
	
	public final void accessible_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST accessible_clause_AST = null;
		
		{
		switch ( LA(1)) {
		case ACCESSIBLE:
		{
			AST tmp183_AST = null;
			tmp183_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp183_AST);
			match(ACCESSIBLE);
			break;
		}
		case ACCESSIBLE_REDUNDANTLY:
		{
			AST tmp184_AST = null;
			tmp184_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp184_AST);
			match(ACCESSIBLE_REDUNDANTLY);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		object_references();
		astFactory.addASTChild(currentAST, returnAST);
		match(SEMI);
		if ( inputState.guessing==0 ) {
			accessible_clause_AST = (AST)currentAST.root;
			accessible_clause_AST.setType(ACCESSIBLE_KEYWORD);
		}
		accessible_clause_AST = (AST)currentAST.root;
		returnAST = accessible_clause_AST;
	}
	
	public final void object_references() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST object_references_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		case LITERAL_super:
		case LITERAL_this:
		case T_OTHER:
		{
			object_ref();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop233:
			do {
				if ((LA(1)==COMMA)) {
					AST tmp186_AST = null;
					tmp186_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp186_AST);
					match(COMMA);
					object_ref();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop233;
				}
				
			} while (true);
			}
			object_references_AST = (AST)currentAST.root;
			break;
		}
		case T_EVERYTHING:
		case T_NOT_SPECIFIED:
		case T_NOTHING:
		{
			store_ref_keyword();
			astFactory.addASTChild(currentAST, returnAST);
			object_references_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = object_references_AST;
	}
	
	public final void object_ref() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST object_ref_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		case LITERAL_super:
		case LITERAL_this:
		{
			store_ref_expression();
			astFactory.addASTChild(currentAST, returnAST);
			object_ref_AST = (AST)currentAST.root;
			break;
		}
		case T_OTHER:
		{
			AST tmp187_AST = null;
			tmp187_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp187_AST);
			match(T_OTHER);
			{
			_loop236:
			do {
				switch ( LA(1)) {
				case DOT:
				{
					AST tmp188_AST = null;
					tmp188_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp188_AST);
					match(DOT);
					AST tmp189_AST = null;
					tmp189_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp189_AST);
					match(IDENT);
					break;
				}
				case LBRACK:
				{
					AST tmp190_AST = null;
					tmp190_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp190_AST);
					match(LBRACK);
					spec_array_ref_expr();
					astFactory.addASTChild(currentAST, returnAST);
					match(RBRACK);
					break;
				}
				default:
				{
					break _loop236;
				}
				}
			} while (true);
			}
			object_ref_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = object_ref_AST;
	}
	
	public final void store_ref_keyword() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST store_ref_keyword_AST = null;
		
		switch ( LA(1)) {
		case T_NOTHING:
		{
			AST tmp192_AST = null;
			tmp192_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp192_AST);
			match(T_NOTHING);
			store_ref_keyword_AST = (AST)currentAST.root;
			break;
		}
		case T_EVERYTHING:
		{
			AST tmp193_AST = null;
			tmp193_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp193_AST);
			match(T_EVERYTHING);
			store_ref_keyword_AST = (AST)currentAST.root;
			break;
		}
		case T_NOT_SPECIFIED:
		{
			AST tmp194_AST = null;
			tmp194_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp194_AST);
			match(T_NOT_SPECIFIED);
			store_ref_keyword_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = store_ref_keyword_AST;
	}
	
	public final void store_ref_expression() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST store_ref_expression_AST = null;
		
		{
		switch ( LA(1)) {
		case IDENT:
		{
			AST tmp195_AST = null;
			tmp195_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp195_AST);
			match(IDENT);
			break;
		}
		case LITERAL_this:
		{
			AST tmp196_AST = null;
			tmp196_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp196_AST);
			match(LITERAL_this);
			break;
		}
		case LITERAL_super:
		{
			AST tmp197_AST = null;
			tmp197_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp197_AST);
			match(LITERAL_super);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		_loop364:
		do {
			switch ( LA(1)) {
			case DOT:
			{
				AST tmp198_AST = null;
				tmp198_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp198_AST);
				match(DOT);
				AST tmp199_AST = null;
				tmp199_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp199_AST);
				match(IDENT);
				break;
			}
			case LBRACK:
			{
				AST tmp200_AST = null;
				tmp200_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp200_AST);
				match(LBRACK);
				spec_array_ref_expr();
				astFactory.addASTChild(currentAST, returnAST);
				match(RBRACK);
				break;
			}
			case LPAREN:
			{
				AST tmp202_AST = null;
				tmp202_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp202_AST);
				match(LPAREN);
				{
				switch ( LA(1)) {
				case IDENT:
				case LPAREN:
				case STRING_LITERAL:
				case LITERAL_super:
				case LITERAL_this:
				case LITERAL_new:
				case LITERAL_void:
				case PLUS:
				case MINUS:
				case INC:
				case DEC:
				case BNOT:
				case LNOT:
				case LITERAL_true:
				case LITERAL_false:
				case LITERAL_null:
				case T_RESULT:
				case T_OLD:
				case T_NOT_MODIFIED:
				case T_FRESH:
				case T_REACH:
				case T_NONNULLELEMENTS:
				case T_TYPEOF:
				case T_ELEMTYPE:
				case T_TYPE:
				case T_LOCKSET:
				case T_IS_INITIALIZED:
				case T_INVARIANT_FOR:
				case INFORMAL_DESCRIPTION:
				case LITERAL_boolean:
				case LITERAL_byte:
				case LITERAL_char:
				case LITERAL_short:
				case LITERAL_int:
				case LITERAL_long:
				case LITERAL_float:
				case LITERAL_double:
				case NUM_INT:
				case CHAR_LITERAL:
				case NUM_FLOAT:
				{
					spec_expression_list();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				case RPAREN:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				match(RPAREN);
				break;
			}
			default:
			{
				break _loop364;
			}
			}
		} while (true);
		}
		store_ref_expression_AST = (AST)currentAST.root;
		returnAST = store_ref_expression_AST;
	}
	
	public final void spec_array_ref_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST spec_array_ref_expr_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		case LPAREN:
		case STRING_LITERAL:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_new:
		case LITERAL_void:
		case PLUS:
		case MINUS:
		case INC:
		case DEC:
		case BNOT:
		case LNOT:
		case LITERAL_true:
		case LITERAL_false:
		case LITERAL_null:
		case T_RESULT:
		case T_OLD:
		case T_NOT_MODIFIED:
		case T_FRESH:
		case T_REACH:
		case T_NONNULLELEMENTS:
		case T_TYPEOF:
		case T_ELEMTYPE:
		case T_TYPE:
		case T_LOCKSET:
		case T_IS_INITIALIZED:
		case T_INVARIANT_FOR:
		case INFORMAL_DESCRIPTION:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_short:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_float:
		case LITERAL_double:
		case NUM_INT:
		case CHAR_LITERAL:
		case NUM_FLOAT:
		{
			spec_expression();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case DOT_DOT:
			{
				AST tmp204_AST = null;
				tmp204_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp204_AST);
				match(DOT_DOT);
				spec_expression();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case RBRACK:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			spec_array_ref_expr_AST = (AST)currentAST.root;
			break;
		}
		case STAR:
		{
			AST tmp205_AST = null;
			tmp205_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp205_AST);
			match(STAR);
			if ( inputState.guessing==0 ) {
				spec_array_ref_expr_AST = (AST)currentAST.root;
				spec_array_ref_expr_AST = (AST)astFactory.make( (new ASTArray(1)).add(astFactory.create(STAR_ELEMS,"*")));
				currentAST.root = spec_array_ref_expr_AST;
				currentAST.child = spec_array_ref_expr_AST!=null &&spec_array_ref_expr_AST.getFirstChild()!=null ?
					spec_array_ref_expr_AST.getFirstChild() : spec_array_ref_expr_AST;
				currentAST.advanceChildToEnd();
			}
			spec_array_ref_expr_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = spec_array_ref_expr_AST;
	}
	
	public final void callable_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST callable_clause_AST = null;
		
		{
		switch ( LA(1)) {
		case CALLABLE:
		{
			AST tmp206_AST = null;
			tmp206_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp206_AST);
			match(CALLABLE);
			break;
		}
		case CALLABLE_REDUNDANTLY:
		{
			AST tmp207_AST = null;
			tmp207_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp207_AST);
			match(CALLABLE_REDUNDANTLY);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		callable_methods();
		astFactory.addASTChild(currentAST, returnAST);
		match(SEMI);
		if ( inputState.guessing==0 ) {
			callable_clause_AST = (AST)currentAST.root;
			callable_clause_AST.setType(CALLABLE_KEYWORD);
		}
		callable_clause_AST = (AST)currentAST.root;
		returnAST = callable_clause_AST;
	}
	
	public final void callable_methods() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST callable_methods_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		case LITERAL_super:
		case LITERAL_this:
		case T_OTHER:
		case LITERAL_new:
		{
			method_name_list();
			astFactory.addASTChild(currentAST, returnAST);
			callable_methods_AST = (AST)currentAST.root;
			break;
		}
		case T_EVERYTHING:
		case T_NOT_SPECIFIED:
		case T_NOTHING:
		{
			store_ref_keyword();
			astFactory.addASTChild(currentAST, returnAST);
			callable_methods_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = callable_methods_AST;
	}
	
	public final void generic_spec_body() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST generic_spec_body_AST = null;
		
		switch ( LA(1)) {
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			simple_spec_body();
			astFactory.addASTChild(currentAST, returnAST);
			generic_spec_body_AST = (AST)currentAST.root;
			break;
		}
		case LCURLY_VBAR:
		{
			AST tmp209_AST = null;
			tmp209_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp209_AST);
			match(LCURLY_VBAR);
			generic_spec_case_seq();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp210_AST = null;
			tmp210_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp210_AST);
			match(VBAR_RCURLY);
			generic_spec_body_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = generic_spec_body_AST;
	}
	
	public final void label_decl() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST label_decl_AST = null;
		
		AST tmp211_AST = null;
		tmp211_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp211_AST);
		match(IDENT);
		AST tmp212_AST = null;
		tmp212_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp212_AST);
		match(COLON);
		if ( inputState.guessing==0 ) {
			label_decl_AST = (AST)currentAST.root;
			label_decl_AST.setType(LABEL_KEYWORD);
		}
		label_decl_AST = (AST)currentAST.root;
		returnAST = label_decl_AST;
	}
	
	public final void requires_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST requires_clause_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case REQUIRES:
			{
				AST tmp213_AST = null;
				tmp213_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp213_AST);
				match(REQUIRES);
				break;
			}
			case PRE:
			{
				AST tmp214_AST = null;
				tmp214_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp214_AST);
				match(PRE);
				break;
			}
			case REQUIRES_REDUNDANTLY:
			{
				AST tmp215_AST = null;
				tmp215_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp215_AST);
				match(REQUIRES_REDUNDANTLY);
				break;
			}
			case PRE_REDUNDANTLY:
			{
				AST tmp216_AST = null;
				tmp216_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp216_AST);
				match(PRE_REDUNDANTLY);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case T_NOT_SPECIFIED:
			{
				AST tmp217_AST = null;
				tmp217_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp217_AST);
				match(T_NOT_SPECIFIED);
				break;
			}
			case IDENT:
			case LPAREN:
			case STRING_LITERAL:
			case LITERAL_super:
			case LITERAL_this:
			case LITERAL_new:
			case LITERAL_void:
			case PLUS:
			case MINUS:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case T_RESULT:
			case T_OLD:
			case T_NOT_MODIFIED:
			case T_FRESH:
			case T_REACH:
			case T_NONNULLELEMENTS:
			case T_TYPEOF:
			case T_ELEMTYPE:
			case T_TYPE:
			case T_LOCKSET:
			case T_IS_INITIALIZED:
			case T_INVARIANT_FOR:
			case INFORMAL_DESCRIPTION:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			case NUM_INT:
			case CHAR_LITERAL:
			case NUM_FLOAT:
			{
				pre_cond();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
			if ( inputState.guessing==0 ) {
				requires_clause_AST = (AST)currentAST.root;
				requires_clause_AST.setType(REQUIRES_KEYWORD);
			}
			requires_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToJmlSpecKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = requires_clause_AST;
	}
	
	public final void when_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST when_clause_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case WHEN:
			{
				AST tmp219_AST = null;
				tmp219_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp219_AST);
				match(WHEN);
				break;
			}
			case WHEN_REDUNDANTLY:
			{
				AST tmp220_AST = null;
				tmp220_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp220_AST);
				match(WHEN_REDUNDANTLY);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case T_NOT_SPECIFIED:
			{
				AST tmp221_AST = null;
				tmp221_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp221_AST);
				match(T_NOT_SPECIFIED);
				break;
			}
			case IDENT:
			case LPAREN:
			case STRING_LITERAL:
			case LITERAL_super:
			case LITERAL_this:
			case LITERAL_new:
			case LITERAL_void:
			case PLUS:
			case MINUS:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case T_RESULT:
			case T_OLD:
			case T_NOT_MODIFIED:
			case T_FRESH:
			case T_REACH:
			case T_NONNULLELEMENTS:
			case T_TYPEOF:
			case T_ELEMTYPE:
			case T_TYPE:
			case T_LOCKSET:
			case T_IS_INITIALIZED:
			case T_INVARIANT_FOR:
			case INFORMAL_DESCRIPTION:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			case NUM_INT:
			case CHAR_LITERAL:
			case NUM_FLOAT:
			{
				predicate();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
			if ( inputState.guessing==0 ) {
				when_clause_AST = (AST)currentAST.root;
				when_clause_AST.setType(WHEN_KEYWORD);
			}
			when_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToJmlSpecKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = when_clause_AST;
	}
	
	public final void measured_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST measured_clause_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case MEASURED_BY:
			{
				AST tmp223_AST = null;
				tmp223_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp223_AST);
				match(MEASURED_BY);
				break;
			}
			case MEASURED_BY_REDUNDANTLY:
			{
				AST tmp224_AST = null;
				tmp224_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp224_AST);
				match(MEASURED_BY_REDUNDANTLY);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case T_NOT_SPECIFIED:
			{
				AST tmp225_AST = null;
				tmp225_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp225_AST);
				match(T_NOT_SPECIFIED);
				break;
			}
			case IDENT:
			case LPAREN:
			case STRING_LITERAL:
			case LITERAL_super:
			case LITERAL_this:
			case LITERAL_new:
			case LITERAL_void:
			case PLUS:
			case MINUS:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case T_RESULT:
			case T_OLD:
			case T_NOT_MODIFIED:
			case T_FRESH:
			case T_REACH:
			case T_NONNULLELEMENTS:
			case T_TYPEOF:
			case T_ELEMTYPE:
			case T_TYPE:
			case T_LOCKSET:
			case T_IS_INITIALIZED:
			case T_INVARIANT_FOR:
			case INFORMAL_DESCRIPTION:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			case NUM_INT:
			case CHAR_LITERAL:
			case NUM_FLOAT:
			{
				spec_expression();
				astFactory.addASTChild(currentAST, returnAST);
				{
				switch ( LA(1)) {
				case LITERAL_if:
				{
					AST tmp226_AST = null;
					tmp226_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp226_AST);
					match(LITERAL_if);
					predicate();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				case SEMI:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
			if ( inputState.guessing==0 ) {
				measured_clause_AST = (AST)currentAST.root;
				measured_clause_AST.setType(MEASURED_BY_KEYWORD);
			}
			measured_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToJmlSpecKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = measured_clause_AST;
	}
	
	public final void generic_spec_case_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST generic_spec_case_seq_AST = null;
		
		generic_spec_case();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop274:
		do {
			if ((LA(1)==ALSO)) {
				AST tmp228_AST = null;
				tmp228_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp228_AST);
				match(ALSO);
				generic_spec_case();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop274;
			}
			
		} while (true);
		}
		generic_spec_case_seq_AST = (AST)currentAST.root;
		returnAST = generic_spec_case_seq_AST;
	}
	
	public final void diverges_clause_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST diverges_clause_seq_AST = null;
		
		{
		int _cnt402=0;
		_loop402:
		do {
			if ((LA(1)==DIVERGES||LA(1)==DIVERGES_REDUNDANTLY)) {
				diverges_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt402>=1 ) { break _loop402; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt402++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			diverges_clause_seq_AST = (AST)currentAST.root;
			
			diverges_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(DIV_SEQ,"diverges_seq")).add(diverges_clause_seq_AST));
			
			currentAST.root = diverges_clause_seq_AST;
			currentAST.child = diverges_clause_seq_AST!=null &&diverges_clause_seq_AST.getFirstChild()!=null ?
				diverges_clause_seq_AST.getFirstChild() : diverges_clause_seq_AST;
			currentAST.advanceChildToEnd();
		}
		diverges_clause_seq_AST = (AST)currentAST.root;
		returnAST = diverges_clause_seq_AST;
	}
	
	public final void exceptional_spec_case() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST exceptional_spec_case_AST = null;
		
		{
		switch ( LA(1)) {
		case FORALL:
		case LET:
		case OLD:
		{
			spec_var_decls();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case IDENT:
		case LCURLY_VBAR:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case WHEN:
		case WHEN_REDUNDANTLY:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case IDENT:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case WHEN:
		case WHEN_REDUNDANTLY:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		{
			spec_header();
			astFactory.addASTChild(currentAST, returnAST);
			{
			if ((_tokenSet_25.member(LA(1))) && (_tokenSet_26.member(LA(2)))) {
				exceptional_spec_case_body();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else if ((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			break;
		}
		case LCURLY_VBAR:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		{
			exceptional_spec_case_body();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			exceptional_spec_case_AST = (AST)currentAST.root;
			exceptional_spec_case_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(SPEC_CASE,"exceptional_spec_case")).add(exceptional_spec_case_AST));
			currentAST.root = exceptional_spec_case_AST;
			currentAST.child = exceptional_spec_case_AST!=null &&exceptional_spec_case_AST.getFirstChild()!=null ?
				exceptional_spec_case_AST.getFirstChild() : exceptional_spec_case_AST;
			currentAST.advanceChildToEnd();
		}
		exceptional_spec_case_AST = (AST)currentAST.root;
		returnAST = exceptional_spec_case_AST;
	}
	
	public final void normal_spec_case() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST normal_spec_case_AST = null;
		
		{
		switch ( LA(1)) {
		case FORALL:
		case LET:
		case OLD:
		{
			spec_var_decls();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case IDENT:
		case LCURLY_VBAR:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case WHEN:
		case WHEN_REDUNDANTLY:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case IDENT:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case WHEN:
		case WHEN_REDUNDANTLY:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		{
			spec_header();
			astFactory.addASTChild(currentAST, returnAST);
			{
			if ((_tokenSet_29.member(LA(1))) && (_tokenSet_30.member(LA(2)))) {
				normal_spec_case_body();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else if ((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			break;
		}
		case LCURLY_VBAR:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		{
			normal_spec_case_body();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			normal_spec_case_AST = (AST)currentAST.root;
			normal_spec_case_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(SPEC_CASE,"normal_spec_case")).add(normal_spec_case_AST));
			currentAST.root = normal_spec_case_AST;
			currentAST.child = normal_spec_case_AST!=null &&normal_spec_case_AST.getFirstChild()!=null ?
				normal_spec_case_AST.getFirstChild() : normal_spec_case_AST;
			currentAST.advanceChildToEnd();
		}
		normal_spec_case_AST = (AST)currentAST.root;
		returnAST = normal_spec_case_AST;
	}
	
	public final void exceptional_spec_case_body() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST exceptional_spec_case_body_AST = null;
		
		switch ( LA(1)) {
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		{
			assignable_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			signals_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			diverges_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			exceptional_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		{
			signals_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			diverges_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			exceptional_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case LCURLY_VBAR:
		{
			AST tmp229_AST = null;
			tmp229_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp229_AST);
			match(LCURLY_VBAR);
			exceptional_spec_case_seq();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp230_AST = null;
			tmp230_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp230_AST);
			match(VBAR_RCURLY);
			exceptional_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = exceptional_spec_case_body_AST;
	}
	
	public final void exceptional_spec_case_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST exceptional_spec_case_seq_AST = null;
		
		exceptional_spec_case();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop284:
		do {
			if ((LA(1)==ALSO)) {
				AST tmp231_AST = null;
				tmp231_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp231_AST);
				match(ALSO);
				exceptional_spec_case();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop284;
			}
			
		} while (true);
		}
		exceptional_spec_case_seq_AST = (AST)currentAST.root;
		returnAST = exceptional_spec_case_seq_AST;
	}
	
	public final void normal_spec_case_body() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST normal_spec_case_body_AST = null;
		
		switch ( LA(1)) {
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		{
			assignable_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			ensures_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			diverges_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			normal_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		{
			ensures_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			diverges_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			normal_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case LCURLY_VBAR:
		{
			AST tmp232_AST = null;
			tmp232_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp232_AST);
			match(LCURLY_VBAR);
			normal_spec_case_seq();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp233_AST = null;
			tmp233_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp233_AST);
			match(VBAR_RCURLY);
			normal_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = normal_spec_case_body_AST;
	}
	
	public final void normal_spec_case_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST normal_spec_case_seq_AST = null;
		
		normal_spec_case();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop292:
		do {
			if ((LA(1)==ALSO)) {
				AST tmp234_AST = null;
				tmp234_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp234_AST);
				match(ALSO);
				normal_spec_case();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop292;
			}
			
		} while (true);
		}
		normal_spec_case_seq_AST = (AST)currentAST.root;
		returnAST = normal_spec_case_seq_AST;
	}
	
	public final void forall_var_decl() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST forall_var_decl_AST = null;
		
		AST tmp235_AST = null;
		tmp235_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp235_AST);
		match(FORALL);
		quantified_var_decl();
		astFactory.addASTChild(currentAST, returnAST);
		match(SEMI);
		forall_var_decl_AST = (AST)currentAST.root;
		returnAST = forall_var_decl_AST;
	}
	
	public final void let_var_decls() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST let_var_decls_AST = null;
		Token  lk = null;
		AST lk_AST = null;
		
		{
		switch ( LA(1)) {
		case LET:
		{
			lk = LT(1);
			lk_AST = astFactory.create(lk);
			astFactory.makeASTRoot(currentAST, lk_AST);
			match(LET);
			if ( inputState.guessing==0 ) {
				reportWarning("The keyword `let' is deprecated, use `old' instead.",
				lk.getLine(), lk.getColumn());
				
			}
			break;
		}
		case OLD:
		{
			AST tmp237_AST = null;
			tmp237_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp237_AST);
			match(OLD);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		int _cnt302=0;
		_loop302:
		do {
			if ((LA(1)==MODEL||LA(1)==GHOST)) {
				local_spec_var_decl();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt302>=1 ) { break _loop302; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt302++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			let_var_decls_AST = (AST)currentAST.root;
			let_var_decls_AST.setType(LETOLD_KEYWORD);
		}
		let_var_decls_AST = (AST)currentAST.root;
		returnAST = let_var_decls_AST;
	}
	
	public final void quantified_var_decl() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST quantified_var_decl_AST = null;
		
		type_spec();
		astFactory.addASTChild(currentAST, returnAST);
		quantified_var_declarators();
		astFactory.addASTChild(currentAST, returnAST);
		if ( inputState.guessing==0 ) {
			quantified_var_decl_AST = (AST)currentAST.root;
			quantified_var_decl_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(QUANT_VARS,"quantified_var_decl")).add(quantified_var_decl_AST));
			currentAST.root = quantified_var_decl_AST;
			currentAST.child = quantified_var_decl_AST!=null &&quantified_var_decl_AST.getFirstChild()!=null ?
				quantified_var_decl_AST.getFirstChild() : quantified_var_decl_AST;
			currentAST.advanceChildToEnd();
		}
		quantified_var_decl_AST = (AST)currentAST.root;
		returnAST = quantified_var_decl_AST;
	}
	
	public final void local_spec_var_decl() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST local_spec_var_decl_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case MODEL:
			{
				AST tmp238_AST = null;
				tmp238_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp238_AST);
				match(MODEL);
				break;
			}
			case GHOST:
			{
				AST tmp239_AST = null;
				tmp239_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp239_AST);
				match(GHOST);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			type_spec();
			astFactory.addASTChild(currentAST, returnAST);
			variable_declarators(no_side_effects);
			astFactory.addASTChild(currentAST, returnAST);
			match(SEMI);
			local_spec_var_decl_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToJmlSpecKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = local_spec_var_decl_AST;
	}
	
	public final void requires_clause_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST requires_clause_seq_AST = null;
		
		{
		int _cnt307=0;
		_loop307:
		do {
			if (((LA(1) >= REQUIRES && LA(1) <= PRE_REDUNDANTLY))) {
				requires_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt307>=1 ) { break _loop307; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt307++;
		} while (true);
		}
		requires_clause_seq_AST = (AST)currentAST.root;
		returnAST = requires_clause_seq_AST;
	}
	
	public final void pre_cond() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST pre_cond_AST = null;
		
		predicate();
		astFactory.addASTChild(currentAST, returnAST);
		pre_cond_AST = (AST)currentAST.root;
		returnAST = pre_cond_AST;
	}
	
	public final void when_clause_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST when_clause_seq_AST = null;
		
		{
		int _cnt314=0;
		_loop314:
		do {
			if ((LA(1)==WHEN||LA(1)==WHEN_REDUNDANTLY)) {
				when_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt314>=1 ) { break _loop314; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt314++;
		} while (true);
		}
		when_clause_seq_AST = (AST)currentAST.root;
		returnAST = when_clause_seq_AST;
	}
	
	public final void measured_clause_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST measured_clause_seq_AST = null;
		
		{
		int _cnt320=0;
		_loop320:
		do {
			if ((LA(1)==MEASURED_BY||LA(1)==MEASURED_BY_REDUNDANTLY)) {
				measured_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt320>=1 ) { break _loop320; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt320++;
		} while (true);
		}
		measured_clause_seq_AST = (AST)currentAST.root;
		returnAST = measured_clause_seq_AST;
	}
	
	public final void label_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST label_statement_AST = null;
		
		AST tmp241_AST = null;
		tmp241_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp241_AST);
		match(LABEL);
		label_statement_list();
		astFactory.addASTChild(currentAST, returnAST);
		match(SEMI);
		if ( inputState.guessing==0 ) {
			label_statement_AST = (AST)currentAST.root;
			label_statement_AST.setType(LABEL_KEYWORD);
		}
		label_statement_AST = (AST)currentAST.root;
		returnAST = label_statement_AST;
	}
	
	public final void label_statement_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST label_statement_list_AST = null;
		
		AST tmp243_AST = null;
		tmp243_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp243_AST);
		match(IDENT);
		{
		_loop329:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp244_AST = null;
				tmp244_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp244_AST);
				match(COMMA);
				AST tmp245_AST = null;
				tmp245_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp245_AST);
				match(IDENT);
			}
			else {
				break _loop329;
			}
			
		} while (true);
		}
		label_statement_list_AST = (AST)currentAST.root;
		returnAST = label_statement_list_AST;
	}
	
	public final void loop_assignable_clause_seq_opt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST loop_assignable_clause_seq_opt_AST = null;
		
		{
		_loop332:
		do {
			if ((LA(1)==LOOP_MODIFIES)) {
				loop_assignable_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop332;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			loop_assignable_clause_seq_opt_AST = (AST)currentAST.root;
			loop_assignable_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(LOOP_ASGNABLE_SEQ,"loop_assignable_seq")).add(loop_assignable_clause_seq_opt_AST)); 
			
			currentAST.root = loop_assignable_clause_seq_opt_AST;
			currentAST.child = loop_assignable_clause_seq_opt_AST!=null &&loop_assignable_clause_seq_opt_AST.getFirstChild()!=null ?
				loop_assignable_clause_seq_opt_AST.getFirstChild() : loop_assignable_clause_seq_opt_AST;
			currentAST.advanceChildToEnd();
		}
		loop_assignable_clause_seq_opt_AST = (AST)currentAST.root;
		returnAST = loop_assignable_clause_seq_opt_AST;
	}
	
	public final void loop_assignable_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST loop_assignable_clause_AST = null;
		
		try {      // for error handling
			{
			AST tmp246_AST = null;
			tmp246_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp246_AST);
			match(LOOP_MODIFIES);
			}
			conditional_store_references();
			astFactory.addASTChild(currentAST, returnAST);
			match(SEMI);
			if ( inputState.guessing==0 ) {
				loop_assignable_clause_AST = (AST)currentAST.root;
				loop_assignable_clause_AST.setType(LOOP_ASSIGNABLE_KEYWORD);
			}
			loop_assignable_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToJmlSpecKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = loop_assignable_clause_AST;
	}
	
	public final void loop_assignable_clause_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST loop_assignable_clause_seq_AST = null;
		
		{
		int _cnt335=0;
		_loop335:
		do {
			if ((LA(1)==LOOP_MODIFIES)) {
				loop_assignable_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt335>=1 ) { break _loop335; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt335++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			loop_assignable_clause_seq_AST = (AST)currentAST.root;
			loop_assignable_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(LOOP_ASGNABLE_SEQ,"loop_assignable_seq")).add(loop_assignable_clause_seq_AST)); 
			
			currentAST.root = loop_assignable_clause_seq_AST;
			currentAST.child = loop_assignable_clause_seq_AST!=null &&loop_assignable_clause_seq_AST.getFirstChild()!=null ?
				loop_assignable_clause_seq_AST.getFirstChild() : loop_assignable_clause_seq_AST;
			currentAST.advanceChildToEnd();
		}
		loop_assignable_clause_seq_AST = (AST)currentAST.root;
		returnAST = loop_assignable_clause_seq_AST;
	}
	
	public final void conditional_store_references() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST conditional_store_references_AST = null;
		
		conditional_store_ref_list();
		astFactory.addASTChild(currentAST, returnAST);
		conditional_store_references_AST = (AST)currentAST.root;
		returnAST = conditional_store_references_AST;
	}
	
	public final void assignable_clause_seq_opt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST assignable_clause_seq_opt_AST = null;
		
		{
		_loop340:
		do {
			if (((LA(1) >= ASSIGNABLE && LA(1) <= MODIFIES_REDUNDANTLY))) {
				assignable_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop340;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			assignable_clause_seq_opt_AST = (AST)currentAST.root;
			assignable_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(ASGNABLE_SEQ,"assignable_seq")).add(assignable_clause_seq_opt_AST)); 
			
			currentAST.root = assignable_clause_seq_opt_AST;
			currentAST.child = assignable_clause_seq_opt_AST!=null &&assignable_clause_seq_opt_AST.getFirstChild()!=null ?
				assignable_clause_seq_opt_AST.getFirstChild() : assignable_clause_seq_opt_AST;
			currentAST.advanceChildToEnd();
		}
		assignable_clause_seq_opt_AST = (AST)currentAST.root;
		returnAST = assignable_clause_seq_opt_AST;
	}
	
	public final void conditional_store_ref_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST conditional_store_ref_list_AST = null;
		
		conditional_store_ref();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop349:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp248_AST = null;
				tmp248_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp248_AST);
				match(COMMA);
				conditional_store_ref();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop349;
			}
			
		} while (true);
		}
		conditional_store_ref_list_AST = (AST)currentAST.root;
		returnAST = conditional_store_ref_list_AST;
	}
	
	public final void conditional_store_ref() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST conditional_store_ref_AST = null;
		
		store_ref();
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case LITERAL_if:
		{
			AST tmp249_AST = null;
			tmp249_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp249_AST);
			match(LITERAL_if);
			predicate();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case SEMI:
		case COMMA:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		conditional_store_ref_AST = (AST)currentAST.root;
		returnAST = conditional_store_ref_AST;
	}
	
	public final void store_ref_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST store_ref_list_AST = null;
		
		store_ref();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop355:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp250_AST = null;
				tmp250_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp250_AST);
				match(COMMA);
				store_ref();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop355;
			}
			
		} while (true);
		}
		store_ref_list_AST = (AST)currentAST.root;
		returnAST = store_ref_list_AST;
	}
	
	public final void informal_desc() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST informal_desc_AST = null;
		Token  id1 = null;
		AST id1_AST = null;
		
		boolean in_ML_JML = lexer.ML_Jml_state;
		
		
		id1 = LT(1);
		id1_AST = astFactory.create(id1);
		match(INFORMAL_DESCRIPTION);
		if ( inputState.guessing==0 ) {
			informal_desc_AST = (AST)currentAST.root;
			if (in_ML_JML) {
			id1_AST.setText(remove_ats_after_newlines(id1_AST.getText()));
			}
			informal_desc_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(DINFORMALLY,"#informally#")).add(id1_AST));
			
			currentAST.root = informal_desc_AST;
			currentAST.child = informal_desc_AST!=null &&informal_desc_AST.getFirstChild()!=null ?
				informal_desc_AST.getFirstChild() : informal_desc_AST;
			currentAST.advanceChildToEnd();
		}
		returnAST = informal_desc_AST;
	}
	
	public final void spec_expression_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST spec_expression_list_AST = null;
		
		spec_expression();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop409:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp251_AST = null;
				tmp251_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp251_AST);
				match(COMMA);
				spec_expression();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop409;
			}
			
		} while (true);
		}
		spec_expression_list_AST = (AST)currentAST.root;
		returnAST = spec_expression_list_AST;
	}
	
	public final void post_cond() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST post_cond_AST = null;
		
		predicate();
		astFactory.addASTChild(currentAST, returnAST);
		post_cond_AST = (AST)currentAST.root;
		returnAST = post_cond_AST;
	}
	
	public final void loop_signals_clause_seq_opt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST loop_signals_clause_seq_opt_AST = null;
		
		{
		_loop379:
		do {
			if ((LA(1)==LOOP_EXSURES)) {
				loop_signals_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop379;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			loop_signals_clause_seq_opt_AST = (AST)currentAST.root;
			
			loop_signals_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(LOOP_SIG_SEQ,"loop_signals_seq")).add(loop_signals_clause_seq_opt_AST));
			
			currentAST.root = loop_signals_clause_seq_opt_AST;
			currentAST.child = loop_signals_clause_seq_opt_AST!=null &&loop_signals_clause_seq_opt_AST.getFirstChild()!=null ?
				loop_signals_clause_seq_opt_AST.getFirstChild() : loop_signals_clause_seq_opt_AST;
			currentAST.advanceChildToEnd();
		}
		loop_signals_clause_seq_opt_AST = (AST)currentAST.root;
		returnAST = loop_signals_clause_seq_opt_AST;
	}
	
	public final void loop_signals_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST loop_signals_clause_AST = null;
		
		String kw = "";
		
		
		try {      // for error handling
			{
			AST tmp252_AST = null;
			tmp252_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp252_AST);
			match(LOOP_EXSURES);
			}
			AST tmp253_AST = null;
			tmp253_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp253_AST);
			match(LPAREN);
			reference_type();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case IDENT:
			{
				AST tmp254_AST = null;
				tmp254_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp254_AST);
				match(IDENT);
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			AST tmp255_AST = null;
			tmp255_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp255_AST);
			match(RPAREN);
			{
			switch ( LA(1)) {
			case T_NOT_SPECIFIED:
			{
				AST tmp256_AST = null;
				tmp256_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp256_AST);
				match(T_NOT_SPECIFIED);
				break;
			}
			case IDENT:
			case LPAREN:
			case STRING_LITERAL:
			case LITERAL_super:
			case LITERAL_this:
			case LITERAL_new:
			case LITERAL_void:
			case PLUS:
			case MINUS:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case T_RESULT:
			case T_OLD:
			case T_NOT_MODIFIED:
			case T_FRESH:
			case T_REACH:
			case T_NONNULLELEMENTS:
			case T_TYPEOF:
			case T_ELEMTYPE:
			case T_TYPE:
			case T_LOCKSET:
			case T_IS_INITIALIZED:
			case T_INVARIANT_FOR:
			case INFORMAL_DESCRIPTION:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			case NUM_INT:
			case CHAR_LITERAL:
			case NUM_FLOAT:
			{
				predicate();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
			if ( inputState.guessing==0 ) {
				loop_signals_clause_AST = (AST)currentAST.root;
				loop_signals_clause_AST.setType(SIGNALS_KEYWORD);
			}
			loop_signals_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToJmlSpecKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = loop_signals_clause_AST;
	}
	
	public final void loop_signals_clause_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST loop_signals_clause_seq_AST = null;
		
		{
		int _cnt382=0;
		_loop382:
		do {
			if ((LA(1)==LOOP_EXSURES)) {
				loop_signals_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt382>=1 ) { break _loop382; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt382++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			loop_signals_clause_seq_AST = (AST)currentAST.root;
			
			loop_signals_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(LOOP_SIG_SEQ,"loop_signals_seq")).add(loop_signals_clause_seq_AST));
			
			currentAST.root = loop_signals_clause_seq_AST;
			currentAST.child = loop_signals_clause_seq_AST!=null &&loop_signals_clause_seq_AST.getFirstChild()!=null ?
				loop_signals_clause_seq_AST.getFirstChild() : loop_signals_clause_seq_AST;
			currentAST.advanceChildToEnd();
		}
		loop_signals_clause_seq_AST = (AST)currentAST.root;
		returnAST = loop_signals_clause_seq_AST;
	}
	
	public final void statement(
		boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST statement_AST = null;
		AST g_AST = null;
		AST c_AST = null;
		AST lm_AST = null;
		AST li_AST = null;
		AST ls_AST = null;
		AST vf_AST = null;
		Token  w = null;
		AST w_AST = null;
		AST we_AST = null;
		AST ws_AST = null;
		Token  d = null;
		AST d_AST = null;
		AST ds_AST = null;
		AST de_AST = null;
		Token  f = null;
		AST f_AST = null;
		AST finit_AST = null;
		AST ftest_AST = null;
		AST fupdater_AST = null;
		AST fstat_AST = null;
		AST mps_AST = null;
		
		switch ( LA(1)) {
		case LCURLY:
		{
			compound_statement(in_model_prog);
			astFactory.addASTChild(currentAST, returnAST);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		{
			spec_statement_jack();
			g_AST = (AST)returnAST;
			compound_statement(in_model_prog);
			c_AST = (AST)returnAST;
			if ( inputState.guessing==0 ) {
				statement_AST = (AST)currentAST.root;
				
							statement_AST = (AST)astFactory.make( (new ASTArray(3)).add(astFactory.create(SPEC_STATEMENT,"spec_statement")).add(g_AST).add(c_AST));
						
				currentAST.root = statement_AST;
				currentAST.child = statement_AST!=null &&statement_AST.getFirstChild()!=null ?
					statement_AST.getFirstChild() : statement_AST;
				currentAST.advanceChildToEnd();
			}
			break;
		}
		case DOC_COMMENT:
		{
			doc_comment();
			{
			if ((LA(1)==LITERAL_class) && (LA(2)==IDENT)) {
				class_definition(in_model_prog);
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					statement_AST = (AST)currentAST.root;
					statement_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(NESTED_CLASS,"nested_class")).add(statement_AST));
					currentAST.root = statement_AST;
					currentAST.child = statement_AST!=null &&statement_AST.getFirstChild()!=null ?
						statement_AST.getFirstChild() : statement_AST;
					currentAST.advanceChildToEnd();
				}
			}
			else if ((LA(1)==LITERAL_final) && (LA(2)==LITERAL_class)) {
				AST tmp258_AST = null;
				tmp258_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp258_AST);
				match(LITERAL_final);
				class_definition(in_model_prog);
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					statement_AST = (AST)currentAST.root;
					statement_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(NESTED_CLASS,"nested_class")).add(statement_AST));
					currentAST.root = statement_AST;
					currentAST.child = statement_AST!=null &&statement_AST.getFirstChild()!=null ?
						statement_AST.getFirstChild() : statement_AST;
					currentAST.advanceChildToEnd();
				}
			}
			else if ((LA(1)==LITERAL_abstract) && (LA(2)==LITERAL_class)) {
				AST tmp259_AST = null;
				tmp259_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp259_AST);
				match(LITERAL_abstract);
				class_definition(in_model_prog);
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					statement_AST = (AST)currentAST.root;
					statement_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(NESTED_CLASS,"nested_class")).add(statement_AST));
					currentAST.root = statement_AST;
					currentAST.child = statement_AST!=null &&statement_AST.getFirstChild()!=null ?
						statement_AST.getFirstChild() : statement_AST;
					currentAST.advanceChildToEnd();
				}
			}
			else if ((_tokenSet_31.member(LA(1))) && (_tokenSet_32.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_class:
		{
			class_definition(in_model_prog);
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				statement_AST = (AST)currentAST.root;
				statement_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(NESTED_CLASS,"nested_class1")).add(statement_AST));
				currentAST.root = statement_AST;
				currentAST.child = statement_AST!=null &&statement_AST.getFirstChild()!=null ?
					statement_AST.getFirstChild() : statement_AST;
				currentAST.advanceChildToEnd();
			}
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_abstract:
		{
			AST tmp260_AST = null;
			tmp260_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp260_AST);
			match(LITERAL_abstract);
			class_definition(in_model_prog);
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				statement_AST = (AST)currentAST.root;
				statement_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(NESTED_CLASS,"nested_class")).add(statement_AST));
				currentAST.root = statement_AST;
				currentAST.child = statement_AST!=null &&statement_AST.getFirstChild()!=null ?
					statement_AST.getFirstChild() : statement_AST;
				currentAST.advanceChildToEnd();
			}
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_if:
		{
			AST tmp261_AST = null;
			tmp261_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp261_AST);
			match(LITERAL_if);
			match(LPAREN);
			expression(side_effects_allowed);
			astFactory.addASTChild(currentAST, returnAST);
			match(RPAREN);
			statement(in_model_prog);
			astFactory.addASTChild(currentAST, returnAST);
			{
			if ((LA(1)==LITERAL_else) && (_tokenSet_17.member(LA(2)))) {
				match(LITERAL_else);
				statement(in_model_prog);
				astFactory.addASTChild(currentAST, returnAST);
			}
			else if ((_tokenSet_31.member(LA(1))) && (_tokenSet_32.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LOOP_MODIFIES:
		case LOOP_EXSURES:
		case LITERAL_while:
		case LITERAL_do:
		case LITERAL_for:
		case MAINTAINING:
		case MAINTAINING_REDUNDANTLY:
		case LOOP_INVARIANT:
		case LOOP_INVARIANT_REDUNDANTLY:
		case DECREASING:
		case DECREASING_REDUNDANTLY:
		case DECREASES:
		case DECREASES_REDUNDANTLY:
		{
			loop_assignable_clause_seq_opt();
			lm_AST = (AST)returnAST;
			loop_invariant_seq_opt();
			li_AST = (AST)returnAST;
			loop_signals_clause_seq_opt();
			ls_AST = (AST)returnAST;
			variant_function_seq_opt();
			vf_AST = (AST)returnAST;
			{
			switch ( LA(1)) {
			case LITERAL_while:
			{
				w = LT(1);
				w_AST = astFactory.create(w);
				match(LITERAL_while);
				match(LPAREN);
				expression(side_effects_allowed);
				we_AST = (AST)returnAST;
				match(RPAREN);
				statement(in_model_prog);
				ws_AST = (AST)returnAST;
				if ( inputState.guessing==0 ) {
					statement_AST = (AST)currentAST.root;
					statement_AST = (AST)astFactory.make( (new ASTArray(7)).add(w_AST).add(lm_AST).add(li_AST).add(ls_AST).add(vf_AST).add(we_AST).add(ws_AST));
					currentAST.root = statement_AST;
					currentAST.child = statement_AST!=null &&statement_AST.getFirstChild()!=null ?
						statement_AST.getFirstChild() : statement_AST;
					currentAST.advanceChildToEnd();
				}
				break;
			}
			case LITERAL_do:
			{
				d = LT(1);
				d_AST = astFactory.create(d);
				match(LITERAL_do);
				statement(in_model_prog);
				ds_AST = (AST)returnAST;
				match(LITERAL_while);
				match(LPAREN);
				expression(side_effects_allowed);
				de_AST = (AST)returnAST;
				match(RPAREN);
				match(SEMI);
				if ( inputState.guessing==0 ) {
					statement_AST = (AST)currentAST.root;
					statement_AST = (AST)astFactory.make( (new ASTArray(7)).add(d_AST).add(lm_AST).add(li_AST).add(ls_AST).add(vf_AST).add(ds_AST).add(de_AST));
					currentAST.root = statement_AST;
					currentAST.child = statement_AST!=null &&statement_AST.getFirstChild()!=null ?
						statement_AST.getFirstChild() : statement_AST;
					currentAST.advanceChildToEnd();
				}
				break;
			}
			case LITERAL_for:
			{
				f = LT(1);
				f_AST = astFactory.create(f);
				match(LITERAL_for);
				AST tmp271_AST = null;
				tmp271_AST = astFactory.create(LT(1));
				match(LPAREN);
				for_init();
				finit_AST = (AST)returnAST;
				AST tmp272_AST = null;
				tmp272_AST = astFactory.create(LT(1));
				match(SEMI);
				for_test();
				ftest_AST = (AST)returnAST;
				AST tmp273_AST = null;
				tmp273_AST = astFactory.create(LT(1));
				match(SEMI);
				for_updater();
				fupdater_AST = (AST)returnAST;
				AST tmp274_AST = null;
				tmp274_AST = astFactory.create(LT(1));
				match(RPAREN);
				statement(in_model_prog);
				fstat_AST = (AST)returnAST;
				if ( inputState.guessing==0 ) {
					statement_AST = (AST)currentAST.root;
					statement_AST = (AST)astFactory.make( (new ASTArray(9)).add(f_AST).add(finit_AST).add(ftest_AST).add(fupdater_AST).add(lm_AST).add(li_AST).add(ls_AST).add(vf_AST).add(fstat_AST));
					currentAST.root = statement_AST;
					currentAST.child = statement_AST!=null &&statement_AST.getFirstChild()!=null ?
						statement_AST.getFirstChild() : statement_AST;
					currentAST.advanceChildToEnd();
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		case LITERAL_break:
		{
			AST tmp275_AST = null;
			tmp275_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp275_AST);
			match(LITERAL_break);
			{
			switch ( LA(1)) {
			case IDENT:
			{
				AST tmp276_AST = null;
				tmp276_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp276_AST);
				match(IDENT);
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_continue:
		{
			AST tmp278_AST = null;
			tmp278_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp278_AST);
			match(LITERAL_continue);
			{
			switch ( LA(1)) {
			case IDENT:
			{
				AST tmp279_AST = null;
				tmp279_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp279_AST);
				match(IDENT);
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_return:
		{
			AST tmp281_AST = null;
			tmp281_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp281_AST);
			match(LITERAL_return);
			{
			switch ( LA(1)) {
			case IDENT:
			case LPAREN:
			case STRING_LITERAL:
			case LITERAL_super:
			case LITERAL_this:
			case LITERAL_new:
			case LITERAL_void:
			case PLUS:
			case MINUS:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case T_RESULT:
			case T_OLD:
			case T_NOT_MODIFIED:
			case T_FRESH:
			case T_REACH:
			case T_NONNULLELEMENTS:
			case T_TYPEOF:
			case T_ELEMTYPE:
			case T_TYPE:
			case T_LOCKSET:
			case T_IS_INITIALIZED:
			case T_INVARIANT_FOR:
			case INFORMAL_DESCRIPTION:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			case NUM_INT:
			case CHAR_LITERAL:
			case NUM_FLOAT:
			{
				expression(side_effects_allowed);
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_switch:
		{
			switch_statement(in_model_prog);
			astFactory.addASTChild(currentAST, returnAST);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_try:
		{
			try_block(in_model_prog);
			astFactory.addASTChild(currentAST, returnAST);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_throw:
		{
			AST tmp283_AST = null;
			tmp283_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp283_AST);
			match(LITERAL_throw);
			expression(side_effects_allowed);
			astFactory.addASTChild(currentAST, returnAST);
			match(SEMI);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_synchronized:
		{
			AST tmp285_AST = null;
			tmp285_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp285_AST);
			match(LITERAL_synchronized);
			match(LPAREN);
			expression(side_effects_allowed);
			astFactory.addASTChild(currentAST, returnAST);
			match(RPAREN);
			compound_statement(in_model_prog);
			astFactory.addASTChild(currentAST, returnAST);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case SEMI:
		{
			AST tmp288_AST = null;
			tmp288_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp288_AST);
			match(SEMI);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_assert:
		{
			assert_statement();
			astFactory.addASTChild(currentAST, returnAST);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LABEL:
		{
			label_statement();
			astFactory.addASTChild(currentAST, returnAST);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case HENCE_BY:
		case HENCE_BY_REDUNDANTLY:
		{
			hence_by_statement();
			astFactory.addASTChild(currentAST, returnAST);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case ASSERT_REDUNDANTLY:
		{
			assert_redundantly_statement();
			astFactory.addASTChild(currentAST, returnAST);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case ASSUME:
		case ASSUME_REDUNDANTLY:
		{
			assume_statement();
			astFactory.addASTChild(currentAST, returnAST);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case SET:
		{
			set_statement();
			astFactory.addASTChild(currentAST, returnAST);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case UNREACHABLE:
		{
			unreachable_statement();
			astFactory.addASTChild(currentAST, returnAST);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case INVARIANT:
		case INVARIANT_REDUNDANTLY:
		case BEHAVIOR:
		case EXCEPTIONAL_BEHAVIOR:
		case NORMAL_BEHAVIOR:
		case CHOOSE:
		case CHOOSE_IF:
		case ABRUPT_BEHAVIOR:
		{
			model_prog_statement();
			mps_AST = (AST)returnAST;
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				
				if (!in_model_prog) {
				reportError("model-program-statements can only be used in model programs",
				((LineAST)mps_AST).line, ((LineAST)mps_AST).column);
				}
				
			}
			statement_AST = (AST)currentAST.root;
			break;
		}
		default:
			if ((LA(1)==LITERAL_final) && (LA(2)==LITERAL_class)) {
				AST tmp289_AST = null;
				tmp289_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp289_AST);
				match(LITERAL_final);
				class_definition(in_model_prog);
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					statement_AST = (AST)currentAST.root;
					statement_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(NESTED_CLASS,"nested_class")).add(statement_AST));
					currentAST.root = statement_AST;
					currentAST.child = statement_AST!=null &&statement_AST.getFirstChild()!=null ?
						statement_AST.getFirstChild() : statement_AST;
					currentAST.advanceChildToEnd();
				}
				statement_AST = (AST)currentAST.root;
			}
			else {
				boolean synPredMatched417 = false;
				if (((_tokenSet_33.member(LA(1))) && (_tokenSet_34.member(LA(2))))) {
					int _m417 = mark();
					synPredMatched417 = true;
					inputState.guessing++;
					try {
						{
						local_declaration();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched417 = false;
					}
					rewind(_m417);
					inputState.guessing--;
				}
				if ( synPredMatched417 ) {
					local_declaration();
					astFactory.addASTChild(currentAST, returnAST);
					match(SEMI);
					statement_AST = (AST)currentAST.root;
				}
				else if ((LA(1)==IDENT) && (LA(2)==COLON)) {
					AST tmp291_AST = null;
					tmp291_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp291_AST);
					match(IDENT);
					AST tmp292_AST = null;
					tmp292_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp292_AST);
					match(COLON);
					statement(in_model_prog);
					astFactory.addASTChild(currentAST, returnAST);
					statement_AST = (AST)currentAST.root;
				}
				else if ((_tokenSet_35.member(LA(1))) && (_tokenSet_36.member(LA(2)))) {
					expression(side_effects_allowed);
					astFactory.addASTChild(currentAST, returnAST);
					match(SEMI);
					statement_AST = (AST)currentAST.root;
				}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			}}
			returnAST = statement_AST;
		}
		
	public final void spec_statement_jack() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST spec_statement_jack_AST = null;
		
		switch ( LA(1)) {
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		{
			requires_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			assignable_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			ensures_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			signals_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			spec_statement_jack_AST = (AST)currentAST.root;
			break;
		}
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		{
			assignable_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			ensures_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			signals_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			spec_statement_jack_AST = (AST)currentAST.root;
			break;
		}
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		{
			ensures_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			signals_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			spec_statement_jack_AST = (AST)currentAST.root;
			break;
		}
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		{
			signals_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			spec_statement_jack_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = spec_statement_jack_AST;
	}
	
	public final void local_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST local_declaration_AST = null;
		
		local_modifiers();
		astFactory.addASTChild(currentAST, returnAST);
		variable_decls(side_effects_allowed);
		astFactory.addASTChild(currentAST, returnAST);
		local_declaration_AST = (AST)currentAST.root;
		returnAST = local_declaration_AST;
	}
	
	public final void loop_invariant_seq_opt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST loop_invariant_seq_opt_AST = null;
		
		{
		_loop530:
		do {
			if (((LA(1) >= MAINTAINING && LA(1) <= LOOP_INVARIANT_REDUNDANTLY))) {
				loop_invariant();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop530;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			loop_invariant_seq_opt_AST = (AST)currentAST.root;
			loop_invariant_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(LOOP_INV_SEQ,"loop_invariant_seq")).add(loop_invariant_seq_opt_AST));
			
			currentAST.root = loop_invariant_seq_opt_AST;
			currentAST.child = loop_invariant_seq_opt_AST!=null &&loop_invariant_seq_opt_AST.getFirstChild()!=null ?
				loop_invariant_seq_opt_AST.getFirstChild() : loop_invariant_seq_opt_AST;
			currentAST.advanceChildToEnd();
		}
		loop_invariant_seq_opt_AST = (AST)currentAST.root;
		returnAST = loop_invariant_seq_opt_AST;
	}
	
	public final void variant_function_seq_opt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST variant_function_seq_opt_AST = null;
		
		{
		_loop535:
		do {
			if (((LA(1) >= DECREASING && LA(1) <= DECREASES_REDUNDANTLY))) {
				variant_function();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop535;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			variant_function_seq_opt_AST = (AST)currentAST.root;
			variant_function_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(VF_SEQ,"variant_function_seq")).add(variant_function_seq_opt_AST));
			
			currentAST.root = variant_function_seq_opt_AST;
			currentAST.child = variant_function_seq_opt_AST!=null &&variant_function_seq_opt_AST.getFirstChild()!=null ?
				variant_function_seq_opt_AST.getFirstChild() : variant_function_seq_opt_AST;
			currentAST.advanceChildToEnd();
		}
		variant_function_seq_opt_AST = (AST)currentAST.root;
		returnAST = variant_function_seq_opt_AST;
	}
	
	public final void for_init() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST for_init_AST = null;
		
		boolean synPredMatched425 = false;
		if (((_tokenSet_33.member(LA(1))) && (_tokenSet_34.member(LA(2))))) {
			int _m425 = mark();
			synPredMatched425 = true;
			inputState.guessing++;
			try {
				{
				local_declaration();
				}
			}
			catch (RecognitionException pe) {
				synPredMatched425 = false;
			}
			rewind(_m425);
			inputState.guessing--;
		}
		if ( synPredMatched425 ) {
			local_declaration();
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				for_init_AST = (AST)currentAST.root;
				for_init_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(FOR_INIT,"for_init")).add(for_init_AST));
				currentAST.root = for_init_AST;
				currentAST.child = for_init_AST!=null &&for_init_AST.getFirstChild()!=null ?
					for_init_AST.getFirstChild() : for_init_AST;
				currentAST.advanceChildToEnd();
			}
			for_init_AST = (AST)currentAST.root;
		}
		else if ((_tokenSet_35.member(LA(1))) && (_tokenSet_37.member(LA(2)))) {
			expression_list(side_effects_allowed);
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				for_init_AST = (AST)currentAST.root;
				for_init_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(FOR_INIT,"for_init")).add(for_init_AST));
				currentAST.root = for_init_AST;
				currentAST.child = for_init_AST!=null &&for_init_AST.getFirstChild()!=null ?
					for_init_AST.getFirstChild() : for_init_AST;
				currentAST.advanceChildToEnd();
			}
			for_init_AST = (AST)currentAST.root;
		}
		else if ((LA(1)==SEMI)) {
			if ( inputState.guessing==0 ) {
				for_init_AST = (AST)currentAST.root;
				for_init_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(FOR_INIT,"for_init")).add(for_init_AST));
				currentAST.root = for_init_AST;
				currentAST.child = for_init_AST!=null &&for_init_AST.getFirstChild()!=null ?
					for_init_AST.getFirstChild() : for_init_AST;
				currentAST.advanceChildToEnd();
			}
			for_init_AST = (AST)currentAST.root;
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		returnAST = for_init_AST;
	}
	
	public final void for_test() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST for_test_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		case LPAREN:
		case STRING_LITERAL:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_new:
		case LITERAL_void:
		case PLUS:
		case MINUS:
		case INC:
		case DEC:
		case BNOT:
		case LNOT:
		case LITERAL_true:
		case LITERAL_false:
		case LITERAL_null:
		case T_RESULT:
		case T_OLD:
		case T_NOT_MODIFIED:
		case T_FRESH:
		case T_REACH:
		case T_NONNULLELEMENTS:
		case T_TYPEOF:
		case T_ELEMTYPE:
		case T_TYPE:
		case T_LOCKSET:
		case T_IS_INITIALIZED:
		case T_INVARIANT_FOR:
		case INFORMAL_DESCRIPTION:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_short:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_float:
		case LITERAL_double:
		case NUM_INT:
		case CHAR_LITERAL:
		case NUM_FLOAT:
		{
			expression(side_effects_allowed);
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				for_test_AST = (AST)currentAST.root;
				for_test_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(FOR_TEST,"for_test")).add(for_test_AST));
				currentAST.root = for_test_AST;
				currentAST.child = for_test_AST!=null &&for_test_AST.getFirstChild()!=null ?
					for_test_AST.getFirstChild() : for_test_AST;
				currentAST.advanceChildToEnd();
			}
			for_test_AST = (AST)currentAST.root;
			break;
		}
		case SEMI:
		{
			if ( inputState.guessing==0 ) {
				for_test_AST = (AST)currentAST.root;
				for_test_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(FOR_TEST,"for_test")).add(for_test_AST));
				currentAST.root = for_test_AST;
				currentAST.child = for_test_AST!=null &&for_test_AST.getFirstChild()!=null ?
					for_test_AST.getFirstChild() : for_test_AST;
				currentAST.advanceChildToEnd();
			}
			for_test_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = for_test_AST;
	}
	
	public final void for_updater() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST for_updater_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		case LPAREN:
		case STRING_LITERAL:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_new:
		case LITERAL_void:
		case PLUS:
		case MINUS:
		case INC:
		case DEC:
		case BNOT:
		case LNOT:
		case LITERAL_true:
		case LITERAL_false:
		case LITERAL_null:
		case T_RESULT:
		case T_OLD:
		case T_NOT_MODIFIED:
		case T_FRESH:
		case T_REACH:
		case T_NONNULLELEMENTS:
		case T_TYPEOF:
		case T_ELEMTYPE:
		case T_TYPE:
		case T_LOCKSET:
		case T_IS_INITIALIZED:
		case T_INVARIANT_FOR:
		case INFORMAL_DESCRIPTION:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_short:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_float:
		case LITERAL_double:
		case NUM_INT:
		case CHAR_LITERAL:
		case NUM_FLOAT:
		{
			expression_list(side_effects_allowed);
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				for_updater_AST = (AST)currentAST.root;
				for_updater_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(FOR_UPDATER,"for_updater")).add(for_updater_AST));
				currentAST.root = for_updater_AST;
				currentAST.child = for_updater_AST!=null &&for_updater_AST.getFirstChild()!=null ?
					for_updater_AST.getFirstChild() : for_updater_AST;
				currentAST.advanceChildToEnd();
			}
			for_updater_AST = (AST)currentAST.root;
			break;
		}
		case RPAREN:
		{
			if ( inputState.guessing==0 ) {
				for_updater_AST = (AST)currentAST.root;
				for_updater_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(FOR_UPDATER,"for_updater")).add(for_updater_AST));
				currentAST.root = for_updater_AST;
				currentAST.child = for_updater_AST!=null &&for_updater_AST.getFirstChild()!=null ?
					for_updater_AST.getFirstChild() : for_updater_AST;
				currentAST.advanceChildToEnd();
			}
			for_updater_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = for_updater_AST;
	}
	
	public final void switch_statement(
		boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST switch_statement_AST = null;
		
		AST tmp294_AST = null;
		tmp294_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp294_AST);
		match(LITERAL_switch);
		match(LPAREN);
		expression(side_effects_allowed);
		astFactory.addASTChild(currentAST, returnAST);
		match(RPAREN);
		match(LCURLY);
		{
		_loop435:
		do {
			if ((LA(1)==LITERAL_case||LA(1)==LITERAL_default)) {
				switch_body(in_model_prog);
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop435;
			}
			
		} while (true);
		}
		match(RCURLY);
		switch_statement_AST = (AST)currentAST.root;
		returnAST = switch_statement_AST;
	}
	
	public final void try_block(
		boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST try_block_AST = null;
		
		AST tmp299_AST = null;
		tmp299_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp299_AST);
		match(LITERAL_try);
		compound_statement(in_model_prog);
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop445:
		do {
			if ((LA(1)==LITERAL_catch)) {
				handler(in_model_prog);
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop445;
			}
			
		} while (true);
		}
		{
		switch ( LA(1)) {
		case LITERAL_finally:
		{
			AST tmp300_AST = null;
			tmp300_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp300_AST);
			match(LITERAL_finally);
			compound_statement(in_model_prog);
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case MODEL:
		case DOC_COMMENT:
		case SEMI:
		case IDENT:
		case T_TYPEOFALLTYPES:
		case LITERAL_final:
		case LITERAL_abstract:
		case LITERAL_synchronized:
		case LITERAL_class:
		case LCURLY:
		case RCURLY:
		case LPAREN:
		case STRING_LITERAL:
		case GHOST:
		case NON_NULL:
		case INVARIANT:
		case INVARIANT_REDUNDANTLY:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_new:
		case LITERAL_void:
		case BEHAVIOR:
		case EXCEPTIONAL_BEHAVIOR:
		case NORMAL_BEHAVIOR:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case LITERAL_if:
		case LABEL:
		case LOOP_MODIFIES:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case LOOP_EXSURES:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		case LITERAL_else:
		case LITERAL_while:
		case LITERAL_do:
		case LITERAL_for:
		case LITERAL_break:
		case LITERAL_continue:
		case LITERAL_return:
		case LITERAL_throw:
		case LITERAL_switch:
		case LITERAL_case:
		case LITERAL_default:
		case LITERAL_try:
		case LITERAL_assert:
		case HENCE_BY:
		case HENCE_BY_REDUNDANTLY:
		case ASSERT_REDUNDANTLY:
		case ASSUME:
		case ASSUME_REDUNDANTLY:
		case SET:
		case UNREACHABLE:
		case CHOOSE:
		case CHOOSE_IF:
		case ABRUPT_BEHAVIOR:
		case MAINTAINING:
		case MAINTAINING_REDUNDANTLY:
		case LOOP_INVARIANT:
		case LOOP_INVARIANT_REDUNDANTLY:
		case DECREASING:
		case DECREASING_REDUNDANTLY:
		case DECREASES:
		case DECREASES_REDUNDANTLY:
		case PLUS:
		case MINUS:
		case INC:
		case DEC:
		case BNOT:
		case LNOT:
		case LITERAL_true:
		case LITERAL_false:
		case LITERAL_null:
		case T_RESULT:
		case T_OLD:
		case T_NOT_MODIFIED:
		case T_FRESH:
		case T_REACH:
		case T_NONNULLELEMENTS:
		case T_TYPEOF:
		case T_ELEMTYPE:
		case T_TYPE:
		case T_LOCKSET:
		case T_IS_INITIALIZED:
		case T_INVARIANT_FOR:
		case INFORMAL_DESCRIPTION:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_short:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_float:
		case LITERAL_double:
		case NUM_INT:
		case CHAR_LITERAL:
		case NUM_FLOAT:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		try_block_AST = (AST)currentAST.root;
		returnAST = try_block_AST;
	}
	
	public final void assert_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST assert_statement_AST = null;
		
		boolean in_JML = lexer.SL_Jml_state || lexer.ML_Jml_state
		|| lexer.JML_reading_JML_file;
		
		
		AST tmp301_AST = null;
		tmp301_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp301_AST);
		match(LITERAL_assert);
		expression(in_JML ? no_side_effects : side_effects_allowed);
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case COLON:
		{
			match(COLON);
			expression(side_effects_allowed);
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			assert_statement_AST = (AST)currentAST.root;
			
			// change to "affirm" internally if in JML mode
			if (in_JML) { assert_statement_AST.setType(AFFIRM_KEYWORD); }
			
		}
		assert_statement_AST = (AST)currentAST.root;
		returnAST = assert_statement_AST;
	}
	
	public final void hence_by_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST hence_by_statement_AST = null;
		
		{
		switch ( LA(1)) {
		case HENCE_BY:
		{
			AST tmp304_AST = null;
			tmp304_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp304_AST);
			match(HENCE_BY);
			break;
		}
		case HENCE_BY_REDUNDANTLY:
		{
			AST tmp305_AST = null;
			tmp305_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp305_AST);
			match(HENCE_BY_REDUNDANTLY);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		predicate();
		astFactory.addASTChild(currentAST, returnAST);
		match(SEMI);
		if ( inputState.guessing==0 ) {
			hence_by_statement_AST = (AST)currentAST.root;
			hence_by_statement_AST.setType(HENCE_BY_KEYWORD);
		}
		hence_by_statement_AST = (AST)currentAST.root;
		returnAST = hence_by_statement_AST;
	}
	
	public final void assert_redundantly_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST assert_redundantly_statement_AST = null;
		
		AST tmp307_AST = null;
		tmp307_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp307_AST);
		match(ASSERT_REDUNDANTLY);
		predicate();
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case COLON:
		{
			match(COLON);
			expression(side_effects_allowed);
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			assert_redundantly_statement_AST = (AST)currentAST.root;
			assert_redundantly_statement_AST.setType(AFFIRM_KEYWORD);
		}
		assert_redundantly_statement_AST = (AST)currentAST.root;
		returnAST = assert_redundantly_statement_AST;
	}
	
	public final void assume_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST assume_statement_AST = null;
		
		{
		switch ( LA(1)) {
		case ASSUME:
		{
			AST tmp310_AST = null;
			tmp310_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp310_AST);
			match(ASSUME);
			break;
		}
		case ASSUME_REDUNDANTLY:
		{
			AST tmp311_AST = null;
			tmp311_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp311_AST);
			match(ASSUME_REDUNDANTLY);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		predicate();
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case COLON:
		{
			match(COLON);
			expression(side_effects_allowed);
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			assume_statement_AST = (AST)currentAST.root;
			assume_statement_AST.setType(ASSUME_KEYWORD);
		}
		assume_statement_AST = (AST)currentAST.root;
		returnAST = assume_statement_AST;
	}
	
	public final void set_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST set_statement_AST = null;
		
		AST tmp314_AST = null;
		tmp314_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp314_AST);
		match(SET);
		spec_assignment_expr();
		astFactory.addASTChild(currentAST, returnAST);
		match(SEMI);
		set_statement_AST = (AST)currentAST.root;
		returnAST = set_statement_AST;
	}
	
	public final void unreachable_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST unreachable_statement_AST = null;
		
		AST tmp316_AST = null;
		tmp316_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp316_AST);
		match(UNREACHABLE);
		match(SEMI);
		unreachable_statement_AST = (AST)currentAST.root;
		returnAST = unreachable_statement_AST;
	}
	
	public final void model_prog_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST model_prog_statement_AST = null;
		
		switch ( LA(1)) {
		case CHOOSE:
		{
			nondeterministic_choice();
			astFactory.addASTChild(currentAST, returnAST);
			model_prog_statement_AST = (AST)currentAST.root;
			break;
		}
		case CHOOSE_IF:
		{
			nondeterministic_if();
			astFactory.addASTChild(currentAST, returnAST);
			model_prog_statement_AST = (AST)currentAST.root;
			break;
		}
		case BEHAVIOR:
		case EXCEPTIONAL_BEHAVIOR:
		case NORMAL_BEHAVIOR:
		case ABRUPT_BEHAVIOR:
		{
			spec_statement();
			astFactory.addASTChild(currentAST, returnAST);
			model_prog_statement_AST = (AST)currentAST.root;
			break;
		}
		case INVARIANT:
		case INVARIANT_REDUNDANTLY:
		{
			invariant();
			astFactory.addASTChild(currentAST, returnAST);
			model_prog_statement_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = model_prog_statement_AST;
	}
	
	public final void local_modifier() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST local_modifier_AST = null;
		
		switch ( LA(1)) {
		case MODEL:
		{
			AST tmp318_AST = null;
			tmp318_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp318_AST);
			match(MODEL);
			local_modifier_AST = (AST)currentAST.root;
			break;
		}
		case GHOST:
		{
			AST tmp319_AST = null;
			tmp319_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp319_AST);
			match(GHOST);
			local_modifier_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_final:
		{
			AST tmp320_AST = null;
			tmp320_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp320_AST);
			match(LITERAL_final);
			local_modifier_AST = (AST)currentAST.root;
			break;
		}
		case NON_NULL:
		{
			AST tmp321_AST = null;
			tmp321_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp321_AST);
			match(NON_NULL);
			local_modifier_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = local_modifier_AST;
	}
	
	public final void local_modifiers() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST local_modifiers_AST = null;
		
		{
		_loop431:
		do {
			if ((_tokenSet_38.member(LA(1)))) {
				local_modifier();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop431;
			}
			
		} while (true);
		}
		local_modifiers_AST = (AST)currentAST.root;
		returnAST = local_modifiers_AST;
	}
	
	public final void switch_body(
		boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST switch_body_AST = null;
		
		switch_label_seq();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop438:
		do {
			if ((_tokenSet_17.member(LA(1)))) {
				statement(in_model_prog);
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop438;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			switch_body_AST = (AST)currentAST.root;
			switch_body_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(CASE)).add(switch_body_AST));
			currentAST.root = switch_body_AST;
			currentAST.child = switch_body_AST!=null &&switch_body_AST.getFirstChild()!=null ?
				switch_body_AST.getFirstChild() : switch_body_AST;
			currentAST.advanceChildToEnd();
		}
		switch_body_AST = (AST)currentAST.root;
		returnAST = switch_body_AST;
	}
	
	public final void switch_label_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST switch_label_seq_AST = null;
		
		{
		int _cnt441=0;
		_loop441:
		do {
			if ((LA(1)==LITERAL_case||LA(1)==LITERAL_default) && (_tokenSet_39.member(LA(2)))) {
				switch_label();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt441>=1 ) { break _loop441; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt441++;
		} while (true);
		}
		switch_label_seq_AST = (AST)currentAST.root;
		returnAST = switch_label_seq_AST;
	}
	
	public final void switch_label() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST switch_label_AST = null;
		
		switch ( LA(1)) {
		case LITERAL_case:
		{
			AST tmp322_AST = null;
			tmp322_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp322_AST);
			match(LITERAL_case);
			expression(side_effects_allowed);
			astFactory.addASTChild(currentAST, returnAST);
			match(COLON);
			switch_label_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_default:
		{
			AST tmp324_AST = null;
			tmp324_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp324_AST);
			match(LITERAL_default);
			match(COLON);
			switch_label_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = switch_label_AST;
	}
	
	public final void handler(
		boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST handler_AST = null;
		
		AST tmp326_AST = null;
		tmp326_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp326_AST);
		match(LITERAL_catch);
		match(LPAREN);
		param_declaration();
		astFactory.addASTChild(currentAST, returnAST);
		match(RPAREN);
		compound_statement(in_model_prog);
		astFactory.addASTChild(currentAST, returnAST);
		handler_AST = (AST)currentAST.root;
		returnAST = handler_AST;
	}
	
	public final void spec_assignment_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST spec_assignment_expr_AST = null;
		
		conditional_expr(no_side_effects);
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case ASSIGN:
		case PLUS_ASSIGN:
		case MINUS_ASSIGN:
		case STAR_ASSIGN:
		case DIV_ASSIGN:
		case MOD_ASSIGN:
		case SR_ASSIGN:
		case BSR_ASSIGN:
		case SL_ASSIGN:
		case BAND_ASSIGN:
		case BOR_ASSIGN:
		case BXOR_ASSIGN:
		{
			{
			switch ( LA(1)) {
			case ASSIGN:
			{
				AST tmp329_AST = null;
				tmp329_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp329_AST);
				match(ASSIGN);
				break;
			}
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			{
				{
				switch ( LA(1)) {
				case PLUS_ASSIGN:
				{
					AST tmp330_AST = null;
					tmp330_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp330_AST);
					match(PLUS_ASSIGN);
					break;
				}
				case MINUS_ASSIGN:
				{
					AST tmp331_AST = null;
					tmp331_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp331_AST);
					match(MINUS_ASSIGN);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					spec_assignment_expr_AST = (AST)currentAST.root;
					spec_assignment_expr_AST.setType(ADDITIVE_ASSIGNMENT_OP);
				}
				break;
			}
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			{
				{
				switch ( LA(1)) {
				case STAR_ASSIGN:
				{
					AST tmp332_AST = null;
					tmp332_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp332_AST);
					match(STAR_ASSIGN);
					break;
				}
				case DIV_ASSIGN:
				{
					AST tmp333_AST = null;
					tmp333_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp333_AST);
					match(DIV_ASSIGN);
					break;
				}
				case MOD_ASSIGN:
				{
					AST tmp334_AST = null;
					tmp334_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp334_AST);
					match(MOD_ASSIGN);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					spec_assignment_expr_AST = (AST)currentAST.root;
					spec_assignment_expr_AST.setType(MULTIPLICATIVE_ASSIGNMENT_OP);
				}
				break;
			}
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			{
				{
				switch ( LA(1)) {
				case SR_ASSIGN:
				{
					AST tmp335_AST = null;
					tmp335_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp335_AST);
					match(SR_ASSIGN);
					break;
				}
				case BSR_ASSIGN:
				{
					AST tmp336_AST = null;
					tmp336_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp336_AST);
					match(BSR_ASSIGN);
					break;
				}
				case SL_ASSIGN:
				{
					AST tmp337_AST = null;
					tmp337_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp337_AST);
					match(SL_ASSIGN);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					spec_assignment_expr_AST = (AST)currentAST.root;
					spec_assignment_expr_AST.setType(SHIFT_ASSIGNMENT_OP);
				}
				break;
			}
			case BAND_ASSIGN:
			case BOR_ASSIGN:
			case BXOR_ASSIGN:
			{
				{
				switch ( LA(1)) {
				case BAND_ASSIGN:
				{
					AST tmp338_AST = null;
					tmp338_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp338_AST);
					match(BAND_ASSIGN);
					break;
				}
				case BOR_ASSIGN:
				{
					AST tmp339_AST = null;
					tmp339_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp339_AST);
					match(BOR_ASSIGN);
					break;
				}
				case BXOR_ASSIGN:
				{
					AST tmp340_AST = null;
					tmp340_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp340_AST);
					match(BXOR_ASSIGN);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					spec_assignment_expr_AST = (AST)currentAST.root;
					spec_assignment_expr_AST.setType(BITWISE_ASSIGNMENT_OP);
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			spec_assignment_expr();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		spec_assignment_expr_AST = (AST)currentAST.root;
		returnAST = spec_assignment_expr_AST;
	}
	
	public final void conditional_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST conditional_expr_AST = null;
		
		equivalence_expr(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case QUESTION:
		{
			AST tmp341_AST = null;
			tmp341_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp341_AST);
			match(QUESTION);
			conditional_expr(in_spec);
			astFactory.addASTChild(currentAST, returnAST);
			match(COLON);
			conditional_expr(in_spec);
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case EOF:
		case SEMI:
		case RCURLY:
		case COMMA:
		case RPAREN:
		case ASSIGN:
		case INITIALLY:
		case READABLE_IF:
		case MONITORED_BY:
		case FOR:
		case RBRACK:
		case LITERAL_if:
		case COLON:
		case DOT_DOT:
		case PLUS_ASSIGN:
		case MINUS_ASSIGN:
		case STAR_ASSIGN:
		case DIV_ASSIGN:
		case MOD_ASSIGN:
		case SR_ASSIGN:
		case BSR_ASSIGN:
		case SL_ASSIGN:
		case BAND_ASSIGN:
		case BOR_ASSIGN:
		case BXOR_ASSIGN:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		conditional_expr_AST = (AST)currentAST.root;
		returnAST = conditional_expr_AST;
	}
	
	public final void nondeterministic_choice() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST nondeterministic_choice_AST = null;
		
		AST tmp343_AST = null;
		tmp343_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp343_AST);
		match(CHOOSE);
		alternative_statements();
		astFactory.addASTChild(currentAST, returnAST);
		nondeterministic_choice_AST = (AST)currentAST.root;
		returnAST = nondeterministic_choice_AST;
	}
	
	public final void nondeterministic_if() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST nondeterministic_if_AST = null;
		
		AST tmp344_AST = null;
		tmp344_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp344_AST);
		match(CHOOSE_IF);
		guarded_statements();
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case ELSE:
		{
			match(ELSE);
			compound_statement(with_jml);
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case MODEL:
		case DOC_COMMENT:
		case SEMI:
		case IDENT:
		case T_TYPEOFALLTYPES:
		case LITERAL_final:
		case LITERAL_abstract:
		case LITERAL_synchronized:
		case LITERAL_class:
		case LCURLY:
		case RCURLY:
		case LPAREN:
		case STRING_LITERAL:
		case GHOST:
		case NON_NULL:
		case INVARIANT:
		case INVARIANT_REDUNDANTLY:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_new:
		case LITERAL_void:
		case BEHAVIOR:
		case EXCEPTIONAL_BEHAVIOR:
		case NORMAL_BEHAVIOR:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case LITERAL_if:
		case LABEL:
		case LOOP_MODIFIES:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case LOOP_EXSURES:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		case LITERAL_else:
		case LITERAL_while:
		case LITERAL_do:
		case LITERAL_for:
		case LITERAL_break:
		case LITERAL_continue:
		case LITERAL_return:
		case LITERAL_throw:
		case LITERAL_switch:
		case LITERAL_case:
		case LITERAL_default:
		case LITERAL_try:
		case LITERAL_assert:
		case HENCE_BY:
		case HENCE_BY_REDUNDANTLY:
		case ASSERT_REDUNDANTLY:
		case ASSUME:
		case ASSUME_REDUNDANTLY:
		case SET:
		case UNREACHABLE:
		case CHOOSE:
		case CHOOSE_IF:
		case ABRUPT_BEHAVIOR:
		case MAINTAINING:
		case MAINTAINING_REDUNDANTLY:
		case LOOP_INVARIANT:
		case LOOP_INVARIANT_REDUNDANTLY:
		case DECREASING:
		case DECREASING_REDUNDANTLY:
		case DECREASES:
		case DECREASES_REDUNDANTLY:
		case PLUS:
		case MINUS:
		case INC:
		case DEC:
		case BNOT:
		case LNOT:
		case LITERAL_true:
		case LITERAL_false:
		case LITERAL_null:
		case T_RESULT:
		case T_OLD:
		case T_NOT_MODIFIED:
		case T_FRESH:
		case T_REACH:
		case T_NONNULLELEMENTS:
		case T_TYPEOF:
		case T_ELEMTYPE:
		case T_TYPE:
		case T_LOCKSET:
		case T_IS_INITIALIZED:
		case T_INVARIANT_FOR:
		case INFORMAL_DESCRIPTION:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_short:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_float:
		case LITERAL_double:
		case NUM_INT:
		case CHAR_LITERAL:
		case NUM_FLOAT:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		nondeterministic_if_AST = (AST)currentAST.root;
		returnAST = nondeterministic_if_AST;
	}
	
	public final void spec_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST spec_statement_AST = null;
		
		switch ( LA(1)) {
		case BEHAVIOR:
		{
			AST tmp346_AST = null;
			tmp346_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp346_AST);
			match(BEHAVIOR);
			generic_spec_statement_case();
			astFactory.addASTChild(currentAST, returnAST);
			spec_statement_AST = (AST)currentAST.root;
			break;
		}
		case EXCEPTIONAL_BEHAVIOR:
		{
			AST tmp347_AST = null;
			tmp347_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp347_AST);
			match(EXCEPTIONAL_BEHAVIOR);
			exceptional_spec_case();
			astFactory.addASTChild(currentAST, returnAST);
			spec_statement_AST = (AST)currentAST.root;
			break;
		}
		case NORMAL_BEHAVIOR:
		{
			AST tmp348_AST = null;
			tmp348_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp348_AST);
			match(NORMAL_BEHAVIOR);
			normal_spec_case();
			astFactory.addASTChild(currentAST, returnAST);
			spec_statement_AST = (AST)currentAST.root;
			break;
		}
		case ABRUPT_BEHAVIOR:
		{
			AST tmp349_AST = null;
			tmp349_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp349_AST);
			match(ABRUPT_BEHAVIOR);
			abrupt_spec_case();
			astFactory.addASTChild(currentAST, returnAST);
			spec_statement_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = spec_statement_AST;
	}
	
	public final void alternative_statements() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST alternative_statements_AST = null;
		
		compound_statement(with_jml);
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop470:
		do {
			if ((LA(1)==OR)) {
				AST tmp350_AST = null;
				tmp350_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp350_AST);
				match(OR);
				compound_statement(with_jml);
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop470;
			}
			
		} while (true);
		}
		alternative_statements_AST = (AST)currentAST.root;
		returnAST = alternative_statements_AST;
	}
	
	public final void guarded_statements() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST guarded_statements_AST = null;
		
		guarded_statement();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop475:
		do {
			if ((LA(1)==OR)) {
				AST tmp351_AST = null;
				tmp351_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp351_AST);
				match(OR);
				guarded_statement();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop475;
			}
			
		} while (true);
		}
		guarded_statements_AST = (AST)currentAST.root;
		returnAST = guarded_statements_AST;
	}
	
	public final void guarded_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST guarded_statement_AST = null;
		
		AST tmp352_AST = null;
		tmp352_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp352_AST);
		match(LCURLY);
		assume_statement();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop478:
		do {
			if ((_tokenSet_17.member(LA(1)))) {
				statement(with_jml);
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop478;
			}
			
		} while (true);
		}
		AST tmp353_AST = null;
		tmp353_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp353_AST);
		match(RCURLY);
		guarded_statement_AST = (AST)currentAST.root;
		returnAST = guarded_statement_AST;
	}
	
	public final void generic_spec_statement_case() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST generic_spec_statement_case_AST = null;
		
		{
		switch ( LA(1)) {
		case FORALL:
		case LET:
		case OLD:
		{
			spec_var_decls();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case IDENT:
		case LCURLY_VBAR:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case WHEN:
		case WHEN_REDUNDANTLY:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		case CONTINUES:
		case CONTINUES_REDUNDANTLY:
		case BREAKS:
		case BREAKS_REDUNDANTLY:
		case RETURNS:
		case RETURNS_REDUNDANTLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case IDENT:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case WHEN:
		case WHEN_REDUNDANTLY:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		{
			spec_header();
			astFactory.addASTChild(currentAST, returnAST);
			{
			if ((_tokenSet_40.member(LA(1))) && (_tokenSet_41.member(LA(2)))) {
				generic_spec_statement_body();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else if ((_tokenSet_42.member(LA(1))) && (_tokenSet_43.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			break;
		}
		case LCURLY_VBAR:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		case CONTINUES:
		case CONTINUES_REDUNDANTLY:
		case BREAKS:
		case BREAKS_REDUNDANTLY:
		case RETURNS:
		case RETURNS_REDUNDANTLY:
		{
			generic_spec_statement_body();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			generic_spec_statement_case_AST = (AST)currentAST.root;
			generic_spec_statement_case_AST =
			(AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(SPEC_CASE,"generic_spec_statement_case")).add(generic_spec_statement_case_AST));
			
			currentAST.root = generic_spec_statement_case_AST;
			currentAST.child = generic_spec_statement_case_AST!=null &&generic_spec_statement_case_AST.getFirstChild()!=null ?
				generic_spec_statement_case_AST.getFirstChild() : generic_spec_statement_case_AST;
			currentAST.advanceChildToEnd();
		}
		generic_spec_statement_case_AST = (AST)currentAST.root;
		returnAST = generic_spec_statement_case_AST;
	}
	
	public final void abrupt_spec_case() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST abrupt_spec_case_AST = null;
		
		{
		switch ( LA(1)) {
		case FORALL:
		case LET:
		case OLD:
		{
			spec_var_decls();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case IDENT:
		case LCURLY_VBAR:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case WHEN:
		case WHEN_REDUNDANTLY:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		case CONTINUES:
		case CONTINUES_REDUNDANTLY:
		case BREAKS:
		case BREAKS_REDUNDANTLY:
		case RETURNS:
		case RETURNS_REDUNDANTLY:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case IDENT:
		case REQUIRES:
		case PRE:
		case REQUIRES_REDUNDANTLY:
		case PRE_REDUNDANTLY:
		case WHEN:
		case WHEN_REDUNDANTLY:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		{
			spec_header();
			astFactory.addASTChild(currentAST, returnAST);
			{
			if ((_tokenSet_44.member(LA(1))) && (_tokenSet_45.member(LA(2)))) {
				abrupt_spec_case_body();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else if ((_tokenSet_42.member(LA(1))) && (_tokenSet_43.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			break;
		}
		case LCURLY_VBAR:
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		case CONTINUES:
		case CONTINUES_REDUNDANTLY:
		case BREAKS:
		case BREAKS_REDUNDANTLY:
		case RETURNS:
		case RETURNS_REDUNDANTLY:
		{
			abrupt_spec_case_body();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			abrupt_spec_case_AST = (AST)currentAST.root;
			abrupt_spec_case_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(SPEC_CASE,"abrupt_spec_case")).add(abrupt_spec_case_AST));
			currentAST.root = abrupt_spec_case_AST;
			currentAST.child = abrupt_spec_case_AST!=null &&abrupt_spec_case_AST.getFirstChild()!=null ?
				abrupt_spec_case_AST.getFirstChild() : abrupt_spec_case_AST;
			currentAST.advanceChildToEnd();
		}
		abrupt_spec_case_AST = (AST)currentAST.root;
		returnAST = abrupt_spec_case_AST;
	}
	
	public final void generic_spec_statement_body() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST generic_spec_statement_body_AST = null;
		
		switch ( LA(1)) {
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		case CONTINUES:
		case CONTINUES_REDUNDANTLY:
		case BREAKS:
		case BREAKS_REDUNDANTLY:
		case RETURNS:
		case RETURNS_REDUNDANTLY:
		{
			simple_spec_statement_body();
			astFactory.addASTChild(currentAST, returnAST);
			generic_spec_statement_body_AST = (AST)currentAST.root;
			break;
		}
		case LCURLY_VBAR:
		{
			AST tmp354_AST = null;
			tmp354_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp354_AST);
			match(LCURLY_VBAR);
			generic_spec_statement_case_seq();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp355_AST = null;
			tmp355_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp355_AST);
			match(VBAR_RCURLY);
			generic_spec_statement_body_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = generic_spec_statement_body_AST;
	}
	
	public final void simple_spec_statement_body() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST simple_spec_statement_body_AST = null;
		
		switch ( LA(1)) {
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		{
			assignable_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			ensures_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			signals_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			diverges_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			continues_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			breaks_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			returns_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			simple_spec_statement_body_AST = (AST)currentAST.root;
			break;
		}
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		{
			ensures_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			signals_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			diverges_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			continues_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			breaks_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			returns_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			simple_spec_statement_body_AST = (AST)currentAST.root;
			break;
		}
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		{
			signals_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			diverges_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			continues_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			breaks_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			returns_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			simple_spec_statement_body_AST = (AST)currentAST.root;
			break;
		}
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			diverges_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			continues_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			breaks_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			returns_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			simple_spec_statement_body_AST = (AST)currentAST.root;
			break;
		}
		case CONTINUES:
		case CONTINUES_REDUNDANTLY:
		{
			continues_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			breaks_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			returns_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			simple_spec_statement_body_AST = (AST)currentAST.root;
			break;
		}
		case BREAKS:
		case BREAKS_REDUNDANTLY:
		{
			breaks_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			returns_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			simple_spec_statement_body_AST = (AST)currentAST.root;
			break;
		}
		case RETURNS:
		case RETURNS_REDUNDANTLY:
		{
			returns_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			simple_spec_statement_body_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = simple_spec_statement_body_AST;
	}
	
	public final void generic_spec_statement_case_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST generic_spec_statement_case_seq_AST = null;
		
		generic_spec_statement_case();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop487:
		do {
			if ((LA(1)==ALSO)) {
				AST tmp356_AST = null;
				tmp356_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp356_AST);
				match(ALSO);
				generic_spec_statement_case();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop487;
			}
			
		} while (true);
		}
		generic_spec_statement_case_seq_AST = (AST)currentAST.root;
		returnAST = generic_spec_statement_case_seq_AST;
	}
	
	public final void continues_clause_seq_opt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST continues_clause_seq_opt_AST = null;
		
		{
		_loop500:
		do {
			if ((LA(1)==CONTINUES||LA(1)==CONTINUES_REDUNDANTLY)) {
				continues_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop500;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			continues_clause_seq_opt_AST = (AST)currentAST.root;
			
			continues_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(CONT_SEQ,"continues_seq")).add(continues_clause_seq_opt_AST));
			
			currentAST.root = continues_clause_seq_opt_AST;
			currentAST.child = continues_clause_seq_opt_AST!=null &&continues_clause_seq_opt_AST.getFirstChild()!=null ?
				continues_clause_seq_opt_AST.getFirstChild() : continues_clause_seq_opt_AST;
			currentAST.advanceChildToEnd();
		}
		continues_clause_seq_opt_AST = (AST)currentAST.root;
		returnAST = continues_clause_seq_opt_AST;
	}
	
	public final void breaks_clause_seq_opt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST breaks_clause_seq_opt_AST = null;
		
		{
		_loop511:
		do {
			if ((LA(1)==BREAKS||LA(1)==BREAKS_REDUNDANTLY)) {
				breaks_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop511;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			breaks_clause_seq_opt_AST = (AST)currentAST.root;
			
			breaks_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(BREAKS_SEQ,"breaks_seq")).add(breaks_clause_seq_opt_AST));
			
			currentAST.root = breaks_clause_seq_opt_AST;
			currentAST.child = breaks_clause_seq_opt_AST!=null &&breaks_clause_seq_opt_AST.getFirstChild()!=null ?
				breaks_clause_seq_opt_AST.getFirstChild() : breaks_clause_seq_opt_AST;
			currentAST.advanceChildToEnd();
		}
		breaks_clause_seq_opt_AST = (AST)currentAST.root;
		returnAST = breaks_clause_seq_opt_AST;
	}
	
	public final void returns_clause_seq_opt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST returns_clause_seq_opt_AST = null;
		
		{
		_loop521:
		do {
			if ((LA(1)==RETURNS||LA(1)==RETURNS_REDUNDANTLY)) {
				returns_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop521;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			returns_clause_seq_opt_AST = (AST)currentAST.root;
			
			returns_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(RETURNS_SEQ,"returns_seq")).add(returns_clause_seq_opt_AST));
			
			currentAST.root = returns_clause_seq_opt_AST;
			currentAST.child = returns_clause_seq_opt_AST!=null &&returns_clause_seq_opt_AST.getFirstChild()!=null ?
				returns_clause_seq_opt_AST.getFirstChild() : returns_clause_seq_opt_AST;
			currentAST.advanceChildToEnd();
		}
		returns_clause_seq_opt_AST = (AST)currentAST.root;
		returnAST = returns_clause_seq_opt_AST;
	}
	
	public final void continues_clause_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST continues_clause_seq_AST = null;
		
		{
		int _cnt503=0;
		_loop503:
		do {
			if ((LA(1)==CONTINUES||LA(1)==CONTINUES_REDUNDANTLY)) {
				continues_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt503>=1 ) { break _loop503; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt503++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			continues_clause_seq_AST = (AST)currentAST.root;
			
			continues_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(CONT_SEQ,"continues_seq")).add(continues_clause_seq_AST));
			
			currentAST.root = continues_clause_seq_AST;
			currentAST.child = continues_clause_seq_AST!=null &&continues_clause_seq_AST.getFirstChild()!=null ?
				continues_clause_seq_AST.getFirstChild() : continues_clause_seq_AST;
			currentAST.advanceChildToEnd();
		}
		continues_clause_seq_AST = (AST)currentAST.root;
		returnAST = continues_clause_seq_AST;
	}
	
	public final void breaks_clause_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST breaks_clause_seq_AST = null;
		
		{
		int _cnt514=0;
		_loop514:
		do {
			if ((LA(1)==BREAKS||LA(1)==BREAKS_REDUNDANTLY)) {
				breaks_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt514>=1 ) { break _loop514; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt514++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			breaks_clause_seq_AST = (AST)currentAST.root;
			
			breaks_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(BREAKS_SEQ,"breaks_seq")).add(breaks_clause_seq_AST));
			
			currentAST.root = breaks_clause_seq_AST;
			currentAST.child = breaks_clause_seq_AST!=null &&breaks_clause_seq_AST.getFirstChild()!=null ?
				breaks_clause_seq_AST.getFirstChild() : breaks_clause_seq_AST;
			currentAST.advanceChildToEnd();
		}
		breaks_clause_seq_AST = (AST)currentAST.root;
		returnAST = breaks_clause_seq_AST;
	}
	
	public final void returns_clause_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST returns_clause_seq_AST = null;
		
		{
		int _cnt524=0;
		_loop524:
		do {
			if ((LA(1)==RETURNS||LA(1)==RETURNS_REDUNDANTLY)) {
				returns_clause();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt524>=1 ) { break _loop524; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt524++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			returns_clause_seq_AST = (AST)currentAST.root;
			
			returns_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(RETURNS_SEQ,"returns_seq")).add(returns_clause_seq_AST));
			
			currentAST.root = returns_clause_seq_AST;
			currentAST.child = returns_clause_seq_AST!=null &&returns_clause_seq_AST.getFirstChild()!=null ?
				returns_clause_seq_AST.getFirstChild() : returns_clause_seq_AST;
			currentAST.advanceChildToEnd();
		}
		returns_clause_seq_AST = (AST)currentAST.root;
		returnAST = returns_clause_seq_AST;
	}
	
	public final void abrupt_spec_case_body() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST abrupt_spec_case_body_AST = null;
		
		switch ( LA(1)) {
		case ASSIGNABLE:
		case MODIFIABLE:
		case MODIFIES:
		case ASSIGNABLE_REDUNDANTLY:
		case MODIFIABLE_REDUNDANTLY:
		case MODIFIES_REDUNDANTLY:
		{
			assignable_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			diverges_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			continues_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			breaks_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			returns_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			abrupt_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			diverges_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			continues_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			breaks_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			returns_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			abrupt_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case CONTINUES:
		case CONTINUES_REDUNDANTLY:
		{
			continues_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			breaks_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			returns_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			abrupt_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case BREAKS:
		case BREAKS_REDUNDANTLY:
		{
			breaks_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			returns_clause_seq_opt();
			astFactory.addASTChild(currentAST, returnAST);
			abrupt_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case RETURNS:
		case RETURNS_REDUNDANTLY:
		{
			returns_clause_seq();
			astFactory.addASTChild(currentAST, returnAST);
			abrupt_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case LCURLY_VBAR:
		{
			AST tmp357_AST = null;
			tmp357_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp357_AST);
			match(LCURLY_VBAR);
			abrupt_spec_case_seq();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp358_AST = null;
			tmp358_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp358_AST);
			match(VBAR_RCURLY);
			abrupt_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = abrupt_spec_case_body_AST;
	}
	
	public final void abrupt_spec_case_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST abrupt_spec_case_seq_AST = null;
		
		abrupt_spec_case();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop497:
		do {
			if ((LA(1)==ALSO)) {
				AST tmp359_AST = null;
				tmp359_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp359_AST);
				match(ALSO);
				abrupt_spec_case();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop497;
			}
			
		} while (true);
		}
		abrupt_spec_case_seq_AST = (AST)currentAST.root;
		returnAST = abrupt_spec_case_seq_AST;
	}
	
	public final void continues_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST continues_clause_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case CONTINUES:
			{
				AST tmp360_AST = null;
				tmp360_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp360_AST);
				match(CONTINUES);
				break;
			}
			case CONTINUES_REDUNDANTLY:
			{
				AST tmp361_AST = null;
				tmp361_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp361_AST);
				match(CONTINUES_REDUNDANTLY);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case R_ARROW:
			{
				target_label();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case SEMI:
			case IDENT:
			case LPAREN:
			case STRING_LITERAL:
			case LITERAL_super:
			case LITERAL_this:
			case LITERAL_new:
			case LITERAL_void:
			case T_NOT_SPECIFIED:
			case PLUS:
			case MINUS:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case T_RESULT:
			case T_OLD:
			case T_NOT_MODIFIED:
			case T_FRESH:
			case T_REACH:
			case T_NONNULLELEMENTS:
			case T_TYPEOF:
			case T_ELEMTYPE:
			case T_TYPE:
			case T_LOCKSET:
			case T_IS_INITIALIZED:
			case T_INVARIANT_FOR:
			case INFORMAL_DESCRIPTION:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			case NUM_INT:
			case CHAR_LITERAL:
			case NUM_FLOAT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case T_NOT_SPECIFIED:
			{
				AST tmp362_AST = null;
				tmp362_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp362_AST);
				match(T_NOT_SPECIFIED);
				break;
			}
			case IDENT:
			case LPAREN:
			case STRING_LITERAL:
			case LITERAL_super:
			case LITERAL_this:
			case LITERAL_new:
			case LITERAL_void:
			case PLUS:
			case MINUS:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case T_RESULT:
			case T_OLD:
			case T_NOT_MODIFIED:
			case T_FRESH:
			case T_REACH:
			case T_NONNULLELEMENTS:
			case T_TYPEOF:
			case T_ELEMTYPE:
			case T_TYPE:
			case T_LOCKSET:
			case T_IS_INITIALIZED:
			case T_INVARIANT_FOR:
			case INFORMAL_DESCRIPTION:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			case NUM_INT:
			case CHAR_LITERAL:
			case NUM_FLOAT:
			{
				predicate();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
			if ( inputState.guessing==0 ) {
				continues_clause_AST = (AST)currentAST.root;
				continues_clause_AST.setType(CONTINUES_KEYWORD);
			}
			continues_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToJmlSpecKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = continues_clause_AST;
	}
	
	public final void target_label() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST target_label_AST = null;
		
		AST tmp364_AST = null;
		tmp364_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp364_AST);
		match(R_ARROW);
		match(LPAREN);
		AST tmp366_AST = null;
		tmp366_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp366_AST);
		match(IDENT);
		match(RPAREN);
		target_label_AST = (AST)currentAST.root;
		returnAST = target_label_AST;
	}
	
	public final void breaks_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST breaks_clause_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BREAKS:
			{
				AST tmp368_AST = null;
				tmp368_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp368_AST);
				match(BREAKS);
				break;
			}
			case BREAKS_REDUNDANTLY:
			{
				AST tmp369_AST = null;
				tmp369_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp369_AST);
				match(BREAKS_REDUNDANTLY);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case R_ARROW:
			{
				target_label();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case SEMI:
			case IDENT:
			case LPAREN:
			case STRING_LITERAL:
			case LITERAL_super:
			case LITERAL_this:
			case LITERAL_new:
			case LITERAL_void:
			case T_NOT_SPECIFIED:
			case PLUS:
			case MINUS:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case T_RESULT:
			case T_OLD:
			case T_NOT_MODIFIED:
			case T_FRESH:
			case T_REACH:
			case T_NONNULLELEMENTS:
			case T_TYPEOF:
			case T_ELEMTYPE:
			case T_TYPE:
			case T_LOCKSET:
			case T_IS_INITIALIZED:
			case T_INVARIANT_FOR:
			case INFORMAL_DESCRIPTION:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			case NUM_INT:
			case CHAR_LITERAL:
			case NUM_FLOAT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case T_NOT_SPECIFIED:
			{
				AST tmp370_AST = null;
				tmp370_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp370_AST);
				match(T_NOT_SPECIFIED);
				break;
			}
			case IDENT:
			case LPAREN:
			case STRING_LITERAL:
			case LITERAL_super:
			case LITERAL_this:
			case LITERAL_new:
			case LITERAL_void:
			case PLUS:
			case MINUS:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case T_RESULT:
			case T_OLD:
			case T_NOT_MODIFIED:
			case T_FRESH:
			case T_REACH:
			case T_NONNULLELEMENTS:
			case T_TYPEOF:
			case T_ELEMTYPE:
			case T_TYPE:
			case T_LOCKSET:
			case T_IS_INITIALIZED:
			case T_INVARIANT_FOR:
			case INFORMAL_DESCRIPTION:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			case NUM_INT:
			case CHAR_LITERAL:
			case NUM_FLOAT:
			{
				predicate();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
			if ( inputState.guessing==0 ) {
				breaks_clause_AST = (AST)currentAST.root;
				breaks_clause_AST.setType(BREAKS_KEYWORD);
			}
			breaks_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToJmlSpecKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = breaks_clause_AST;
	}
	
	public final void returns_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST returns_clause_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case RETURNS:
			{
				AST tmp372_AST = null;
				tmp372_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp372_AST);
				match(RETURNS);
				break;
			}
			case RETURNS_REDUNDANTLY:
			{
				AST tmp373_AST = null;
				tmp373_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp373_AST);
				match(RETURNS_REDUNDANTLY);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case T_NOT_SPECIFIED:
			{
				AST tmp374_AST = null;
				tmp374_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp374_AST);
				match(T_NOT_SPECIFIED);
				break;
			}
			case IDENT:
			case LPAREN:
			case STRING_LITERAL:
			case LITERAL_super:
			case LITERAL_this:
			case LITERAL_new:
			case LITERAL_void:
			case PLUS:
			case MINUS:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case T_RESULT:
			case T_OLD:
			case T_NOT_MODIFIED:
			case T_FRESH:
			case T_REACH:
			case T_NONNULLELEMENTS:
			case T_TYPEOF:
			case T_ELEMTYPE:
			case T_TYPE:
			case T_LOCKSET:
			case T_IS_INITIALIZED:
			case T_INVARIANT_FOR:
			case INFORMAL_DESCRIPTION:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			case NUM_INT:
			case CHAR_LITERAL:
			case NUM_FLOAT:
			{
				predicate();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
			if ( inputState.guessing==0 ) {
				returns_clause_AST = (AST)currentAST.root;
				returns_clause_AST.setType(RETURNS_KEYWORD);
			}
			returns_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException err) {
			if (inputState.guessing==0) {
				
				reportError(err);
				consumeToJmlSpecKeyword();
				
			} else {
				throw err;
			}
		}
		returnAST = returns_clause_AST;
	}
	
	public final void loop_invariant() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST loop_invariant_AST = null;
		
		String kw = "";
		
		
		{
		switch ( LA(1)) {
		case MAINTAINING:
		{
			AST tmp376_AST = null;
			tmp376_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp376_AST);
			match(MAINTAINING);
			break;
		}
		case MAINTAINING_REDUNDANTLY:
		{
			AST tmp377_AST = null;
			tmp377_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp377_AST);
			match(MAINTAINING_REDUNDANTLY);
			break;
		}
		case LOOP_INVARIANT:
		{
			AST tmp378_AST = null;
			tmp378_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp378_AST);
			match(LOOP_INVARIANT);
			break;
		}
		case LOOP_INVARIANT_REDUNDANTLY:
		{
			AST tmp379_AST = null;
			tmp379_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp379_AST);
			match(LOOP_INVARIANT_REDUNDANTLY);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		predicate();
		astFactory.addASTChild(currentAST, returnAST);
		match(SEMI);
		if ( inputState.guessing==0 ) {
			loop_invariant_AST = (AST)currentAST.root;
			loop_invariant_AST.setType(MAINTAINING_KEYWORD);
		}
		loop_invariant_AST = (AST)currentAST.root;
		returnAST = loop_invariant_AST;
	}
	
	public final void variant_function() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST variant_function_AST = null;
		
		String kw = "";
		
		
		{
		switch ( LA(1)) {
		case DECREASING:
		{
			AST tmp381_AST = null;
			tmp381_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp381_AST);
			match(DECREASING);
			break;
		}
		case DECREASING_REDUNDANTLY:
		{
			AST tmp382_AST = null;
			tmp382_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp382_AST);
			match(DECREASING_REDUNDANTLY);
			break;
		}
		case DECREASES:
		{
			AST tmp383_AST = null;
			tmp383_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp383_AST);
			match(DECREASES);
			break;
		}
		case DECREASES_REDUNDANTLY:
		{
			AST tmp384_AST = null;
			tmp384_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp384_AST);
			match(DECREASES_REDUNDANTLY);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		spec_expression();
		astFactory.addASTChild(currentAST, returnAST);
		match(SEMI);
		if ( inputState.guessing==0 ) {
			variant_function_AST = (AST)currentAST.root;
			variant_function_AST.setType(DECREASING_KEYWORD);
		}
		variant_function_AST = (AST)currentAST.root;
		returnAST = variant_function_AST;
	}
	
	public final void assignment_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST assignment_expr_AST = null;
		Token  a = null;
		AST a_AST = null;
		Token  b = null;
		AST b_AST = null;
		Token  c = null;
		AST c_AST = null;
		Token  d = null;
		AST d_AST = null;
		Token  e = null;
		AST e_AST = null;
		Token  f = null;
		AST f_AST = null;
		Token  g = null;
		AST g_AST = null;
		Token  h = null;
		AST h_AST = null;
		Token  i = null;
		AST i_AST = null;
		Token  j = null;
		AST j_AST = null;
		Token  k = null;
		AST k_AST = null;
		Token  l = null;
		AST l_AST = null;
		
		int line = 0, col = 0;
		
		
		conditional_expr(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case ASSIGN:
		case PLUS_ASSIGN:
		case MINUS_ASSIGN:
		case STAR_ASSIGN:
		case DIV_ASSIGN:
		case MOD_ASSIGN:
		case SR_ASSIGN:
		case BSR_ASSIGN:
		case SL_ASSIGN:
		case BAND_ASSIGN:
		case BOR_ASSIGN:
		case BXOR_ASSIGN:
		{
			{
			switch ( LA(1)) {
			case ASSIGN:
			{
				a = LT(1);
				a_AST = astFactory.create(a);
				astFactory.makeASTRoot(currentAST, a_AST);
				match(ASSIGN);
				if ( inputState.guessing==0 ) {
					line = a.getLine(); col = a.getColumn();
				}
				break;
			}
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			{
				{
				switch ( LA(1)) {
				case PLUS_ASSIGN:
				{
					b = LT(1);
					b_AST = astFactory.create(b);
					astFactory.makeASTRoot(currentAST, b_AST);
					match(PLUS_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = b.getLine(); col = b.getColumn();
					}
					break;
				}
				case MINUS_ASSIGN:
				{
					c = LT(1);
					c_AST = astFactory.create(c);
					astFactory.makeASTRoot(currentAST, c_AST);
					match(MINUS_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = c.getLine(); col = c.getColumn();
					}
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					assignment_expr_AST = (AST)currentAST.root;
					assignment_expr_AST.setType(ADDITIVE_ASSIGNMENT_OP);
				}
				break;
			}
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			{
				{
				switch ( LA(1)) {
				case STAR_ASSIGN:
				{
					d = LT(1);
					d_AST = astFactory.create(d);
					astFactory.makeASTRoot(currentAST, d_AST);
					match(STAR_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = d.getLine(); col = d.getColumn();
					}
					break;
				}
				case DIV_ASSIGN:
				{
					e = LT(1);
					e_AST = astFactory.create(e);
					astFactory.makeASTRoot(currentAST, e_AST);
					match(DIV_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = e.getLine(); col = e.getColumn();
					}
					break;
				}
				case MOD_ASSIGN:
				{
					f = LT(1);
					f_AST = astFactory.create(f);
					astFactory.makeASTRoot(currentAST, f_AST);
					match(MOD_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = f.getLine(); col = f.getColumn();
					}
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					assignment_expr_AST = (AST)currentAST.root;
					assignment_expr_AST.setType(MULTIPLICATIVE_ASSIGNMENT_OP);
				}
				break;
			}
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			{
				{
				switch ( LA(1)) {
				case SR_ASSIGN:
				{
					g = LT(1);
					g_AST = astFactory.create(g);
					astFactory.makeASTRoot(currentAST, g_AST);
					match(SR_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = g.getLine(); col = g.getColumn();
					}
					break;
				}
				case BSR_ASSIGN:
				{
					h = LT(1);
					h_AST = astFactory.create(h);
					astFactory.makeASTRoot(currentAST, h_AST);
					match(BSR_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = h.getLine(); col = h.getColumn();
					}
					break;
				}
				case SL_ASSIGN:
				{
					i = LT(1);
					i_AST = astFactory.create(i);
					astFactory.makeASTRoot(currentAST, i_AST);
					match(SL_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = i.getLine(); col = i.getColumn();
					}
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					assignment_expr_AST = (AST)currentAST.root;
					assignment_expr_AST.setType(SHIFT_ASSIGNMENT_OP);
				}
				break;
			}
			case BAND_ASSIGN:
			case BOR_ASSIGN:
			case BXOR_ASSIGN:
			{
				{
				switch ( LA(1)) {
				case BAND_ASSIGN:
				{
					j = LT(1);
					j_AST = astFactory.create(j);
					astFactory.makeASTRoot(currentAST, j_AST);
					match(BAND_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = j.getLine(); col = j.getColumn();
					}
					break;
				}
				case BOR_ASSIGN:
				{
					k = LT(1);
					k_AST = astFactory.create(k);
					astFactory.makeASTRoot(currentAST, k_AST);
					match(BOR_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = k.getLine(); col = k.getColumn();
					}
					break;
				}
				case BXOR_ASSIGN:
				{
					l = LT(1);
					l_AST = astFactory.create(l);
					astFactory.makeASTRoot(currentAST, l_AST);
					match(BXOR_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = l.getLine(); col = l.getColumn();
					}
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				if ( inputState.guessing==0 ) {
					assignment_expr_AST = (AST)currentAST.root;
					assignment_expr_AST.setType(BITWISE_ASSIGNMENT_OP);
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			assignment_expr(in_spec);
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				
				if (in_spec) {
				reportError("assignment operators are not allowed in JML specification expressions",
				line, col);
				}
				
			}
			break;
		}
		case EOF:
		case SEMI:
		case RCURLY:
		case COMMA:
		case RPAREN:
		case INITIALLY:
		case READABLE_IF:
		case MONITORED_BY:
		case FOR:
		case RBRACK:
		case LITERAL_if:
		case COLON:
		case DOT_DOT:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		assignment_expr_AST = (AST)currentAST.root;
		returnAST = assignment_expr_AST;
	}
	
	public final void equivalence_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST equivalence_expr_AST = null;
		Token  e = null;
		AST e_AST = null;
		Token  n = null;
		AST n_AST = null;
		
		int line = 0, col = 0;
		
		
		implies_expr(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop554:
		do {
			if ((LA(1)==EQUIV||LA(1)==NOT_EQUIV)) {
				{
				switch ( LA(1)) {
				case EQUIV:
				{
					e = LT(1);
					e_AST = astFactory.create(e);
					astFactory.makeASTRoot(currentAST, e_AST);
					match(EQUIV);
					if ( inputState.guessing==0 ) {
						line = e.getLine(); col = e.getColumn();
					}
					break;
				}
				case NOT_EQUIV:
				{
					n = LT(1);
					n_AST = astFactory.create(n);
					astFactory.makeASTRoot(currentAST, n_AST);
					match(NOT_EQUIV);
					if ( inputState.guessing==0 ) {
						line = n.getLine(); col = n.getColumn();
					}
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				implies_expr(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					equivalence_expr_AST = (AST)currentAST.root;
					equivalence_expr_AST.setType(EQUIVALENCE_OP);
					if (!in_spec) {
					reportError("<==> and <=!=> can only be used in JML specification expressions",
					line, col);
					}
					
				}
			}
			else {
				break _loop554;
			}
			
		} while (true);
		}
		equivalence_expr_AST = (AST)currentAST.root;
		returnAST = equivalence_expr_AST;
	}
	
	public final void implies_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST implies_expr_AST = null;
		Token  li = null;
		AST li_AST = null;
		Token  bi = null;
		AST bi_AST = null;
		
		logical_or_expr(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case EOF:
		case SEMI:
		case RCURLY:
		case COMMA:
		case RPAREN:
		case ASSIGN:
		case INITIALLY:
		case READABLE_IF:
		case MONITORED_BY:
		case FOR:
		case RBRACK:
		case LITERAL_if:
		case COLON:
		case DOT_DOT:
		case PLUS_ASSIGN:
		case MINUS_ASSIGN:
		case STAR_ASSIGN:
		case DIV_ASSIGN:
		case MOD_ASSIGN:
		case SR_ASSIGN:
		case BSR_ASSIGN:
		case SL_ASSIGN:
		case BAND_ASSIGN:
		case BOR_ASSIGN:
		case BXOR_ASSIGN:
		case QUESTION:
		case EQUIV:
		case NOT_EQUIV:
		case LIMPLIES:
		{
			{
			switch ( LA(1)) {
			case LIMPLIES:
			{
				li = LT(1);
				li_AST = astFactory.create(li);
				astFactory.makeASTRoot(currentAST, li_AST);
				match(LIMPLIES);
				implies_non_backward_expr(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					implies_expr_AST = (AST)currentAST.root;
					
					implies_expr_AST.setType(IMPLICATION_OP);
					if (!in_spec) {
					reportError("==> can only be used in JML specification expressions",
					li.getLine(), li.getColumn());
					}
					
				}
				break;
			}
			case EOF:
			case SEMI:
			case RCURLY:
			case COMMA:
			case RPAREN:
			case ASSIGN:
			case INITIALLY:
			case READABLE_IF:
			case MONITORED_BY:
			case FOR:
			case RBRACK:
			case LITERAL_if:
			case COLON:
			case DOT_DOT:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BOR_ASSIGN:
			case BXOR_ASSIGN:
			case QUESTION:
			case EQUIV:
			case NOT_EQUIV:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		case BACKWARD_IMPLIES:
		{
			{
			int _cnt559=0;
			_loop559:
			do {
				if ((LA(1)==BACKWARD_IMPLIES)) {
					bi = LT(1);
					bi_AST = astFactory.create(bi);
					astFactory.makeASTRoot(currentAST, bi_AST);
					match(BACKWARD_IMPLIES);
					logical_or_expr(in_spec);
					astFactory.addASTChild(currentAST, returnAST);
					if ( inputState.guessing==0 ) {
						implies_expr_AST = (AST)currentAST.root;
						
						implies_expr_AST.setType(IMPLICATION_OP);
						if (!in_spec) {
						reportError("<== can only be used in JML specification expressions",
						bi.getLine(), bi.getColumn());
						}
						
					}
				}
				else {
					if ( _cnt559>=1 ) { break _loop559; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt559++;
			} while (true);
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		implies_expr_AST = (AST)currentAST.root;
		returnAST = implies_expr_AST;
	}
	
	public final void logical_or_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST logical_or_expr_AST = null;
		
		logical_and_expr(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop564:
		do {
			if ((LA(1)==LOR)) {
				AST tmp386_AST = null;
				tmp386_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp386_AST);
				match(LOR);
				logical_and_expr(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					logical_or_expr_AST = (AST)currentAST.root;
					logical_or_expr_AST.setType(LOGICAL_OP);
				}
			}
			else {
				break _loop564;
			}
			
		} while (true);
		}
		logical_or_expr_AST = (AST)currentAST.root;
		returnAST = logical_or_expr_AST;
	}
	
	public final void implies_non_backward_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST implies_non_backward_expr_AST = null;
		Token  li = null;
		AST li_AST = null;
		
		logical_or_expr(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case LIMPLIES:
		{
			li = LT(1);
			li_AST = astFactory.create(li);
			astFactory.makeASTRoot(currentAST, li_AST);
			match(LIMPLIES);
			implies_non_backward_expr(in_spec);
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				implies_non_backward_expr_AST = (AST)currentAST.root;
				
				implies_non_backward_expr_AST.setType(IMPLICATION_OP);
				if (!in_spec) {
				reportError("==> can only be used in JML specification expressions",
				li.getLine(), li.getColumn());
				}
				
			}
			break;
		}
		case EOF:
		case SEMI:
		case RCURLY:
		case COMMA:
		case RPAREN:
		case ASSIGN:
		case INITIALLY:
		case READABLE_IF:
		case MONITORED_BY:
		case FOR:
		case RBRACK:
		case LITERAL_if:
		case COLON:
		case DOT_DOT:
		case PLUS_ASSIGN:
		case MINUS_ASSIGN:
		case STAR_ASSIGN:
		case DIV_ASSIGN:
		case MOD_ASSIGN:
		case SR_ASSIGN:
		case BSR_ASSIGN:
		case SL_ASSIGN:
		case BAND_ASSIGN:
		case BOR_ASSIGN:
		case BXOR_ASSIGN:
		case QUESTION:
		case EQUIV:
		case NOT_EQUIV:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		implies_non_backward_expr_AST = (AST)currentAST.root;
		returnAST = implies_non_backward_expr_AST;
	}
	
	public final void logical_and_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST logical_and_expr_AST = null;
		
		inclusive_or_expr(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop567:
		do {
			if ((LA(1)==LAND)) {
				AST tmp387_AST = null;
				tmp387_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp387_AST);
				match(LAND);
				inclusive_or_expr(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					logical_and_expr_AST = (AST)currentAST.root;
					logical_and_expr_AST.setType(LOGICAL_OP);
				}
			}
			else {
				break _loop567;
			}
			
		} while (true);
		}
		logical_and_expr_AST = (AST)currentAST.root;
		returnAST = logical_and_expr_AST;
	}
	
	public final void inclusive_or_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST inclusive_or_expr_AST = null;
		
		exclusive_or_expr(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop570:
		do {
			if ((LA(1)==BOR)) {
				AST tmp388_AST = null;
				tmp388_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp388_AST);
				match(BOR);
				exclusive_or_expr(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					inclusive_or_expr_AST = (AST)currentAST.root;
					inclusive_or_expr_AST.setType(BITWISE_OP);
				}
			}
			else {
				break _loop570;
			}
			
		} while (true);
		}
		inclusive_or_expr_AST = (AST)currentAST.root;
		returnAST = inclusive_or_expr_AST;
	}
	
	public final void exclusive_or_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST exclusive_or_expr_AST = null;
		
		and_expr(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop573:
		do {
			if ((LA(1)==BXOR)) {
				AST tmp389_AST = null;
				tmp389_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp389_AST);
				match(BXOR);
				and_expr(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					exclusive_or_expr_AST = (AST)currentAST.root;
					exclusive_or_expr_AST.setType(BITWISE_OP);
				}
			}
			else {
				break _loop573;
			}
			
		} while (true);
		}
		exclusive_or_expr_AST = (AST)currentAST.root;
		returnAST = exclusive_or_expr_AST;
	}
	
	public final void and_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST and_expr_AST = null;
		
		equality_expr(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop576:
		do {
			if ((LA(1)==BAND)) {
				AST tmp390_AST = null;
				tmp390_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp390_AST);
				match(BAND);
				equality_expr(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					and_expr_AST = (AST)currentAST.root;
					and_expr_AST.setType(BITWISE_OP);
				}
			}
			else {
				break _loop576;
			}
			
		} while (true);
		}
		and_expr_AST = (AST)currentAST.root;
		returnAST = and_expr_AST;
	}
	
	public final void equality_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST equality_expr_AST = null;
		
		relational_expr(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop580:
		do {
			if ((LA(1)==NOT_EQUAL||LA(1)==EQUAL)) {
				{
				switch ( LA(1)) {
				case NOT_EQUAL:
				{
					AST tmp391_AST = null;
					tmp391_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp391_AST);
					match(NOT_EQUAL);
					break;
				}
				case EQUAL:
				{
					AST tmp392_AST = null;
					tmp392_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp392_AST);
					match(EQUAL);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				relational_expr(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					equality_expr_AST = (AST)currentAST.root;
					equality_expr_AST.setType(EQUALITY_OP);
				}
			}
			else {
				break _loop580;
			}
			
		} while (true);
		}
		equality_expr_AST = (AST)currentAST.root;
		returnAST = equality_expr_AST;
	}
	
	public final void relational_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST relational_expr_AST = null;
		Token  iso = null;
		AST iso_AST = null;
		
		shift_expr(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case EOF:
		case SEMI:
		case RCURLY:
		case COMMA:
		case RPAREN:
		case ASSIGN:
		case INITIALLY:
		case READABLE_IF:
		case MONITORED_BY:
		case FOR:
		case RBRACK:
		case LITERAL_if:
		case COLON:
		case DOT_DOT:
		case PLUS_ASSIGN:
		case MINUS_ASSIGN:
		case STAR_ASSIGN:
		case DIV_ASSIGN:
		case MOD_ASSIGN:
		case SR_ASSIGN:
		case BSR_ASSIGN:
		case SL_ASSIGN:
		case BAND_ASSIGN:
		case BOR_ASSIGN:
		case BXOR_ASSIGN:
		case QUESTION:
		case EQUIV:
		case NOT_EQUIV:
		case LIMPLIES:
		case BACKWARD_IMPLIES:
		case LOR:
		case LAND:
		case BOR:
		case BXOR:
		case BAND:
		case NOT_EQUAL:
		case EQUAL:
		case LT:
		case GT:
		case LE:
		case GE:
		case IS_SUBTYPE_OF:
		{
			{
			_loop586:
			do {
				if (((LA(1) >= LT && LA(1) <= IS_SUBTYPE_OF))) {
					{
					switch ( LA(1)) {
					case LT:
					case GT:
					case LE:
					case GE:
					{
						{
						switch ( LA(1)) {
						case LT:
						{
							AST tmp393_AST = null;
							tmp393_AST = astFactory.create(LT(1));
							astFactory.makeASTRoot(currentAST, tmp393_AST);
							match(LT);
							break;
						}
						case GT:
						{
							AST tmp394_AST = null;
							tmp394_AST = astFactory.create(LT(1));
							astFactory.makeASTRoot(currentAST, tmp394_AST);
							match(GT);
							break;
						}
						case LE:
						{
							AST tmp395_AST = null;
							tmp395_AST = astFactory.create(LT(1));
							astFactory.makeASTRoot(currentAST, tmp395_AST);
							match(LE);
							break;
						}
						case GE:
						{
							AST tmp396_AST = null;
							tmp396_AST = astFactory.create(LT(1));
							astFactory.makeASTRoot(currentAST, tmp396_AST);
							match(GE);
							break;
						}
						default:
						{
							throw new NoViableAltException(LT(1), getFilename());
						}
						}
						}
						if ( inputState.guessing==0 ) {
							relational_expr_AST = (AST)currentAST.root;
							relational_expr_AST.setType(RELATIONAL_OP);
						}
						break;
					}
					case IS_SUBTYPE_OF:
					{
						iso = LT(1);
						iso_AST = astFactory.create(iso);
						astFactory.makeASTRoot(currentAST, iso_AST);
						match(IS_SUBTYPE_OF);
						if ( inputState.guessing==0 ) {
							if (!in_spec) {
							reportError("<: can only be used in JML specification expressions",
							iso.getLine(), iso.getColumn());
							}
							
						}
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					shift_expr(in_spec);
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop586;
				}
				
			} while (true);
			}
			break;
		}
		case LITERAL_instanceof:
		{
			AST tmp397_AST = null;
			tmp397_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp397_AST);
			match(LITERAL_instanceof);
			type_spec();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		relational_expr_AST = (AST)currentAST.root;
		returnAST = relational_expr_AST;
	}
	
	public final void shift_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST shift_expr_AST = null;
		
		additive_expr(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop590:
		do {
			if (((LA(1) >= SL && LA(1) <= BSR))) {
				{
				switch ( LA(1)) {
				case SL:
				{
					AST tmp398_AST = null;
					tmp398_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp398_AST);
					match(SL);
					break;
				}
				case SR:
				{
					AST tmp399_AST = null;
					tmp399_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp399_AST);
					match(SR);
					break;
				}
				case BSR:
				{
					AST tmp400_AST = null;
					tmp400_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp400_AST);
					match(BSR);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				additive_expr(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					shift_expr_AST = (AST)currentAST.root;
					shift_expr_AST.setType(SHIFT_OP);
				}
			}
			else {
				break _loop590;
			}
			
		} while (true);
		}
		shift_expr_AST = (AST)currentAST.root;
		returnAST = shift_expr_AST;
	}
	
	public final void additive_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST additive_expr_AST = null;
		
		mult_expr(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop594:
		do {
			if ((LA(1)==PLUS||LA(1)==MINUS)) {
				{
				switch ( LA(1)) {
				case PLUS:
				{
					AST tmp401_AST = null;
					tmp401_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp401_AST);
					match(PLUS);
					break;
				}
				case MINUS:
				{
					AST tmp402_AST = null;
					tmp402_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp402_AST);
					match(MINUS);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				mult_expr(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					additive_expr_AST = (AST)currentAST.root;
					additive_expr_AST.setType(ADDITIVE_OP);
				}
			}
			else {
				break _loop594;
			}
			
		} while (true);
		}
		additive_expr_AST = (AST)currentAST.root;
		returnAST = additive_expr_AST;
	}
	
	public final void mult_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST mult_expr_AST = null;
		
		unary_expr(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop598:
		do {
			if ((_tokenSet_46.member(LA(1)))) {
				{
				switch ( LA(1)) {
				case STAR:
				{
					AST tmp403_AST = null;
					tmp403_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp403_AST);
					match(STAR);
					break;
				}
				case DIV:
				{
					AST tmp404_AST = null;
					tmp404_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp404_AST);
					match(DIV);
					break;
				}
				case MOD:
				{
					AST tmp405_AST = null;
					tmp405_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp405_AST);
					match(MOD);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				unary_expr(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					mult_expr_AST = (AST)currentAST.root;
					mult_expr_AST.setType(MULTIPLICATIVE_OP);
				}
			}
			else {
				break _loop598;
			}
			
		} while (true);
		}
		mult_expr_AST = (AST)currentAST.root;
		returnAST = mult_expr_AST;
	}
	
	public final void unary_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST unary_expr_AST = null;
		Token  i = null;
		AST i_AST = null;
		Token  d = null;
		AST d_AST = null;
		
		int line = 0, col = 0;
		
		
		switch ( LA(1)) {
		case INC:
		case DEC:
		{
			{
			switch ( LA(1)) {
			case INC:
			{
				i = LT(1);
				i_AST = astFactory.create(i);
				astFactory.makeASTRoot(currentAST, i_AST);
				match(INC);
				if ( inputState.guessing==0 ) {
					line = i.getLine(); col = i.getColumn();
				}
				break;
			}
			case DEC:
			{
				d = LT(1);
				d_AST = astFactory.create(d);
				astFactory.makeASTRoot(currentAST, d_AST);
				match(DEC);
				if ( inputState.guessing==0 ) {
					line = d.getLine(); col = d.getColumn();
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			unary_expr(in_spec);
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				unary_expr_AST = (AST)currentAST.root;
				
				unary_expr_AST.setType(PRE_INCREMENT_OP);
				if (in_spec) {
				reportError("++ and -- are not allowed in JML specification expressions",
				line, col);
				}
				
			}
			unary_expr_AST = (AST)currentAST.root;
			break;
		}
		case PLUS:
		case MINUS:
		{
			{
			switch ( LA(1)) {
			case PLUS:
			{
				AST tmp406_AST = null;
				tmp406_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp406_AST);
				match(PLUS);
				break;
			}
			case MINUS:
			{
				AST tmp407_AST = null;
				tmp407_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp407_AST);
				match(MINUS);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			unary_expr(in_spec);
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				unary_expr_AST = (AST)currentAST.root;
				unary_expr_AST.setType(UNARY_NUMERIC_OP);
			}
			unary_expr_AST = (AST)currentAST.root;
			break;
		}
		case IDENT:
		case LPAREN:
		case STRING_LITERAL:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_new:
		case LITERAL_void:
		case BNOT:
		case LNOT:
		case LITERAL_true:
		case LITERAL_false:
		case LITERAL_null:
		case T_RESULT:
		case T_OLD:
		case T_NOT_MODIFIED:
		case T_FRESH:
		case T_REACH:
		case T_NONNULLELEMENTS:
		case T_TYPEOF:
		case T_ELEMTYPE:
		case T_TYPE:
		case T_LOCKSET:
		case T_IS_INITIALIZED:
		case T_INVARIANT_FOR:
		case INFORMAL_DESCRIPTION:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_short:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_float:
		case LITERAL_double:
		case NUM_INT:
		case CHAR_LITERAL:
		case NUM_FLOAT:
		{
			unaryExpressionNotPlusMinus(in_spec);
			astFactory.addASTChild(currentAST, returnAST);
			unary_expr_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = unary_expr_AST;
	}
	
	public final void unaryExpressionNotPlusMinus(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST unaryExpressionNotPlusMinus_AST = null;
		AST t_AST = null;
		AST c_AST = null;
		AST t2_AST = null;
		AST c2_AST = null;
		
		switch ( LA(1)) {
		case BNOT:
		{
			AST tmp408_AST = null;
			tmp408_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp408_AST);
			match(BNOT);
			unary_expr(in_spec);
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				unaryExpressionNotPlusMinus_AST = (AST)currentAST.root;
				unaryExpressionNotPlusMinus_AST.setType(UNARY_NUMERIC_OP);
			}
			unaryExpressionNotPlusMinus_AST = (AST)currentAST.root;
			break;
		}
		case LNOT:
		{
			AST tmp409_AST = null;
			tmp409_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp409_AST);
			match(LNOT);
			unary_expr(in_spec);
			astFactory.addASTChild(currentAST, returnAST);
			unaryExpressionNotPlusMinus_AST = (AST)currentAST.root;
			break;
		}
		case IDENT:
		case LPAREN:
		case STRING_LITERAL:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_new:
		case LITERAL_void:
		case LITERAL_true:
		case LITERAL_false:
		case LITERAL_null:
		case T_RESULT:
		case T_OLD:
		case T_NOT_MODIFIED:
		case T_FRESH:
		case T_REACH:
		case T_NONNULLELEMENTS:
		case T_TYPEOF:
		case T_ELEMTYPE:
		case T_TYPE:
		case T_LOCKSET:
		case T_IS_INITIALIZED:
		case T_INVARIANT_FOR:
		case INFORMAL_DESCRIPTION:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_short:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_float:
		case LITERAL_double:
		case NUM_INT:
		case CHAR_LITERAL:
		case NUM_FLOAT:
		{
			{
			if ((LA(1)==LPAREN) && (_tokenSet_47.member(LA(2)))) {
				AST tmp410_AST = null;
				tmp410_AST = astFactory.create(LT(1));
				match(LPAREN);
				builtInType_spec();
				t_AST = (AST)returnAST;
				AST tmp411_AST = null;
				tmp411_AST = astFactory.create(LT(1));
				match(RPAREN);
				unary_expr(in_spec);
				c_AST = (AST)returnAST;
				if ( inputState.guessing==0 ) {
					unaryExpressionNotPlusMinus_AST = (AST)currentAST.root;
					unaryExpressionNotPlusMinus_AST = (AST)astFactory.make( (new ASTArray(3)).add(astFactory.create(CAST,"cast")).add(t_AST).add(c_AST));
					currentAST.root = unaryExpressionNotPlusMinus_AST;
					currentAST.child = unaryExpressionNotPlusMinus_AST!=null &&unaryExpressionNotPlusMinus_AST.getFirstChild()!=null ?
						unaryExpressionNotPlusMinus_AST.getFirstChild() : unaryExpressionNotPlusMinus_AST;
					currentAST.advanceChildToEnd();
				}
			}
			else {
				boolean synPredMatched605 = false;
				if (((LA(1)==LPAREN) && (LA(2)==IDENT))) {
					int _m605 = mark();
					synPredMatched605 = true;
					inputState.guessing++;
					try {
						{
						match(LPAREN);
						reference_type_spec();
						match(RPAREN);
						unaryExpressionNotPlusMinus(in_spec);
						}
					}
					catch (RecognitionException pe) {
						synPredMatched605 = false;
					}
					rewind(_m605);
					inputState.guessing--;
				}
				if ( synPredMatched605 ) {
					AST tmp412_AST = null;
					tmp412_AST = astFactory.create(LT(1));
					match(LPAREN);
					reference_type_spec();
					t2_AST = (AST)returnAST;
					AST tmp413_AST = null;
					tmp413_AST = astFactory.create(LT(1));
					match(RPAREN);
					unaryExpressionNotPlusMinus(in_spec);
					c2_AST = (AST)returnAST;
					if ( inputState.guessing==0 ) {
						unaryExpressionNotPlusMinus_AST = (AST)currentAST.root;
						unaryExpressionNotPlusMinus_AST = (AST)astFactory.make( (new ASTArray(3)).add(astFactory.create(CAST,"cast")).add(t2_AST).add(c2_AST));
						currentAST.root = unaryExpressionNotPlusMinus_AST;
						currentAST.child = unaryExpressionNotPlusMinus_AST!=null &&unaryExpressionNotPlusMinus_AST.getFirstChild()!=null ?
							unaryExpressionNotPlusMinus_AST.getFirstChild() : unaryExpressionNotPlusMinus_AST;
						currentAST.advanceChildToEnd();
					}
				}
				else if ((_tokenSet_48.member(LA(1))) && (_tokenSet_49.member(LA(2)))) {
					postfix_expr(in_spec);
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				unaryExpressionNotPlusMinus_AST = (AST)currentAST.root;
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			returnAST = unaryExpressionNotPlusMinus_AST;
		}
		
	public final void builtInType_spec() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST builtInType_spec_AST = null;
		
		builtInType();
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case LBRACK:
		{
			dims();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case RPAREN:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		builtInType_spec_AST = (AST)currentAST.root;
		returnAST = builtInType_spec_AST;
	}
	
	public final void reference_type_spec() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST reference_type_spec_AST = null;
		
		reference_type();
		astFactory.addASTChild(currentAST, returnAST);
		{
		switch ( LA(1)) {
		case LBRACK:
		{
			dims();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case RPAREN:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		reference_type_spec_AST = (AST)currentAST.root;
		returnAST = reference_type_spec_AST;
	}
	
	public final void postfix_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST postfix_expr_AST = null;
		Token  lbc = null;
		AST lbc_AST = null;
		Token  in = null;
		AST in_AST = null;
		Token  de = null;
		AST de_AST = null;
		Token  lbt = null;
		AST lbt_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		case LPAREN:
		case STRING_LITERAL:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_new:
		case LITERAL_true:
		case LITERAL_false:
		case LITERAL_null:
		case T_RESULT:
		case T_OLD:
		case T_NOT_MODIFIED:
		case T_FRESH:
		case T_REACH:
		case T_NONNULLELEMENTS:
		case T_TYPEOF:
		case T_ELEMTYPE:
		case T_TYPE:
		case T_LOCKSET:
		case T_IS_INITIALIZED:
		case T_INVARIANT_FOR:
		case INFORMAL_DESCRIPTION:
		case NUM_INT:
		case CHAR_LITERAL:
		case NUM_FLOAT:
		{
			primary_expr(in_spec);
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop617:
			do {
				switch ( LA(1)) {
				case DOT:
				{
					AST tmp414_AST = null;
					tmp414_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp414_AST);
					match(DOT);
					{
					switch ( LA(1)) {
					case IDENT:
					{
						AST tmp415_AST = null;
						tmp415_AST = astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp415_AST);
						match(IDENT);
						break;
					}
					case LITERAL_this:
					{
						AST tmp416_AST = null;
						tmp416_AST = astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp416_AST);
						match(LITERAL_this);
						break;
					}
					case LITERAL_class:
					{
						AST tmp417_AST = null;
						tmp417_AST = astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp417_AST);
						match(LITERAL_class);
						break;
					}
					case LITERAL_new:
					{
						new_expr(in_spec);
						astFactory.addASTChild(currentAST, returnAST);
						break;
					}
					case LITERAL_super:
					{
						AST tmp418_AST = null;
						tmp418_AST = astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp418_AST);
						match(LITERAL_super);
						AST tmp419_AST = null;
						tmp419_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp419_AST);
						match(LPAREN);
						{
						switch ( LA(1)) {
						case IDENT:
						case LPAREN:
						case STRING_LITERAL:
						case LITERAL_super:
						case LITERAL_this:
						case LITERAL_new:
						case LITERAL_void:
						case PLUS:
						case MINUS:
						case INC:
						case DEC:
						case BNOT:
						case LNOT:
						case LITERAL_true:
						case LITERAL_false:
						case LITERAL_null:
						case T_RESULT:
						case T_OLD:
						case T_NOT_MODIFIED:
						case T_FRESH:
						case T_REACH:
						case T_NONNULLELEMENTS:
						case T_TYPEOF:
						case T_ELEMTYPE:
						case T_TYPE:
						case T_LOCKSET:
						case T_IS_INITIALIZED:
						case T_INVARIANT_FOR:
						case INFORMAL_DESCRIPTION:
						case LITERAL_boolean:
						case LITERAL_byte:
						case LITERAL_char:
						case LITERAL_short:
						case LITERAL_int:
						case LITERAL_long:
						case LITERAL_float:
						case LITERAL_double:
						case NUM_INT:
						case CHAR_LITERAL:
						case NUM_FLOAT:
						{
							expression_list(in_spec);
							astFactory.addASTChild(currentAST, returnAST);
							break;
						}
						case RPAREN:
						{
							break;
						}
						default:
						{
							throw new NoViableAltException(LT(1), getFilename());
						}
						}
						}
						AST tmp420_AST = null;
						tmp420_AST = astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp420_AST);
						match(RPAREN);
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					break;
				}
				case LPAREN:
				{
					AST tmp421_AST = null;
					tmp421_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp421_AST);
					match(LPAREN);
					{
					switch ( LA(1)) {
					case IDENT:
					case LPAREN:
					case STRING_LITERAL:
					case LITERAL_super:
					case LITERAL_this:
					case LITERAL_new:
					case LITERAL_void:
					case PLUS:
					case MINUS:
					case INC:
					case DEC:
					case BNOT:
					case LNOT:
					case LITERAL_true:
					case LITERAL_false:
					case LITERAL_null:
					case T_RESULT:
					case T_OLD:
					case T_NOT_MODIFIED:
					case T_FRESH:
					case T_REACH:
					case T_NONNULLELEMENTS:
					case T_TYPEOF:
					case T_ELEMTYPE:
					case T_TYPE:
					case T_LOCKSET:
					case T_IS_INITIALIZED:
					case T_INVARIANT_FOR:
					case INFORMAL_DESCRIPTION:
					case LITERAL_boolean:
					case LITERAL_byte:
					case LITERAL_char:
					case LITERAL_short:
					case LITERAL_int:
					case LITERAL_long:
					case LITERAL_float:
					case LITERAL_double:
					case NUM_INT:
					case CHAR_LITERAL:
					case NUM_FLOAT:
					{
						expression_list(in_spec);
						astFactory.addASTChild(currentAST, returnAST);
						break;
					}
					case RPAREN:
					{
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					match(RPAREN);
					break;
				}
				default:
					if ((LA(1)==LBRACK) && (LA(2)==RBRACK)) {
						{
						int _cnt615=0;
						_loop615:
						do {
							if ((LA(1)==LBRACK)) {
								lbc = LT(1);
								lbc_AST = astFactory.create(lbc);
								astFactory.makeASTRoot(currentAST, lbc_AST);
								match(LBRACK);
								if ( inputState.guessing==0 ) {
									lbc_AST.setType(ARRAY_DECLARATOR);
									lbc_AST.setText("array_declarator");
									
								}
								match(RBRACK);
							}
							else {
								if ( _cnt615>=1 ) { break _loop615; } else {throw new NoViableAltException(LT(1), getFilename());}
							}
							
							_cnt615++;
						} while (true);
						}
						AST tmp424_AST = null;
						tmp424_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp424_AST);
						match(DOT);
						AST tmp425_AST = null;
						tmp425_AST = astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp425_AST);
						match(LITERAL_class);
					}
					else if ((LA(1)==LBRACK) && (_tokenSet_35.member(LA(2)))) {
						AST tmp426_AST = null;
						tmp426_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp426_AST);
						match(LBRACK);
						expression(in_spec);
						astFactory.addASTChild(currentAST, returnAST);
						match(RBRACK);
					}
				else {
					break _loop617;
				}
				}
			} while (true);
			}
			{
			switch ( LA(1)) {
			case INC:
			{
				in = LT(1);
				in_AST = astFactory.create(in);
				astFactory.makeASTRoot(currentAST, in_AST);
				match(INC);
				if ( inputState.guessing==0 ) {
					in_AST.setType(POST_INCREMENT_OP);
					if (in_spec) {
					reportError("++ is not allowed in JML specification expressions",
					in.getLine(), in.getColumn());
					}
					
				}
				break;
			}
			case DEC:
			{
				de = LT(1);
				de_AST = astFactory.create(de);
				astFactory.makeASTRoot(currentAST, de_AST);
				match(DEC);
				if ( inputState.guessing==0 ) {
					de_AST.setType(POST_INCREMENT_OP);
					if (in_spec) {
					reportError("-- is not allowed in JML specification expressions",
					de.getLine(), de.getColumn());
					}
					
				}
				break;
			}
			case EOF:
			case SEMI:
			case STAR:
			case RCURLY:
			case COMMA:
			case RPAREN:
			case ASSIGN:
			case INITIALLY:
			case READABLE_IF:
			case MONITORED_BY:
			case FOR:
			case RBRACK:
			case LITERAL_if:
			case COLON:
			case DOT_DOT:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BOR_ASSIGN:
			case BXOR_ASSIGN:
			case QUESTION:
			case EQUIV:
			case NOT_EQUIV:
			case LIMPLIES:
			case BACKWARD_IMPLIES:
			case LOR:
			case LAND:
			case BOR:
			case BXOR:
			case BAND:
			case NOT_EQUAL:
			case EQUAL:
			case LT:
			case GT:
			case LE:
			case GE:
			case IS_SUBTYPE_OF:
			case LITERAL_instanceof:
			case SL:
			case SR:
			case BSR:
			case PLUS:
			case MINUS:
			case DIV:
			case MOD:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			postfix_expr_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_void:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_short:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_float:
		case LITERAL_double:
		{
			builtInType();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop620:
			do {
				if ((LA(1)==LBRACK)) {
					lbt = LT(1);
					lbt_AST = astFactory.create(lbt);
					astFactory.makeASTRoot(currentAST, lbt_AST);
					match(LBRACK);
					if ( inputState.guessing==0 ) {
						lbt_AST.setType(ARRAY_DECLARATOR);
						lbt_AST.setText("array_declarator");
						
					}
					match(RBRACK);
				}
				else {
					break _loop620;
				}
				
			} while (true);
			}
			AST tmp429_AST = null;
			tmp429_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp429_AST);
			match(DOT);
			AST tmp430_AST = null;
			tmp430_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp430_AST);
			match(LITERAL_class);
			postfix_expr_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = postfix_expr_AST;
	}
	
	public final void primary_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST primary_expr_AST = null;
		Token  id = null;
		AST id_AST = null;
		AST jmlp_AST = null;
		AST sqe_AST = null;
		Token  lbln = null;
		AST lbln_AST = null;
		Token  lblp = null;
		AST lblp_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		{
			id = LT(1);
			id_AST = astFactory.create(id);
			astFactory.addASTChild(currentAST, id_AST);
			match(IDENT);
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_new:
		{
			new_expr(in_spec);
			astFactory.addASTChild(currentAST, returnAST);
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		case STRING_LITERAL:
		case NUM_INT:
		case CHAR_LITERAL:
		case NUM_FLOAT:
		{
			constant();
			astFactory.addASTChild(currentAST, returnAST);
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_super:
		{
			AST tmp431_AST = null;
			tmp431_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp431_AST);
			match(LITERAL_super);
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_true:
		{
			AST tmp432_AST = null;
			tmp432_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp432_AST);
			match(LITERAL_true);
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_false:
		{
			AST tmp433_AST = null;
			tmp433_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp433_AST);
			match(LITERAL_false);
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_this:
		{
			AST tmp434_AST = null;
			tmp434_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp434_AST);
			match(LITERAL_this);
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_null:
		{
			AST tmp435_AST = null;
			tmp435_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp435_AST);
			match(LITERAL_null);
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		case T_RESULT:
		case T_OLD:
		case T_NOT_MODIFIED:
		case T_FRESH:
		case T_REACH:
		case T_NONNULLELEMENTS:
		case T_TYPEOF:
		case T_ELEMTYPE:
		case T_TYPE:
		case T_LOCKSET:
		case T_IS_INITIALIZED:
		case T_INVARIANT_FOR:
		case INFORMAL_DESCRIPTION:
		{
			jml_primary();
			jmlp_AST = (AST)returnAST;
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				
				if (!in_spec) {
				reportError("Can't use a jml-primary outside a specification",
				((LineAST)jmlp_AST).line, ((LineAST)jmlp_AST).column);
				}
				
			}
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		case LPAREN:
		{
			match(LPAREN);
			{
			switch ( LA(1)) {
			case IDENT:
			case LPAREN:
			case STRING_LITERAL:
			case LITERAL_super:
			case LITERAL_this:
			case LITERAL_new:
			case LITERAL_void:
			case PLUS:
			case MINUS:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case T_RESULT:
			case T_OLD:
			case T_NOT_MODIFIED:
			case T_FRESH:
			case T_REACH:
			case T_NONNULLELEMENTS:
			case T_TYPEOF:
			case T_ELEMTYPE:
			case T_TYPE:
			case T_LOCKSET:
			case T_IS_INITIALIZED:
			case T_INVARIANT_FOR:
			case INFORMAL_DESCRIPTION:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			case NUM_INT:
			case CHAR_LITERAL:
			case NUM_FLOAT:
			{
				expression(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case T_FORALL:
			case T_EXISTS:
			case T_MAX:
			case T_MIN:
			case T_SUM:
			case T_PRODUCT:
			case T_NUM_OF:
			{
				spec_quantified_expr();
				sqe_AST = (AST)returnAST;
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					if (!in_spec) {
					reportError("Can't use a quantifier outside a specification",
					((LineAST)sqe_AST).line, ((LineAST)sqe_AST).column);
					}
					
				}
				break;
			}
			case T_LBLNEG:
			{
				lbln = LT(1);
				lbln_AST = astFactory.create(lbln);
				astFactory.makeASTRoot(currentAST, lbln_AST);
				match(T_LBLNEG);
				AST tmp437_AST = null;
				tmp437_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp437_AST);
				match(IDENT);
				spec_expression();
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					if (!in_spec) {
					reportError("Can't use \\lblneg outside a specification",
					lbln.getLine(), lbln.getColumn());
					}
					
				}
				break;
			}
			case T_LBLPOS:
			{
				lblp = LT(1);
				lblp_AST = astFactory.create(lblp);
				astFactory.makeASTRoot(currentAST, lblp_AST);
				match(T_LBLPOS);
				AST tmp438_AST = null;
				tmp438_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp438_AST);
				match(IDENT);
				spec_expression();
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					if (!in_spec) {
					reportError("Can't use \\lblpos outside a specification",
					lblp.getLine(), lblp.getColumn());
					}
					
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RPAREN);
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = primary_expr_AST;
	}
	
	public final void new_expr(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST new_expr_AST = null;
		
		AST tmp440_AST = null;
		tmp440_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp440_AST);
		match(LITERAL_new);
		type();
		astFactory.addASTChild(currentAST, returnAST);
		new_suffix(in_spec);
		astFactory.addASTChild(currentAST, returnAST);
		new_expr_AST = (AST)currentAST.root;
		returnAST = new_expr_AST;
	}
	
	public final void constant() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST constant_AST = null;
		
		switch ( LA(1)) {
		case NUM_INT:
		{
			AST tmp441_AST = null;
			tmp441_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp441_AST);
			match(NUM_INT);
			constant_AST = (AST)currentAST.root;
			break;
		}
		case CHAR_LITERAL:
		{
			AST tmp442_AST = null;
			tmp442_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp442_AST);
			match(CHAR_LITERAL);
			constant_AST = (AST)currentAST.root;
			break;
		}
		case STRING_LITERAL:
		{
			AST tmp443_AST = null;
			tmp443_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp443_AST);
			match(STRING_LITERAL);
			constant_AST = (AST)currentAST.root;
			break;
		}
		case NUM_FLOAT:
		{
			AST tmp444_AST = null;
			tmp444_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp444_AST);
			match(NUM_FLOAT);
			constant_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = constant_AST;
	}
	
	public final void jml_primary() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST jml_primary_AST = null;
		
		switch ( LA(1)) {
		case T_RESULT:
		{
			AST tmp445_AST = null;
			tmp445_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp445_AST);
			match(T_RESULT);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_OLD:
		{
			AST tmp446_AST = null;
			tmp446_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp446_AST);
			match(T_OLD);
			match(LPAREN);
			spec_expression();
			astFactory.addASTChild(currentAST, returnAST);
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_NOT_MODIFIED:
		{
			AST tmp449_AST = null;
			tmp449_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp449_AST);
			match(T_NOT_MODIFIED);
			match(LPAREN);
			store_references();
			astFactory.addASTChild(currentAST, returnAST);
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_FRESH:
		{
			AST tmp452_AST = null;
			tmp452_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp452_AST);
			match(T_FRESH);
			match(LPAREN);
			spec_expression_list();
			astFactory.addASTChild(currentAST, returnAST);
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_REACH:
		{
			AST tmp455_AST = null;
			tmp455_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp455_AST);
			match(T_REACH);
			match(LPAREN);
			spec_expression();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case COMMA:
			{
				match(COMMA);
				reference_type();
				astFactory.addASTChild(currentAST, returnAST);
				{
				switch ( LA(1)) {
				case COMMA:
				{
					match(COMMA);
					store_ref_expression();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				case RPAREN:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case INFORMAL_DESCRIPTION:
		{
			informal_desc();
			astFactory.addASTChild(currentAST, returnAST);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_NONNULLELEMENTS:
		{
			AST tmp460_AST = null;
			tmp460_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp460_AST);
			match(T_NONNULLELEMENTS);
			match(LPAREN);
			spec_expression();
			astFactory.addASTChild(currentAST, returnAST);
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_TYPEOF:
		{
			AST tmp463_AST = null;
			tmp463_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp463_AST);
			match(T_TYPEOF);
			match(LPAREN);
			spec_expression();
			astFactory.addASTChild(currentAST, returnAST);
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_ELEMTYPE:
		{
			AST tmp466_AST = null;
			tmp466_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp466_AST);
			match(T_ELEMTYPE);
			match(LPAREN);
			spec_expression();
			astFactory.addASTChild(currentAST, returnAST);
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_TYPE:
		{
			AST tmp469_AST = null;
			tmp469_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp469_AST);
			match(T_TYPE);
			match(LPAREN);
			type();
			astFactory.addASTChild(currentAST, returnAST);
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_LOCKSET:
		{
			AST tmp472_AST = null;
			tmp472_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp472_AST);
			match(T_LOCKSET);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_IS_INITIALIZED:
		{
			AST tmp473_AST = null;
			tmp473_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp473_AST);
			match(T_IS_INITIALIZED);
			match(LPAREN);
			reference_type();
			astFactory.addASTChild(currentAST, returnAST);
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_INVARIANT_FOR:
		{
			AST tmp476_AST = null;
			tmp476_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp476_AST);
			match(T_INVARIANT_FOR);
			match(LPAREN);
			spec_expression();
			astFactory.addASTChild(currentAST, returnAST);
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = jml_primary_AST;
	}
	
	public final void spec_quantified_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST spec_quantified_expr_AST = null;
		
		quantifier();
		astFactory.addASTChild(currentAST, returnAST);
		wrap_quantified_var_decl();
		astFactory.addASTChild(currentAST, returnAST);
		match(SEMI);
		{
		switch ( LA(1)) {
		case IDENT:
		case LPAREN:
		case STRING_LITERAL:
		case LITERAL_super:
		case LITERAL_this:
		case LITERAL_new:
		case LITERAL_void:
		case PLUS:
		case MINUS:
		case INC:
		case DEC:
		case BNOT:
		case LNOT:
		case LITERAL_true:
		case LITERAL_false:
		case LITERAL_null:
		case T_RESULT:
		case T_OLD:
		case T_NOT_MODIFIED:
		case T_FRESH:
		case T_REACH:
		case T_NONNULLELEMENTS:
		case T_TYPEOF:
		case T_ELEMTYPE:
		case T_TYPE:
		case T_LOCKSET:
		case T_IS_INITIALIZED:
		case T_INVARIANT_FOR:
		case INFORMAL_DESCRIPTION:
		case LITERAL_boolean:
		case LITERAL_byte:
		case LITERAL_char:
		case LITERAL_short:
		case LITERAL_int:
		case LITERAL_long:
		case LITERAL_float:
		case LITERAL_double:
		case NUM_INT:
		case CHAR_LITERAL:
		case NUM_FLOAT:
		{
			spec_expression();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case SEMI:
			{
				match(SEMI);
				spec_expression();
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		case SEMI:
		{
			match(SEMI);
			spec_expression();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			spec_quantified_expr_AST = (AST)currentAST.root;
			spec_quantified_expr_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(QUANTIFIED_EXPR,"quantified_exp")).add(spec_quantified_expr_AST));
			
			currentAST.root = spec_quantified_expr_AST;
			currentAST.child = spec_quantified_expr_AST!=null &&spec_quantified_expr_AST.getFirstChild()!=null ?
				spec_quantified_expr_AST.getFirstChild() : spec_quantified_expr_AST;
			currentAST.advanceChildToEnd();
		}
		spec_quantified_expr_AST = (AST)currentAST.root;
		returnAST = spec_quantified_expr_AST;
	}
	
	public final void new_suffix(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST new_suffix_AST = null;
		AST sce_AST = null;
		
		switch ( LA(1)) {
		case LPAREN:
		{
			match(LPAREN);
			{
			switch ( LA(1)) {
			case IDENT:
			case LPAREN:
			case STRING_LITERAL:
			case LITERAL_super:
			case LITERAL_this:
			case LITERAL_new:
			case LITERAL_void:
			case PLUS:
			case MINUS:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case T_RESULT:
			case T_OLD:
			case T_NOT_MODIFIED:
			case T_FRESH:
			case T_REACH:
			case T_NONNULLELEMENTS:
			case T_TYPEOF:
			case T_ELEMTYPE:
			case T_TYPE:
			case T_LOCKSET:
			case T_IS_INITIALIZED:
			case T_INVARIANT_FOR:
			case INFORMAL_DESCRIPTION:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_long:
			case LITERAL_float:
			case LITERAL_double:
			case NUM_INT:
			case CHAR_LITERAL:
			case NUM_FLOAT:
			{
				expression_list(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RPAREN);
			{
			switch ( LA(1)) {
			case LCURLY:
			{
				class_block(in_spec, no_jml_stmts);
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case EOF:
			case SEMI:
			case DOT:
			case STAR:
			case RCURLY:
			case COMMA:
			case LPAREN:
			case RPAREN:
			case ASSIGN:
			case INITIALLY:
			case READABLE_IF:
			case MONITORED_BY:
			case FOR:
			case LBRACK:
			case RBRACK:
			case LITERAL_if:
			case COLON:
			case DOT_DOT:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BOR_ASSIGN:
			case BXOR_ASSIGN:
			case QUESTION:
			case EQUIV:
			case NOT_EQUIV:
			case LIMPLIES:
			case BACKWARD_IMPLIES:
			case LOR:
			case LAND:
			case BOR:
			case BXOR:
			case BAND:
			case NOT_EQUAL:
			case EQUAL:
			case LT:
			case GT:
			case LE:
			case GE:
			case IS_SUBTYPE_OF:
			case LITERAL_instanceof:
			case SL:
			case SR:
			case BSR:
			case PLUS:
			case MINUS:
			case DIV:
			case MOD:
			case INC:
			case DEC:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			new_suffix_AST = (AST)currentAST.root;
			break;
		}
		case LBRACK:
		{
			array_decl(in_spec);
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case LCURLY:
			{
				array_initializer(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
				break;
			}
			case EOF:
			case SEMI:
			case DOT:
			case STAR:
			case RCURLY:
			case COMMA:
			case LPAREN:
			case RPAREN:
			case ASSIGN:
			case INITIALLY:
			case READABLE_IF:
			case MONITORED_BY:
			case FOR:
			case LBRACK:
			case RBRACK:
			case LITERAL_if:
			case COLON:
			case DOT_DOT:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BOR_ASSIGN:
			case BXOR_ASSIGN:
			case QUESTION:
			case EQUIV:
			case NOT_EQUIV:
			case LIMPLIES:
			case BACKWARD_IMPLIES:
			case LOR:
			case LAND:
			case BOR:
			case BXOR:
			case BAND:
			case NOT_EQUAL:
			case EQUAL:
			case LT:
			case GT:
			case LE:
			case GE:
			case IS_SUBTYPE_OF:
			case LITERAL_instanceof:
			case SL:
			case SR:
			case BSR:
			case PLUS:
			case MINUS:
			case DIV:
			case MOD:
			case INC:
			case DEC:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			new_suffix_AST = (AST)currentAST.root;
			break;
		}
		case LCURLY:
		{
			set_comprehension();
			sce_AST = (AST)returnAST;
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				
				if (!in_spec) {
				reportError("cannot use set-comprehension outside specification",
				((LineAST)sce_AST).line, ((LineAST)sce_AST).column);
				}
				
			}
			new_suffix_AST = (AST)currentAST.root;
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		returnAST = new_suffix_AST;
	}
	
	public final void array_decl(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST array_decl_AST = null;
		
		{
		int _cnt636=0;
		_loop636:
		do {
			if ((LA(1)==LBRACK) && (_tokenSet_35.member(LA(2)))) {
				dim_exprs(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
			}
			else if ((LA(1)==LBRACK) && (LA(2)==RBRACK)) {
				dims();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				if ( _cnt636>=1 ) { break _loop636; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt636++;
		} while (true);
		}
		array_decl_AST = (AST)currentAST.root;
		returnAST = array_decl_AST;
	}
	
	public final void set_comprehension() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST set_comprehension_AST = null;
		
		match(LCURLY);
		type_spec();
		astFactory.addASTChild(currentAST, returnAST);
		quantified_var_declarator();
		astFactory.addASTChild(currentAST, returnAST);
		match(BOR);
		set_comprehension_pred();
		astFactory.addASTChild(currentAST, returnAST);
		match(RCURLY);
		if ( inputState.guessing==0 ) {
			set_comprehension_AST = (AST)currentAST.root;
			set_comprehension_AST = 
			(AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(SET_COMPR,"#set_compr#")).add(set_comprehension_AST));
			currentAST.root = set_comprehension_AST;
			currentAST.child = set_comprehension_AST!=null &&set_comprehension_AST.getFirstChild()!=null ?
				set_comprehension_AST.getFirstChild() : set_comprehension_AST;
			currentAST.advanceChildToEnd();
		}
		set_comprehension_AST = (AST)currentAST.root;
		returnAST = set_comprehension_AST;
	}
	
	public final void dim_exprs(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST dim_exprs_AST = null;
		
		{
		int _cnt639=0;
		_loop639:
		do {
			if ((LA(1)==LBRACK) && (_tokenSet_35.member(LA(2)))) {
				AST tmp487_AST = null;
				tmp487_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp487_AST);
				match(LBRACK);
				expression(in_spec);
				astFactory.addASTChild(currentAST, returnAST);
				match(RBRACK);
			}
			else {
				if ( _cnt639>=1 ) { break _loop639; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt639++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			dim_exprs_AST = (AST)currentAST.root;
			dim_exprs_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(DIM_EXPRS,"#dim_exprs#")).add(dim_exprs_AST));
			currentAST.root = dim_exprs_AST;
			currentAST.child = dim_exprs_AST!=null &&dim_exprs_AST.getFirstChild()!=null ?
				dim_exprs_AST.getFirstChild() : dim_exprs_AST;
			currentAST.advanceChildToEnd();
		}
		dim_exprs_AST = (AST)currentAST.root;
		returnAST = dim_exprs_AST;
	}
	
	public final void quantified_var_declarator() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST quantified_var_declarator_AST = null;
		
		AST tmp489_AST = null;
		tmp489_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp489_AST);
		match(IDENT);
		{
		switch ( LA(1)) {
		case LBRACK:
		{
			dims();
			astFactory.addASTChild(currentAST, returnAST);
			break;
		}
		case SEMI:
		case COMMA:
		case BOR:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		quantified_var_declarator_AST = (AST)currentAST.root;
		returnAST = quantified_var_declarator_AST;
	}
	
	public final void set_comprehension_pred() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST set_comprehension_pred_AST = null;
		
		has_expression();
		astFactory.addASTChild(currentAST, returnAST);
		AST tmp490_AST = null;
		tmp490_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp490_AST);
		match(LAND);
		predicate();
		astFactory.addASTChild(currentAST, returnAST);
		if ( inputState.guessing==0 ) {
			set_comprehension_pred_AST = (AST)currentAST.root;
			set_comprehension_pred_AST.setType(LOGICAL_OP);
		}
		set_comprehension_pred_AST = (AST)currentAST.root;
		returnAST = set_comprehension_pred_AST;
	}
	
	public final void has_expression() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST has_expression_AST = null;
		
		primary_expr(no_side_effects);
		astFactory.addASTChild(currentAST, returnAST);
		{
		int _cnt648=0;
		_loop648:
		do {
			if ((LA(1)==DOT)) {
				AST tmp491_AST = null;
				tmp491_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp491_AST);
				match(DOT);
				AST tmp492_AST = null;
				tmp492_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp492_AST);
				match(IDENT);
			}
			else {
				if ( _cnt648>=1 ) { break _loop648; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt648++;
		} while (true);
		}
		AST tmp493_AST = null;
		tmp493_AST = astFactory.create(LT(1));
		astFactory.makeASTRoot(currentAST, tmp493_AST);
		match(LPAREN);
		{
		AST tmp494_AST = null;
		tmp494_AST = astFactory.create(LT(1));
		astFactory.addASTChild(currentAST, tmp494_AST);
		match(IDENT);
		}
		match(RPAREN);
		has_expression_AST = (AST)currentAST.root;
		returnAST = has_expression_AST;
	}
	
	public final void quantifier() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST quantifier_AST = null;
		
		{
		switch ( LA(1)) {
		case T_FORALL:
		{
			AST tmp496_AST = null;
			tmp496_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp496_AST);
			match(T_FORALL);
			break;
		}
		case T_EXISTS:
		{
			AST tmp497_AST = null;
			tmp497_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp497_AST);
			match(T_EXISTS);
			break;
		}
		case T_MAX:
		{
			AST tmp498_AST = null;
			tmp498_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp498_AST);
			match(T_MAX);
			break;
		}
		case T_MIN:
		{
			AST tmp499_AST = null;
			tmp499_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp499_AST);
			match(T_MIN);
			break;
		}
		case T_SUM:
		{
			AST tmp500_AST = null;
			tmp500_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp500_AST);
			match(T_SUM);
			break;
		}
		case T_PRODUCT:
		{
			AST tmp501_AST = null;
			tmp501_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp501_AST);
			match(T_PRODUCT);
			break;
		}
		case T_NUM_OF:
		{
			AST tmp502_AST = null;
			tmp502_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp502_AST);
			match(T_NUM_OF);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			quantifier_AST = (AST)currentAST.root;
			quantifier_AST.setType(QUANTIFIER_TOKEN);
			
		}
		quantifier_AST = (AST)currentAST.root;
		returnAST = quantifier_AST;
	}
	
	public final void wrap_quantified_var_decl() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST wrap_quantified_var_decl_AST = null;
		
		quantified_var_decl();
		astFactory.addASTChild(currentAST, returnAST);
		if ( inputState.guessing==0 ) {
			wrap_quantified_var_decl_AST = (AST)currentAST.root;
			wrap_quantified_var_decl_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(QUANT_VARS,"quantified_vars")).add(wrap_quantified_var_decl_AST));
			
			currentAST.root = wrap_quantified_var_decl_AST;
			currentAST.child = wrap_quantified_var_decl_AST!=null &&wrap_quantified_var_decl_AST.getFirstChild()!=null ?
				wrap_quantified_var_decl_AST.getFirstChild() : wrap_quantified_var_decl_AST;
			currentAST.advanceChildToEnd();
		}
		wrap_quantified_var_decl_AST = (AST)currentAST.root;
		returnAST = wrap_quantified_var_decl_AST;
	}
	
	public final void quantified_var_declarators() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST quantified_var_declarators_AST = null;
		
		quantified_var_declarator();
		astFactory.addASTChild(currentAST, returnAST);
		{
		_loop659:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp503_AST = null;
				tmp503_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp503_AST);
				match(COMMA);
				quantified_var_declarator();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				break _loop659;
			}
			
		} while (true);
		}
		quantified_var_declarators_AST = (AST)currentAST.root;
		returnAST = quantified_var_declarators_AST;
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
		"BADCHAR"
	};
	
	protected void buildTokenTypeASTClassMap() {
		tokenTypeToASTClassMap=null;
	};
	
	private static final long[] mk_tokenSet_0() {
		long[] data = { 0L, 22799473113563136L, 0L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_0 = new BitSet(mk_tokenSet_0());
	private static final long[] mk_tokenSet_1() {
		long[] data = { 2L, -270778927595651072L, 8556382335L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_1 = new BitSet(mk_tokenSet_1());
	private static final long[] mk_tokenSet_2() {
		long[] data = { 2L, -252764529086169088L, 8556382335L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_2 = new BitSet(mk_tokenSet_2());
	private static final long[] mk_tokenSet_3() {
		long[] data = { 0L, 23080948090273792L, 0L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_3 = new BitSet(mk_tokenSet_3());
	private static final long[] mk_tokenSet_4() {
		long[] data = { 2L, -271341877549072384L, 8556382335L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_4 = new BitSet(mk_tokenSet_4());
	private static final long[] mk_tokenSet_5() {
		long[] data = { 2L, -253327479039590400L, 8556382335L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_5 = new BitSet(mk_tokenSet_5());
	private static final long[] mk_tokenSet_6() {
		long[] data = { 0L, 25895697857380352L, 0L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_6 = new BitSet(mk_tokenSet_6());
	private static final long[] mk_tokenSet_7() {
		long[] data = { 0L, -273593677362757632L, 8556382335L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_7 = new BitSet(mk_tokenSet_7());
	private static final long[] mk_tokenSet_8() {
		long[] data = { 0L, -287104476244869120L, 8556380223L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_8 = new BitSet(mk_tokenSet_8());
	private static final long[] mk_tokenSet_9() {
		long[] data = new long[12];
		data[1]=-111464090777419776L;
		data[2]=1801290454772222591L;
		data[3]=4361803784168L;
		data[5]=4177920L;
		return data;
	}
	public static final BitSet _tokenSet_9 = new BitSet(mk_tokenSet_9());
	private static final long[] mk_tokenSet_10() {
		long[] data = new long[12];
		data[1]=-124974889659531264L;
		data[2]=1801008979795511423L;
		data[3]=4361803784168L;
		data[5]=4177920L;
		return data;
	}
	public static final BitSet _tokenSet_10 = new BitSet(mk_tokenSet_10());
	private static final long[] mk_tokenSet_11() {
		long[] data = new long[12];
		data[1]=-88946092640567296L;
		data[2]=-424548958664065L;
		data[3]=4362609623022L;
		data[4]=9164825241698959360L;
		data[5]=33554430L;
		return data;
	}
	public static final BitSet _tokenSet_11 = new BitSet(mk_tokenSet_11());
	private static final long[] mk_tokenSet_12() {
		long[] data = new long[12];
		data[1]=162129586585337856L;
		data[2]=562949953423424L;
		data[5]=4177920L;
		return data;
	}
	public static final BitSet _tokenSet_12 = new BitSet(mk_tokenSet_12());
	private static final long[] mk_tokenSet_13() {
		long[] data = { 0L, 54043195528445952L, -9223372036854710272L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_13 = new BitSet(mk_tokenSet_13());
	private static final long[] mk_tokenSet_14() {
		long[] data = new long[8];
		data[1]=18014398509481984L;
		data[2]=1800313951041355776L;
		data[3]=4361803784168L;
		return data;
	}
	public static final BitSet _tokenSet_14 = new BitSet(mk_tokenSet_14());
	private static final long[] mk_tokenSet_15() {
		long[] data = new long[12];
		data[1]=-124974889659531264L;
		data[2]=9219437717931229759L;
		data[3]=4362609623022L;
		data[4]=9164825241698959360L;
		data[5]=33554430L;
		return data;
	}
	public static final BitSet _tokenSet_15 = new BitSet(mk_tokenSet_15());
	private static final long[] mk_tokenSet_16() {
		long[] data = { 0L, 0L, 132070244352000L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_16 = new BitSet(mk_tokenSet_16());
	private static final long[] mk_tokenSet_17() {
		long[] data = new long[12];
		data[1]=-9046605751480483840L;
		data[2]=32094226873385541L;
		data[3]=9162565743424052736L;
		data[4]=9164825243838098432L;
		data[5]=33554430L;
		return data;
	}
	public static final BitSet _tokenSet_17 = new BitSet(mk_tokenSet_17());
	private static final long[] mk_tokenSet_18() {
		long[] data = new long[12];
		data[1]=162129586585337856L;
		data[2]=562949953421312L;
		data[5]=4177920L;
		return data;
	}
	public static final BitSet _tokenSet_18 = new BitSet(mk_tokenSet_18());
	private static final long[] mk_tokenSet_19() {
		long[] data = { 0L, 54043195528445952L, -9223372036854775808L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_19 = new BitSet(mk_tokenSet_19());
	private static final long[] mk_tokenSet_20() {
		long[] data = new long[12];
		data[1]=-124974889659531264L;
		data[2]=562958509801535L;
		data[5]=4177920L;
		return data;
	}
	public static final BitSet _tokenSet_20 = new BitSet(mk_tokenSet_20());
	private static final long[] mk_tokenSet_21() {
		long[] data = new long[12];
		data[1]=-88946092640567296L;
		data[2]=-9222809078344908737L;
		data[5]=4177920L;
		return data;
	}
	public static final BitSet _tokenSet_21 = new BitSet(mk_tokenSet_21());
	private static final long[] mk_tokenSet_22() {
		long[] data = new long[12];
		data[1]=18014398509481984L;
		data[2]=568997269537280L;
		data[4]=9164825241698959360L;
		data[5]=33554430L;
		return data;
	}
	public static final BitSet _tokenSet_22 = new BitSet(mk_tokenSet_22());
	private static final long[] mk_tokenSet_23() {
		long[] data = new long[12];
		data[1]=18014398509481984L;
		data[2]=1924145348608L;
		data[3]=805314560L;
		data[5]=8192L;
		return data;
	}
	public static final BitSet _tokenSet_23 = new BitSet(mk_tokenSet_23());
	private static final long[] mk_tokenSet_24() {
		long[] data = new long[12];
		data[1]=18014398509481984L;
		data[2]=568997269536768L;
		data[3]=8192L;
		data[4]=9164825241698959360L;
		data[5]=33554430L;
		return data;
	}
	public static final BitSet _tokenSet_24 = new BitSet(mk_tokenSet_24());
	private static final long[] mk_tokenSet_25() {
		long[] data = new long[8];
		data[3]=1031056392200L;
		return data;
	}
	public static final BitSet _tokenSet_25 = new BitSet(mk_tokenSet_25());
	private static final long[] mk_tokenSet_26() {
		long[] data = new long[12];
		data[1]=18014398509481984L;
		data[2]=1924145414144L;
		data[3]=1031861960648L;
		data[5]=8192L;
		return data;
	}
	public static final BitSet _tokenSet_26 = new BitSet(mk_tokenSet_26());
	private static final long[] mk_tokenSet_27() {
		long[] data = new long[12];
		data[0]=2L;
		data[1]=-111464090777419776L;
		data[2]=1798631182823442047L;
		data[3]=9169325540911619600L;
		data[4]=9164825243838098432L;
		data[5]=33554430L;
		return data;
	}
	public static final BitSet _tokenSet_27 = new BitSet(mk_tokenSet_27());
	private static final long[] mk_tokenSet_28() {
		long[] data = new long[12];
		data[0]=2L;
		data[1]=-3377699720527872L;
		data[2]=-143073981378945L;
		data[3]=-1073741826L;
		data[4]=-262145L;
		data[5]=4294967295L;
		return data;
	}
	public static final BitSet _tokenSet_28 = new BitSet(mk_tokenSet_28());
	private static final long[] mk_tokenSet_29() {
		long[] data = new long[8];
		data[3]=32476495880L;
		return data;
	}
	public static final BitSet _tokenSet_29 = new BitSet(mk_tokenSet_29());
	private static final long[] mk_tokenSet_30() {
		long[] data = new long[12];
		data[1]=18014398509481984L;
		data[2]=569272147443712L;
		data[3]=33282064328L;
		data[4]=9164825241698959360L;
		data[5]=33554430L;
		return data;
	}
	public static final BitSet _tokenSet_30 = new BitSet(mk_tokenSet_30());
	private static final long[] mk_tokenSet_31() {
		long[] data = new long[12];
		data[1]=-9046605751480483840L;
		data[2]=32094226873386565L;
		data[3]=9169325540911619584L;
		data[4]=9164825243838098432L;
		data[5]=33554430L;
		return data;
	}
	public static final BitSet _tokenSet_31 = new BitSet(mk_tokenSet_31());
	private static final long[] mk_tokenSet_32() {
		long[] data = new long[12];
		data[0]=2L;
		data[1]=-3377699720527872L;
		data[2]=-7422075259887956353L;
		data[3]=-1073741848L;
		data[4]=-262145L;
		data[5]=4294967295L;
		return data;
	}
	public static final BitSet _tokenSet_32 = new BitSet(mk_tokenSet_32());
	private static final long[] mk_tokenSet_33() {
		long[] data = new long[12];
		data[1]=-9060116550362595328L;
		data[2]=562956395872256L;
		data[5]=4177920L;
		return data;
	}
	public static final BitSet _tokenSet_33 = new BitSet(mk_tokenSet_33());
	private static final long[] mk_tokenSet_34() {
		long[] data = new long[12];
		data[1]=-9024087753343631360L;
		data[2]=-9222809080458903552L;
		data[5]=4177920L;
		return data;
	}
	public static final BitSet _tokenSet_34 = new BitSet(mk_tokenSet_34());
	private static final long[] mk_tokenSet_35() {
		long[] data = new long[12];
		data[1]=18014398509481984L;
		data[2]=568997269536768L;
		data[4]=9164825241698959360L;
		data[5]=33554430L;
		return data;
	}
	public static final BitSet _tokenSet_35 = new BitSet(mk_tokenSet_35());
	private static final long[] mk_tokenSet_36() {
		long[] data = new long[12];
		data[1]=135107988821114880L;
		data[2]=-9222803039584714752L;
		data[3]=-9223372036854775808L;
		data[4]=-2147482625L;
		data[5]=4294967295L;
		return data;
	}
	public static final BitSet _tokenSet_36 = new BitSet(mk_tokenSet_36());
	private static final long[] mk_tokenSet_37() {
		long[] data = new long[12];
		data[1]=135107988821114880L;
		data[2]=-9222803039584706560L;
		data[3]=-9223372036854775808L;
		data[4]=-2147482625L;
		data[5]=4294967295L;
		return data;
	}
	public static final BitSet _tokenSet_37 = new BitSet(mk_tokenSet_37());
	private static final long[] mk_tokenSet_38() {
		long[] data = { 0L, -9222246136947933184L, 6442450944L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_38 = new BitSet(mk_tokenSet_38());
	private static final long[] mk_tokenSet_39() {
		long[] data = new long[12];
		data[1]=18014398509481984L;
		data[2]=568997269536768L;
		data[3]=524288L;
		data[4]=9164825241698959360L;
		data[5]=33554430L;
		return data;
	}
	public static final BitSet _tokenSet_39 = new BitSet(mk_tokenSet_39());
	private static final long[] mk_tokenSet_40() {
		long[] data = new long[10];
		data[3]=4361803530248L;
		data[4]=8060928L;
		return data;
	}
	public static final BitSet _tokenSet_40 = new BitSet(mk_tokenSet_40());
	private static final long[] mk_tokenSet_41() {
		long[] data = new long[12];
		data[1]=27021597764222976L;
		data[2]=569272147443712L;
		data[3]=4362609098696L;
		data[4]=9164825241707282432L;
		data[5]=33554430L;
		return data;
	}
	public static final BitSet _tokenSet_41 = new BitSet(mk_tokenSet_41());
	private static final long[] mk_tokenSet_42() {
		long[] data = new long[12];
		data[1]=-9046605751480483840L;
		data[2]=33220126780229189L;
		data[3]=9169325540911619600L;
		data[4]=9164825243838098432L;
		data[5]=33554430L;
		return data;
	}
	public static final BitSet _tokenSet_42 = new BitSet(mk_tokenSet_42());
	private static final long[] mk_tokenSet_43() {
		long[] data = new long[12];
		data[0]=2L;
		data[1]=-3377699720527872L;
		data[2]=-7422075259887956353L;
		data[3]=-1073741832L;
		data[4]=-262145L;
		data[5]=4294967295L;
		return data;
	}
	public static final BitSet _tokenSet_43 = new BitSet(mk_tokenSet_43());
	private static final long[] mk_tokenSet_44() {
		long[] data = new long[10];
		data[3]=3298799124488L;
		data[4]=8060928L;
		return data;
	}
	public static final BitSet _tokenSet_44 = new BitSet(mk_tokenSet_44());
	private static final long[] mk_tokenSet_45() {
		long[] data = new long[12];
		data[1]=27021597764222976L;
		data[2]=569272147443712L;
		data[3]=3299604692936L;
		data[4]=9164825241707282432L;
		data[5]=33554430L;
		return data;
	}
	public static final BitSet _tokenSet_45 = new BitSet(mk_tokenSet_45());
	private static final long[] mk_tokenSet_46() {
		long[] data = new long[10];
		data[1]=72057594037927936L;
		data[4]=54043195528445952L;
		return data;
	}
	public static final BitSet _tokenSet_46 = new BitSet(mk_tokenSet_46());
	private static final long[] mk_tokenSet_47() {
		long[] data = new long[12];
		data[2]=562949953421312L;
		data[5]=4177920L;
		return data;
	}
	public static final BitSet _tokenSet_47 = new BitSet(mk_tokenSet_47());
	private static final long[] mk_tokenSet_48() {
		long[] data = new long[12];
		data[1]=18014398509481984L;
		data[2]=568997269536768L;
		data[4]=8070450532247928832L;
		data[5]=33554430L;
		return data;
	}
	public static final BitSet _tokenSet_48 = new BitSet(mk_tokenSet_48());
	private static final long[] mk_tokenSet_49() {
		long[] data = new long[12];
		data[0]=2L;
		data[1]=135107988821114880L;
		data[2]=-9222802902116260864L;
		data[3]=-9223372035780247551L;
		data[4]=-2147482625L;
		data[5]=4294967295L;
		return data;
	}
	public static final BitSet _tokenSet_49 = new BitSet(mk_tokenSet_49());
	
	}
