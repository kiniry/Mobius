// $ANTLR 2.7.1: "expandedjmldeclparser.g" -> "JmlDeclParser.java"$

// @(#)$Id: jmldeclparser.g,v 1.11 2001/08/02 18:36:23 leavens Exp $


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

// JML Parser grammar.
//
// AUTHORS: Clyde Ruby, Gary T. Leavens, Anand Ganapathy, and Arun Raghavan,
//          with help from Albert Baker


package jml;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.util.Vector;

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
//LB import edu.iastate.cs.jml.checker.attributes.*;

public class JmlDeclParser extends antlr.LLkParser
       implements JmlDeclParserTokenTypes
 {

  // an initializer, to set the tree type
  {
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

protected JmlDeclParser(TokenBuffer tokenBuf, int k) {
  super(tokenBuf,k);
  tokenNames = _tokenNames;
}

public JmlDeclParser(TokenBuffer tokenBuf) {
  this(tokenBuf,2);
}

protected JmlDeclParser(TokenStream lexer, int k) {
  super(lexer,k);
  tokenNames = _tokenNames;
}

public JmlDeclParser(TokenStream lexer) {
  this(lexer,2);
}

public JmlDeclParser(ParserSharedInputState state) {
  super(state,2);
  tokenNames = _tokenNames;
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				class_or_interface_def();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				type_definition_AST = (AST)currentAST.root;
				break;
			}
			case SEMI:
			{
				AST tmp1_AST = null;
				if (inputState.guessing==0) {
					tmp1_AST = (AST)astFactory.create(LT(1));
				}
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
	
	public final void doc_comment() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST doc_comment_AST = null;
		Token  d = null;
		AST d_AST = null;
		
		d = LT(1);
		if (inputState.guessing==0) {
			d_AST = (AST)astFactory.create(d);
			astFactory.addASTChild(currentAST, d_AST);
		}
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
			doc_comment_AST = (AST)astFactory.make( (new ASTArray(1)).add((AST)astFactory.create(DOC_COMMENT_START,"doc_comment_start")));
			} else {
			doc_comment_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(DOC_COMMENT_START,"doc_comment_start")).add(dp.getAST()));
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
		_loop60:
		do {
			if ((_tokenSet_0.member(LA(1)))) {
				modifier();
				if (inputState.guessing==0) {
					mod_AST = (AST)returnAST;
				}
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
				break _loop60;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			modifiers_AST = (AST)currentAST.root;
			
			ms = Typing.defaultPrivacyModifiers(ms);
			String mod_set_string = "modifier_set (" + ms + ")";
			modifiers_AST = (AST)astFactory.create(MODIFIER_SET,mod_set_string);
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			class_or_interface_def_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_interface:
		{
			interface_definition();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
	
	public final void field(
		boolean in_spec, boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST field_AST = null;
		AST dc_AST = null;
		AST mods_AST = null;
		AST m_AST = null;
		AST msfd_AST = null;
		
		ModifierSet ms = null;
		
		
		try {      // for error handling
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
				{
				{
				_loop6:
				do {
					if ((LA(1)==DOC_COMMENT)) {
						doc_comment();
					}
					else {
						break _loop6;
					}
					
				} while (true);
				}
				}
				{
				if ((LA(1)==LITERAL_static) && (LA(2)==LCURLY)) {
					AST tmp2_AST = null;
					if (inputState.guessing==0) {
						tmp2_AST = (AST)astFactory.create(LT(1));
					}
					match(LITERAL_static);
					compound_statement(in_model_prog);
				}
				else if ((LA(1)==LCURLY)) {
					compound_statement(in_model_prog);
				}
				else if ((_tokenSet_1.member(LA(1))) && (_tokenSet_2.member(LA(2)))) {
					modifiers();
					if (inputState.guessing==0) {
						mods_AST = (AST)returnAST;
					}
					if ( inputState.guessing==0 ) {
						
						if (mods_AST instanceof LineAST) {
						ms = ((MTypeAttrib)((LineAST)mods_AST).type).getModifiers();
						in_spec = in_spec || ms.has(Modifier.MODEL)
						|| ms.has(Modifier.GHOST);
						}
						
					}
					{
					if ((_tokenSet_3.member(LA(1))) && (_tokenSet_4.member(LA(2)))) {
						member_decl(in_spec, in_model_prog);
						if (inputState.guessing==0) {
							m_AST = (AST)returnAST;
						}
						if ( inputState.guessing==0 ) {
							field_AST = (AST)currentAST.root;
							field_AST = (AST)astFactory.make( (new ASTArray(3)).add(null).add(mods_AST).add(m_AST));
							currentAST.root = field_AST;
							currentAST.child = field_AST!=null &&field_AST.getFirstChild()!=null ?
								field_AST.getFirstChild() : field_AST;
							currentAST.advanceChildToEnd();
						}
					}
					else if ((_tokenSet_5.member(LA(1))) && (_tokenSet_6.member(LA(2)))) {
						method_spec_first_decl(mods_AST, in_model_prog);
						if (inputState.guessing==0) {
							msfd_AST = (AST)returnAST;
						}
						if ( inputState.guessing==0 ) {
							field_AST = (AST)currentAST.root;
							
							if( msfd_AST != null ) {
							field_AST = msfd_AST;
							}
							
							currentAST.root = field_AST;
							currentAST.child = field_AST!=null &&field_AST.getFirstChild()!=null ?
								field_AST.getFirstChild() : field_AST;
							currentAST.advanceChildToEnd();
						}
					}
					else if ((_tokenSet_7.member(LA(1)))) {
						jml_declaration();
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
				break;
			}
			case SEMI:
			{
				AST tmp3_AST = null;
				if (inputState.guessing==0) {
					tmp3_AST = (AST)astFactory.create(LT(1));
				}
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
	
	public final void compound_statement(
		boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST compound_statement_AST = null;
		
		AST tmp4_AST = null;
		if (inputState.guessing==0) {
			tmp4_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp4_AST);
		}
		match(LCURLY);
		{
		_loop415:
		do {
			if ((_tokenSet_8.member(LA(1)))) {
				statement(in_model_prog);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop415;
			}
			
		} while (true);
		}
		AST tmp5_AST = null;
		if (inputState.guessing==0) {
			tmp5_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp5_AST);
		}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			member_decl_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_interface:
		{
			interface_definition();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			member_decl_AST = (AST)currentAST.root;
			break;
		}
		default:
			boolean synPredMatched84 = false;
			if (((_tokenSet_9.member(LA(1))) && (_tokenSet_10.member(LA(2))))) {
				int _m84 = mark();
				synPredMatched84 = true;
				inputState.guessing++;
				try {
					{
					variable_decls(in_spec);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched84 = false;
				}
				rewind(_m84);
				inputState.guessing--;
			}
			if ( synPredMatched84 ) {
				variable_decls(in_spec);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				AST tmp6_AST = null;
				tmp6_AST = (AST)astFactory.create(LT(1));
				match(SEMI);
				member_decl_AST = (AST)currentAST.root;
			}
			else if ((_tokenSet_9.member(LA(1))) && (_tokenSet_4.member(LA(2)))) {
				method_decl(in_model_prog);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
		AST mspec_AST = null;
		AST mods_AST = null;
		AST ts_AST = null;
		AST mh_AST = null;
		AST mb_AST = null;
		AST cmh_AST = null;
		AST cmb_AST = null;
		
		method_specification(m);
		if (inputState.guessing==0) {
			mspec_AST = (AST)returnAST;
		}
		{
		switch ( LA(1)) {
		case STATIC_INITIALIZER:
		{
			AST tmp7_AST = null;
			if (inputState.guessing==0) {
				tmp7_AST = (AST)astFactory.create(LT(1));
			}
			match(STATIC_INITIALIZER);
			break;
		}
		case INITIALIZER:
		{
			AST tmp8_AST = null;
			if (inputState.guessing==0) {
				tmp8_AST = (AST)astFactory.create(LT(1));
			}
			match(INITIALIZER);
			break;
		}
		case LCURLY:
		{
			compound_statement(in_model_prog);
			break;
		}
		default:
			if ((LA(1)==LITERAL_static) && (LA(2)==LCURLY)) {
				AST tmp9_AST = null;
				if (inputState.guessing==0) {
					tmp9_AST = (AST)astFactory.create(LT(1));
				}
				match(LITERAL_static);
				compound_statement(in_model_prog);
			}
			else if ((_tokenSet_11.member(LA(1))) && (_tokenSet_12.member(LA(2)))) {
				modifiers();
				if (inputState.guessing==0) {
					mods_AST = (AST)returnAST;
				}
				{
				if ((_tokenSet_9.member(LA(1))) && (_tokenSet_10.member(LA(2)))) {
					type_spec();
					if (inputState.guessing==0) {
						ts_AST = (AST)returnAST;
					}
					method_head();
					if (inputState.guessing==0) {
						mh_AST = (AST)returnAST;
					}
					method_body(in_model_prog);
					if (inputState.guessing==0) {
						mb_AST = (AST)returnAST;
					}
					if ( inputState.guessing==0 ) {
						method_spec_first_decl_AST = (AST)currentAST.root;
						
						if( mods_AST != null )
						{
						method_spec_first_decl_AST = mods_AST;
						method_spec_first_decl_AST.setNextSibling(
						(AST)astFactory.make( (new ASTArray(4)).add((AST)astFactory.create(METH,"#meth#")).add(ts_AST).add(mh_AST).add((AST)astFactory.create(SEMI,";"))) );
						}  else {
						method_spec_first_decl_AST = 
						(AST)astFactory.make( (new ASTArray(4)).add((AST)astFactory.create(METH,"#meth#")).add(ts_AST).add(mh_AST).add((AST)astFactory.create(SEMI,";")));
						}
						
						currentAST.root = method_spec_first_decl_AST;
						currentAST.child = method_spec_first_decl_AST!=null &&method_spec_first_decl_AST.getFirstChild()!=null ?
							method_spec_first_decl_AST.getFirstChild() : method_spec_first_decl_AST;
						currentAST.advanceChildToEnd();
					}
				}
				else if ((LA(1)==IDENT) && (LA(2)==LPAREN)) {
					method_head();
					if (inputState.guessing==0) {
						cmh_AST = (AST)returnAST;
					}
					method_body(in_model_prog);
					if (inputState.guessing==0) {
						cmb_AST = (AST)returnAST;
					}
					if ( inputState.guessing==0 ) {
						method_spec_first_decl_AST = (AST)currentAST.root;
						
						if( mods_AST != null )
						{
						method_spec_first_decl_AST = mods_AST;
						method_spec_first_decl_AST.setNextSibling(
						(AST)astFactory.make( (new ASTArray(3)).add((AST)astFactory.create(CONSTRUCTOR,"#constr#")).add(cmh_AST).add((AST)astFactory.create(SEMI,";"))) );
						} else {
						method_spec_first_decl_AST =
						(AST)astFactory.make( (new ASTArray(3)).add((AST)astFactory.create(CONSTRUCTOR,"#constr#")).add(cmh_AST).add((AST)astFactory.create(SEMI,";")));
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			jml_declaration_AST = (AST)currentAST.root;
			break;
		}
		case CONSTRAINT:
		case CONSTRAINT_REDUNDANTLY:
		{
			history_constraint();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			jml_declaration_AST = (AST)currentAST.root;
			break;
		}
		case DEPENDS:
		case DEPENDS_REDUNDANTLY:
		{
			depends_decl();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			jml_declaration_AST = (AST)currentAST.root;
			break;
		}
		case REPRESENTS:
		case REPRESENTS_REDUNDANTLY:
		{
			represents_decl();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		
		AST tmp10_AST = null;
		if (inputState.guessing==0) {
			tmp10_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp10_AST);
		}
		match(AXIOM);
		predicate();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp11_AST = null;
		tmp11_AST = (AST)astFactory.create(LT(1));
		match(SEMI);
		axiom_pragma_AST = (AST)currentAST.root;
		returnAST = axiom_pragma_AST;
	}
	
	public final void method_specification(
		AST mods
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST method_specification_AST = null;
		
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			method_specification_AST = (AST)currentAST.root;
			break;
		}
		case ALSO:
		case AND:
		{
			extending_specification();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			break;
		}
		case T_TYPEOFALLTYPES:
		{
			AST tmp12_AST = null;
			if (inputState.guessing==0) {
				tmp12_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp12_AST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
	
	public final void method_head() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST method_head_AST = null;
		
		AST tmp13_AST = null;
		if (inputState.guessing==0) {
			tmp13_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp13_AST);
		}
		match(IDENT);
		AST tmp14_AST = null;
		tmp14_AST = (AST)astFactory.create(LT(1));
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
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
		AST tmp15_AST = null;
		tmp15_AST = (AST)astFactory.create(LT(1));
		match(RPAREN);
		{
		switch ( LA(1)) {
		case LBRACK:
		{
			dims();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			method_body_AST = (AST)currentAST.root;
			break;
		}
		case SEMI:
		{
			AST tmp16_AST = null;
			if (inputState.guessing==0) {
				tmp16_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp16_AST);
			}
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
	
	public final void method_decl(
		boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST method_decl_AST = null;
		AST t_AST = null;
		AST mh_AST = null;
		AST mods_AST = null;
		AST ch_AST = null;
		AST mds_AST = null;
		
		if ((_tokenSet_9.member(LA(1))) && (_tokenSet_10.member(LA(2)))) {
			type_spec();
			if (inputState.guessing==0) {
				t_AST = (AST)returnAST;
			}
			method_head();
			if (inputState.guessing==0) {
				mh_AST = (AST)returnAST;
			}
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
				if (inputState.guessing==0) {
					mods_AST = (AST)returnAST;
				}
				method_specification(mods_AST);
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
			if ( inputState.guessing==0 ) {
				method_decl_AST = (AST)currentAST.root;
				method_decl_AST = (AST)astFactory.make( (new ASTArray(4)).add((AST)astFactory.create(METH,"#meth#")).add(t_AST).add(mh_AST).add((AST)astFactory.create(SEMI,";")));
				currentAST.root = method_decl_AST;
				currentAST.child = method_decl_AST!=null &&method_decl_AST.getFirstChild()!=null ?
					method_decl_AST.getFirstChild() : method_decl_AST;
				currentAST.advanceChildToEnd();
			}
		}
		else if ((LA(1)==IDENT) && (LA(2)==LPAREN)) {
			method_head();
			if (inputState.guessing==0) {
				ch_AST = (AST)returnAST;
			}
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
				if (inputState.guessing==0) {
					mds_AST = (AST)returnAST;
				}
				method_specification(mds_AST);
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
			if ( inputState.guessing==0 ) {
				method_decl_AST = (AST)currentAST.root;
				method_decl_AST = (AST)astFactory.make( (new ASTArray(3)).add((AST)astFactory.create(CONSTRUCTOR,"#constr#")).add(ch_AST).add((AST)astFactory.create(SEMI,";")));
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
	
	public final void variable_declarator(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST variable_declarator_AST = null;
		
		AST tmp17_AST = null;
		if (inputState.guessing==0) {
			tmp17_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp17_AST);
		}
		match(IDENT);
		{
		switch ( LA(1)) {
		case LBRACK:
		{
			dims();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			AST tmp18_AST = null;
			tmp18_AST = (AST)astFactory.create(LT(1));
			match(ASSIGN);
			initializer(in_spec);
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
	
	public final void dims() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST dims_AST = null;
		
		{
		int _cnt644=0;
		_loop644:
		do {
			if ((LA(1)==LBRACK) && (LA(2)==RBRACK)) {
				AST tmp19_AST = null;
				if (inputState.guessing==0) {
					tmp19_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp19_AST);
				}
				match(LBRACK);
				AST tmp20_AST = null;
				tmp20_AST = (AST)astFactory.create(LT(1));
				match(RBRACK);
			}
			else {
				if ( _cnt644>=1 ) { break _loop644; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt644++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			dims_AST = (AST)currentAST.root;
			dims_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(DIMS,"#dims#")).add(dims_AST));
			currentAST.root = dims_AST;
			currentAST.child = dims_AST!=null &&dims_AST.getFirstChild()!=null ?
				dims_AST.getFirstChild() : dims_AST;
			currentAST.advanceChildToEnd();
		}
		dims_AST = (AST)currentAST.root;
		returnAST = dims_AST;
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			initializer_AST = (AST)currentAST.root;
			break;
		}
		case LCURLY:
		{
			array_initializer(in_spec);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
	
	public final void variable_decls(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST variable_decls_AST = null;
		
		type_spec();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		variable_declarators(in_spec);
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		switch ( LA(1)) {
		case INITIALLY:
		case READABLE_IF:
		case MONITORED_BY:
		{
			jml_var_assertion();
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
			variable_decls_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(VAR_DECL,"#vardecl#")).add(variable_decls_AST));
			currentAST.root = variable_decls_AST;
			currentAST.child = variable_decls_AST!=null &&variable_decls_AST.getFirstChild()!=null ?
				variable_decls_AST.getFirstChild() : variable_decls_AST;
			currentAST.advanceChildToEnd();
		}
		variable_decls_AST = (AST)currentAST.root;
		returnAST = variable_decls_AST;
	}
	
	public final void variable_declarators(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST variable_declarators_AST = null;
		
		variable_declarator(in_spec);
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop102:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp21_AST = null;
				if (inputState.guessing==0) {
					tmp21_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp21_AST);
				}
				match(COMMA);
				variable_declarator(in_spec);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop102;
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
				AST tmp22_AST = null;
				if (inputState.guessing==0) {
					tmp22_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp22_AST);
				}
				match(INITIALLY);
				break;
			}
			case READABLE_IF:
			{
				AST tmp23_AST = null;
				if (inputState.guessing==0) {
					tmp23_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp23_AST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			jml_var_assertion_AST = (AST)currentAST.root;
			break;
		}
		case MONITORED_BY:
		{
			monitored_by_clause();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
	
	public final void compilation_unit() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST compilation_unit_AST = null;
		
		try {      // for error handling
			{
			if ((LA(1)==LITERAL_package||LA(1)==DOC_COMMENT) && (_tokenSet_13.member(LA(2)))) {
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else if ((_tokenSet_14.member(LA(1))) && (_tokenSet_15.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			{
			if ((LA(1)==REFINE||LA(1)==DOC_COMMENT) && (_tokenSet_16.member(LA(2)))) {
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else if ((_tokenSet_17.member(LA(1))) && (_tokenSet_18.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			{
			_loop34:
			do {
				if (((LA(1) >= MODEL && LA(1) <= DOC_COMMENT)) && (_tokenSet_19.member(LA(2)))) {
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
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					break _loop34;
				}
				
			} while (true);
			}
			{
			_loop36:
			do {
				if ((_tokenSet_20.member(LA(1)))) {
					type_definition();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					break _loop36;
				}
				
			} while (true);
			}
			AST tmp24_AST = null;
			if (inputState.guessing==0) {
				tmp24_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp24_AST);
			}
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
		int _cnt41=0;
		_loop41:
		do {
			if ((LA(1)==DOC_COMMENT)) {
				d = LT(1);
				if (inputState.guessing==0) {
					d_AST = (AST)astFactory.create(d);
					astFactory.addASTChild(currentAST, d_AST);
				}
				match(DOC_COMMENT);
				if ( inputState.guessing==0 ) {
					line = ((LineAST)d_AST).line;
					col = ((LineAST)d_AST).column;
					
				}
			}
			else {
				if ( _cnt41>=1 ) { break _loop41; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt41++;
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
			AST tmp25_AST = null;
			if (inputState.guessing==0) {
				tmp25_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp25_AST);
			}
			match(LITERAL_package);
			name();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp26_AST = null;
			tmp26_AST = (AST)astFactory.create(LT(1));
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
			AST tmp27_AST = null;
			if (inputState.guessing==0) {
				tmp27_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp27_AST);
			}
			match(REFINE);
			ident_list();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp28_AST = null;
			if (inputState.guessing==0) {
				tmp28_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp28_AST);
			}
			match(L_ARROW);
			AST tmp29_AST = null;
			if (inputState.guessing==0) {
				tmp29_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp29_AST);
			}
			match(STRING_LITERAL);
			AST tmp30_AST = null;
			tmp30_AST = (AST)astFactory.create(LT(1));
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
				AST tmp31_AST = null;
				if (inputState.guessing==0) {
					tmp31_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp31_AST);
				}
				match(LITERAL_import);
				name_star();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				AST tmp32_AST = null;
				tmp32_AST = (AST)astFactory.create(LT(1));
				match(SEMI);
				import_definition_AST = (AST)currentAST.root;
				break;
			}
			case MODEL:
			{
				AST tmp33_AST = null;
				if (inputState.guessing==0) {
					tmp33_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp33_AST);
				}
				match(MODEL);
				AST tmp34_AST = null;
				if (inputState.guessing==0) {
					tmp34_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp34_AST);
				}
				match(LITERAL_import);
				name_star();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				AST tmp35_AST = null;
				tmp35_AST = (AST)astFactory.create(LT(1));
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
	
	public final void start_predicate() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST start_predicate_AST = null;
		
		predicate();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		start_predicate_AST = (AST)currentAST.root;
		returnAST = start_predicate_AST;
	}
	
	public final void predicate() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST predicate_AST = null;
		
		spec_expression();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		predicate_AST = (AST)currentAST.root;
		returnAST = predicate_AST;
	}
	
	public final void start_signals() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST start_signals_AST = null;
		
		signals_clause();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
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
				AST tmp36_AST = null;
				if (inputState.guessing==0) {
					tmp36_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp36_AST);
				}
				match(SIGNALS);
				break;
			}
			case SIGNALS_REDUNDANTLY:
			{
				AST tmp37_AST = null;
				if (inputState.guessing==0) {
					tmp37_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp37_AST);
				}
				match(SIGNALS_REDUNDANTLY);
				break;
			}
			case EXSURES:
			{
				AST tmp38_AST = null;
				if (inputState.guessing==0) {
					tmp38_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp38_AST);
				}
				match(EXSURES);
				break;
			}
			case EXSURES_REDUNDANTLY:
			{
				AST tmp39_AST = null;
				if (inputState.guessing==0) {
					tmp39_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp39_AST);
				}
				match(EXSURES_REDUNDANTLY);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			AST tmp40_AST = null;
			if (inputState.guessing==0) {
				tmp40_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp40_AST);
			}
			match(LPAREN);
			reference_type();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			switch ( LA(1)) {
			case IDENT:
			{
				AST tmp41_AST = null;
				if (inputState.guessing==0) {
					tmp41_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp41_AST);
				}
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
			AST tmp42_AST = null;
			if (inputState.guessing==0) {
				tmp42_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp42_AST);
			}
			match(RPAREN);
			{
			switch ( LA(1)) {
			case T_NOT_SPECIFIED:
			{
				AST tmp43_AST = null;
				if (inputState.guessing==0) {
					tmp43_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp43_AST);
				}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			AST tmp44_AST = null;
			tmp44_AST = (AST)astFactory.create(LT(1));
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
		
		AST tmp45_AST = null;
		if (inputState.guessing==0) {
			tmp45_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp45_AST);
		}
		match(IDENT);
		{
		_loop46:
		do {
			if ((LA(1)==DOT)) {
				AST tmp46_AST = null;
				if (inputState.guessing==0) {
					tmp46_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp46_AST);
				}
				match(DOT);
				AST tmp47_AST = null;
				if (inputState.guessing==0) {
					tmp47_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp47_AST);
				}
				match(IDENT);
			}
			else {
				break _loop46;
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
		
		AST tmp48_AST = null;
		if (inputState.guessing==0) {
			tmp48_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp48_AST);
		}
		match(IDENT);
		{
		_loop49:
		do {
			if ((LA(1)==DOT) && (LA(2)==IDENT)) {
				AST tmp49_AST = null;
				if (inputState.guessing==0) {
					tmp49_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp49_AST);
				}
				match(DOT);
				AST tmp50_AST = null;
				if (inputState.guessing==0) {
					tmp50_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp50_AST);
				}
				match(IDENT);
			}
			else {
				break _loop49;
			}
			
		} while (true);
		}
		{
		switch ( LA(1)) {
		case DOT:
		{
			AST tmp51_AST = null;
			if (inputState.guessing==0) {
				tmp51_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp51_AST);
			}
			match(DOT);
			AST tmp52_AST = null;
			if (inputState.guessing==0) {
				tmp52_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp52_AST);
			}
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
	
	public final void class_definition(
		boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST class_definition_AST = null;
		
		AST tmp53_AST = null;
		if (inputState.guessing==0) {
			tmp53_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp53_AST);
		}
		match(LITERAL_class);
		AST tmp54_AST = null;
		if (inputState.guessing==0) {
			tmp54_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp54_AST);
		}
		match(IDENT);
		{
		switch ( LA(1)) {
		case LITERAL_extends:
		{
			AST tmp55_AST = null;
			if (inputState.guessing==0) {
				tmp55_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp55_AST);
			}
			match(LITERAL_extends);
			name();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			switch ( LA(1)) {
			case WEAKLY:
			{
				AST tmp56_AST = null;
				if (inputState.guessing==0) {
					tmp56_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp56_AST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		class_definition_AST = (AST)currentAST.root;
		returnAST = class_definition_AST;
	}
	
	public final void interface_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST interface_definition_AST = null;
		
		AST tmp57_AST = null;
		if (inputState.guessing==0) {
			tmp57_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp57_AST);
		}
		match(LITERAL_interface);
		AST tmp58_AST = null;
		if (inputState.guessing==0) {
			tmp58_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp58_AST);
		}
		match(IDENT);
		{
		switch ( LA(1)) {
		case LITERAL_extends:
		{
			interface_extends();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		interface_definition_AST = (AST)currentAST.root;
		returnAST = interface_definition_AST;
	}
	
	public final void type() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST type_AST = null;
		
		switch ( LA(1)) {
		case IDENT:
		{
			reference_type();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
	
	public final void reference_type() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST reference_type_AST = null;
		
		name();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
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
			AST tmp59_AST = null;
			if (inputState.guessing==0) {
				tmp59_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp59_AST);
			}
			match(LITERAL_void);
			break;
		}
		case LITERAL_boolean:
		{
			AST tmp60_AST = null;
			if (inputState.guessing==0) {
				tmp60_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp60_AST);
			}
			match(LITERAL_boolean);
			break;
		}
		case LITERAL_byte:
		{
			AST tmp61_AST = null;
			if (inputState.guessing==0) {
				tmp61_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp61_AST);
			}
			match(LITERAL_byte);
			break;
		}
		case LITERAL_char:
		{
			AST tmp62_AST = null;
			if (inputState.guessing==0) {
				tmp62_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp62_AST);
			}
			match(LITERAL_char);
			break;
		}
		case LITERAL_short:
		{
			AST tmp63_AST = null;
			if (inputState.guessing==0) {
				tmp63_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp63_AST);
			}
			match(LITERAL_short);
			break;
		}
		case LITERAL_int:
		{
			AST tmp64_AST = null;
			if (inputState.guessing==0) {
				tmp64_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp64_AST);
			}
			match(LITERAL_int);
			break;
		}
		case LITERAL_long:
		{
			AST tmp65_AST = null;
			if (inputState.guessing==0) {
				tmp65_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp65_AST);
			}
			match(LITERAL_long);
			break;
		}
		case LITERAL_float:
		{
			AST tmp66_AST = null;
			if (inputState.guessing==0) {
				tmp66_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp66_AST);
			}
			match(LITERAL_float);
			break;
		}
		case LITERAL_double:
		{
			AST tmp67_AST = null;
			if (inputState.guessing==0) {
				tmp67_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp67_AST);
			}
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
				AST tmp68_AST = null;
				if (inputState.guessing==0) {
					tmp68_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp68_AST);
				}
				match(LITERAL_private);
				break;
			}
			case LITERAL_public:
			{
				AST tmp69_AST = null;
				if (inputState.guessing==0) {
					tmp69_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp69_AST);
				}
				match(LITERAL_public);
				break;
			}
			case LITERAL_protected:
			{
				AST tmp70_AST = null;
				if (inputState.guessing==0) {
					tmp70_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp70_AST);
				}
				match(LITERAL_protected);
				break;
			}
			case LITERAL_static:
			{
				AST tmp71_AST = null;
				if (inputState.guessing==0) {
					tmp71_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp71_AST);
				}
				match(LITERAL_static);
				break;
			}
			case LITERAL_transient:
			{
				AST tmp72_AST = null;
				if (inputState.guessing==0) {
					tmp72_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp72_AST);
				}
				match(LITERAL_transient);
				break;
			}
			case LITERAL_final:
			{
				AST tmp73_AST = null;
				if (inputState.guessing==0) {
					tmp73_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp73_AST);
				}
				match(LITERAL_final);
				break;
			}
			case LITERAL_abstract:
			{
				AST tmp74_AST = null;
				if (inputState.guessing==0) {
					tmp74_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp74_AST);
				}
				match(LITERAL_abstract);
				break;
			}
			case LITERAL_native:
			{
				AST tmp75_AST = null;
				if (inputState.guessing==0) {
					tmp75_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp75_AST);
				}
				match(LITERAL_native);
				break;
			}
			case LITERAL_synchronized:
			{
				AST tmp76_AST = null;
				if (inputState.guessing==0) {
					tmp76_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp76_AST);
				}
				match(LITERAL_synchronized);
				break;
			}
			case LITERAL_const:
			{
				AST tmp77_AST = null;
				if (inputState.guessing==0) {
					tmp77_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp77_AST);
				}
				match(LITERAL_const);
				break;
			}
			case LITERAL_volatile:
			{
				AST tmp78_AST = null;
				if (inputState.guessing==0) {
					tmp78_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp78_AST);
				}
				match(LITERAL_volatile);
				break;
			}
			case LITERAL_strictfp:
			{
				AST tmp79_AST = null;
				if (inputState.guessing==0) {
					tmp79_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp79_AST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			AST tmp80_AST = null;
			if (inputState.guessing==0) {
				tmp80_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp80_AST);
			}
			match(MODEL);
			break;
		}
		case PURE:
		{
			AST tmp81_AST = null;
			if (inputState.guessing==0) {
				tmp81_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp81_AST);
			}
			match(PURE);
			break;
		}
		case INSTANCE:
		{
			AST tmp82_AST = null;
			if (inputState.guessing==0) {
				tmp82_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp82_AST);
			}
			match(INSTANCE);
			break;
		}
		case SPEC_PUBLIC:
		{
			AST tmp83_AST = null;
			if (inputState.guessing==0) {
				tmp83_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp83_AST);
			}
			match(SPEC_PUBLIC);
			break;
		}
		case SPEC_PROTECTED:
		{
			AST tmp84_AST = null;
			if (inputState.guessing==0) {
				tmp84_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp84_AST);
			}
			match(SPEC_PROTECTED);
			break;
		}
		case MONITORED:
		{
			AST tmp85_AST = null;
			if (inputState.guessing==0) {
				tmp85_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp85_AST);
			}
			match(MONITORED);
			break;
		}
		case UNINITIALIZED:
		{
			AST tmp86_AST = null;
			if (inputState.guessing==0) {
				tmp86_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp86_AST);
			}
			match(UNINITIALIZED);
			break;
		}
		case GHOST:
		{
			AST tmp87_AST = null;
			if (inputState.guessing==0) {
				tmp87_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp87_AST);
			}
			match(GHOST);
			break;
		}
		case NON_NULL:
		{
			AST tmp88_AST = null;
			if (inputState.guessing==0) {
				tmp88_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp88_AST);
			}
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
		
		AST tmp89_AST = null;
		if (inputState.guessing==0) {
			tmp89_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp89_AST);
		}
		match(LITERAL_implements);
		name_weakly_list();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		implements_clause_AST = (AST)currentAST.root;
		returnAST = implements_clause_AST;
	}
	
	public final void class_block(
		boolean in_spec, boolean in_model_prog
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST class_block_AST = null;
		
		AST tmp90_AST = null;
		if (inputState.guessing==0) {
			tmp90_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp90_AST);
		}
		match(LCURLY);
		{
		_loop69:
		do {
			if ((_tokenSet_21.member(LA(1)))) {
				field(in_spec, in_model_prog);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop69;
			}
			
		} while (true);
		}
		AST tmp91_AST = null;
		if (inputState.guessing==0) {
			tmp91_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp91_AST);
		}
		match(RCURLY);
		class_block_AST = (AST)currentAST.root;
		returnAST = class_block_AST;
	}
	
	public final void interface_extends() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST interface_extends_AST = null;
		
		AST tmp92_AST = null;
		if (inputState.guessing==0) {
			tmp92_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp92_AST);
		}
		match(LITERAL_extends);
		name_weakly_list();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		interface_extends_AST = (AST)currentAST.root;
		returnAST = interface_extends_AST;
	}
	
	public final void name_weakly_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST name_weakly_list_AST = null;
		
		name();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		switch ( LA(1)) {
		case WEAKLY:
		{
			AST tmp93_AST = null;
			if (inputState.guessing==0) {
				tmp93_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp93_AST);
			}
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
		_loop78:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp94_AST = null;
				if (inputState.guessing==0) {
					tmp94_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp94_AST);
				}
				match(COMMA);
				name();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				{
				switch ( LA(1)) {
				case WEAKLY:
				{
					AST tmp95_AST = null;
					if (inputState.guessing==0) {
						tmp95_AST = (AST)astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp95_AST);
					}
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
				break _loop78;
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
		_loop81:
		do {
			if ((LA(1)==DOC_COMMENT)) {
				doc_comment();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop81;
			}
			
		} while (true);
		}
		doc_comments_AST = (AST)currentAST.root;
		returnAST = doc_comments_AST;
	}
	
	public final void param_declaration_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST param_declaration_list_AST = null;
		
		param_declaration();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop96:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp96_AST = null;
				if (inputState.guessing==0) {
					tmp96_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp96_AST);
				}
				match(COMMA);
				param_declaration();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop96;
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
		
		AST tmp97_AST = null;
		if (inputState.guessing==0) {
			tmp97_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp97_AST);
		}
		match(LITERAL_throws);
		name_list();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		throws_clause_AST = (AST)currentAST.root;
		returnAST = throws_clause_AST;
	}
	
	public final void name_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST name_list_AST = null;
		
		name();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop93:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp98_AST = null;
				if (inputState.guessing==0) {
					tmp98_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp98_AST);
				}
				match(COMMA);
				name();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop93;
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
			AST tmp99_AST = null;
			if (inputState.guessing==0) {
				tmp99_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp99_AST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp100_AST = null;
		if (inputState.guessing==0) {
			tmp100_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp100_AST);
		}
		match(IDENT);
		{
		switch ( LA(1)) {
		case LBRACK:
		{
			dims();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
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
			param_declaration_AST = (AST)currentAST.root;
			param_declaration_AST =
			(AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(PARAM)).add(param_declaration_AST));
			currentAST.root = param_declaration_AST;
			currentAST.child = param_declaration_AST!=null &&param_declaration_AST.getFirstChild()!=null ?
				param_declaration_AST.getFirstChild() : param_declaration_AST;
			currentAST.advanceChildToEnd();
		}
		param_declaration_AST = (AST)currentAST.root;
		returnAST = param_declaration_AST;
	}
	
	public final void expression(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST expression_AST = null;
		
		assignment_expr(in_spec);
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		expression_AST = (AST)currentAST.root;
		returnAST = expression_AST;
	}
	
	public final void array_initializer(
		boolean in_spec
	) throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST array_initializer_AST = null;
		
		AST tmp101_AST = null;
		if (inputState.guessing==0) {
			tmp101_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp101_AST);
		}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		AST tmp102_AST = null;
		if (inputState.guessing==0) {
			tmp102_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp102_AST);
		}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop109:
		do {
			if ((LA(1)==COMMA) && (_tokenSet_22.member(LA(2)))) {
				{
				AST tmp103_AST = null;
				tmp103_AST = (AST)astFactory.create(LT(1));
				match(COMMA);
				}
				initializer(in_spec);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop109;
			}
			
		} while (true);
		}
		{
		switch ( LA(1)) {
		case COMMA:
		{
			AST tmp104_AST = null;
			tmp104_AST = (AST)astFactory.create(LT(1));
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
		
		AST tmp105_AST = null;
		if (inputState.guessing==0) {
			tmp105_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp105_AST);
		}
		match(IDENT);
		{
		_loop114:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp106_AST = null;
				if (inputState.guessing==0) {
					tmp106_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp106_AST);
				}
				match(COMMA);
				AST tmp107_AST = null;
				if (inputState.guessing==0) {
					tmp107_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp107_AST);
				}
				match(IDENT);
			}
			else {
				break _loop114;
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
		
		AST tmp108_AST = null;
		if (inputState.guessing==0) {
			tmp108_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp108_AST);
		}
		match(MONITORED_BY);
		expression_list(no_side_effects);
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop542:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp109_AST = null;
				if (inputState.guessing==0) {
					tmp109_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp109_AST);
				}
				match(COMMA);
				expression(in_spec);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop542;
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
			AST tmp110_AST = null;
			if (inputState.guessing==0) {
				tmp110_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp110_AST);
			}
			match(INVARIANT);
			break;
		}
		case INVARIANT_REDUNDANTLY:
		{
			AST tmp111_AST = null;
			if (inputState.guessing==0) {
				tmp111_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp111_AST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp112_AST = null;
		tmp112_AST = (AST)astFactory.create(LT(1));
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
			AST tmp113_AST = null;
			if (inputState.guessing==0) {
				tmp113_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp113_AST);
			}
			match(CONSTRAINT);
			break;
		}
		case CONSTRAINT_REDUNDANTLY:
		{
			AST tmp114_AST = null;
			if (inputState.guessing==0) {
				tmp114_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp114_AST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		switch ( LA(1)) {
		case FOR:
		{
			AST tmp115_AST = null;
			if (inputState.guessing==0) {
				tmp115_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp115_AST);
			}
			match(FOR);
			constrained_list();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		AST tmp116_AST = null;
		tmp116_AST = (AST)astFactory.create(LT(1));
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
			AST tmp117_AST = null;
			if (inputState.guessing==0) {
				tmp117_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp117_AST);
			}
			match(DEPENDS);
			break;
		}
		case DEPENDS_REDUNDANTLY:
		{
			AST tmp118_AST = null;
			if (inputState.guessing==0) {
				tmp118_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp118_AST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp119_AST = null;
		tmp119_AST = (AST)astFactory.create(LT(1));
		match(L_ARROW);
		store_references();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp120_AST = null;
		tmp120_AST = (AST)astFactory.create(LT(1));
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
			AST tmp121_AST = null;
			if (inputState.guessing==0) {
				tmp121_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp121_AST);
			}
			match(REPRESENTS);
			break;
		}
		case REPRESENTS_REDUNDANTLY:
		{
			AST tmp122_AST = null;
			if (inputState.guessing==0) {
				tmp122_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp122_AST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp123_AST = null;
		tmp123_AST = (AST)astFactory.create(LT(1));
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			constrained_list_AST = (AST)currentAST.root;
			break;
		}
		case T_EVERYTHING:
		{
			AST tmp124_AST = null;
			if (inputState.guessing==0) {
				tmp124_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp124_AST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop129:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp125_AST = null;
				if (inputState.guessing==0) {
					tmp125_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp125_AST);
				}
				match(COMMA);
				method_name();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop129;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		switch ( LA(1)) {
		case LPAREN:
		{
			AST tmp126_AST = null;
			if (inputState.guessing==0) {
				tmp126_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp126_AST);
			}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp127_AST = null;
			tmp127_AST = (AST)astFactory.create(LT(1));
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
				AST tmp128_AST = null;
				if (inputState.guessing==0) {
					tmp128_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp128_AST);
				}
				match(LITERAL_super);
				break;
			}
			case LITERAL_this:
			{
				AST tmp129_AST = null;
				if (inputState.guessing==0) {
					tmp129_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp129_AST);
				}
				match(LITERAL_this);
				break;
			}
			case IDENT:
			{
				AST tmp130_AST = null;
				if (inputState.guessing==0) {
					tmp130_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp130_AST);
				}
				match(IDENT);
				break;
			}
			case T_OTHER:
			{
				AST tmp131_AST = null;
				if (inputState.guessing==0) {
					tmp131_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp131_AST);
				}
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
			_loop136:
			do {
				if ((LA(1)==DOT)) {
					AST tmp132_AST = null;
					if (inputState.guessing==0) {
						tmp132_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp132_AST);
					}
					match(DOT);
					AST tmp133_AST = null;
					if (inputState.guessing==0) {
						tmp133_AST = (AST)astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp133_AST);
					}
					match(IDENT);
				}
				else {
					break _loop136;
				}
				
			} while (true);
			}
			method_ref_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_new:
		{
			constructor_ref();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop140:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp134_AST = null;
				if (inputState.guessing==0) {
					tmp134_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp134_AST);
				}
				match(COMMA);
				param_disambig();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop140;
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
		
		AST tmp135_AST = null;
		if (inputState.guessing==0) {
			tmp135_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp135_AST);
		}
		match(LITERAL_new);
		reference_type();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		constructor_ref_AST = (AST)currentAST.root;
		returnAST = constructor_ref_AST;
	}
	
	public final void param_disambig() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST param_disambig_AST = null;
		
		type_spec();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		switch ( LA(1)) {
		case IDENT:
		{
			AST tmp136_AST = null;
			if (inputState.guessing==0) {
				tmp136_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp136_AST);
			}
			match(IDENT);
			{
			switch ( LA(1)) {
			case LBRACK:
			{
				dims();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
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
			(AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(PARAM)).add(param_disambig_AST));
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			store_ref_AST = (AST)currentAST.root;
			break;
		}
		case T_FIELDS_OF:
		{
			AST tmp137_AST = null;
			if (inputState.guessing==0) {
				tmp137_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp137_AST);
			}
			match(T_FIELDS_OF);
			AST tmp138_AST = null;
			tmp138_AST = (AST)astFactory.create(LT(1));
			match(LPAREN);
			spec_expression();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			switch ( LA(1)) {
			case COMMA:
			{
				AST tmp139_AST = null;
				tmp139_AST = (AST)astFactory.create(LT(1));
				match(COMMA);
				reference_type();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				{
				switch ( LA(1)) {
				case COMMA:
				{
					AST tmp140_AST = null;
					tmp140_AST = (AST)astFactory.create(LT(1));
					match(COMMA);
					store_ref_expression();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp141_AST = null;
			tmp141_AST = (AST)astFactory.create(LT(1));
			match(RPAREN);
			store_ref_AST = (AST)currentAST.root;
			break;
		}
		case INFORMAL_DESCRIPTION:
		{
			informal_desc();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			store_ref_AST = (AST)currentAST.root;
			break;
		}
		case T_EVERYTHING:
		case T_NOT_SPECIFIED:
		case T_NOTHING:
		{
			store_ref_keyword();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		store_references_AST = (AST)currentAST.root;
		returnAST = store_references_AST;
	}
	
	public final void represents_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST represents_expr_AST = null;
		
		store_ref();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		switch ( LA(1)) {
		case T_SUCH_THAT:
		{
			AST tmp142_AST = null;
			if (inputState.guessing==0) {
				tmp142_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp142_AST);
			}
			match(T_SUCH_THAT);
			predicate();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			break;
		}
		case L_ARROW:
		{
			AST tmp143_AST = null;
			if (inputState.guessing==0) {
				tmp143_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp143_AST);
			}
			match(L_ARROW);
			spec_expression();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
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
			AST tmp144_AST = null;
			if (inputState.guessing==0) {
				tmp144_AST = (AST)astFactory.create(LT(1));
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			switch ( LA(1)) {
			case SUBCLASSING_CONTRACT:
			{
				subclassing_contract();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			switch ( LA(1)) {
			case FOR_EXAMPLE:
			case IMPLIES_THAT:
			{
				redundant_spec();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			AST tmp145_AST = null;
			if (inputState.guessing==0) {
				tmp145_AST = (AST)astFactory.create(LT(1));
			}
			match(ALSO);
			modifiers();
			if (inputState.guessing==0) {
				m_AST = (AST)returnAST;
			}
			specification(m_AST);
			if (inputState.guessing==0) {
				sp_AST = (AST)returnAST;
			}
			if ( inputState.guessing==0 ) {
				extending_specification_AST = (AST)currentAST.root;
				extending_specification_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(EXT_ALSO,"EXT_also")).add(sp_AST));
				currentAST.root = extending_specification_AST;
				currentAST.child = extending_specification_AST!=null &&extending_specification_AST.getFirstChild()!=null ?
					extending_specification_AST.getFirstChild() : extending_specification_AST;
				currentAST.advanceChildToEnd();
			}
			break;
		}
		case AND:
		{
			AST tmp146_AST = null;
			tmp146_AST = (AST)astFactory.create(LT(1));
			match(AND);
			conjoinable_spec_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			switch ( LA(1)) {
			case ALSO:
			{
				AST tmp147_AST = null;
				if (inputState.guessing==0) {
					tmp147_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp147_AST);
				}
				match(ALSO);
				spec_case_seq();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
				extending_specification_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(EXT_AND,"EXT_and")).add(extending_specification_AST));
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop218:
		do {
			if ((LA(1)==ALSO)) {
				AST tmp148_AST = null;
				if (inputState.guessing==0) {
					tmp148_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp148_AST);
				}
				match(ALSO);
				spec_case();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop218;
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
			AST tmp149_AST = null;
			if (inputState.guessing==0) {
				tmp149_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp149_AST);
			}
			match(SUBCLASSING_CONTRACT);
			accessible_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			callable_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			subclassing_contract_AST = (AST)currentAST.root;
		}
		else if ((LA(1)==SUBCLASSING_CONTRACT) && (LA(2)==CALLABLE||LA(2)==CALLABLE_REDUNDANTLY)) {
			AST tmp150_AST = null;
			if (inputState.guessing==0) {
				tmp150_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp150_AST);
			}
			match(SUBCLASSING_CONTRACT);
			callable_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			switch ( LA(1)) {
			case FOR_EXAMPLE:
			{
				examples();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop163:
		do {
			if ((LA(1)==AND)) {
				AST tmp151_AST = null;
				if (inputState.guessing==0) {
					tmp151_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp151_AST);
				}
				match(AND);
				conjoinable_spec();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop163;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop223:
		do {
			if ((LA(1)==ALSO)) {
				AST tmp152_AST = null;
				if (inputState.guessing==0) {
					tmp152_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp152_AST);
				}
				match(ALSO);
				spec_case();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop223;
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			if ( inputState.guessing==0 ) {
				conjoinable_spec_AST = (AST)currentAST.root;
				
				conjoinable_spec_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(CONJOINABLE_SPEC,"conjoinable_spec")).add(conjoinable_spec_AST));
				
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			behavior_conjoinable_spec();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			if ( inputState.guessing==0 ) {
				conjoinable_spec_AST = (AST)currentAST.root;
				
				conjoinable_spec_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(CONJOINABLE_SPEC,"conjoinable_spec")).add(conjoinable_spec_AST));
				
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		if ( inputState.guessing==0 ) {
			generic_conjoinable_spec_AST = (AST)currentAST.root;
			generic_conjoinable_spec_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(CONJOINABLE_SPEC,"conjoinable_spec")).add(generic_conjoinable_spec_AST));
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
				AST tmp153_AST = null;
				if (inputState.guessing==0) {
					tmp153_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp153_AST);
				}
				match(LITERAL_public);
				break;
			}
			case LITERAL_private:
			{
				AST tmp154_AST = null;
				if (inputState.guessing==0) {
					tmp154_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp154_AST);
				}
				match(LITERAL_private);
				break;
			}
			case LITERAL_protected:
			{
				AST tmp155_AST = null;
				if (inputState.guessing==0) {
					tmp155_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp155_AST);
				}
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
				privacy_opt_AST = (AST)astFactory.create(PRIVACY_MODIFIER,priv_mod_str);
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
			AST tmp156_AST = null;
			if (inputState.guessing==0) {
				tmp156_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp156_AST);
			}
			match(BEHAVIOR);
			{
			switch ( LA(1)) {
			case FORALL:
			case LET:
			case OLD:
			{
				spec_var_decls();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			behavior_conjoinable_spec_AST = (AST)currentAST.root;
			break;
		}
		case EXCEPTIONAL_BEHAVIOR:
		{
			AST tmp157_AST = null;
			if (inputState.guessing==0) {
				tmp157_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp157_AST);
			}
			match(EXCEPTIONAL_BEHAVIOR);
			{
			switch ( LA(1)) {
			case FORALL:
			case LET:
			case OLD:
			{
				spec_var_decls();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
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
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			exceptional_simple_spec_body();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			behavior_conjoinable_spec_AST = (AST)currentAST.root;
			break;
		}
		case NORMAL_BEHAVIOR:
		{
			AST tmp158_AST = null;
			if (inputState.guessing==0) {
				tmp158_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp158_AST);
			}
			match(NORMAL_BEHAVIOR);
			{
			switch ( LA(1)) {
			case FORALL:
			case LET:
			case OLD:
			{
				spec_var_decls();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
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
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			normal_simple_spec_body();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			int _cnt298=0;
			_loop298:
			do {
				if ((LA(1)==FORALL)) {
					forall_var_decl();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					if ( _cnt298>=1 ) { break _loop298; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt298++;
			} while (true);
			}
			{
			switch ( LA(1)) {
			case LET:
			case OLD:
			{
				let_var_decls();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			ensures_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			signals_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			diverges_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			simple_spec_body_AST = (AST)currentAST.root;
			break;
		}
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		{
			ensures_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			signals_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			diverges_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			simple_spec_body_AST = (AST)currentAST.root;
			break;
		}
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		{
			signals_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			diverges_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			simple_spec_body_AST = (AST)currentAST.root;
			break;
		}
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			diverges_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			signals_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			diverges_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			exceptional_simple_spec_body_AST = (AST)currentAST.root;
			break;
		}
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		{
			signals_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			diverges_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			ensures_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			diverges_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			normal_simple_spec_body_AST = (AST)currentAST.root;
			break;
		}
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		{
			ensures_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			diverges_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		int _cnt345=0;
		_loop345:
		do {
			if (((LA(1) >= ASSIGNABLE && LA(1) <= MODIFIES_REDUNDANTLY)) && (_tokenSet_23.member(LA(2)))) {
				assignable_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt345>=1 ) { break _loop345; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt345++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			assignable_clause_seq_AST = (AST)currentAST.root;
			assignable_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(ASGNABLE_SEQ,"assignable_seq")).add(assignable_clause_seq_AST)); 
			
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
		_loop391:
		do {
			if (((LA(1) >= SIGNALS && LA(1) <= EXSURES_REDUNDANTLY)) && (LA(2)==LPAREN)) {
				signals_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop391;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			signals_clause_seq_opt_AST = (AST)currentAST.root;
			
			signals_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(SIG_SEQ,"signals_seq")).add(signals_clause_seq_opt_AST));
			
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
		_loop401:
		do {
			if ((LA(1)==DIVERGES||LA(1)==DIVERGES_REDUNDANTLY)) {
				diverges_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop401;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			diverges_clause_seq_opt_AST = (AST)currentAST.root;
			
			diverges_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(DIV_SEQ,"diverges_seq")).add(diverges_clause_seq_opt_AST));
			
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
		int _cnt394=0;
		_loop394:
		do {
			if (((LA(1) >= SIGNALS && LA(1) <= EXSURES_REDUNDANTLY)) && (LA(2)==LPAREN)) {
				signals_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt394>=1 ) { break _loop394; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt394++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			signals_clause_seq_AST = (AST)currentAST.root;
			
			signals_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(SIG_SEQ,"signals_seq")).add(signals_clause_seq_AST));
			
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
		_loop371:
		do {
			if (((LA(1) >= ENSURES && LA(1) <= POST_REDUNDANTLY)) && (_tokenSet_24.member(LA(2)))) {
				ensures_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop371;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			ensures_clause_seq_opt_AST = (AST)currentAST.root;
			
			ensures_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(ENS_SEQ,"ensures_seq")).add(ensures_clause_seq_opt_AST)); 
			
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
		int _cnt374=0;
		_loop374:
		do {
			if (((LA(1) >= ENSURES && LA(1) <= POST_REDUNDANTLY)) && (_tokenSet_24.member(LA(2)))) {
				ensures_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt374>=1 ) { break _loop374; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt374++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			ensures_clause_seq_AST = (AST)currentAST.root;
			
			ensures_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(ENS_SEQ,"ensures_seq")).add(ensures_clause_seq_AST)); 
			
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
		
		AST tmp159_AST = null;
		if (inputState.guessing==0) {
			tmp159_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp159_AST);
		}
		match(IMPLIES_THAT);
		spec_case_seq();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		implications_AST = (AST)currentAST.root;
		returnAST = implications_AST;
	}
	
	public final void examples() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST examples_AST = null;
		
		AST tmp160_AST = null;
		if (inputState.guessing==0) {
			tmp160_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp160_AST);
		}
		match(FOR_EXAMPLE);
		example_seq();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		examples_AST = (AST)currentAST.root;
		returnAST = examples_AST;
	}
	
	public final void example_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST example_seq_AST = null;
		
		example();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop180:
		do {
			if ((LA(1)==ALSO)) {
				AST tmp161_AST = null;
				if (inputState.guessing==0) {
					tmp161_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp161_AST);
				}
				match(ALSO);
				example();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop180;
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			if ( inputState.guessing==0 ) {
				example_AST = (AST)currentAST.root;
				example_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(SPEC_CASE,"generic_example")).add(example_AST));
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			switch ( LA(1)) {
			case EXAMPLE:
			{
				AST tmp162_AST = null;
				if (inputState.guessing==0) {
					tmp162_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp162_AST);
				}
				match(EXAMPLE);
				{
				switch ( LA(1)) {
				case FORALL:
				case LET:
				case OLD:
				{
					spec_var_decls();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
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
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				if ( inputState.guessing==0 ) {
					example_AST = (AST)currentAST.root;
					example_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(SPEC_CASE,"example")).add(example_AST));
					currentAST.root = example_AST;
					currentAST.child = example_AST!=null &&example_AST.getFirstChild()!=null ?
						example_AST.getFirstChild() : example_AST;
					currentAST.advanceChildToEnd();
				}
				break;
			}
			case EXCEPTIONAL_EXAMPLE:
			{
				AST tmp163_AST = null;
				if (inputState.guessing==0) {
					tmp163_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp163_AST);
				}
				match(EXCEPTIONAL_EXAMPLE);
				{
				switch ( LA(1)) {
				case FORALL:
				case LET:
				case OLD:
				{
					spec_var_decls();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
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
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
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
						if (inputState.guessing==0) {
							astFactory.addASTChild(currentAST, returnAST);
						}
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
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
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
					example_AST = (AST)currentAST.root;
					example_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(SPEC_CASE,"example")).add(example_AST));
					currentAST.root = example_AST;
					currentAST.child = example_AST!=null &&example_AST.getFirstChild()!=null ?
						example_AST.getFirstChild() : example_AST;
					currentAST.advanceChildToEnd();
				}
				break;
			}
			case NORMAL_EXAMPLE:
			{
				AST tmp164_AST = null;
				if (inputState.guessing==0) {
					tmp164_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp164_AST);
				}
				match(NORMAL_EXAMPLE);
				{
				switch ( LA(1)) {
				case FORALL:
				case LET:
				case OLD:
				{
					spec_var_decls();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
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
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
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
						if (inputState.guessing==0) {
							astFactory.addASTChild(currentAST, returnAST);
						}
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
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
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
					example_AST = (AST)currentAST.root;
					example_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(SPEC_CASE,"example")).add(example_AST));
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
			int _cnt254=0;
			_loop254:
			do {
				if ((LA(1)==IDENT) && (LA(2)==COLON)) {
					label_decl();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					if ( _cnt254>=1 ) { break _loop254; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt254++;
			} while (true);
			}
			{
			_loop256:
			do {
				if (((LA(1) >= REQUIRES && LA(1) <= PRE_REDUNDANTLY)) && (_tokenSet_24.member(LA(2)))) {
					requires_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					break _loop256;
				}
				
			} while (true);
			}
			{
			_loop258:
			do {
				if ((LA(1)==WHEN||LA(1)==WHEN_REDUNDANTLY)) {
					when_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					break _loop258;
				}
				
			} while (true);
			}
			{
			_loop260:
			do {
				if ((LA(1)==MEASURED_BY||LA(1)==MEASURED_BY_REDUNDANTLY)) {
					measured_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					break _loop260;
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
			int _cnt262=0;
			_loop262:
			do {
				if (((LA(1) >= REQUIRES && LA(1) <= PRE_REDUNDANTLY)) && (_tokenSet_24.member(LA(2)))) {
					requires_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					if ( _cnt262>=1 ) { break _loop262; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt262++;
			} while (true);
			}
			{
			_loop264:
			do {
				if ((LA(1)==WHEN||LA(1)==WHEN_REDUNDANTLY)) {
					when_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					break _loop264;
				}
				
			} while (true);
			}
			{
			_loop266:
			do {
				if ((LA(1)==MEASURED_BY||LA(1)==MEASURED_BY_REDUNDANTLY)) {
					measured_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					break _loop266;
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
			int _cnt268=0;
			_loop268:
			do {
				if ((LA(1)==WHEN||LA(1)==WHEN_REDUNDANTLY)) {
					when_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					if ( _cnt268>=1 ) { break _loop268; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt268++;
			} while (true);
			}
			{
			_loop270:
			do {
				if ((LA(1)==MEASURED_BY||LA(1)==MEASURED_BY_REDUNDANTLY)) {
					measured_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					break _loop270;
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
			int _cnt272=0;
			_loop272:
			do {
				if ((LA(1)==MEASURED_BY||LA(1)==MEASURED_BY_REDUNDANTLY)) {
					measured_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					if ( _cnt272>=1 ) { break _loop272; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt272++;
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
			int _cnt195=0;
			_loop195:
			do {
				if (((LA(1) >= ASSIGNABLE && LA(1) <= MODIFIES_REDUNDANTLY))) {
					assignable_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					if ( _cnt195>=1 ) { break _loop195; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt195++;
			} while (true);
			}
			{
			_loop197:
			do {
				if (((LA(1) >= SIGNALS && LA(1) <= EXSURES_REDUNDANTLY))) {
					signals_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					break _loop197;
				}
				
			} while (true);
			}
			{
			_loop199:
			do {
				if ((LA(1)==DIVERGES||LA(1)==DIVERGES_REDUNDANTLY)) {
					diverges_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					break _loop199;
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
			int _cnt201=0;
			_loop201:
			do {
				if (((LA(1) >= SIGNALS && LA(1) <= EXSURES_REDUNDANTLY))) {
					signals_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					if ( _cnt201>=1 ) { break _loop201; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt201++;
			} while (true);
			}
			{
			_loop203:
			do {
				if ((LA(1)==DIVERGES||LA(1)==DIVERGES_REDUNDANTLY)) {
					diverges_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					break _loop203;
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
			int _cnt206=0;
			_loop206:
			do {
				if (((LA(1) >= ASSIGNABLE && LA(1) <= MODIFIES_REDUNDANTLY))) {
					assignable_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					if ( _cnt206>=1 ) { break _loop206; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt206++;
			} while (true);
			}
			{
			_loop208:
			do {
				if (((LA(1) >= ENSURES && LA(1) <= POST_REDUNDANTLY))) {
					ensures_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					break _loop208;
				}
				
			} while (true);
			}
			{
			_loop210:
			do {
				if ((LA(1)==DIVERGES||LA(1)==DIVERGES_REDUNDANTLY)) {
					diverges_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					break _loop210;
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
			int _cnt212=0;
			_loop212:
			do {
				if (((LA(1) >= ENSURES && LA(1) <= POST_REDUNDANTLY))) {
					ensures_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					if ( _cnt212>=1 ) { break _loop212; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt212++;
			} while (true);
			}
			{
			_loop214:
			do {
				if ((LA(1)==DIVERGES||LA(1)==DIVERGES_REDUNDANTLY)) {
					diverges_clause();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					break _loop214;
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
				AST tmp165_AST = null;
				if (inputState.guessing==0) {
					tmp165_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp165_AST);
				}
				match(ASSIGNABLE);
				break;
			}
			case MODIFIABLE:
			{
				AST tmp166_AST = null;
				if (inputState.guessing==0) {
					tmp166_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp166_AST);
				}
				match(MODIFIABLE);
				break;
			}
			case MODIFIES:
			{
				AST tmp167_AST = null;
				if (inputState.guessing==0) {
					tmp167_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp167_AST);
				}
				match(MODIFIES);
				break;
			}
			case ASSIGNABLE_REDUNDANTLY:
			{
				AST tmp168_AST = null;
				if (inputState.guessing==0) {
					tmp168_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp168_AST);
				}
				match(ASSIGNABLE_REDUNDANTLY);
				break;
			}
			case MODIFIABLE_REDUNDANTLY:
			{
				AST tmp169_AST = null;
				if (inputState.guessing==0) {
					tmp169_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp169_AST);
				}
				match(MODIFIABLE_REDUNDANTLY);
				break;
			}
			case MODIFIES_REDUNDANTLY:
			{
				AST tmp170_AST = null;
				if (inputState.guessing==0) {
					tmp170_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp170_AST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp171_AST = null;
			tmp171_AST = (AST)astFactory.create(LT(1));
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
				AST tmp172_AST = null;
				if (inputState.guessing==0) {
					tmp172_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp172_AST);
				}
				match(DIVERGES);
				break;
			}
			case DIVERGES_REDUNDANTLY:
			{
				AST tmp173_AST = null;
				if (inputState.guessing==0) {
					tmp173_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp173_AST);
				}
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
				AST tmp174_AST = null;
				if (inputState.guessing==0) {
					tmp174_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp174_AST);
				}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			AST tmp175_AST = null;
			tmp175_AST = (AST)astFactory.create(LT(1));
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
				AST tmp176_AST = null;
				if (inputState.guessing==0) {
					tmp176_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp176_AST);
				}
				match(ENSURES);
				break;
			}
			case POST:
			{
				AST tmp177_AST = null;
				if (inputState.guessing==0) {
					tmp177_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp177_AST);
				}
				match(POST);
				break;
			}
			case ENSURES_REDUNDANTLY:
			{
				AST tmp178_AST = null;
				if (inputState.guessing==0) {
					tmp178_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp178_AST);
				}
				match(ENSURES_REDUNDANTLY);
				break;
			}
			case POST_REDUNDANTLY:
			{
				AST tmp179_AST = null;
				if (inputState.guessing==0) {
					tmp179_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp179_AST);
				}
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
				AST tmp180_AST = null;
				if (inputState.guessing==0) {
					tmp180_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp180_AST);
				}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			AST tmp181_AST = null;
			tmp181_AST = (AST)astFactory.create(LT(1));
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				if ( inputState.guessing==0 ) {
					initial_spec_case_AST = (AST)currentAST.root;
					
					initial_spec_case_AST =
					(AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(SPEC_CASE,"generic_spec_case")).add(initial_spec_case_AST));
					
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
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
					break;
				}
				case MODEL_PROGRAM:
				{
					model_program();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
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
					initial_spec_case_AST = (AST)currentAST.root;
					
					initial_spec_case_AST =
					(AST)astFactory.make( (new ASTArray(3)).add((AST)astFactory.create(SPEC_CASE,"spec_case")).add(privs).add(initial_spec_case_AST));
					
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				if ( inputState.guessing==0 ) {
					spec_case_AST = (AST)currentAST.root;
					
					spec_case_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(SPEC_CASE,"generic_spec_case")).add(spec_case_AST)); 
					
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				{
				switch ( LA(1)) {
				case BEHAVIOR:
				case EXCEPTIONAL_BEHAVIOR:
				case NORMAL_BEHAVIOR:
				{
					behavior_spec();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
					break;
				}
				case MODEL_PROGRAM:
				{
					model_program();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
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
					spec_case_AST = (AST)currentAST.root;
					
					spec_case_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(SPEC_CASE,"spec_case")).add(spec_case_AST)); 
					
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
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
			generic_spec_case_AST = (AST)currentAST.root;
			generic_spec_case_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(SPEC_CASE,"generic_spec_case")).add(generic_spec_case_AST));
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
			AST tmp182_AST = null;
			if (inputState.guessing==0) {
				tmp182_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp182_AST);
			}
			match(BEHAVIOR);
			generic_spec_case();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			behavior_spec_AST = (AST)currentAST.root;
			break;
		}
		case EXCEPTIONAL_BEHAVIOR:
		{
			AST tmp183_AST = null;
			if (inputState.guessing==0) {
				tmp183_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp183_AST);
			}
			match(EXCEPTIONAL_BEHAVIOR);
			exceptional_spec_case();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			behavior_spec_AST = (AST)currentAST.root;
			break;
		}
		case NORMAL_BEHAVIOR:
		{
			AST tmp184_AST = null;
			if (inputState.guessing==0) {
				tmp184_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp184_AST);
			}
			match(NORMAL_BEHAVIOR);
			normal_spec_case();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		
		AST tmp185_AST = null;
		if (inputState.guessing==0) {
			tmp185_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp185_AST);
		}
		match(MODEL_PROGRAM);
		compound_statement(with_jml);
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		model_program_AST = (AST)currentAST.root;
		returnAST = model_program_AST;
	}
	
	public final void accessible_clause_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST accessible_clause_seq_AST = null;
		
		{
		int _cnt230=0;
		_loop230:
		do {
			if ((LA(1)==ACCESSIBLE||LA(1)==ACCESSIBLE_REDUNDANTLY)) {
				accessible_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt230>=1 ) { break _loop230; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt230++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			accessible_clause_seq_AST = (AST)currentAST.root;
			accessible_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(ACCESSIBLE_SEQ,"accessible_seq")).add(accessible_clause_seq_AST));
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
		_loop244:
		do {
			if ((LA(1)==CALLABLE||LA(1)==CALLABLE_REDUNDANTLY)) {
				callable_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop244;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			callable_clause_seq_opt_AST = (AST)currentAST.root;
			callable_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(CALLABLE_SEQ,"callable_seq")).add(callable_clause_seq_opt_AST));
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
		int _cnt241=0;
		_loop241:
		do {
			if ((LA(1)==CALLABLE||LA(1)==CALLABLE_REDUNDANTLY)) {
				callable_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt241>=1 ) { break _loop241; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt241++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			callable_clause_seq_AST = (AST)currentAST.root;
			callable_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(CALLABLE_SEQ,"callable_seq")).add(callable_clause_seq_AST));
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
			AST tmp186_AST = null;
			if (inputState.guessing==0) {
				tmp186_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp186_AST);
			}
			match(ACCESSIBLE);
			break;
		}
		case ACCESSIBLE_REDUNDANTLY:
		{
			AST tmp187_AST = null;
			if (inputState.guessing==0) {
				tmp187_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp187_AST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp188_AST = null;
		tmp188_AST = (AST)astFactory.create(LT(1));
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			_loop235:
			do {
				if ((LA(1)==COMMA)) {
					AST tmp189_AST = null;
					if (inputState.guessing==0) {
						tmp189_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp189_AST);
					}
					match(COMMA);
					object_ref();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					break _loop235;
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			object_ref_AST = (AST)currentAST.root;
			break;
		}
		case T_OTHER:
		{
			AST tmp190_AST = null;
			if (inputState.guessing==0) {
				tmp190_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp190_AST);
			}
			match(T_OTHER);
			{
			_loop238:
			do {
				switch ( LA(1)) {
				case DOT:
				{
					AST tmp191_AST = null;
					if (inputState.guessing==0) {
						tmp191_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp191_AST);
					}
					match(DOT);
					AST tmp192_AST = null;
					if (inputState.guessing==0) {
						tmp192_AST = (AST)astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp192_AST);
					}
					match(IDENT);
					break;
				}
				case LBRACK:
				{
					AST tmp193_AST = null;
					if (inputState.guessing==0) {
						tmp193_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp193_AST);
					}
					match(LBRACK);
					spec_array_ref_expr();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
					AST tmp194_AST = null;
					tmp194_AST = (AST)astFactory.create(LT(1));
					match(RBRACK);
					break;
				}
				default:
				{
					break _loop238;
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
			AST tmp195_AST = null;
			if (inputState.guessing==0) {
				tmp195_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp195_AST);
			}
			match(T_NOTHING);
			store_ref_keyword_AST = (AST)currentAST.root;
			break;
		}
		case T_EVERYTHING:
		{
			AST tmp196_AST = null;
			if (inputState.guessing==0) {
				tmp196_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp196_AST);
			}
			match(T_EVERYTHING);
			store_ref_keyword_AST = (AST)currentAST.root;
			break;
		}
		case T_NOT_SPECIFIED:
		{
			AST tmp197_AST = null;
			if (inputState.guessing==0) {
				tmp197_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp197_AST);
			}
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
			AST tmp198_AST = null;
			if (inputState.guessing==0) {
				tmp198_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp198_AST);
			}
			match(IDENT);
			break;
		}
		case LITERAL_this:
		{
			AST tmp199_AST = null;
			if (inputState.guessing==0) {
				tmp199_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp199_AST);
			}
			match(LITERAL_this);
			break;
		}
		case LITERAL_super:
		{
			AST tmp200_AST = null;
			if (inputState.guessing==0) {
				tmp200_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp200_AST);
			}
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
		_loop366:
		do {
			switch ( LA(1)) {
			case DOT:
			{
				AST tmp201_AST = null;
				if (inputState.guessing==0) {
					tmp201_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp201_AST);
				}
				match(DOT);
				AST tmp202_AST = null;
				if (inputState.guessing==0) {
					tmp202_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp202_AST);
				}
				match(IDENT);
				break;
			}
			case LBRACK:
			{
				AST tmp203_AST = null;
				if (inputState.guessing==0) {
					tmp203_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp203_AST);
				}
				match(LBRACK);
				spec_array_ref_expr();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				AST tmp204_AST = null;
				tmp204_AST = (AST)astFactory.create(LT(1));
				match(RBRACK);
				break;
			}
			case LPAREN:
			{
				AST tmp205_AST = null;
				if (inputState.guessing==0) {
					tmp205_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp205_AST);
				}
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
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
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
				AST tmp206_AST = null;
				tmp206_AST = (AST)astFactory.create(LT(1));
				match(RPAREN);
				break;
			}
			default:
			{
				break _loop366;
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			switch ( LA(1)) {
			case DOT_DOT:
			{
				AST tmp207_AST = null;
				if (inputState.guessing==0) {
					tmp207_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp207_AST);
				}
				match(DOT_DOT);
				spec_expression();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			AST tmp208_AST = null;
			if (inputState.guessing==0) {
				tmp208_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp208_AST);
			}
			match(STAR);
			if ( inputState.guessing==0 ) {
				spec_array_ref_expr_AST = (AST)currentAST.root;
				spec_array_ref_expr_AST = (AST)astFactory.make( (new ASTArray(1)).add((AST)astFactory.create(STAR_ELEMS,"*")));
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
			AST tmp209_AST = null;
			if (inputState.guessing==0) {
				tmp209_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp209_AST);
			}
			match(CALLABLE);
			break;
		}
		case CALLABLE_REDUNDANTLY:
		{
			AST tmp210_AST = null;
			if (inputState.guessing==0) {
				tmp210_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp210_AST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp211_AST = null;
		tmp211_AST = (AST)astFactory.create(LT(1));
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			callable_methods_AST = (AST)currentAST.root;
			break;
		}
		case T_EVERYTHING:
		case T_NOT_SPECIFIED:
		case T_NOTHING:
		{
			store_ref_keyword();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			generic_spec_body_AST = (AST)currentAST.root;
			break;
		}
		case LCURLY_VBAR:
		{
			AST tmp212_AST = null;
			if (inputState.guessing==0) {
				tmp212_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp212_AST);
			}
			match(LCURLY_VBAR);
			generic_spec_case_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp213_AST = null;
			if (inputState.guessing==0) {
				tmp213_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp213_AST);
			}
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
		
		AST tmp214_AST = null;
		if (inputState.guessing==0) {
			tmp214_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp214_AST);
		}
		match(IDENT);
		AST tmp215_AST = null;
		if (inputState.guessing==0) {
			tmp215_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp215_AST);
		}
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
				AST tmp216_AST = null;
				if (inputState.guessing==0) {
					tmp216_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp216_AST);
				}
				match(REQUIRES);
				break;
			}
			case PRE:
			{
				AST tmp217_AST = null;
				if (inputState.guessing==0) {
					tmp217_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp217_AST);
				}
				match(PRE);
				break;
			}
			case REQUIRES_REDUNDANTLY:
			{
				AST tmp218_AST = null;
				if (inputState.guessing==0) {
					tmp218_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp218_AST);
				}
				match(REQUIRES_REDUNDANTLY);
				break;
			}
			case PRE_REDUNDANTLY:
			{
				AST tmp219_AST = null;
				if (inputState.guessing==0) {
					tmp219_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp219_AST);
				}
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
				AST tmp220_AST = null;
				if (inputState.guessing==0) {
					tmp220_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp220_AST);
				}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			AST tmp221_AST = null;
			tmp221_AST = (AST)astFactory.create(LT(1));
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
				AST tmp222_AST = null;
				if (inputState.guessing==0) {
					tmp222_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp222_AST);
				}
				match(WHEN);
				break;
			}
			case WHEN_REDUNDANTLY:
			{
				AST tmp223_AST = null;
				if (inputState.guessing==0) {
					tmp223_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp223_AST);
				}
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
				AST tmp224_AST = null;
				if (inputState.guessing==0) {
					tmp224_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp224_AST);
				}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			AST tmp225_AST = null;
			tmp225_AST = (AST)astFactory.create(LT(1));
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
				AST tmp226_AST = null;
				if (inputState.guessing==0) {
					tmp226_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp226_AST);
				}
				match(MEASURED_BY);
				break;
			}
			case MEASURED_BY_REDUNDANTLY:
			{
				AST tmp227_AST = null;
				if (inputState.guessing==0) {
					tmp227_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp227_AST);
				}
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
				AST tmp228_AST = null;
				if (inputState.guessing==0) {
					tmp228_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp228_AST);
				}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				{
				switch ( LA(1)) {
				case LITERAL_if:
				{
					AST tmp229_AST = null;
					if (inputState.guessing==0) {
						tmp229_AST = (AST)astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp229_AST);
					}
					match(LITERAL_if);
					predicate();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
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
			AST tmp230_AST = null;
			tmp230_AST = (AST)astFactory.create(LT(1));
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop276:
		do {
			if ((LA(1)==ALSO)) {
				AST tmp231_AST = null;
				if (inputState.guessing==0) {
					tmp231_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp231_AST);
				}
				match(ALSO);
				generic_spec_case();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop276;
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
		int _cnt404=0;
		_loop404:
		do {
			if ((LA(1)==DIVERGES||LA(1)==DIVERGES_REDUNDANTLY)) {
				diverges_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt404>=1 ) { break _loop404; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt404++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			diverges_clause_seq_AST = (AST)currentAST.root;
			
			diverges_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(DIV_SEQ,"diverges_seq")).add(diverges_clause_seq_AST));
			
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			if ((_tokenSet_25.member(LA(1))) && (_tokenSet_26.member(LA(2)))) {
				exceptional_spec_case_body();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
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
			exceptional_spec_case_AST = (AST)currentAST.root;
			exceptional_spec_case_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(SPEC_CASE,"exceptional_spec_case")).add(exceptional_spec_case_AST));
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			if ((_tokenSet_29.member(LA(1))) && (_tokenSet_30.member(LA(2)))) {
				normal_spec_case_body();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
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
			normal_spec_case_AST = (AST)currentAST.root;
			normal_spec_case_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(SPEC_CASE,"normal_spec_case")).add(normal_spec_case_AST));
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			signals_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			diverges_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			exceptional_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		{
			signals_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			diverges_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			exceptional_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case LCURLY_VBAR:
		{
			AST tmp232_AST = null;
			if (inputState.guessing==0) {
				tmp232_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp232_AST);
			}
			match(LCURLY_VBAR);
			exceptional_spec_case_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp233_AST = null;
			if (inputState.guessing==0) {
				tmp233_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp233_AST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop286:
		do {
			if ((LA(1)==ALSO)) {
				AST tmp234_AST = null;
				if (inputState.guessing==0) {
					tmp234_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp234_AST);
				}
				match(ALSO);
				exceptional_spec_case();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop286;
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			ensures_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			diverges_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			normal_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		{
			ensures_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			diverges_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			normal_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case LCURLY_VBAR:
		{
			AST tmp235_AST = null;
			if (inputState.guessing==0) {
				tmp235_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp235_AST);
			}
			match(LCURLY_VBAR);
			normal_spec_case_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp236_AST = null;
			if (inputState.guessing==0) {
				tmp236_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp236_AST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop294:
		do {
			if ((LA(1)==ALSO)) {
				AST tmp237_AST = null;
				if (inputState.guessing==0) {
					tmp237_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp237_AST);
				}
				match(ALSO);
				normal_spec_case();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop294;
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
		
		AST tmp238_AST = null;
		if (inputState.guessing==0) {
			tmp238_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp238_AST);
		}
		match(FORALL);
		quantified_var_decl();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp239_AST = null;
		tmp239_AST = (AST)astFactory.create(LT(1));
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
			if (inputState.guessing==0) {
				lk_AST = (AST)astFactory.create(lk);
				astFactory.makeASTRoot(currentAST, lk_AST);
			}
			match(LET);
			if ( inputState.guessing==0 ) {
				reportWarning("The keyword `let' is deprecated, use `old' instead.",
				lk.getLine(), lk.getColumn());
				
			}
			break;
		}
		case OLD:
		{
			AST tmp240_AST = null;
			if (inputState.guessing==0) {
				tmp240_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp240_AST);
			}
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
		int _cnt304=0;
		_loop304:
		do {
			if ((LA(1)==MODEL||LA(1)==GHOST)) {
				local_spec_var_decl();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt304>=1 ) { break _loop304; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt304++;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		quantified_var_declarators();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		if ( inputState.guessing==0 ) {
			quantified_var_decl_AST = (AST)currentAST.root;
			quantified_var_decl_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(QUANT_VARS,"quantified_var_decl")).add(quantified_var_decl_AST));
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
				AST tmp241_AST = null;
				if (inputState.guessing==0) {
					tmp241_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp241_AST);
				}
				match(MODEL);
				break;
			}
			case GHOST:
			{
				AST tmp242_AST = null;
				if (inputState.guessing==0) {
					tmp242_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp242_AST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			variable_declarators(no_side_effects);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp243_AST = null;
			tmp243_AST = (AST)astFactory.create(LT(1));
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
		int _cnt309=0;
		_loop309:
		do {
			if (((LA(1) >= REQUIRES && LA(1) <= PRE_REDUNDANTLY))) {
				requires_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt309>=1 ) { break _loop309; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt309++;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		pre_cond_AST = (AST)currentAST.root;
		returnAST = pre_cond_AST;
	}
	
	public final void when_clause_seq() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST when_clause_seq_AST = null;
		
		{
		int _cnt316=0;
		_loop316:
		do {
			if ((LA(1)==WHEN||LA(1)==WHEN_REDUNDANTLY)) {
				when_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt316>=1 ) { break _loop316; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt316++;
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
		int _cnt322=0;
		_loop322:
		do {
			if ((LA(1)==MEASURED_BY||LA(1)==MEASURED_BY_REDUNDANTLY)) {
				measured_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt322>=1 ) { break _loop322; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt322++;
		} while (true);
		}
		measured_clause_seq_AST = (AST)currentAST.root;
		returnAST = measured_clause_seq_AST;
	}
	
	public final void label_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST label_statement_AST = null;
		
		AST tmp244_AST = null;
		if (inputState.guessing==0) {
			tmp244_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp244_AST);
		}
		match(LABEL);
		label_statement_list();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp245_AST = null;
		tmp245_AST = (AST)astFactory.create(LT(1));
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
		
		AST tmp246_AST = null;
		if (inputState.guessing==0) {
			tmp246_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp246_AST);
		}
		match(IDENT);
		{
		_loop331:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp247_AST = null;
				if (inputState.guessing==0) {
					tmp247_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp247_AST);
				}
				match(COMMA);
				AST tmp248_AST = null;
				if (inputState.guessing==0) {
					tmp248_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp248_AST);
				}
				match(IDENT);
			}
			else {
				break _loop331;
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
		_loop334:
		do {
			if ((LA(1)==LOOP_MODIFIES)) {
				loop_assignable_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop334;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			loop_assignable_clause_seq_opt_AST = (AST)currentAST.root;
			loop_assignable_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(LOOP_ASGNABLE_SEQ,"loop_assignable_seq")).add(loop_assignable_clause_seq_opt_AST)); 
			
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
			AST tmp249_AST = null;
			if (inputState.guessing==0) {
				tmp249_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp249_AST);
			}
			match(LOOP_MODIFIES);
			}
			conditional_store_references();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp250_AST = null;
			tmp250_AST = (AST)astFactory.create(LT(1));
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
		int _cnt337=0;
		_loop337:
		do {
			if ((LA(1)==LOOP_MODIFIES)) {
				loop_assignable_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt337>=1 ) { break _loop337; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt337++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			loop_assignable_clause_seq_AST = (AST)currentAST.root;
			loop_assignable_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(LOOP_ASGNABLE_SEQ,"loop_assignable_seq")).add(loop_assignable_clause_seq_AST)); 
			
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		conditional_store_references_AST = (AST)currentAST.root;
		returnAST = conditional_store_references_AST;
	}
	
	public final void assignable_clause_seq_opt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST assignable_clause_seq_opt_AST = null;
		
		{
		_loop342:
		do {
			if (((LA(1) >= ASSIGNABLE && LA(1) <= MODIFIES_REDUNDANTLY))) {
				assignable_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop342;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			assignable_clause_seq_opt_AST = (AST)currentAST.root;
			assignable_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(ASGNABLE_SEQ,"assignable_seq")).add(assignable_clause_seq_opt_AST)); 
			
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop351:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp251_AST = null;
				if (inputState.guessing==0) {
					tmp251_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp251_AST);
				}
				match(COMMA);
				conditional_store_ref();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop351;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		switch ( LA(1)) {
		case LITERAL_if:
		{
			AST tmp252_AST = null;
			if (inputState.guessing==0) {
				tmp252_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp252_AST);
			}
			match(LITERAL_if);
			predicate();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop357:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp253_AST = null;
				if (inputState.guessing==0) {
					tmp253_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp253_AST);
				}
				match(COMMA);
				store_ref();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop357;
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
		if (inputState.guessing==0) {
			id1_AST = (AST)astFactory.create(id1);
		}
		match(INFORMAL_DESCRIPTION);
		if ( inputState.guessing==0 ) {
			informal_desc_AST = (AST)currentAST.root;
			if (in_ML_JML) {
			id1_AST.setText(remove_ats_after_newlines(id1_AST.getText()));
			}
			informal_desc_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(DINFORMALLY,"#informally#")).add(id1_AST));
			
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop411:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp254_AST = null;
				if (inputState.guessing==0) {
					tmp254_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp254_AST);
				}
				match(COMMA);
				spec_expression();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop411;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		post_cond_AST = (AST)currentAST.root;
		returnAST = post_cond_AST;
	}
	
	public final void loop_signals_clause_seq_opt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST loop_signals_clause_seq_opt_AST = null;
		
		{
		_loop381:
		do {
			if ((LA(1)==LOOP_EXSURES)) {
				loop_signals_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop381;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			loop_signals_clause_seq_opt_AST = (AST)currentAST.root;
			
			loop_signals_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(LOOP_SIG_SEQ,"loop_signals_seq")).add(loop_signals_clause_seq_opt_AST));
			
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
			AST tmp255_AST = null;
			if (inputState.guessing==0) {
				tmp255_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp255_AST);
			}
			match(LOOP_EXSURES);
			}
			AST tmp256_AST = null;
			if (inputState.guessing==0) {
				tmp256_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp256_AST);
			}
			match(LPAREN);
			reference_type();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			switch ( LA(1)) {
			case IDENT:
			{
				AST tmp257_AST = null;
				if (inputState.guessing==0) {
					tmp257_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp257_AST);
				}
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
			AST tmp258_AST = null;
			if (inputState.guessing==0) {
				tmp258_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp258_AST);
			}
			match(RPAREN);
			{
			switch ( LA(1)) {
			case T_NOT_SPECIFIED:
			{
				AST tmp259_AST = null;
				if (inputState.guessing==0) {
					tmp259_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp259_AST);
				}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			AST tmp260_AST = null;
			tmp260_AST = (AST)astFactory.create(LT(1));
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
		int _cnt384=0;
		_loop384:
		do {
			if ((LA(1)==LOOP_EXSURES)) {
				loop_signals_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt384>=1 ) { break _loop384; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt384++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			loop_signals_clause_seq_AST = (AST)currentAST.root;
			
			loop_signals_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(LOOP_SIG_SEQ,"loop_signals_seq")).add(loop_signals_clause_seq_AST));
			
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				g_AST = (AST)returnAST;
			}
			compound_statement(in_model_prog);
			if (inputState.guessing==0) {
				c_AST = (AST)returnAST;
			}
			if ( inputState.guessing==0 ) {
				statement_AST = (AST)currentAST.root;
				
							statement_AST = (AST)astFactory.make( (new ASTArray(3)).add((AST)astFactory.create(SPEC_STATEMENT,"spec_statement")).add(g_AST).add(c_AST));
						
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				if ( inputState.guessing==0 ) {
					statement_AST = (AST)currentAST.root;
					statement_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(NESTED_CLASS,"nested_class")).add(statement_AST));
					currentAST.root = statement_AST;
					currentAST.child = statement_AST!=null &&statement_AST.getFirstChild()!=null ?
						statement_AST.getFirstChild() : statement_AST;
					currentAST.advanceChildToEnd();
				}
			}
			else if ((LA(1)==LITERAL_final) && (LA(2)==LITERAL_class)) {
				AST tmp261_AST = null;
				if (inputState.guessing==0) {
					tmp261_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp261_AST);
				}
				match(LITERAL_final);
				class_definition(in_model_prog);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				if ( inputState.guessing==0 ) {
					statement_AST = (AST)currentAST.root;
					statement_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(NESTED_CLASS,"nested_class")).add(statement_AST));
					currentAST.root = statement_AST;
					currentAST.child = statement_AST!=null &&statement_AST.getFirstChild()!=null ?
						statement_AST.getFirstChild() : statement_AST;
					currentAST.advanceChildToEnd();
				}
			}
			else if ((LA(1)==LITERAL_abstract) && (LA(2)==LITERAL_class)) {
				AST tmp262_AST = null;
				if (inputState.guessing==0) {
					tmp262_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp262_AST);
				}
				match(LITERAL_abstract);
				class_definition(in_model_prog);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				if ( inputState.guessing==0 ) {
					statement_AST = (AST)currentAST.root;
					statement_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(NESTED_CLASS,"nested_class")).add(statement_AST));
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			if ( inputState.guessing==0 ) {
				statement_AST = (AST)currentAST.root;
				statement_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(NESTED_CLASS,"nested_class1")).add(statement_AST));
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
			AST tmp263_AST = null;
			if (inputState.guessing==0) {
				tmp263_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp263_AST);
			}
			match(LITERAL_abstract);
			class_definition(in_model_prog);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			if ( inputState.guessing==0 ) {
				statement_AST = (AST)currentAST.root;
				statement_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(NESTED_CLASS,"nested_class")).add(statement_AST));
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
			AST tmp264_AST = null;
			if (inputState.guessing==0) {
				tmp264_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp264_AST);
			}
			match(LITERAL_if);
			AST tmp265_AST = null;
			tmp265_AST = (AST)astFactory.create(LT(1));
			match(LPAREN);
			expression(side_effects_allowed);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp266_AST = null;
			tmp266_AST = (AST)astFactory.create(LT(1));
			match(RPAREN);
			statement(in_model_prog);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			if ((LA(1)==LITERAL_else) && (_tokenSet_8.member(LA(2)))) {
				AST tmp267_AST = null;
				tmp267_AST = (AST)astFactory.create(LT(1));
				match(LITERAL_else);
				statement(in_model_prog);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
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
			if (inputState.guessing==0) {
				lm_AST = (AST)returnAST;
			}
			loop_invariant_seq_opt();
			if (inputState.guessing==0) {
				li_AST = (AST)returnAST;
			}
			loop_signals_clause_seq_opt();
			if (inputState.guessing==0) {
				ls_AST = (AST)returnAST;
			}
			variant_function_seq_opt();
			if (inputState.guessing==0) {
				vf_AST = (AST)returnAST;
			}
			{
			switch ( LA(1)) {
			case LITERAL_while:
			{
				w = LT(1);
				if (inputState.guessing==0) {
					w_AST = (AST)astFactory.create(w);
				}
				match(LITERAL_while);
				AST tmp268_AST = null;
				tmp268_AST = (AST)astFactory.create(LT(1));
				match(LPAREN);
				expression(side_effects_allowed);
				if (inputState.guessing==0) {
					we_AST = (AST)returnAST;
				}
				AST tmp269_AST = null;
				tmp269_AST = (AST)astFactory.create(LT(1));
				match(RPAREN);
				statement(in_model_prog);
				if (inputState.guessing==0) {
					ws_AST = (AST)returnAST;
				}
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
				if (inputState.guessing==0) {
					d_AST = (AST)astFactory.create(d);
				}
				match(LITERAL_do);
				statement(in_model_prog);
				if (inputState.guessing==0) {
					ds_AST = (AST)returnAST;
				}
				AST tmp270_AST = null;
				if (inputState.guessing==0) {
					tmp270_AST = (AST)astFactory.create(LT(1));
				}
				match(LITERAL_while);
				AST tmp271_AST = null;
				tmp271_AST = (AST)astFactory.create(LT(1));
				match(LPAREN);
				expression(side_effects_allowed);
				if (inputState.guessing==0) {
					de_AST = (AST)returnAST;
				}
				AST tmp272_AST = null;
				tmp272_AST = (AST)astFactory.create(LT(1));
				match(RPAREN);
				AST tmp273_AST = null;
				tmp273_AST = (AST)astFactory.create(LT(1));
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
				if (inputState.guessing==0) {
					f_AST = (AST)astFactory.create(f);
				}
				match(LITERAL_for);
				AST tmp274_AST = null;
				if (inputState.guessing==0) {
					tmp274_AST = (AST)astFactory.create(LT(1));
				}
				match(LPAREN);
				for_init();
				if (inputState.guessing==0) {
					finit_AST = (AST)returnAST;
				}
				AST tmp275_AST = null;
				if (inputState.guessing==0) {
					tmp275_AST = (AST)astFactory.create(LT(1));
				}
				match(SEMI);
				for_test();
				if (inputState.guessing==0) {
					ftest_AST = (AST)returnAST;
				}
				AST tmp276_AST = null;
				if (inputState.guessing==0) {
					tmp276_AST = (AST)astFactory.create(LT(1));
				}
				match(SEMI);
				for_updater();
				if (inputState.guessing==0) {
					fupdater_AST = (AST)returnAST;
				}
				AST tmp277_AST = null;
				if (inputState.guessing==0) {
					tmp277_AST = (AST)astFactory.create(LT(1));
				}
				match(RPAREN);
				statement(in_model_prog);
				if (inputState.guessing==0) {
					fstat_AST = (AST)returnAST;
				}
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
			AST tmp278_AST = null;
			if (inputState.guessing==0) {
				tmp278_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp278_AST);
			}
			match(LITERAL_break);
			{
			switch ( LA(1)) {
			case IDENT:
			{
				AST tmp279_AST = null;
				if (inputState.guessing==0) {
					tmp279_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp279_AST);
				}
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
			AST tmp280_AST = null;
			tmp280_AST = (AST)astFactory.create(LT(1));
			match(SEMI);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_continue:
		{
			AST tmp281_AST = null;
			if (inputState.guessing==0) {
				tmp281_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp281_AST);
			}
			match(LITERAL_continue);
			{
			switch ( LA(1)) {
			case IDENT:
			{
				AST tmp282_AST = null;
				if (inputState.guessing==0) {
					tmp282_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp282_AST);
				}
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
			AST tmp283_AST = null;
			tmp283_AST = (AST)astFactory.create(LT(1));
			match(SEMI);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_return:
		{
			AST tmp284_AST = null;
			if (inputState.guessing==0) {
				tmp284_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp284_AST);
			}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			AST tmp285_AST = null;
			tmp285_AST = (AST)astFactory.create(LT(1));
			match(SEMI);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_switch:
		{
			switch_statement(in_model_prog);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_try:
		{
			try_block(in_model_prog);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_throw:
		{
			AST tmp286_AST = null;
			if (inputState.guessing==0) {
				tmp286_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp286_AST);
			}
			match(LITERAL_throw);
			expression(side_effects_allowed);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp287_AST = null;
			tmp287_AST = (AST)astFactory.create(LT(1));
			match(SEMI);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_synchronized:
		{
			AST tmp288_AST = null;
			if (inputState.guessing==0) {
				tmp288_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp288_AST);
			}
			match(LITERAL_synchronized);
			AST tmp289_AST = null;
			tmp289_AST = (AST)astFactory.create(LT(1));
			match(LPAREN);
			expression(side_effects_allowed);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp290_AST = null;
			tmp290_AST = (AST)astFactory.create(LT(1));
			match(RPAREN);
			compound_statement(in_model_prog);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			statement_AST = (AST)currentAST.root;
			break;
		}
		case SEMI:
		{
			AST tmp291_AST = null;
			if (inputState.guessing==0) {
				tmp291_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp291_AST);
			}
			match(SEMI);
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_assert:
		{
			assert_statement();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			statement_AST = (AST)currentAST.root;
			break;
		}
		case LABEL:
		{
			label_statement();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			statement_AST = (AST)currentAST.root;
			break;
		}
		case HENCE_BY:
		case HENCE_BY_REDUNDANTLY:
		{
			hence_by_statement();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			statement_AST = (AST)currentAST.root;
			break;
		}
		case ASSERT_REDUNDANTLY:
		{
			assert_redundantly_statement();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			statement_AST = (AST)currentAST.root;
			break;
		}
		case ASSUME:
		case ASSUME_REDUNDANTLY:
		{
			assume_statement();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			statement_AST = (AST)currentAST.root;
			break;
		}
		case SET:
		{
			set_statement();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			statement_AST = (AST)currentAST.root;
			break;
		}
		case UNREACHABLE:
		{
			unreachable_statement();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				mps_AST = (AST)returnAST;
				astFactory.addASTChild(currentAST, returnAST);
			}
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
				AST tmp292_AST = null;
				if (inputState.guessing==0) {
					tmp292_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp292_AST);
				}
				match(LITERAL_final);
				class_definition(in_model_prog);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				if ( inputState.guessing==0 ) {
					statement_AST = (AST)currentAST.root;
					statement_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(NESTED_CLASS,"nested_class")).add(statement_AST));
					currentAST.root = statement_AST;
					currentAST.child = statement_AST!=null &&statement_AST.getFirstChild()!=null ?
						statement_AST.getFirstChild() : statement_AST;
					currentAST.advanceChildToEnd();
				}
				statement_AST = (AST)currentAST.root;
			}
			else {
				boolean synPredMatched419 = false;
				if (((_tokenSet_33.member(LA(1))) && (_tokenSet_34.member(LA(2))))) {
					int _m419 = mark();
					synPredMatched419 = true;
					inputState.guessing++;
					try {
						{
						local_declaration();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched419 = false;
					}
					rewind(_m419);
					inputState.guessing--;
				}
				if ( synPredMatched419 ) {
					local_declaration();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
					AST tmp293_AST = null;
					tmp293_AST = (AST)astFactory.create(LT(1));
					match(SEMI);
					statement_AST = (AST)currentAST.root;
				}
				else if ((LA(1)==IDENT) && (LA(2)==COLON)) {
					AST tmp294_AST = null;
					if (inputState.guessing==0) {
						tmp294_AST = (AST)astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp294_AST);
					}
					match(IDENT);
					AST tmp295_AST = null;
					if (inputState.guessing==0) {
						tmp295_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp295_AST);
					}
					match(COLON);
					statement(in_model_prog);
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
					statement_AST = (AST)currentAST.root;
				}
				else if ((_tokenSet_35.member(LA(1))) && (_tokenSet_36.member(LA(2)))) {
					expression(side_effects_allowed);
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
					AST tmp296_AST = null;
					tmp296_AST = (AST)astFactory.create(LT(1));
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			assignable_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			ensures_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			signals_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			ensures_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			signals_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			spec_statement_jack_AST = (AST)currentAST.root;
			break;
		}
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		{
			ensures_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			signals_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			spec_statement_jack_AST = (AST)currentAST.root;
			break;
		}
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		{
			signals_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		variable_decls(side_effects_allowed);
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		local_declaration_AST = (AST)currentAST.root;
		returnAST = local_declaration_AST;
	}
	
	public final void loop_invariant_seq_opt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST loop_invariant_seq_opt_AST = null;
		
		{
		_loop532:
		do {
			if (((LA(1) >= MAINTAINING && LA(1) <= LOOP_INVARIANT_REDUNDANTLY))) {
				loop_invariant();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop532;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			loop_invariant_seq_opt_AST = (AST)currentAST.root;
			loop_invariant_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(LOOP_INV_SEQ,"loop_invariant_seq")).add(loop_invariant_seq_opt_AST));
			
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
		_loop537:
		do {
			if (((LA(1) >= DECREASING && LA(1) <= DECREASES_REDUNDANTLY))) {
				variant_function();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop537;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			variant_function_seq_opt_AST = (AST)currentAST.root;
			variant_function_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(VF_SEQ,"variant_function_seq")).add(variant_function_seq_opt_AST));
			
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
		
		boolean synPredMatched427 = false;
		if (((_tokenSet_33.member(LA(1))) && (_tokenSet_34.member(LA(2))))) {
			int _m427 = mark();
			synPredMatched427 = true;
			inputState.guessing++;
			try {
				{
				local_declaration();
				}
			}
			catch (RecognitionException pe) {
				synPredMatched427 = false;
			}
			rewind(_m427);
			inputState.guessing--;
		}
		if ( synPredMatched427 ) {
			local_declaration();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			if ( inputState.guessing==0 ) {
				for_init_AST = (AST)currentAST.root;
				for_init_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(FOR_INIT,"for_init")).add(for_init_AST));
				currentAST.root = for_init_AST;
				currentAST.child = for_init_AST!=null &&for_init_AST.getFirstChild()!=null ?
					for_init_AST.getFirstChild() : for_init_AST;
				currentAST.advanceChildToEnd();
			}
			for_init_AST = (AST)currentAST.root;
		}
		else if ((_tokenSet_35.member(LA(1))) && (_tokenSet_37.member(LA(2)))) {
			expression_list(side_effects_allowed);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			if ( inputState.guessing==0 ) {
				for_init_AST = (AST)currentAST.root;
				for_init_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(FOR_INIT,"for_init")).add(for_init_AST));
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
				for_init_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(FOR_INIT,"for_init")).add(for_init_AST));
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			if ( inputState.guessing==0 ) {
				for_test_AST = (AST)currentAST.root;
				for_test_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(FOR_TEST,"for_test")).add(for_test_AST));
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
				for_test_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(FOR_TEST,"for_test")).add(for_test_AST));
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			if ( inputState.guessing==0 ) {
				for_updater_AST = (AST)currentAST.root;
				for_updater_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(FOR_UPDATER,"for_updater")).add(for_updater_AST));
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
				for_updater_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(FOR_UPDATER,"for_updater")).add(for_updater_AST));
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
		
		AST tmp297_AST = null;
		if (inputState.guessing==0) {
			tmp297_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp297_AST);
		}
		match(LITERAL_switch);
		AST tmp298_AST = null;
		tmp298_AST = (AST)astFactory.create(LT(1));
		match(LPAREN);
		expression(side_effects_allowed);
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp299_AST = null;
		tmp299_AST = (AST)astFactory.create(LT(1));
		match(RPAREN);
		AST tmp300_AST = null;
		tmp300_AST = (AST)astFactory.create(LT(1));
		match(LCURLY);
		{
		_loop437:
		do {
			if ((LA(1)==LITERAL_case||LA(1)==LITERAL_default)) {
				switch_body(in_model_prog);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop437;
			}
			
		} while (true);
		}
		AST tmp301_AST = null;
		tmp301_AST = (AST)astFactory.create(LT(1));
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
		
		AST tmp302_AST = null;
		if (inputState.guessing==0) {
			tmp302_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp302_AST);
		}
		match(LITERAL_try);
		compound_statement(in_model_prog);
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop447:
		do {
			if ((LA(1)==LITERAL_catch)) {
				handler(in_model_prog);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop447;
			}
			
		} while (true);
		}
		{
		switch ( LA(1)) {
		case LITERAL_finally:
		{
			AST tmp303_AST = null;
			if (inputState.guessing==0) {
				tmp303_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp303_AST);
			}
			match(LITERAL_finally);
			compound_statement(in_model_prog);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		
		
		AST tmp304_AST = null;
		if (inputState.guessing==0) {
			tmp304_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp304_AST);
		}
		match(LITERAL_assert);
		expression(in_JML ? no_side_effects : side_effects_allowed);
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		switch ( LA(1)) {
		case COLON:
		{
			AST tmp305_AST = null;
			tmp305_AST = (AST)astFactory.create(LT(1));
			match(COLON);
			expression(side_effects_allowed);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		AST tmp306_AST = null;
		tmp306_AST = (AST)astFactory.create(LT(1));
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
			AST tmp307_AST = null;
			if (inputState.guessing==0) {
				tmp307_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp307_AST);
			}
			match(HENCE_BY);
			break;
		}
		case HENCE_BY_REDUNDANTLY:
		{
			AST tmp308_AST = null;
			if (inputState.guessing==0) {
				tmp308_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp308_AST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp309_AST = null;
		tmp309_AST = (AST)astFactory.create(LT(1));
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
		
		AST tmp310_AST = null;
		if (inputState.guessing==0) {
			tmp310_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp310_AST);
		}
		match(ASSERT_REDUNDANTLY);
		predicate();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		switch ( LA(1)) {
		case COLON:
		{
			AST tmp311_AST = null;
			tmp311_AST = (AST)astFactory.create(LT(1));
			match(COLON);
			expression(side_effects_allowed);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		AST tmp312_AST = null;
		tmp312_AST = (AST)astFactory.create(LT(1));
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
			AST tmp313_AST = null;
			if (inputState.guessing==0) {
				tmp313_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp313_AST);
			}
			match(ASSUME);
			break;
		}
		case ASSUME_REDUNDANTLY:
		{
			AST tmp314_AST = null;
			if (inputState.guessing==0) {
				tmp314_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp314_AST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		switch ( LA(1)) {
		case COLON:
		{
			AST tmp315_AST = null;
			tmp315_AST = (AST)astFactory.create(LT(1));
			match(COLON);
			expression(side_effects_allowed);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		AST tmp316_AST = null;
		tmp316_AST = (AST)astFactory.create(LT(1));
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
		
		AST tmp317_AST = null;
		if (inputState.guessing==0) {
			tmp317_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp317_AST);
		}
		match(SET);
		spec_assignment_expr();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp318_AST = null;
		tmp318_AST = (AST)astFactory.create(LT(1));
		match(SEMI);
		set_statement_AST = (AST)currentAST.root;
		returnAST = set_statement_AST;
	}
	
	public final void unreachable_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST unreachable_statement_AST = null;
		
		AST tmp319_AST = null;
		if (inputState.guessing==0) {
			tmp319_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp319_AST);
		}
		match(UNREACHABLE);
		AST tmp320_AST = null;
		tmp320_AST = (AST)astFactory.create(LT(1));
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			model_prog_statement_AST = (AST)currentAST.root;
			break;
		}
		case CHOOSE_IF:
		{
			nondeterministic_if();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			model_prog_statement_AST = (AST)currentAST.root;
			break;
		}
		case BEHAVIOR:
		case EXCEPTIONAL_BEHAVIOR:
		case NORMAL_BEHAVIOR:
		case ABRUPT_BEHAVIOR:
		{
			spec_statement();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			model_prog_statement_AST = (AST)currentAST.root;
			break;
		}
		case INVARIANT:
		case INVARIANT_REDUNDANTLY:
		{
			invariant();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			AST tmp321_AST = null;
			if (inputState.guessing==0) {
				tmp321_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp321_AST);
			}
			match(MODEL);
			local_modifier_AST = (AST)currentAST.root;
			break;
		}
		case GHOST:
		{
			AST tmp322_AST = null;
			if (inputState.guessing==0) {
				tmp322_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp322_AST);
			}
			match(GHOST);
			local_modifier_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_final:
		{
			AST tmp323_AST = null;
			if (inputState.guessing==0) {
				tmp323_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp323_AST);
			}
			match(LITERAL_final);
			local_modifier_AST = (AST)currentAST.root;
			break;
		}
		case NON_NULL:
		{
			AST tmp324_AST = null;
			if (inputState.guessing==0) {
				tmp324_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp324_AST);
			}
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
		_loop433:
		do {
			if ((_tokenSet_38.member(LA(1)))) {
				local_modifier();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop433;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop440:
		do {
			if ((_tokenSet_8.member(LA(1)))) {
				statement(in_model_prog);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop440;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			switch_body_AST = (AST)currentAST.root;
			switch_body_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(CASE)).add(switch_body_AST));
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
		int _cnt443=0;
		_loop443:
		do {
			if ((LA(1)==LITERAL_case||LA(1)==LITERAL_default) && (_tokenSet_39.member(LA(2)))) {
				switch_label();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt443>=1 ) { break _loop443; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt443++;
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
			AST tmp325_AST = null;
			if (inputState.guessing==0) {
				tmp325_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp325_AST);
			}
			match(LITERAL_case);
			expression(side_effects_allowed);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp326_AST = null;
			tmp326_AST = (AST)astFactory.create(LT(1));
			match(COLON);
			switch_label_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_default:
		{
			AST tmp327_AST = null;
			if (inputState.guessing==0) {
				tmp327_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp327_AST);
			}
			match(LITERAL_default);
			AST tmp328_AST = null;
			tmp328_AST = (AST)astFactory.create(LT(1));
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
		
		AST tmp329_AST = null;
		if (inputState.guessing==0) {
			tmp329_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp329_AST);
		}
		match(LITERAL_catch);
		AST tmp330_AST = null;
		tmp330_AST = (AST)astFactory.create(LT(1));
		match(LPAREN);
		param_declaration();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp331_AST = null;
		tmp331_AST = (AST)astFactory.create(LT(1));
		match(RPAREN);
		compound_statement(in_model_prog);
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		handler_AST = (AST)currentAST.root;
		returnAST = handler_AST;
	}
	
	public final void spec_assignment_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST spec_assignment_expr_AST = null;
		
		conditional_expr(no_side_effects);
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
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
				AST tmp332_AST = null;
				if (inputState.guessing==0) {
					tmp332_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp332_AST);
				}
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
					AST tmp333_AST = null;
					if (inputState.guessing==0) {
						tmp333_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp333_AST);
					}
					match(PLUS_ASSIGN);
					break;
				}
				case MINUS_ASSIGN:
				{
					AST tmp334_AST = null;
					if (inputState.guessing==0) {
						tmp334_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp334_AST);
					}
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
					AST tmp335_AST = null;
					if (inputState.guessing==0) {
						tmp335_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp335_AST);
					}
					match(STAR_ASSIGN);
					break;
				}
				case DIV_ASSIGN:
				{
					AST tmp336_AST = null;
					if (inputState.guessing==0) {
						tmp336_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp336_AST);
					}
					match(DIV_ASSIGN);
					break;
				}
				case MOD_ASSIGN:
				{
					AST tmp337_AST = null;
					if (inputState.guessing==0) {
						tmp337_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp337_AST);
					}
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
					AST tmp338_AST = null;
					if (inputState.guessing==0) {
						tmp338_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp338_AST);
					}
					match(SR_ASSIGN);
					break;
				}
				case BSR_ASSIGN:
				{
					AST tmp339_AST = null;
					if (inputState.guessing==0) {
						tmp339_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp339_AST);
					}
					match(BSR_ASSIGN);
					break;
				}
				case SL_ASSIGN:
				{
					AST tmp340_AST = null;
					if (inputState.guessing==0) {
						tmp340_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp340_AST);
					}
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
					AST tmp341_AST = null;
					if (inputState.guessing==0) {
						tmp341_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp341_AST);
					}
					match(BAND_ASSIGN);
					break;
				}
				case BOR_ASSIGN:
				{
					AST tmp342_AST = null;
					if (inputState.guessing==0) {
						tmp342_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp342_AST);
					}
					match(BOR_ASSIGN);
					break;
				}
				case BXOR_ASSIGN:
				{
					AST tmp343_AST = null;
					if (inputState.guessing==0) {
						tmp343_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp343_AST);
					}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		switch ( LA(1)) {
		case QUESTION:
		{
			AST tmp344_AST = null;
			if (inputState.guessing==0) {
				tmp344_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp344_AST);
			}
			match(QUESTION);
			conditional_expr(in_spec);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp345_AST = null;
			tmp345_AST = (AST)astFactory.create(LT(1));
			match(COLON);
			conditional_expr(in_spec);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
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
		
		AST tmp346_AST = null;
		if (inputState.guessing==0) {
			tmp346_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp346_AST);
		}
		match(CHOOSE);
		alternative_statements();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		nondeterministic_choice_AST = (AST)currentAST.root;
		returnAST = nondeterministic_choice_AST;
	}
	
	public final void nondeterministic_if() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST nondeterministic_if_AST = null;
		
		AST tmp347_AST = null;
		if (inputState.guessing==0) {
			tmp347_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp347_AST);
		}
		match(CHOOSE_IF);
		guarded_statements();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		switch ( LA(1)) {
		case ELSE:
		{
			AST tmp348_AST = null;
			tmp348_AST = (AST)astFactory.create(LT(1));
			match(ELSE);
			compound_statement(with_jml);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			AST tmp349_AST = null;
			if (inputState.guessing==0) {
				tmp349_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp349_AST);
			}
			match(BEHAVIOR);
			generic_spec_statement_case();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			spec_statement_AST = (AST)currentAST.root;
			break;
		}
		case EXCEPTIONAL_BEHAVIOR:
		{
			AST tmp350_AST = null;
			if (inputState.guessing==0) {
				tmp350_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp350_AST);
			}
			match(EXCEPTIONAL_BEHAVIOR);
			exceptional_spec_case();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			spec_statement_AST = (AST)currentAST.root;
			break;
		}
		case NORMAL_BEHAVIOR:
		{
			AST tmp351_AST = null;
			if (inputState.guessing==0) {
				tmp351_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp351_AST);
			}
			match(NORMAL_BEHAVIOR);
			normal_spec_case();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			spec_statement_AST = (AST)currentAST.root;
			break;
		}
		case ABRUPT_BEHAVIOR:
		{
			AST tmp352_AST = null;
			if (inputState.guessing==0) {
				tmp352_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp352_AST);
			}
			match(ABRUPT_BEHAVIOR);
			abrupt_spec_case();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop472:
		do {
			if ((LA(1)==OR)) {
				AST tmp353_AST = null;
				if (inputState.guessing==0) {
					tmp353_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp353_AST);
				}
				match(OR);
				compound_statement(with_jml);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop472;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop477:
		do {
			if ((LA(1)==OR)) {
				AST tmp354_AST = null;
				if (inputState.guessing==0) {
					tmp354_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp354_AST);
				}
				match(OR);
				guarded_statement();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop477;
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
		
		AST tmp355_AST = null;
		if (inputState.guessing==0) {
			tmp355_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp355_AST);
		}
		match(LCURLY);
		assume_statement();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop480:
		do {
			if ((_tokenSet_8.member(LA(1)))) {
				statement(with_jml);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop480;
			}
			
		} while (true);
		}
		AST tmp356_AST = null;
		if (inputState.guessing==0) {
			tmp356_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp356_AST);
		}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			if ((_tokenSet_40.member(LA(1))) && (_tokenSet_41.member(LA(2)))) {
				generic_spec_statement_body();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
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
			generic_spec_statement_case_AST = (AST)currentAST.root;
			generic_spec_statement_case_AST =
			(AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(SPEC_CASE,"generic_spec_statement_case")).add(generic_spec_statement_case_AST));
			
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			if ((_tokenSet_44.member(LA(1))) && (_tokenSet_45.member(LA(2)))) {
				abrupt_spec_case_body();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
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
			abrupt_spec_case_AST = (AST)currentAST.root;
			abrupt_spec_case_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(SPEC_CASE,"abrupt_spec_case")).add(abrupt_spec_case_AST));
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			generic_spec_statement_body_AST = (AST)currentAST.root;
			break;
		}
		case LCURLY_VBAR:
		{
			AST tmp357_AST = null;
			if (inputState.guessing==0) {
				tmp357_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp357_AST);
			}
			match(LCURLY_VBAR);
			generic_spec_statement_case_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp358_AST = null;
			if (inputState.guessing==0) {
				tmp358_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp358_AST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			ensures_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			signals_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			diverges_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			continues_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			breaks_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			returns_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			simple_spec_statement_body_AST = (AST)currentAST.root;
			break;
		}
		case ENSURES:
		case POST:
		case ENSURES_REDUNDANTLY:
		case POST_REDUNDANTLY:
		{
			ensures_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			signals_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			diverges_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			continues_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			breaks_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			returns_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			simple_spec_statement_body_AST = (AST)currentAST.root;
			break;
		}
		case SIGNALS:
		case SIGNALS_REDUNDANTLY:
		case EXSURES:
		case EXSURES_REDUNDANTLY:
		{
			signals_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			diverges_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			continues_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			breaks_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			returns_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			simple_spec_statement_body_AST = (AST)currentAST.root;
			break;
		}
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			diverges_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			continues_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			breaks_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			returns_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			simple_spec_statement_body_AST = (AST)currentAST.root;
			break;
		}
		case CONTINUES:
		case CONTINUES_REDUNDANTLY:
		{
			continues_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			breaks_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			returns_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			simple_spec_statement_body_AST = (AST)currentAST.root;
			break;
		}
		case BREAKS:
		case BREAKS_REDUNDANTLY:
		{
			breaks_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			returns_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			simple_spec_statement_body_AST = (AST)currentAST.root;
			break;
		}
		case RETURNS:
		case RETURNS_REDUNDANTLY:
		{
			returns_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop489:
		do {
			if ((LA(1)==ALSO)) {
				AST tmp359_AST = null;
				if (inputState.guessing==0) {
					tmp359_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp359_AST);
				}
				match(ALSO);
				generic_spec_statement_case();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop489;
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
		_loop502:
		do {
			if ((LA(1)==CONTINUES||LA(1)==CONTINUES_REDUNDANTLY)) {
				continues_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop502;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			continues_clause_seq_opt_AST = (AST)currentAST.root;
			
			continues_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(CONT_SEQ,"continues_seq")).add(continues_clause_seq_opt_AST));
			
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
		_loop513:
		do {
			if ((LA(1)==BREAKS||LA(1)==BREAKS_REDUNDANTLY)) {
				breaks_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop513;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			breaks_clause_seq_opt_AST = (AST)currentAST.root;
			
			breaks_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(BREAKS_SEQ,"breaks_seq")).add(breaks_clause_seq_opt_AST));
			
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
		_loop523:
		do {
			if ((LA(1)==RETURNS||LA(1)==RETURNS_REDUNDANTLY)) {
				returns_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop523;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			returns_clause_seq_opt_AST = (AST)currentAST.root;
			
			returns_clause_seq_opt_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(RETURNS_SEQ,"returns_seq")).add(returns_clause_seq_opt_AST));
			
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
		int _cnt505=0;
		_loop505:
		do {
			if ((LA(1)==CONTINUES||LA(1)==CONTINUES_REDUNDANTLY)) {
				continues_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt505>=1 ) { break _loop505; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt505++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			continues_clause_seq_AST = (AST)currentAST.root;
			
			continues_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(CONT_SEQ,"continues_seq")).add(continues_clause_seq_AST));
			
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
		int _cnt516=0;
		_loop516:
		do {
			if ((LA(1)==BREAKS||LA(1)==BREAKS_REDUNDANTLY)) {
				breaks_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt516>=1 ) { break _loop516; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt516++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			breaks_clause_seq_AST = (AST)currentAST.root;
			
			breaks_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(BREAKS_SEQ,"breaks_seq")).add(breaks_clause_seq_AST));
			
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
		int _cnt526=0;
		_loop526:
		do {
			if ((LA(1)==RETURNS||LA(1)==RETURNS_REDUNDANTLY)) {
				returns_clause();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt526>=1 ) { break _loop526; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt526++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			returns_clause_seq_AST = (AST)currentAST.root;
			
			returns_clause_seq_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(RETURNS_SEQ,"returns_seq")).add(returns_clause_seq_AST));
			
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			diverges_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			continues_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			breaks_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			returns_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			abrupt_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case DIVERGES:
		case DIVERGES_REDUNDANTLY:
		{
			diverges_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			continues_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			breaks_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			returns_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			abrupt_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case CONTINUES:
		case CONTINUES_REDUNDANTLY:
		{
			continues_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			breaks_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			returns_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			abrupt_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case BREAKS:
		case BREAKS_REDUNDANTLY:
		{
			breaks_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			returns_clause_seq_opt();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			abrupt_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case RETURNS:
		case RETURNS_REDUNDANTLY:
		{
			returns_clause_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			abrupt_spec_case_body_AST = (AST)currentAST.root;
			break;
		}
		case LCURLY_VBAR:
		{
			AST tmp360_AST = null;
			if (inputState.guessing==0) {
				tmp360_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp360_AST);
			}
			match(LCURLY_VBAR);
			abrupt_spec_case_seq();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp361_AST = null;
			if (inputState.guessing==0) {
				tmp361_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp361_AST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop499:
		do {
			if ((LA(1)==ALSO)) {
				AST tmp362_AST = null;
				if (inputState.guessing==0) {
					tmp362_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp362_AST);
				}
				match(ALSO);
				abrupt_spec_case();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop499;
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
				AST tmp363_AST = null;
				if (inputState.guessing==0) {
					tmp363_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp363_AST);
				}
				match(CONTINUES);
				break;
			}
			case CONTINUES_REDUNDANTLY:
			{
				AST tmp364_AST = null;
				if (inputState.guessing==0) {
					tmp364_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp364_AST);
				}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
				AST tmp365_AST = null;
				if (inputState.guessing==0) {
					tmp365_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp365_AST);
				}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			AST tmp366_AST = null;
			tmp366_AST = (AST)astFactory.create(LT(1));
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
		
		AST tmp367_AST = null;
		if (inputState.guessing==0) {
			tmp367_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp367_AST);
		}
		match(R_ARROW);
		AST tmp368_AST = null;
		tmp368_AST = (AST)astFactory.create(LT(1));
		match(LPAREN);
		AST tmp369_AST = null;
		if (inputState.guessing==0) {
			tmp369_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp369_AST);
		}
		match(IDENT);
		AST tmp370_AST = null;
		tmp370_AST = (AST)astFactory.create(LT(1));
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
				AST tmp371_AST = null;
				if (inputState.guessing==0) {
					tmp371_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp371_AST);
				}
				match(BREAKS);
				break;
			}
			case BREAKS_REDUNDANTLY:
			{
				AST tmp372_AST = null;
				if (inputState.guessing==0) {
					tmp372_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp372_AST);
				}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
				AST tmp373_AST = null;
				if (inputState.guessing==0) {
					tmp373_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp373_AST);
				}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			AST tmp374_AST = null;
			tmp374_AST = (AST)astFactory.create(LT(1));
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
				AST tmp375_AST = null;
				if (inputState.guessing==0) {
					tmp375_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp375_AST);
				}
				match(RETURNS);
				break;
			}
			case RETURNS_REDUNDANTLY:
			{
				AST tmp376_AST = null;
				if (inputState.guessing==0) {
					tmp376_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp376_AST);
				}
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
				AST tmp377_AST = null;
				if (inputState.guessing==0) {
					tmp377_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp377_AST);
				}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			AST tmp378_AST = null;
			tmp378_AST = (AST)astFactory.create(LT(1));
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
			AST tmp379_AST = null;
			if (inputState.guessing==0) {
				tmp379_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp379_AST);
			}
			match(MAINTAINING);
			break;
		}
		case MAINTAINING_REDUNDANTLY:
		{
			AST tmp380_AST = null;
			if (inputState.guessing==0) {
				tmp380_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp380_AST);
			}
			match(MAINTAINING_REDUNDANTLY);
			break;
		}
		case LOOP_INVARIANT:
		{
			AST tmp381_AST = null;
			if (inputState.guessing==0) {
				tmp381_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp381_AST);
			}
			match(LOOP_INVARIANT);
			break;
		}
		case LOOP_INVARIANT_REDUNDANTLY:
		{
			AST tmp382_AST = null;
			if (inputState.guessing==0) {
				tmp382_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp382_AST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp383_AST = null;
		tmp383_AST = (AST)astFactory.create(LT(1));
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
			AST tmp384_AST = null;
			if (inputState.guessing==0) {
				tmp384_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp384_AST);
			}
			match(DECREASING);
			break;
		}
		case DECREASING_REDUNDANTLY:
		{
			AST tmp385_AST = null;
			if (inputState.guessing==0) {
				tmp385_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp385_AST);
			}
			match(DECREASING_REDUNDANTLY);
			break;
		}
		case DECREASES:
		{
			AST tmp386_AST = null;
			if (inputState.guessing==0) {
				tmp386_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp386_AST);
			}
			match(DECREASES);
			break;
		}
		case DECREASES_REDUNDANTLY:
		{
			AST tmp387_AST = null;
			if (inputState.guessing==0) {
				tmp387_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp387_AST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp388_AST = null;
		tmp388_AST = (AST)astFactory.create(LT(1));
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
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
				if (inputState.guessing==0) {
					a_AST = (AST)astFactory.create(a);
					astFactory.makeASTRoot(currentAST, a_AST);
				}
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
					if (inputState.guessing==0) {
						b_AST = (AST)astFactory.create(b);
						astFactory.makeASTRoot(currentAST, b_AST);
					}
					match(PLUS_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = b.getLine(); col = b.getColumn();
					}
					break;
				}
				case MINUS_ASSIGN:
				{
					c = LT(1);
					if (inputState.guessing==0) {
						c_AST = (AST)astFactory.create(c);
						astFactory.makeASTRoot(currentAST, c_AST);
					}
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
					if (inputState.guessing==0) {
						d_AST = (AST)astFactory.create(d);
						astFactory.makeASTRoot(currentAST, d_AST);
					}
					match(STAR_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = d.getLine(); col = d.getColumn();
					}
					break;
				}
				case DIV_ASSIGN:
				{
					e = LT(1);
					if (inputState.guessing==0) {
						e_AST = (AST)astFactory.create(e);
						astFactory.makeASTRoot(currentAST, e_AST);
					}
					match(DIV_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = e.getLine(); col = e.getColumn();
					}
					break;
				}
				case MOD_ASSIGN:
				{
					f = LT(1);
					if (inputState.guessing==0) {
						f_AST = (AST)astFactory.create(f);
						astFactory.makeASTRoot(currentAST, f_AST);
					}
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
					if (inputState.guessing==0) {
						g_AST = (AST)astFactory.create(g);
						astFactory.makeASTRoot(currentAST, g_AST);
					}
					match(SR_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = g.getLine(); col = g.getColumn();
					}
					break;
				}
				case BSR_ASSIGN:
				{
					h = LT(1);
					if (inputState.guessing==0) {
						h_AST = (AST)astFactory.create(h);
						astFactory.makeASTRoot(currentAST, h_AST);
					}
					match(BSR_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = h.getLine(); col = h.getColumn();
					}
					break;
				}
				case SL_ASSIGN:
				{
					i = LT(1);
					if (inputState.guessing==0) {
						i_AST = (AST)astFactory.create(i);
						astFactory.makeASTRoot(currentAST, i_AST);
					}
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
					if (inputState.guessing==0) {
						j_AST = (AST)astFactory.create(j);
						astFactory.makeASTRoot(currentAST, j_AST);
					}
					match(BAND_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = j.getLine(); col = j.getColumn();
					}
					break;
				}
				case BOR_ASSIGN:
				{
					k = LT(1);
					if (inputState.guessing==0) {
						k_AST = (AST)astFactory.create(k);
						astFactory.makeASTRoot(currentAST, k_AST);
					}
					match(BOR_ASSIGN);
					if ( inputState.guessing==0 ) {
						line = k.getLine(); col = k.getColumn();
					}
					break;
				}
				case BXOR_ASSIGN:
				{
					l = LT(1);
					if (inputState.guessing==0) {
						l_AST = (AST)astFactory.create(l);
						astFactory.makeASTRoot(currentAST, l_AST);
					}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop556:
		do {
			if ((LA(1)==EQUIV||LA(1)==NOT_EQUIV)) {
				{
				switch ( LA(1)) {
				case EQUIV:
				{
					e = LT(1);
					if (inputState.guessing==0) {
						e_AST = (AST)astFactory.create(e);
						astFactory.makeASTRoot(currentAST, e_AST);
					}
					match(EQUIV);
					if ( inputState.guessing==0 ) {
						line = e.getLine(); col = e.getColumn();
					}
					break;
				}
				case NOT_EQUIV:
				{
					n = LT(1);
					if (inputState.guessing==0) {
						n_AST = (AST)astFactory.create(n);
						astFactory.makeASTRoot(currentAST, n_AST);
					}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
				break _loop556;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
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
				if (inputState.guessing==0) {
					li_AST = (AST)astFactory.create(li);
					astFactory.makeASTRoot(currentAST, li_AST);
				}
				match(LIMPLIES);
				implies_non_backward_expr(in_spec);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			int _cnt561=0;
			_loop561:
			do {
				if ((LA(1)==BACKWARD_IMPLIES)) {
					bi = LT(1);
					if (inputState.guessing==0) {
						bi_AST = (AST)astFactory.create(bi);
						astFactory.makeASTRoot(currentAST, bi_AST);
					}
					match(BACKWARD_IMPLIES);
					logical_or_expr(in_spec);
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
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
					if ( _cnt561>=1 ) { break _loop561; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt561++;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop566:
		do {
			if ((LA(1)==LOR)) {
				AST tmp389_AST = null;
				if (inputState.guessing==0) {
					tmp389_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp389_AST);
				}
				match(LOR);
				logical_and_expr(in_spec);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				if ( inputState.guessing==0 ) {
					logical_or_expr_AST = (AST)currentAST.root;
					logical_or_expr_AST.setType(LOGICAL_OP);
				}
			}
			else {
				break _loop566;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		switch ( LA(1)) {
		case LIMPLIES:
		{
			li = LT(1);
			if (inputState.guessing==0) {
				li_AST = (AST)astFactory.create(li);
				astFactory.makeASTRoot(currentAST, li_AST);
			}
			match(LIMPLIES);
			implies_non_backward_expr(in_spec);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop569:
		do {
			if ((LA(1)==LAND)) {
				AST tmp390_AST = null;
				if (inputState.guessing==0) {
					tmp390_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp390_AST);
				}
				match(LAND);
				inclusive_or_expr(in_spec);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				if ( inputState.guessing==0 ) {
					logical_and_expr_AST = (AST)currentAST.root;
					logical_and_expr_AST.setType(LOGICAL_OP);
				}
			}
			else {
				break _loop569;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop572:
		do {
			if ((LA(1)==BOR)) {
				AST tmp391_AST = null;
				if (inputState.guessing==0) {
					tmp391_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp391_AST);
				}
				match(BOR);
				exclusive_or_expr(in_spec);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				if ( inputState.guessing==0 ) {
					inclusive_or_expr_AST = (AST)currentAST.root;
					inclusive_or_expr_AST.setType(BITWISE_OP);
				}
			}
			else {
				break _loop572;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop575:
		do {
			if ((LA(1)==BXOR)) {
				AST tmp392_AST = null;
				if (inputState.guessing==0) {
					tmp392_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp392_AST);
				}
				match(BXOR);
				and_expr(in_spec);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				if ( inputState.guessing==0 ) {
					exclusive_or_expr_AST = (AST)currentAST.root;
					exclusive_or_expr_AST.setType(BITWISE_OP);
				}
			}
			else {
				break _loop575;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop578:
		do {
			if ((LA(1)==BAND)) {
				AST tmp393_AST = null;
				if (inputState.guessing==0) {
					tmp393_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp393_AST);
				}
				match(BAND);
				equality_expr(in_spec);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				if ( inputState.guessing==0 ) {
					and_expr_AST = (AST)currentAST.root;
					and_expr_AST.setType(BITWISE_OP);
				}
			}
			else {
				break _loop578;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop582:
		do {
			if ((LA(1)==NOT_EQUAL||LA(1)==EQUAL)) {
				{
				switch ( LA(1)) {
				case NOT_EQUAL:
				{
					AST tmp394_AST = null;
					if (inputState.guessing==0) {
						tmp394_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp394_AST);
					}
					match(NOT_EQUAL);
					break;
				}
				case EQUAL:
				{
					AST tmp395_AST = null;
					if (inputState.guessing==0) {
						tmp395_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp395_AST);
					}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				if ( inputState.guessing==0 ) {
					equality_expr_AST = (AST)currentAST.root;
					equality_expr_AST.setType(EQUALITY_OP);
				}
			}
			else {
				break _loop582;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
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
			_loop588:
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
							AST tmp396_AST = null;
							if (inputState.guessing==0) {
								tmp396_AST = (AST)astFactory.create(LT(1));
								astFactory.makeASTRoot(currentAST, tmp396_AST);
							}
							match(LT);
							break;
						}
						case GT:
						{
							AST tmp397_AST = null;
							if (inputState.guessing==0) {
								tmp397_AST = (AST)astFactory.create(LT(1));
								astFactory.makeASTRoot(currentAST, tmp397_AST);
							}
							match(GT);
							break;
						}
						case LE:
						{
							AST tmp398_AST = null;
							if (inputState.guessing==0) {
								tmp398_AST = (AST)astFactory.create(LT(1));
								astFactory.makeASTRoot(currentAST, tmp398_AST);
							}
							match(LE);
							break;
						}
						case GE:
						{
							AST tmp399_AST = null;
							if (inputState.guessing==0) {
								tmp399_AST = (AST)astFactory.create(LT(1));
								astFactory.makeASTRoot(currentAST, tmp399_AST);
							}
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
						if (inputState.guessing==0) {
							iso_AST = (AST)astFactory.create(iso);
							astFactory.makeASTRoot(currentAST, iso_AST);
						}
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
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
				}
				else {
					break _loop588;
				}
				
			} while (true);
			}
			break;
		}
		case LITERAL_instanceof:
		{
			AST tmp400_AST = null;
			if (inputState.guessing==0) {
				tmp400_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp400_AST);
			}
			match(LITERAL_instanceof);
			type_spec();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop592:
		do {
			if (((LA(1) >= SL && LA(1) <= BSR))) {
				{
				switch ( LA(1)) {
				case SL:
				{
					AST tmp401_AST = null;
					if (inputState.guessing==0) {
						tmp401_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp401_AST);
					}
					match(SL);
					break;
				}
				case SR:
				{
					AST tmp402_AST = null;
					if (inputState.guessing==0) {
						tmp402_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp402_AST);
					}
					match(SR);
					break;
				}
				case BSR:
				{
					AST tmp403_AST = null;
					if (inputState.guessing==0) {
						tmp403_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp403_AST);
					}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				if ( inputState.guessing==0 ) {
					shift_expr_AST = (AST)currentAST.root;
					shift_expr_AST.setType(SHIFT_OP);
				}
			}
			else {
				break _loop592;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop596:
		do {
			if ((LA(1)==PLUS||LA(1)==MINUS)) {
				{
				switch ( LA(1)) {
				case PLUS:
				{
					AST tmp404_AST = null;
					if (inputState.guessing==0) {
						tmp404_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp404_AST);
					}
					match(PLUS);
					break;
				}
				case MINUS:
				{
					AST tmp405_AST = null;
					if (inputState.guessing==0) {
						tmp405_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp405_AST);
					}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				if ( inputState.guessing==0 ) {
					additive_expr_AST = (AST)currentAST.root;
					additive_expr_AST.setType(ADDITIVE_OP);
				}
			}
			else {
				break _loop596;
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop600:
		do {
			if ((_tokenSet_46.member(LA(1)))) {
				{
				switch ( LA(1)) {
				case STAR:
				{
					AST tmp406_AST = null;
					if (inputState.guessing==0) {
						tmp406_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp406_AST);
					}
					match(STAR);
					break;
				}
				case DIV:
				{
					AST tmp407_AST = null;
					if (inputState.guessing==0) {
						tmp407_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp407_AST);
					}
					match(DIV);
					break;
				}
				case MOD:
				{
					AST tmp408_AST = null;
					if (inputState.guessing==0) {
						tmp408_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp408_AST);
					}
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				if ( inputState.guessing==0 ) {
					mult_expr_AST = (AST)currentAST.root;
					mult_expr_AST.setType(MULTIPLICATIVE_OP);
				}
			}
			else {
				break _loop600;
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
				if (inputState.guessing==0) {
					i_AST = (AST)astFactory.create(i);
					astFactory.makeASTRoot(currentAST, i_AST);
				}
				match(INC);
				if ( inputState.guessing==0 ) {
					line = i.getLine(); col = i.getColumn();
				}
				break;
			}
			case DEC:
			{
				d = LT(1);
				if (inputState.guessing==0) {
					d_AST = (AST)astFactory.create(d);
					astFactory.makeASTRoot(currentAST, d_AST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
				AST tmp409_AST = null;
				if (inputState.guessing==0) {
					tmp409_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp409_AST);
				}
				match(PLUS);
				break;
			}
			case MINUS:
			{
				AST tmp410_AST = null;
				if (inputState.guessing==0) {
					tmp410_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp410_AST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			AST tmp411_AST = null;
			if (inputState.guessing==0) {
				tmp411_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp411_AST);
			}
			match(BNOT);
			unary_expr(in_spec);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			if ( inputState.guessing==0 ) {
				unaryExpressionNotPlusMinus_AST = (AST)currentAST.root;
				unaryExpressionNotPlusMinus_AST.setType(UNARY_NUMERIC_OP);
			}
			unaryExpressionNotPlusMinus_AST = (AST)currentAST.root;
			break;
		}
		case LNOT:
		{
			AST tmp412_AST = null;
			if (inputState.guessing==0) {
				tmp412_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp412_AST);
			}
			match(LNOT);
			unary_expr(in_spec);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
				AST tmp413_AST = null;
				if (inputState.guessing==0) {
					tmp413_AST = (AST)astFactory.create(LT(1));
				}
				match(LPAREN);
				builtInType_spec();
				if (inputState.guessing==0) {
					t_AST = (AST)returnAST;
				}
				AST tmp414_AST = null;
				if (inputState.guessing==0) {
					tmp414_AST = (AST)astFactory.create(LT(1));
				}
				match(RPAREN);
				unary_expr(in_spec);
				if (inputState.guessing==0) {
					c_AST = (AST)returnAST;
				}
				if ( inputState.guessing==0 ) {
					unaryExpressionNotPlusMinus_AST = (AST)currentAST.root;
					unaryExpressionNotPlusMinus_AST = (AST)astFactory.make( (new ASTArray(3)).add((AST)astFactory.create(CAST,"cast")).add(t_AST).add(c_AST));
					currentAST.root = unaryExpressionNotPlusMinus_AST;
					currentAST.child = unaryExpressionNotPlusMinus_AST!=null &&unaryExpressionNotPlusMinus_AST.getFirstChild()!=null ?
						unaryExpressionNotPlusMinus_AST.getFirstChild() : unaryExpressionNotPlusMinus_AST;
					currentAST.advanceChildToEnd();
				}
			}
			else {
				boolean synPredMatched607 = false;
				if (((LA(1)==LPAREN) && (LA(2)==IDENT))) {
					int _m607 = mark();
					synPredMatched607 = true;
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
						synPredMatched607 = false;
					}
					rewind(_m607);
					inputState.guessing--;
				}
				if ( synPredMatched607 ) {
					AST tmp415_AST = null;
					if (inputState.guessing==0) {
						tmp415_AST = (AST)astFactory.create(LT(1));
					}
					match(LPAREN);
					reference_type_spec();
					if (inputState.guessing==0) {
						t2_AST = (AST)returnAST;
					}
					AST tmp416_AST = null;
					if (inputState.guessing==0) {
						tmp416_AST = (AST)astFactory.create(LT(1));
					}
					match(RPAREN);
					unaryExpressionNotPlusMinus(in_spec);
					if (inputState.guessing==0) {
						c2_AST = (AST)returnAST;
					}
					if ( inputState.guessing==0 ) {
						unaryExpressionNotPlusMinus_AST = (AST)currentAST.root;
						unaryExpressionNotPlusMinus_AST = (AST)astFactory.make( (new ASTArray(3)).add((AST)astFactory.create(CAST,"cast")).add(t2_AST).add(c2_AST));
						currentAST.root = unaryExpressionNotPlusMinus_AST;
						currentAST.child = unaryExpressionNotPlusMinus_AST!=null &&unaryExpressionNotPlusMinus_AST.getFirstChild()!=null ?
							unaryExpressionNotPlusMinus_AST.getFirstChild() : unaryExpressionNotPlusMinus_AST;
						currentAST.advanceChildToEnd();
					}
				}
				else if ((_tokenSet_48.member(LA(1))) && (_tokenSet_49.member(LA(2)))) {
					postfix_expr(in_spec);
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
					}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		switch ( LA(1)) {
		case LBRACK:
		{
			dims();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
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
		builtInType_spec_AST = (AST)currentAST.root;
		returnAST = builtInType_spec_AST;
	}
	
	public final void reference_type_spec() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST reference_type_spec_AST = null;
		
		reference_type();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		switch ( LA(1)) {
		case LBRACK:
		{
			dims();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			_loop619:
			do {
				switch ( LA(1)) {
				case DOT:
				{
					AST tmp417_AST = null;
					if (inputState.guessing==0) {
						tmp417_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp417_AST);
					}
					match(DOT);
					{
					switch ( LA(1)) {
					case IDENT:
					{
						AST tmp418_AST = null;
						if (inputState.guessing==0) {
							tmp418_AST = (AST)astFactory.create(LT(1));
							astFactory.addASTChild(currentAST, tmp418_AST);
						}
						match(IDENT);
						break;
					}
					case LITERAL_this:
					{
						AST tmp419_AST = null;
						if (inputState.guessing==0) {
							tmp419_AST = (AST)astFactory.create(LT(1));
							astFactory.addASTChild(currentAST, tmp419_AST);
						}
						match(LITERAL_this);
						break;
					}
					case LITERAL_class:
					{
						AST tmp420_AST = null;
						if (inputState.guessing==0) {
							tmp420_AST = (AST)astFactory.create(LT(1));
							astFactory.addASTChild(currentAST, tmp420_AST);
						}
						match(LITERAL_class);
						break;
					}
					case LITERAL_new:
					{
						new_expr(in_spec);
						if (inputState.guessing==0) {
							astFactory.addASTChild(currentAST, returnAST);
						}
						break;
					}
					case LITERAL_super:
					{
						AST tmp421_AST = null;
						if (inputState.guessing==0) {
							tmp421_AST = (AST)astFactory.create(LT(1));
							astFactory.addASTChild(currentAST, tmp421_AST);
						}
						match(LITERAL_super);
						AST tmp422_AST = null;
						if (inputState.guessing==0) {
							tmp422_AST = (AST)astFactory.create(LT(1));
							astFactory.makeASTRoot(currentAST, tmp422_AST);
						}
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
							if (inputState.guessing==0) {
								astFactory.addASTChild(currentAST, returnAST);
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
						AST tmp423_AST = null;
						if (inputState.guessing==0) {
							tmp423_AST = (AST)astFactory.create(LT(1));
							astFactory.addASTChild(currentAST, tmp423_AST);
						}
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
					AST tmp424_AST = null;
					if (inputState.guessing==0) {
						tmp424_AST = (AST)astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp424_AST);
					}
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
						if (inputState.guessing==0) {
							astFactory.addASTChild(currentAST, returnAST);
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
					AST tmp425_AST = null;
					tmp425_AST = (AST)astFactory.create(LT(1));
					match(RPAREN);
					break;
				}
				default:
					if ((LA(1)==LBRACK) && (LA(2)==RBRACK)) {
						{
						int _cnt617=0;
						_loop617:
						do {
							if ((LA(1)==LBRACK)) {
								lbc = LT(1);
								if (inputState.guessing==0) {
									lbc_AST = (AST)astFactory.create(lbc);
									astFactory.makeASTRoot(currentAST, lbc_AST);
								}
								match(LBRACK);
								if ( inputState.guessing==0 ) {
									lbc_AST.setType(ARRAY_DECLARATOR);
									lbc_AST.setText("array_declarator");
									
								}
								AST tmp426_AST = null;
								tmp426_AST = (AST)astFactory.create(LT(1));
								match(RBRACK);
							}
							else {
								if ( _cnt617>=1 ) { break _loop617; } else {throw new NoViableAltException(LT(1), getFilename());}
							}
							
							_cnt617++;
						} while (true);
						}
						AST tmp427_AST = null;
						if (inputState.guessing==0) {
							tmp427_AST = (AST)astFactory.create(LT(1));
							astFactory.makeASTRoot(currentAST, tmp427_AST);
						}
						match(DOT);
						AST tmp428_AST = null;
						if (inputState.guessing==0) {
							tmp428_AST = (AST)astFactory.create(LT(1));
							astFactory.addASTChild(currentAST, tmp428_AST);
						}
						match(LITERAL_class);
					}
					else if ((LA(1)==LBRACK) && (_tokenSet_35.member(LA(2)))) {
						AST tmp429_AST = null;
						if (inputState.guessing==0) {
							tmp429_AST = (AST)astFactory.create(LT(1));
							astFactory.makeASTRoot(currentAST, tmp429_AST);
						}
						match(LBRACK);
						expression(in_spec);
						if (inputState.guessing==0) {
							astFactory.addASTChild(currentAST, returnAST);
						}
						AST tmp430_AST = null;
						tmp430_AST = (AST)astFactory.create(LT(1));
						match(RBRACK);
					}
				else {
					break _loop619;
				}
				}
			} while (true);
			}
			{
			switch ( LA(1)) {
			case INC:
			{
				in = LT(1);
				if (inputState.guessing==0) {
					in_AST = (AST)astFactory.create(in);
					astFactory.makeASTRoot(currentAST, in_AST);
				}
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
				if (inputState.guessing==0) {
					de_AST = (AST)astFactory.create(de);
					astFactory.makeASTRoot(currentAST, de_AST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			_loop622:
			do {
				if ((LA(1)==LBRACK)) {
					lbt = LT(1);
					if (inputState.guessing==0) {
						lbt_AST = (AST)astFactory.create(lbt);
						astFactory.makeASTRoot(currentAST, lbt_AST);
					}
					match(LBRACK);
					if ( inputState.guessing==0 ) {
						lbt_AST.setType(ARRAY_DECLARATOR);
						lbt_AST.setText("array_declarator");
						
					}
					AST tmp431_AST = null;
					tmp431_AST = (AST)astFactory.create(LT(1));
					match(RBRACK);
				}
				else {
					break _loop622;
				}
				
			} while (true);
			}
			AST tmp432_AST = null;
			if (inputState.guessing==0) {
				tmp432_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp432_AST);
			}
			match(DOT);
			AST tmp433_AST = null;
			if (inputState.guessing==0) {
				tmp433_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp433_AST);
			}
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
			if (inputState.guessing==0) {
				id_AST = (AST)astFactory.create(id);
				astFactory.addASTChild(currentAST, id_AST);
			}
			match(IDENT);
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_new:
		{
			new_expr(in_spec);
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		case STRING_LITERAL:
		case NUM_INT:
		case CHAR_LITERAL:
		case NUM_FLOAT:
		{
			constant();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_super:
		{
			AST tmp434_AST = null;
			if (inputState.guessing==0) {
				tmp434_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp434_AST);
			}
			match(LITERAL_super);
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_true:
		{
			AST tmp435_AST = null;
			if (inputState.guessing==0) {
				tmp435_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp435_AST);
			}
			match(LITERAL_true);
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_false:
		{
			AST tmp436_AST = null;
			if (inputState.guessing==0) {
				tmp436_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp436_AST);
			}
			match(LITERAL_false);
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_this:
		{
			AST tmp437_AST = null;
			if (inputState.guessing==0) {
				tmp437_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp437_AST);
			}
			match(LITERAL_this);
			primary_expr_AST = (AST)currentAST.root;
			break;
		}
		case LITERAL_null:
		{
			AST tmp438_AST = null;
			if (inputState.guessing==0) {
				tmp438_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp438_AST);
			}
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
			if (inputState.guessing==0) {
				jmlp_AST = (AST)returnAST;
				astFactory.addASTChild(currentAST, returnAST);
			}
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
			AST tmp439_AST = null;
			tmp439_AST = (AST)astFactory.create(LT(1));
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
				if (inputState.guessing==0) {
					sqe_AST = (AST)returnAST;
					astFactory.addASTChild(currentAST, returnAST);
				}
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
				if (inputState.guessing==0) {
					lbln_AST = (AST)astFactory.create(lbln);
					astFactory.makeASTRoot(currentAST, lbln_AST);
				}
				match(T_LBLNEG);
				AST tmp440_AST = null;
				if (inputState.guessing==0) {
					tmp440_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp440_AST);
				}
				match(IDENT);
				spec_expression();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
				if (inputState.guessing==0) {
					lblp_AST = (AST)astFactory.create(lblp);
					astFactory.makeASTRoot(currentAST, lblp_AST);
				}
				match(T_LBLPOS);
				AST tmp441_AST = null;
				if (inputState.guessing==0) {
					tmp441_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp441_AST);
				}
				match(IDENT);
				spec_expression();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			AST tmp442_AST = null;
			tmp442_AST = (AST)astFactory.create(LT(1));
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
		
		AST tmp443_AST = null;
		if (inputState.guessing==0) {
			tmp443_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp443_AST);
		}
		match(LITERAL_new);
		type();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		new_suffix(in_spec);
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
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
			AST tmp444_AST = null;
			if (inputState.guessing==0) {
				tmp444_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp444_AST);
			}
			match(NUM_INT);
			constant_AST = (AST)currentAST.root;
			break;
		}
		case CHAR_LITERAL:
		{
			AST tmp445_AST = null;
			if (inputState.guessing==0) {
				tmp445_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp445_AST);
			}
			match(CHAR_LITERAL);
			constant_AST = (AST)currentAST.root;
			break;
		}
		case STRING_LITERAL:
		{
			AST tmp446_AST = null;
			if (inputState.guessing==0) {
				tmp446_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp446_AST);
			}
			match(STRING_LITERAL);
			constant_AST = (AST)currentAST.root;
			break;
		}
		case NUM_FLOAT:
		{
			AST tmp447_AST = null;
			if (inputState.guessing==0) {
				tmp447_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp447_AST);
			}
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
			AST tmp448_AST = null;
			if (inputState.guessing==0) {
				tmp448_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp448_AST);
			}
			match(T_RESULT);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_OLD:
		{
			AST tmp449_AST = null;
			if (inputState.guessing==0) {
				tmp449_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp449_AST);
			}
			match(T_OLD);
			AST tmp450_AST = null;
			tmp450_AST = (AST)astFactory.create(LT(1));
			match(LPAREN);
			spec_expression();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp451_AST = null;
			tmp451_AST = (AST)astFactory.create(LT(1));
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_NOT_MODIFIED:
		{
			AST tmp452_AST = null;
			if (inputState.guessing==0) {
				tmp452_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp452_AST);
			}
			match(T_NOT_MODIFIED);
			AST tmp453_AST = null;
			tmp453_AST = (AST)astFactory.create(LT(1));
			match(LPAREN);
			store_references();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp454_AST = null;
			tmp454_AST = (AST)astFactory.create(LT(1));
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_FRESH:
		{
			AST tmp455_AST = null;
			if (inputState.guessing==0) {
				tmp455_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp455_AST);
			}
			match(T_FRESH);
			AST tmp456_AST = null;
			tmp456_AST = (AST)astFactory.create(LT(1));
			match(LPAREN);
			spec_expression_list();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp457_AST = null;
			tmp457_AST = (AST)astFactory.create(LT(1));
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_REACH:
		{
			AST tmp458_AST = null;
			if (inputState.guessing==0) {
				tmp458_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp458_AST);
			}
			match(T_REACH);
			AST tmp459_AST = null;
			tmp459_AST = (AST)astFactory.create(LT(1));
			match(LPAREN);
			spec_expression();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			switch ( LA(1)) {
			case COMMA:
			{
				AST tmp460_AST = null;
				tmp460_AST = (AST)astFactory.create(LT(1));
				match(COMMA);
				reference_type();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				{
				switch ( LA(1)) {
				case COMMA:
				{
					AST tmp461_AST = null;
					tmp461_AST = (AST)astFactory.create(LT(1));
					match(COMMA);
					store_ref_expression();
					if (inputState.guessing==0) {
						astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp462_AST = null;
			tmp462_AST = (AST)astFactory.create(LT(1));
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case INFORMAL_DESCRIPTION:
		{
			informal_desc();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_NONNULLELEMENTS:
		{
			AST tmp463_AST = null;
			if (inputState.guessing==0) {
				tmp463_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp463_AST);
			}
			match(T_NONNULLELEMENTS);
			AST tmp464_AST = null;
			tmp464_AST = (AST)astFactory.create(LT(1));
			match(LPAREN);
			spec_expression();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp465_AST = null;
			tmp465_AST = (AST)astFactory.create(LT(1));
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_TYPEOF:
		{
			AST tmp466_AST = null;
			if (inputState.guessing==0) {
				tmp466_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp466_AST);
			}
			match(T_TYPEOF);
			AST tmp467_AST = null;
			tmp467_AST = (AST)astFactory.create(LT(1));
			match(LPAREN);
			spec_expression();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp468_AST = null;
			tmp468_AST = (AST)astFactory.create(LT(1));
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_ELEMTYPE:
		{
			AST tmp469_AST = null;
			if (inputState.guessing==0) {
				tmp469_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp469_AST);
			}
			match(T_ELEMTYPE);
			AST tmp470_AST = null;
			tmp470_AST = (AST)astFactory.create(LT(1));
			match(LPAREN);
			spec_expression();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp471_AST = null;
			tmp471_AST = (AST)astFactory.create(LT(1));
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_TYPE:
		{
			AST tmp472_AST = null;
			if (inputState.guessing==0) {
				tmp472_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp472_AST);
			}
			match(T_TYPE);
			AST tmp473_AST = null;
			tmp473_AST = (AST)astFactory.create(LT(1));
			match(LPAREN);
			type();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp474_AST = null;
			tmp474_AST = (AST)astFactory.create(LT(1));
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_LOCKSET:
		{
			AST tmp475_AST = null;
			if (inputState.guessing==0) {
				tmp475_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp475_AST);
			}
			match(T_LOCKSET);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_IS_INITIALIZED:
		{
			AST tmp476_AST = null;
			if (inputState.guessing==0) {
				tmp476_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp476_AST);
			}
			match(T_IS_INITIALIZED);
			AST tmp477_AST = null;
			tmp477_AST = (AST)astFactory.create(LT(1));
			match(LPAREN);
			reference_type();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp478_AST = null;
			tmp478_AST = (AST)astFactory.create(LT(1));
			match(RPAREN);
			jml_primary_AST = (AST)currentAST.root;
			break;
		}
		case T_INVARIANT_FOR:
		{
			AST tmp479_AST = null;
			if (inputState.guessing==0) {
				tmp479_AST = (AST)astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp479_AST);
			}
			match(T_INVARIANT_FOR);
			AST tmp480_AST = null;
			tmp480_AST = (AST)astFactory.create(LT(1));
			match(LPAREN);
			spec_expression();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			AST tmp481_AST = null;
			tmp481_AST = (AST)astFactory.create(LT(1));
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		wrap_quantified_var_decl();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp482_AST = null;
		tmp482_AST = (AST)astFactory.create(LT(1));
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			switch ( LA(1)) {
			case SEMI:
			{
				AST tmp483_AST = null;
				tmp483_AST = (AST)astFactory.create(LT(1));
				match(SEMI);
				spec_expression();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
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
			break;
		}
		case SEMI:
		{
			AST tmp484_AST = null;
			tmp484_AST = (AST)astFactory.create(LT(1));
			match(SEMI);
			spec_expression();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
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
			spec_quantified_expr_AST = (AST)currentAST.root;
			spec_quantified_expr_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(QUANTIFIED_EXPR,"quantified_exp")).add(spec_quantified_expr_AST));
			
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
			AST tmp485_AST = null;
			tmp485_AST = (AST)astFactory.create(LT(1));
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
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp486_AST = null;
			tmp486_AST = (AST)astFactory.create(LT(1));
			match(RPAREN);
			{
			switch ( LA(1)) {
			case LCURLY:
			{
				class_block(in_spec, no_jml_stmts);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
			{
			switch ( LA(1)) {
			case LCURLY:
			{
				array_initializer(in_spec);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
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
			if (inputState.guessing==0) {
				sce_AST = (AST)returnAST;
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		int _cnt638=0;
		_loop638:
		do {
			if ((LA(1)==LBRACK) && (_tokenSet_35.member(LA(2)))) {
				dim_exprs(in_spec);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else if ((LA(1)==LBRACK) && (LA(2)==RBRACK)) {
				dims();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				if ( _cnt638>=1 ) { break _loop638; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt638++;
		} while (true);
		}
		array_decl_AST = (AST)currentAST.root;
		returnAST = array_decl_AST;
	}
	
	public final void set_comprehension() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST set_comprehension_AST = null;
		
		AST tmp487_AST = null;
		tmp487_AST = (AST)astFactory.create(LT(1));
		match(LCURLY);
		type_spec();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		quantified_var_declarator();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp488_AST = null;
		tmp488_AST = (AST)astFactory.create(LT(1));
		match(BOR);
		set_comprehension_pred();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp489_AST = null;
		tmp489_AST = (AST)astFactory.create(LT(1));
		match(RCURLY);
		if ( inputState.guessing==0 ) {
			set_comprehension_AST = (AST)currentAST.root;
			set_comprehension_AST = 
			(AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(SET_COMPR,"#set_compr#")).add(set_comprehension_AST));
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
		int _cnt641=0;
		_loop641:
		do {
			if ((LA(1)==LBRACK) && (_tokenSet_35.member(LA(2)))) {
				AST tmp490_AST = null;
				if (inputState.guessing==0) {
					tmp490_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp490_AST);
				}
				match(LBRACK);
				expression(in_spec);
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
				AST tmp491_AST = null;
				tmp491_AST = (AST)astFactory.create(LT(1));
				match(RBRACK);
			}
			else {
				if ( _cnt641>=1 ) { break _loop641; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt641++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			dim_exprs_AST = (AST)currentAST.root;
			dim_exprs_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(DIM_EXPRS,"#dim_exprs#")).add(dim_exprs_AST));
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
		
		AST tmp492_AST = null;
		if (inputState.guessing==0) {
			tmp492_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp492_AST);
		}
		match(IDENT);
		{
		switch ( LA(1)) {
		case LBRACK:
		{
			dims();
			if (inputState.guessing==0) {
				astFactory.addASTChild(currentAST, returnAST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		AST tmp493_AST = null;
		if (inputState.guessing==0) {
			tmp493_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp493_AST);
		}
		match(LAND);
		predicate();
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		int _cnt650=0;
		_loop650:
		do {
			if ((LA(1)==DOT)) {
				AST tmp494_AST = null;
				if (inputState.guessing==0) {
					tmp494_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp494_AST);
				}
				match(DOT);
				AST tmp495_AST = null;
				if (inputState.guessing==0) {
					tmp495_AST = (AST)astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp495_AST);
				}
				match(IDENT);
			}
			else {
				if ( _cnt650>=1 ) { break _loop650; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt650++;
		} while (true);
		}
		AST tmp496_AST = null;
		if (inputState.guessing==0) {
			tmp496_AST = (AST)astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp496_AST);
		}
		match(LPAREN);
		{
		AST tmp497_AST = null;
		if (inputState.guessing==0) {
			tmp497_AST = (AST)astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp497_AST);
		}
		match(IDENT);
		}
		AST tmp498_AST = null;
		tmp498_AST = (AST)astFactory.create(LT(1));
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
			AST tmp499_AST = null;
			if (inputState.guessing==0) {
				tmp499_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp499_AST);
			}
			match(T_FORALL);
			break;
		}
		case T_EXISTS:
		{
			AST tmp500_AST = null;
			if (inputState.guessing==0) {
				tmp500_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp500_AST);
			}
			match(T_EXISTS);
			break;
		}
		case T_MAX:
		{
			AST tmp501_AST = null;
			if (inputState.guessing==0) {
				tmp501_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp501_AST);
			}
			match(T_MAX);
			break;
		}
		case T_MIN:
		{
			AST tmp502_AST = null;
			if (inputState.guessing==0) {
				tmp502_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp502_AST);
			}
			match(T_MIN);
			break;
		}
		case T_SUM:
		{
			AST tmp503_AST = null;
			if (inputState.guessing==0) {
				tmp503_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp503_AST);
			}
			match(T_SUM);
			break;
		}
		case T_PRODUCT:
		{
			AST tmp504_AST = null;
			if (inputState.guessing==0) {
				tmp504_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp504_AST);
			}
			match(T_PRODUCT);
			break;
		}
		case T_NUM_OF:
		{
			AST tmp505_AST = null;
			if (inputState.guessing==0) {
				tmp505_AST = (AST)astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp505_AST);
			}
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		if ( inputState.guessing==0 ) {
			wrap_quantified_var_decl_AST = (AST)currentAST.root;
			wrap_quantified_var_decl_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(QUANT_VARS,"quantified_vars")).add(wrap_quantified_var_decl_AST));
			
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
		if (inputState.guessing==0) {
			astFactory.addASTChild(currentAST, returnAST);
		}
		{
		_loop661:
		do {
			if ((LA(1)==COMMA)) {
				AST tmp506_AST = null;
				if (inputState.guessing==0) {
					tmp506_AST = (AST)astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp506_AST);
				}
				match(COMMA);
				quantified_var_declarator();
				if (inputState.guessing==0) {
					astFactory.addASTChild(currentAST, returnAST);
				}
			}
			else {
				break _loop661;
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
	
	private static final long _tokenSet_0_data_[] = { 0L, -287104476244869120L, 8556380223L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_0 = new BitSet(_tokenSet_0_data_);
	private static final long _tokenSet_1_data_[] = { 0L, -124974889659531264L, 1801008979795511423L, 4361803784168L, 0L, 4177920L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_1 = new BitSet(_tokenSet_1_data_);
	private static final long _tokenSet_2_data_[] = { 0L, -88946092640567296L, -424548958664065L, 4362609623022L, 9164825241698959360L, 33554430L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_2 = new BitSet(_tokenSet_2_data_);
	private static final long _tokenSet_3_data_[] = { 0L, 162129586585337856L, 562949953423424L, 0L, 0L, 4177920L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_3 = new BitSet(_tokenSet_3_data_);
	private static final long _tokenSet_4_data_[] = { 0L, 54043195528445952L, -9223372036854710272L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_4 = new BitSet(_tokenSet_4_data_);
	private static final long _tokenSet_5_data_[] = { 0L, 18014398509481984L, 1800313951041355776L, 4361803784168L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_5 = new BitSet(_tokenSet_5_data_);
	private static final long _tokenSet_6_data_[] = { 0L, -124974889659531264L, 9219437717931229759L, 4362609623022L, 9164825241698959360L, 33554430L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_6 = new BitSet(_tokenSet_6_data_);
	private static final long _tokenSet_7_data_[] = { 0L, 0L, 132070244352000L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_7 = new BitSet(_tokenSet_7_data_);
	private static final long _tokenSet_8_data_[] = { 0L, -9046605751480483840L, 32094226873385541L, 9162565743424052736L, 9164825243838098432L, 33554430L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_8 = new BitSet(_tokenSet_8_data_);
	private static final long _tokenSet_9_data_[] = { 0L, 162129586585337856L, 562949953421312L, 0L, 0L, 4177920L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_9 = new BitSet(_tokenSet_9_data_);
	private static final long _tokenSet_10_data_[] = { 0L, 54043195528445952L, -9223372036854775808L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_10 = new BitSet(_tokenSet_10_data_);
	private static final long _tokenSet_11_data_[] = { 0L, -124974889659531264L, 562958509801535L, 0L, 0L, 4177920L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_11 = new BitSet(_tokenSet_11_data_);
	private static final long _tokenSet_12_data_[] = { 0L, -88946092640567296L, -9222809078344908737L, 0L, 0L, 4177920L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_12 = new BitSet(_tokenSet_12_data_);
	private static final long _tokenSet_13_data_[] = { 0L, 22799473113563136L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_13 = new BitSet(_tokenSet_13_data_);
	private static final long _tokenSet_14_data_[] = { 2L, -270778927595651072L, 8556382335L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_14 = new BitSet(_tokenSet_14_data_);
	private static final long _tokenSet_15_data_[] = { 2L, -252764529086169088L, 8556382335L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_15 = new BitSet(_tokenSet_15_data_);
	private static final long _tokenSet_16_data_[] = { 0L, 23080948090273792L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_16 = new BitSet(_tokenSet_16_data_);
	private static final long _tokenSet_17_data_[] = { 2L, -271341877549072384L, 8556382335L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_17 = new BitSet(_tokenSet_17_data_);
	private static final long _tokenSet_18_data_[] = { 2L, -253327479039590400L, 8556382335L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_18 = new BitSet(_tokenSet_18_data_);
	private static final long _tokenSet_19_data_[] = { 0L, 25895697857380352L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_19 = new BitSet(_tokenSet_19_data_);
	private static final long _tokenSet_20_data_[] = { 0L, -273593677362757632L, 8556382335L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_20 = new BitSet(_tokenSet_20_data_);
	private static final long _tokenSet_21_data_[] = { 0L, -111464090777419776L, 1801290454772222591L, 4361803784168L, 0L, 4177920L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_21 = new BitSet(_tokenSet_21_data_);
	private static final long _tokenSet_22_data_[] = { 0L, 18014398509481984L, 568997269537280L, 0L, 9164825241698959360L, 33554430L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_22 = new BitSet(_tokenSet_22_data_);
	private static final long _tokenSet_23_data_[] = { 0L, 18014398509481984L, 1924145348608L, 805314560L, 0L, 8192L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_23 = new BitSet(_tokenSet_23_data_);
	private static final long _tokenSet_24_data_[] = { 0L, 18014398509481984L, 568997269536768L, 8192L, 9164825241698959360L, 33554430L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_24 = new BitSet(_tokenSet_24_data_);
	private static final long _tokenSet_25_data_[] = { 0L, 0L, 0L, 1031056392200L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_25 = new BitSet(_tokenSet_25_data_);
	private static final long _tokenSet_26_data_[] = { 0L, 18014398509481984L, 1924145414144L, 1031861960648L, 0L, 8192L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_26 = new BitSet(_tokenSet_26_data_);
	private static final long _tokenSet_27_data_[] = { 2L, -111464090777419776L, 1798631182823442047L, 9169325540911619600L, 9164825243838098432L, 33554430L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_27 = new BitSet(_tokenSet_27_data_);
	private static final long _tokenSet_28_data_[] = { 2L, -3377699720527872L, -143073981378945L, -1073741826L, -262145L, 4294967295L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_28 = new BitSet(_tokenSet_28_data_);
	private static final long _tokenSet_29_data_[] = { 0L, 0L, 0L, 32476495880L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_29 = new BitSet(_tokenSet_29_data_);
	private static final long _tokenSet_30_data_[] = { 0L, 18014398509481984L, 569272147443712L, 33282064328L, 9164825241698959360L, 33554430L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_30 = new BitSet(_tokenSet_30_data_);
	private static final long _tokenSet_31_data_[] = { 0L, -9046605751480483840L, 32094226873386565L, 9169325540911619584L, 9164825243838098432L, 33554430L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_31 = new BitSet(_tokenSet_31_data_);
	private static final long _tokenSet_32_data_[] = { 2L, -3377699720527872L, -7422075259887956353L, -1073741848L, -262145L, 4294967295L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_32 = new BitSet(_tokenSet_32_data_);
	private static final long _tokenSet_33_data_[] = { 0L, -9060116550362595328L, 562956395872256L, 0L, 0L, 4177920L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_33 = new BitSet(_tokenSet_33_data_);
	private static final long _tokenSet_34_data_[] = { 0L, -9024087753343631360L, -9222809080458903552L, 0L, 0L, 4177920L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_34 = new BitSet(_tokenSet_34_data_);
	private static final long _tokenSet_35_data_[] = { 0L, 18014398509481984L, 568997269536768L, 0L, 9164825241698959360L, 33554430L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_35 = new BitSet(_tokenSet_35_data_);
	private static final long _tokenSet_36_data_[] = { 0L, 135107988821114880L, -9222803039584714752L, -9223372036854775808L, -2147482625L, 4294967295L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_36 = new BitSet(_tokenSet_36_data_);
	private static final long _tokenSet_37_data_[] = { 0L, 135107988821114880L, -9222803039584706560L, -9223372036854775808L, -2147482625L, 4294967295L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_37 = new BitSet(_tokenSet_37_data_);
	private static final long _tokenSet_38_data_[] = { 0L, -9222246136947933184L, 6442450944L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_38 = new BitSet(_tokenSet_38_data_);
	private static final long _tokenSet_39_data_[] = { 0L, 18014398509481984L, 568997269536768L, 524288L, 9164825241698959360L, 33554430L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_39 = new BitSet(_tokenSet_39_data_);
	private static final long _tokenSet_40_data_[] = { 0L, 0L, 0L, 4361803530248L, 8060928L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_40 = new BitSet(_tokenSet_40_data_);
	private static final long _tokenSet_41_data_[] = { 0L, 27021597764222976L, 569272147443712L, 4362609098696L, 9164825241707282432L, 33554430L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_41 = new BitSet(_tokenSet_41_data_);
	private static final long _tokenSet_42_data_[] = { 0L, -9046605751480483840L, 33220126780229189L, 9169325540911619600L, 9164825243838098432L, 33554430L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_42 = new BitSet(_tokenSet_42_data_);
	private static final long _tokenSet_43_data_[] = { 2L, -3377699720527872L, -7422075259887956353L, -1073741832L, -262145L, 4294967295L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_43 = new BitSet(_tokenSet_43_data_);
	private static final long _tokenSet_44_data_[] = { 0L, 0L, 0L, 3298799124488L, 8060928L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_44 = new BitSet(_tokenSet_44_data_);
	private static final long _tokenSet_45_data_[] = { 0L, 27021597764222976L, 569272147443712L, 3299604692936L, 9164825241707282432L, 33554430L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_45 = new BitSet(_tokenSet_45_data_);
	private static final long _tokenSet_46_data_[] = { 0L, 72057594037927936L, 0L, 0L, 54043195528445952L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_46 = new BitSet(_tokenSet_46_data_);
	private static final long _tokenSet_47_data_[] = { 0L, 0L, 562949953421312L, 0L, 0L, 4177920L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_47 = new BitSet(_tokenSet_47_data_);
	private static final long _tokenSet_48_data_[] = { 0L, 18014398509481984L, 568997269536768L, 0L, 8070450532247928832L, 33554430L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_48 = new BitSet(_tokenSet_48_data_);
	private static final long _tokenSet_49_data_[] = { 2L, 135107988821114880L, -9222802902116260864L, -9223372035780247551L, -2147482625L, 4294967295L, 0L, 0L, 0L, 0L, 0L, 0L };
	public static final BitSet _tokenSet_49 = new BitSet(_tokenSet_49_data_);
	
	}
