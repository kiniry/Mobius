header {
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
}
{
import java.io.*;
import antlr.*;
//LB import edu.iastate.cs.jml.checker.attributes.*;
}class JmlDeclParser extends Parser;

options {
	k= 2;
	codeGenMakeSwitchThreshold= 2;
	codeGenBitsetTestThreshold= 3;
	defaultErrorHandler= false;
	buildAST= true;
	importVocab=Java;
}

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
}
type_definition :(doc_comment!)? modifiers class_or_interface_def
    |!  SEMI
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToTopLevelKeyword();
    }

field[boolean in_spec, boolean in_model_prog] {
    ModifierSet ms = null;
}
:!  // method, constructor, or variable declaration
        dc:((doc_comment)*)
        (   // Ambiguity:
            // the "static" keyword can occur
            // both as a modifier and as the beginning of
            // a static initalizer.  But Antlr generates looks for the
            // static initializer first.
            options {generateAmbigWarnings = false;} :
            // "static { ... }" class initializer
            "static" compound_statement[in_model_prog]
        | // "{ ... }" instance initializer
            compound_statement[in_model_prog]
        | mods:modifiers
                {
                    if (#mods instanceof LineAST) {
                        ms = ((MTypeAttrib)((LineAST)#mods).type).getModifiers();
                        in_spec = in_spec || ms.has(Modifier.MODEL)
                                          || ms.has(Modifier.GHOST);
                    }
                }
          ( m:member_decl[in_spec, in_model_prog]
                { #field = #(null, #mods, #m); }
          |! msfd:method_spec_first_decl[#mods, in_model_prog] // added for JML
                {
                    if( #msfd != null ) {
                        #field = #msfd;
                    }
                }
          | jml_declaration           // added for JML
          )
        )
    |!  axiom_pragma         // added for JML (from ESC/Java)
    |!  SEMI        // optional semi-colon
    ;
exception 
catch [RecognitionException err] {
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
    }

method_spec_first_decl[AST m, boolean in_model_prog] :!   mspec:method_specification[m]
        (   STATIC_INITIALIZER
        |   INITIALIZER
            
        | // "static { ... }" class initializer
            "static" compound_statement[in_model_prog]
        | // "{ ... }" instance initializer
            compound_statement[in_model_prog]
        | mods:modifiers
            ( ts:type_spec mh:method_head mb:method_body[in_model_prog]
                {
                    if( #mods != null )
                    {
                        #method_spec_first_decl = #mods;
                        #method_spec_first_decl.setNextSibling(
                        #( [METH, "#meth#"], ts, mh, [SEMI, ";"]) );
                    }  else {
                        #method_spec_first_decl = 
                            #( [METH, "#meth#"], ts, mh, [SEMI, ";"]);
                    }
                }
            | cmh:method_head cmb:method_body[in_model_prog] // constructor
                {
                    if( #mods != null )
                    {
                        #method_spec_first_decl = #mods;
                        #method_spec_first_decl.setNextSibling(
                            #( [CONSTRUCTOR, "#constr#"], cmh, [SEMI, ";"]) );
                    } else {
                        #method_spec_first_decl =
                            #( [CONSTRUCTOR, "#constr#"], cmh, [SEMI, ";"]);
                    }
                }
            )
        )
    ;

method_decl[boolean in_model_prog] :!  t:type_spec mh:method_head
        (mods:modifiers method_specification[#mods]!)?
        method_body[in_model_prog]!
        { #method_decl = #( [METH, "#meth#"], #t, #mh, [SEMI, ";"] ); }
    |!  ch:method_head
        (mds:modifiers method_specification[#mds]!)?  // constructor
        method_body[in_model_prog]!
        { #method_decl = #( [CONSTRUCTOR, "#constr#"], #ch, [SEMI, ";"] ); }
    ;

variable_declarator[boolean in_spec] :IDENT (dims)? ( ASSIGN! initializer[in_spec]! )?
    ;

variable_decls[boolean in_spec] :type_spec variable_declarators[in_spec] ( jml_var_assertion! )?
        { #variable_decls = #( [VAR_DECL, "#vardecl#"], variable_decls ); }
    ;

// inherited from grammar JmlParser
compilation_unit 
options {
	defaultErrorHandler= true;
}
:// A compilation unit starts with an optional package definition
        ( options {generateAmbigWarnings = false;} :
           ((ignored_doc_comments "package")=> ignored_doc_comments!)?
            package_definition
        )?

        // added for JML
        ( options {generateAmbigWarnings = false;} :
            ((ignored_doc_comments REFINE)=> ignored_doc_comments!)?
            refine_prefix
        )?

        ( options {warnWhenFollowAmbig = false;} :
            ((ignored_doc_comments (MODEL)? "import")=> ignored_doc_comments!)?
            import_definition
        )*

        // Wrapping things up with any number of class or interface
        //    definitions
        ( type_definition )*

        EOF
        { checkForMissingCommentEnd(); }
    ;
exception 
catch [RecognitionException err] {
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
    }

// inherited from grammar JmlParser
start_predicate :predicate;

// inherited from grammar JmlParser
start_signals :signals_clause;

// inherited from grammar JmlParser
ignored_doc_comments {
    int line = 0, col = 0;
}
:( d:DOC_COMMENT
            { line = ((LineAST)#d).line;
                col = ((LineAST)#d).column;
            } )+
        {
            reportWarning("doc comment appears before "
                + "'package', 'refine', or 'import', ignored",
                line, col);
        }
    ;

// inherited from grammar JmlParser
package_definition :"package"^ name SEMI!
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToTopLevelKeyword();
    }

// inherited from grammar JmlParser
import_definition :"import"^  name_star SEMI!
        // added "model" keyword for Jml
    |   MODEL "import"^  name_star SEMI! 
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToTopLevelKeyword();
    }

// inherited from grammar JmlParser
name :IDENT  ( DOT^ IDENT )*
    ;

// inherited from grammar JmlParser
name_star :IDENT ( DOT^ IDENT )* ( DOT^ STAR )?
    ;

// inherited from grammar JmlParser
doc_comment :d:DOC_COMMENT
        { 
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
              #doc_comment = #([DOC_COMMENT_START,"doc_comment_start"]);
          } else {
              #doc_comment = #([DOC_COMMENT_START,"doc_comment_start"], dp.getAST());
              }
            }
    ;

// inherited from grammar JmlParser
class_or_interface_def :class_definition[no_jml_stmts]
    |   interface_definition
    ;

// inherited from grammar JmlParser
type_spec :(type | T_TYPEOFALLTYPES)  // the latter added from ESC/Java
        (dims)?
    ;

// inherited from grammar JmlParser
type :reference_type
    |   builtInType
    ;

// inherited from grammar JmlParser
reference_type :name
    ;

// inherited from grammar JmlParser
modifiers {
  ModifierSet ms = new ModifierSet();
  int linenum = 0;
  int colnum = 0;
}
:!  ( options {greedy = true;} :
          mod:modifier
          { LineAST lineASTmod = (LineAST)#mod;
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
        )*
        {
           ms = Typing.defaultPrivacyModifiers(ms);
           String mod_set_string = "modifier_set (" + ms + ")";
           #modifiers = #[MODIFIER_SET, mod_set_string];
           LineAST lineASTmodifiers = (LineAST)#modifiers;
           lineASTmodifiers.type = new Modifiers(ms);
           lineASTmodifiers.line = linenum;
           lineASTmodifiers.column = colnum;
        }
    ;

// inherited from grammar JmlParser
modifier {
  Modifier r = Modifier.NONE;
}
:( "private"
      | "public"
      | "protected"
      | "static"
      | "transient"
      | "final"
      | "abstract"
      | "native"
      | "synchronized"
      | "const"
      | "volatile"
      | "strictfp"
      )
      { #modifier.setType(JAVA_MODIFIER);
        r = new Modifier(#modifier.getText());
        ((LineAST)#modifier).type = new Modifiers(r);
      }
    | jml_modifier          // added for JML
    ;

// inherited from grammar JmlParser
class_definition[boolean in_model_prog] :"class"^ IDENT // aha! a class!

        // it _might_ have a superclass...
        // "weakly" keyword added for Jml
        ( "extends" name (WEAKLY)? )?

        // it might implement some interfaces...
        ( implements_clause )?

        // now parse the body of the class
        class_block[side_effects_allowed, in_model_prog]
    ;

// inherited from grammar JmlParser
class_block[boolean in_spec, boolean in_model_prog] :LCURLY
            ( field[in_spec, in_model_prog] )*
        RCURLY
    ;

// inherited from grammar JmlParser
interface_definition :"interface"^ IDENT // aha! an interface!
            
        // it might extend some other interfaces
        (interface_extends)?

        // now parse the body of the interface (looks like a class...)
        class_block[side_effects_allowed, no_jml_stmts]
    ;

// inherited from grammar JmlParser
interface_extends :"extends"^ name_weakly_list
    ;

// inherited from grammar JmlParser
implements_clause :"implements"^ name_weakly_list
    ;

// inherited from grammar JmlParser
name_weakly_list :name (WEAKLY)? ( COMMA^ name (WEAKLY)? )* 
    ;

// inherited from grammar JmlParser
doc_comments :(doc_comment)*
    ;

// inherited from grammar JmlParser
member_decl[boolean in_spec, boolean in_model_prog] :(variable_decls[in_spec]) => variable_decls[in_spec] SEMI!
    |   method_decl[in_model_prog]
    |   class_definition[in_model_prog]   // nested or inner class
    |   interface_definition              // nested or inner interface
    ;

// inherited from grammar JmlParser
method_head :IDENT  // the name of the method

    // parse the formal parameter declarations.
    LPAREN! (param_declaration_list)? RPAREN!
    
    // again, the array specification is skipped...
    (dims)?

    // get the list of exceptions that this method is declared to throw
    (throws_clause)?
    ;

// inherited from grammar JmlParser
method_body[boolean in_model_prog] :compound_statement[in_model_prog]
        // The SEMI is necessary to avoid ambiguities
    |   SEMI
    ;

// inherited from grammar JmlParser
throws_clause :"throws" name_list 
    ;

// inherited from grammar JmlParser
name_list :name ( COMMA^ name )* 
    ;

// inherited from grammar JmlParser
param_declaration_list :param_declaration ( COMMA^ param_declaration )*
    ;

// inherited from grammar JmlParser
param_declaration :("final")? type_spec IDENT (dims)?
        { #param_declaration =
            #( [PARAM], param_declaration ); }
    ;

// inherited from grammar JmlParser
variable_declarators[boolean in_spec] :variable_declarator[in_spec] (COMMA^ variable_declarator[in_spec] )*
    ;

// inherited from grammar JmlParser
initializer[boolean in_spec] :expression[in_spec]
    |   array_initializer[in_spec]
    ;

// inherited from grammar JmlParser
array_initializer[boolean in_spec] :LCURLY (initializer_list[in_spec])? RCURLY  
    ;

// inherited from grammar JmlParser
initializer_list[boolean in_spec] :initializer[in_spec]
        (
            // CONFLICT: does a COMMA after an initializer start a 
            //           new initializer or start the option ',' 
            //           at end?ANTLR generates proper code by 
            //       matching the comma as soon as possible.
            options {
                warnWhenFollowAmbig = false;
            }
        :
            (COMMA!) initializer[in_spec]
        )*
        (COMMA!)?
    ;

// inherited from grammar JmlParser
refine_prefix :REFINE^ ident_list L_ARROW STRING_LITERAL SEMI!
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToTopLevelKeyword();
    }

// inherited from grammar JmlParser
ident_list :IDENT ( COMMA^ IDENT )* 
    ;

// inherited from grammar JmlParser
jml_var_assertion :(INITIALLY^ | READABLE_IF^) predicate
    | monitored_by_clause           // added from ESC/Java
    ;

// inherited from grammar JmlParser
monitored_by_clause :MONITORED_BY^ expression_list[no_side_effects]
    ;

// inherited from grammar JmlParser
jml_modifier {
  Modifier r = Modifier.NONE;
}
:( MODEL
      | PURE
      | INSTANCE
      | SPEC_PUBLIC
      | SPEC_PROTECTED
      | MONITORED
      | UNINITIALIZED
      | GHOST
      | NON_NULL
      )
      { #jml_modifier.setType(JML_MODIFIER);
        r = new Modifier(#jml_modifier.getText());
        ((LineAST)#jml_modifier).type = new Modifiers(r);
      }
    ;

// inherited from grammar JmlParser
jml_declaration :invariant
    | history_constraint
    | depends_decl
    | represents_decl
    ;

// inherited from grammar JmlParser
invariant :( INVARIANT^
      | INVARIANT_REDUNDANTLY^
      )
      predicate SEMI!
            { #invariant.setType(INVARIANT_KEYWORD); }
    ;

// inherited from grammar JmlParser
history_constraint :( CONSTRAINT^
      | CONSTRAINT_REDUNDANTLY^
      )
          predicate (FOR constrained_list)? SEMI!
            { #history_constraint.setType(CONSTRAINT_KEYWORD); }
    ;

// inherited from grammar JmlParser
constrained_list :method_name_list
    |   T_EVERYTHING
    ;

// inherited from grammar JmlParser
method_name_list :method_name ( COMMA^ method_name )*
    ;

// inherited from grammar JmlParser
method_name :method_ref ( LPAREN^ (param_disambig_list)? RPAREN! )? 
    ;

// inherited from grammar JmlParser
method_ref :("super" | "this" | IDENT | T_OTHER)
        ( DOT^ IDENT )*
    |   constructor_ref
    ;

// inherited from grammar JmlParser
constructor_ref :"new"^ reference_type
    ;

// inherited from grammar JmlParser
param_disambig_list :param_disambig ( COMMA^ param_disambig )*
    ;

// inherited from grammar JmlParser
param_disambig :type_spec ( IDENT (dims)? )?
        { #param_disambig = 
            #( [PARAM], #param_disambig ); }
    ;

// inherited from grammar JmlParser
depends_decl :( DEPENDS^
      | DEPENDS_REDUNDANTLY^
      )
      store_ref L_ARROW! store_references SEMI!
            { #depends_decl.setType(DEPENDS_KEYWORD); }
    ;

// inherited from grammar JmlParser
represents_decl :( REPRESENTS^
      | REPRESENTS_REDUNDANTLY^
      )
      represents_expr SEMI!
            { #represents_decl.setType(REPRESENTS_KEYWORD); }
    ;

// inherited from grammar JmlParser
represents_expr :store_ref ( T_SUCH_THAT^ predicate | L_ARROW^ spec_expression )
    ;

// inherited from grammar JmlParser
axiom_pragma :AXIOM^ predicate SEMI!
    ;

// inherited from grammar JmlParser
method_specification_opt[AST mods] :! "void"
        { #method_specification_opt = null; }
    | method_specification[mods]
    ;

// inherited from grammar JmlParser
method_specification[AST mods] :specification[mods]
    | extending_specification
        {
            if (!(mods == null
                || ((MTypeAttrib)((LineAST) mods).type)
                    .getModifiers().printsEmpty())) {
                reportWarning("can't use a modifier before 'also' or 'and'"
                    + ": " + mods,
                    ((LineAST)mods).line, ((LineAST)mods).column);
            }
        }
    ;

// inherited from grammar JmlParser
specification[AST mods] :initial_spec_case_seq[mods] (subclassing_contract)? (redundant_spec)?
    | subclassing_contract (redundant_spec)?
        {
            if (!(mods == null
                || ((MTypeAttrib)((LineAST) mods).type)
                    .getModifiers().printsEmpty())) {
                reportWarning("can't use a modifier before 'subclassing_contract'"
                    + ": " + mods,
                    ((LineAST)mods).line, ((LineAST)mods).column);
            }
        }
    | redundant_spec
        {
            if (!(mods == null
                || ((MTypeAttrib)((LineAST) mods).type)
                    .getModifiers().printsEmpty())) {
                reportWarning("can't use a modifier before 'implies_that'"
                    + ": " + mods,
                    ((LineAST)mods).line, ((LineAST)mods).column);
            }
        }
    ;

// inherited from grammar JmlParser
extending_specification :! ALSO m:modifiers sp:specification[#m]
       { #extending_specification = #([EXT_ALSO, "EXT_also"], sp); }
    | AND! conjoinable_spec_seq (ALSO spec_case_seq)?
        (subclassing_contract)? (redundant_spec)?
       { #extending_specification = #([EXT_AND, "EXT_and"],
                      #extending_specification); }
    ;

// inherited from grammar JmlParser
conjoinable_spec_seq :conjoinable_spec (AND^ conjoinable_spec)*
    ;

// inherited from grammar JmlParser
conjoinable_spec :generic_conjoinable_spec
          {
        #conjoinable_spec = #([CONJOINABLE_SPEC,"conjoinable_spec"],
                      #conjoinable_spec);
          }
    | privacy_opt behavior_conjoinable_spec
         {
        #conjoinable_spec = #([CONJOINABLE_SPEC,"conjoinable_spec"],
                                      #conjoinable_spec);
          }
    ;

// inherited from grammar JmlParser
generic_conjoinable_spec :(spec_var_decls)? simple_spec_body
      { #generic_conjoinable_spec = #([CONJOINABLE_SPEC,"conjoinable_spec"],
                      #generic_conjoinable_spec); }
    ;

// inherited from grammar JmlParser
privacy_opt {
  Modifier r = Modifier.NONE;
}
:/* nothing */ 
    | ("public" | "private" | "protected")
         { r = new Modifier(#privacy_opt.getText());
           ModifierSet ms = new ModifierSet(r);
           // save column and line information
           LineAST lineASTprivacy_opt = (LineAST)#privacy_opt;
           int linenum = lineASTprivacy_opt.line;
           int colnum = lineASTprivacy_opt.column;
           // create a new special token
           ms = Typing.defaultPrivacyModifiers(ms);
           String priv_mod_str = "privacy_modifier (" + ms + ")";
           #privacy_opt = #[PRIVACY_MODIFIER, priv_mod_str];
           lineASTprivacy_opt = (LineAST)#privacy_opt;
           lineASTprivacy_opt.type = new Modifiers(ms);
           lineASTprivacy_opt.line = linenum;
           lineASTprivacy_opt.column = colnum;
         }
    ;

// inherited from grammar JmlParser
behavior_conjoinable_spec :BEHAVIOR (spec_var_decls)? simple_spec_body
    | EXCEPTIONAL_BEHAVIOR
      (spec_var_decls)? exceptional_simple_spec_body
    | NORMAL_BEHAVIOR
      (spec_var_decls)? normal_simple_spec_body
    ;

// inherited from grammar JmlParser
exceptional_simple_spec_body :assignable_clause_seq signals_clause_seq_opt diverges_clause_seq_opt
    | signals_clause_seq diverges_clause_seq_opt
    ;

// inherited from grammar JmlParser
normal_simple_spec_body :assignable_clause_seq ensures_clause_seq_opt diverges_clause_seq_opt
    | ensures_clause_seq diverges_clause_seq_opt
    ;

// inherited from grammar JmlParser
redundant_spec :implications (examples)?
    | examples
    ;

// inherited from grammar JmlParser
examples :FOR_EXAMPLE^ example_seq
    ;

// inherited from grammar JmlParser
example_seq :example (ALSO^ example)*
    ;

// inherited from grammar JmlParser
example :(spec_var_decls)? (spec_header)? simple_spec_body
        { #example = #([SPEC_CASE, "generic_example"], #example); }
    | privacy_opt
      ( EXAMPLE (spec_var_decls)? (spec_header)? simple_spec_body
        { #example = #([SPEC_CASE, "example"], #example); }
      | EXCEPTIONAL_EXAMPLE (spec_var_decls)?
            ( spec_header (exceptional_example_body)?
            | exceptional_example_body
        )
                { #example = #([SPEC_CASE, "example"], #example); }
      | NORMAL_EXAMPLE (spec_var_decls)?
            ( spec_header (normal_example_body)?
            | normal_example_body
        )
        { #example = #([SPEC_CASE, "example"], #example); }
      )
    ;

// inherited from grammar JmlParser
exceptional_example_body :(assignable_clause)+ (signals_clause)* (diverges_clause)*
    | (signals_clause)+ (diverges_clause)*
    ;

// inherited from grammar JmlParser
normal_example_body :(assignable_clause)+ (ensures_clause)* (diverges_clause)*
    | (ensures_clause)+ (diverges_clause)*
    ;

// inherited from grammar JmlParser
implications :IMPLIES_THAT^ spec_case_seq
    ;

// inherited from grammar JmlParser
initial_spec_case_seq[AST mods] :initial_spec_case[mods] (ALSO^ spec_case)*
    ;

// inherited from grammar JmlParser
initial_spec_case[AST mods] {
    LineAST privs = modifiers2privacy(mods);
}
:generic_spec_case
      {
        #initial_spec_case =
            #([SPEC_CASE,"generic_spec_case"], #initial_spec_case);
      }
    | ( behavior_spec
      | model_program
          )
      {
        #initial_spec_case =
            #([SPEC_CASE,"spec_case"], privs, #initial_spec_case);
      }
    ;
exception 
catch [RecognitionException err] {
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
    }

// inherited from grammar JmlParser
spec_case_seq :spec_case (ALSO^ spec_case)*
    ;

// inherited from grammar JmlParser
spec_case :generic_spec_case
          {
        #spec_case = #([SPEC_CASE,"generic_spec_case"],#spec_case); 
          }
    | (privacy_opt
        ( behavior_spec
        | model_program
            )
          {
        #spec_case = #([SPEC_CASE,"spec_case"],#spec_case); 
          }
      )
    ;
exception 
catch [RecognitionException err] {
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
    }

// inherited from grammar JmlParser
subclassing_contract :SUBCLASSING_CONTRACT^ accessible_clause_seq callable_clause_seq_opt
    | SUBCLASSING_CONTRACT^ callable_clause_seq
    ;

// inherited from grammar JmlParser
accessible_clause_seq :(accessible_clause)+
       { #accessible_clause_seq = #([ACCESSIBLE_SEQ,"accessible_seq"],#accessible_clause_seq); }
    ;

// inherited from grammar JmlParser
accessible_clause :( ACCESSIBLE^ 
      | ACCESSIBLE_REDUNDANTLY^
      )
      object_references SEMI!
            { #accessible_clause.setType(ACCESSIBLE_KEYWORD); }
    ;

// inherited from grammar JmlParser
object_references :object_ref (COMMA^ object_ref)*
    | store_ref_keyword
    ;

// inherited from grammar JmlParser
object_ref :store_ref_expression
    | T_OTHER
      ( DOT^ IDENT
       | LBRACK^ spec_array_ref_expr RBRACK!
          )*
    ;

// inherited from grammar JmlParser
callable_clause_seq :(callable_clause)+
      { #callable_clause_seq = #([CALLABLE_SEQ,"callable_seq"], #callable_clause_seq); }
    ;

// inherited from grammar JmlParser
callable_clause_seq_opt :(callable_clause)*
      { #callable_clause_seq_opt = #([CALLABLE_SEQ,"callable_seq"], #callable_clause_seq_opt); }
    ;

// inherited from grammar JmlParser
callable_clause :( CALLABLE^
      | CALLABLE_REDUNDANTLY^
      )
      callable_methods SEMI!
            { #callable_clause.setType(CALLABLE_KEYWORD); }
    ;

// inherited from grammar JmlParser
callable_methods :method_name_list
    | store_ref_keyword
    ;

// inherited from grammar JmlParser
generic_spec_case :(spec_var_decls)?
      ( spec_header (generic_spec_body)?
      | generic_spec_body
      )
      { #generic_spec_case = #([SPEC_CASE, "generic_spec_case"],
                            #generic_spec_case); }
    ;

// inherited from grammar JmlParser
spec_header :(label_decl)+ (requires_clause)* (when_clause)* (measured_clause)*
    | (requires_clause)+ (when_clause)* (measured_clause)*
    | (when_clause)+ (measured_clause)*
    | (measured_clause)+
    ;

// inherited from grammar JmlParser
generic_spec_body :simple_spec_body
    | LCURLY_VBAR generic_spec_case_seq VBAR_RCURLY
    ;

// inherited from grammar JmlParser
generic_spec_case_seq :generic_spec_case (ALSO^ generic_spec_case)*
    ;

// inherited from grammar JmlParser
simple_spec_body :assignable_clause_seq ensures_clause_seq_opt signals_clause_seq_opt
      diverges_clause_seq_opt
    | ensures_clause_seq signals_clause_seq_opt diverges_clause_seq_opt
    | signals_clause_seq diverges_clause_seq_opt
    | diverges_clause_seq
    ;

// inherited from grammar JmlParser
behavior_spec :BEHAVIOR generic_spec_case
    | EXCEPTIONAL_BEHAVIOR exceptional_spec_case
    | NORMAL_BEHAVIOR normal_spec_case
    ;

// inherited from grammar JmlParser
exceptional_spec_case :(spec_var_decls)?
          ( spec_header (exceptional_spec_case_body)?
           | exceptional_spec_case_body)
     { #exceptional_spec_case = #([SPEC_CASE, "exceptional_spec_case"],
                            #exceptional_spec_case); }
    ;

// inherited from grammar JmlParser
exceptional_spec_case_body :assignable_clause_seq signals_clause_seq_opt diverges_clause_seq_opt
    | signals_clause_seq diverges_clause_seq_opt
    | LCURLY_VBAR exceptional_spec_case_seq VBAR_RCURLY
    ;

// inherited from grammar JmlParser
exceptional_spec_case_seq :exceptional_spec_case (ALSO^ exceptional_spec_case)*
    ;

// inherited from grammar JmlParser
normal_spec_case :(spec_var_decls)? 
      ( spec_header (normal_spec_case_body)?
      | normal_spec_case_body
      )
         { #normal_spec_case = #([SPEC_CASE, "normal_spec_case"],
                            #normal_spec_case); }
    ;

// inherited from grammar JmlParser
normal_spec_case_body :assignable_clause_seq ensures_clause_seq_opt diverges_clause_seq_opt
    | ensures_clause_seq diverges_clause_seq_opt
    | LCURLY_VBAR normal_spec_case_seq VBAR_RCURLY
    ;

// inherited from grammar JmlParser
normal_spec_case_seq :normal_spec_case (ALSO^ normal_spec_case)*
    ;

// inherited from grammar JmlParser
model_program :MODEL_PROGRAM compound_statement[with_jml]
    ;

// inherited from grammar JmlParser
spec_var_decls :(forall_var_decl)+ (let_var_decls)?
    |   let_var_decls
    ;

// inherited from grammar JmlParser
forall_var_decl :FORALL^ quantified_var_decl SEMI!
    ;

// inherited from grammar JmlParser
let_var_decls :( lk:LET^
            { reportWarning("The keyword `let' is deprecated, use `old' instead.",
                    lk.getLine(), lk.getColumn());
            }
        | OLD^
        )
        (local_spec_var_decl)+
        { #let_var_decls.setType(LETOLD_KEYWORD); }
    ;

// inherited from grammar JmlParser
local_spec_var_decl :(MODEL^ | GHOST^) type_spec variable_declarators[no_side_effects] SEMI!
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToJmlSpecKeyword();
    }

// inherited from grammar JmlParser
requires_clause_seq :(requires_clause)+
    ;

// inherited from grammar JmlParser
requires_clause :( REQUIRES^ | PRE^
      | REQUIRES_REDUNDANTLY^ | PRE_REDUNDANTLY^
      )
      (T_NOT_SPECIFIED | pre_cond) SEMI!
          { #requires_clause.setType(REQUIRES_KEYWORD); }
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToJmlSpecKeyword();
    }

// inherited from grammar JmlParser
pre_cond :predicate
    ;

// inherited from grammar JmlParser
when_clause_seq :(when_clause)+
    ;

// inherited from grammar JmlParser
when_clause :( WHEN^
      | WHEN_REDUNDANTLY^
      )
      (T_NOT_SPECIFIED | predicate) SEMI!
            { #when_clause.setType(WHEN_KEYWORD); }
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToJmlSpecKeyword();
    }

// inherited from grammar JmlParser
measured_clause_seq :(measured_clause)+
    ;

// inherited from grammar JmlParser
measured_clause :( MEASURED_BY^
      | MEASURED_BY_REDUNDANTLY^
      )
      (T_NOT_SPECIFIED | spec_expression ("if" predicate)?) SEMI!
            { #measured_clause.setType(MEASURED_BY_KEYWORD); }
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToJmlSpecKeyword();
    }

// inherited from grammar JmlParser
label_decl :IDENT COLON^
     {#label_decl.setType(LABEL_KEYWORD);}
           ;

// inherited from grammar JmlParser
label_statement :LABEL^ label_statement_list SEMI!
         {#label_statement.setType(LABEL_KEYWORD);}
    ;

// inherited from grammar JmlParser
label_statement_list :IDENT (COMMA^ IDENT)*
                     ;

// inherited from grammar JmlParser
loop_assignable_clause_seq_opt :(loop_assignable_clause)* 
      { #loop_assignable_clause_seq_opt = #([LOOP_ASGNABLE_SEQ,"loop_assignable_seq"], #loop_assignable_clause_seq_opt); 
          }
    ;

// inherited from grammar JmlParser
loop_assignable_clause_seq :(loop_assignable_clause)+ 
      { #loop_assignable_clause_seq = #([LOOP_ASGNABLE_SEQ,"loop_assignable_seq"], #loop_assignable_clause_seq); 
          }
    ;

// inherited from grammar JmlParser
loop_assignable_clause :( LOOP_MODIFIES^ )
      conditional_store_references SEMI!
            { #loop_assignable_clause.setType(LOOP_ASSIGNABLE_KEYWORD); }
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToJmlSpecKeyword();
    }

// inherited from grammar JmlParser
assignable_clause_seq_opt :(assignable_clause)* 
      { #assignable_clause_seq_opt = #([ASGNABLE_SEQ,"assignable_seq"], #assignable_clause_seq_opt); 
          }
    ;

// inherited from grammar JmlParser
assignable_clause_seq :(assignable_clause)+ 
      { #assignable_clause_seq = #([ASGNABLE_SEQ,"assignable_seq"], #assignable_clause_seq); 
          }
    ;

// inherited from grammar JmlParser
assignable_clause :( ASSIGNABLE^ | MODIFIABLE^ | MODIFIES^
      | ASSIGNABLE_REDUNDANTLY^ | MODIFIABLE_REDUNDANTLY^
      | MODIFIES_REDUNDANTLY^ 
      )
      conditional_store_references SEMI!
            { #assignable_clause.setType(ASSIGNABLE_KEYWORD); }
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToJmlSpecKeyword();
    }

// inherited from grammar JmlParser
conditional_store_references :conditional_store_ref_list
    ;

// inherited from grammar JmlParser
conditional_store_ref_list :conditional_store_ref (COMMA^ conditional_store_ref)*
    ;

// inherited from grammar JmlParser
conditional_store_ref :store_ref ("if"^ predicate)?
    ;

// inherited from grammar JmlParser
store_references :store_ref_list
    ;

// inherited from grammar JmlParser
store_ref_list :store_ref (COMMA^ store_ref)*
    ;

// inherited from grammar JmlParser
store_ref :store_ref_expression
    | T_FIELDS_OF^ 
        LPAREN! 
          spec_expression ( COMMA! reference_type
                    (COMMA! store_ref_expression)?
                  )?
        RPAREN!
    | informal_desc
    | store_ref_keyword
    ;

// inherited from grammar JmlParser
store_ref_keyword :T_NOTHING
    | T_EVERYTHING
    | T_NOT_SPECIFIED
    ;

// inherited from grammar JmlParser
store_ref_expression :( IDENT | "this" | "super" )
        ( DOT^ IDENT
        | LBRACK^ spec_array_ref_expr RBRACK!
        //LB : changement pour admettre les appels de methode pure dans les 
        //clauses modifies.
        |   LPAREN^
                ( spec_expression_list )?
            RPAREN!
        )*
    ;

// inherited from grammar JmlParser
spec_array_ref_expr :spec_expression ( DOT_DOT^ spec_expression )?
     // array element access or 
     // array reference expressions like e1[e2 .. e3]

    | STAR
        // array reference like e1[*]
        { #spec_array_ref_expr = #([STAR_ELEMS, "*"]); }
    ;

// inherited from grammar JmlParser
ensures_clause_seq_opt :(ensures_clause)*
      {
        #ensures_clause_seq_opt = #([ENS_SEQ,"ensures_seq"], #ensures_clause_seq_opt); 
      }
    ;

// inherited from grammar JmlParser
ensures_clause_seq :(ensures_clause)+
      {
        #ensures_clause_seq = #([ENS_SEQ,"ensures_seq"], #ensures_clause_seq); 
      }
    ;

// inherited from grammar JmlParser
ensures_clause :( ENSURES^ | POST^
      | ENSURES_REDUNDANTLY^ | POST_REDUNDANTLY^
      )
      (T_NOT_SPECIFIED | post_cond) SEMI!
            { #ensures_clause.setType(ENSURES_KEYWORD); }
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToJmlSpecKeyword();
    }

// inherited from grammar JmlParser
post_cond :predicate
    ;

// inherited from grammar JmlParser
loop_signals_clause_seq_opt :(loop_signals_clause)*
      {
        #loop_signals_clause_seq_opt = #([LOOP_SIG_SEQ,"loop_signals_seq"], #loop_signals_clause_seq_opt);
      }
    ;

// inherited from grammar JmlParser
loop_signals_clause_seq :(loop_signals_clause)+
      {
        #loop_signals_clause_seq = #([LOOP_SIG_SEQ,"loop_signals_seq"], #loop_signals_clause_seq);
      }
    ;

// inherited from grammar JmlParser
loop_signals_clause {
  String kw = "";
}
:( LOOP_EXSURES^
      )
      LPAREN reference_type (IDENT)? RPAREN
      (T_NOT_SPECIFIED | predicate)? SEMI!
         // [[[put true in the parse tree if the predicate is omitted]]]
            { #loop_signals_clause.setType(SIGNALS_KEYWORD); }
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToJmlSpecKeyword();
    }

// inherited from grammar JmlParser
signals_clause_seq_opt :(signals_clause)*
      {
        #signals_clause_seq_opt = #([SIG_SEQ,"signals_seq"], #signals_clause_seq_opt);
      }
    ;

// inherited from grammar JmlParser
signals_clause_seq :(signals_clause)+
      {
        #signals_clause_seq = #([SIG_SEQ,"signals_seq"], #signals_clause_seq);
      }
    ;

// inherited from grammar JmlParser
signals_clause {
  String kw = "";
}
:( SIGNALS^
      | SIGNALS_REDUNDANTLY^
      | EXSURES^
      | EXSURES_REDUNDANTLY^
      )
      LPAREN reference_type (IDENT)? RPAREN
      (T_NOT_SPECIFIED | predicate)? SEMI!
         // [[[put true in the parse tree if the predicate is omitted]]]
            { #signals_clause.setType(SIGNALS_KEYWORD); }
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToJmlSpecKeyword();
    }

// inherited from grammar JmlParser
diverges_clause_seq_opt :(diverges_clause)*
        {
        #diverges_clause_seq_opt = #([DIV_SEQ,"diverges_seq"], #diverges_clause_seq_opt);
        }
    ;

// inherited from grammar JmlParser
diverges_clause_seq :(diverges_clause)+
        {
        #diverges_clause_seq = #([DIV_SEQ,"diverges_seq"], #diverges_clause_seq);
        }
    ;

// inherited from grammar JmlParser
diverges_clause :( DIVERGES^
      | DIVERGES_REDUNDANTLY^
      )
      (T_NOT_SPECIFIED | predicate) SEMI!
            { #diverges_clause.setType(DIVERGES_KEYWORD); }
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToJmlSpecKeyword();
    }

// inherited from grammar JmlParser
predicate :spec_expression
    ;

// inherited from grammar JmlParser
spec_expression_list :spec_expression (COMMA^ spec_expression)*
    ;

// inherited from grammar JmlParser
spec_expression :expression[no_side_effects]
    ;

// inherited from grammar JmlParser
compound_statement[boolean in_model_prog] :LCURLY (statement[in_model_prog])* RCURLY
    ;

// inherited from grammar JmlParser
statement[boolean in_model_prog] :compound_statement[in_model_prog]
	
	|!  g:spec_statement_jack c:compound_statement[in_model_prog] {
			#statement = #( [SPEC_STATEMENT, "spec_statement"], g, c);
		}
    // classes can be declared local to a method
    // also documentation comments appear sometimes out of place
    // e.g., in java.lang.Integer.toString()
    |  doc_comment!
       ( options {greedy=true;}
       : class_definition[in_model_prog]
            { #statement = #( [NESTED_CLASS, "nested_class"], #statement ); }
       | "final" class_definition[in_model_prog]
            { #statement = #( [NESTED_CLASS, "nested_class"], #statement ); }
       | "abstract" class_definition[in_model_prog]
            { #statement = #( [NESTED_CLASS, "nested_class"], #statement ); }
       )?
    |   class_definition[in_model_prog]
            { #statement = #( [NESTED_CLASS, "nested_class1"], #statement ); }
    |   "final" class_definition[in_model_prog]
            { #statement = #( [NESTED_CLASS, "nested_class"], #statement ); }
    |   "abstract" class_definition[in_model_prog]
            { #statement = #( [NESTED_CLASS, "nested_class"], #statement ); }

    // If it _looks_ like a decl, it's a decl...
    |   (local_declaration)=> local_declaration SEMI!

    // Attach a label to the front of a statement
    |   IDENT COLON^ statement[in_model_prog]

    // An expression statement.  This could be a method call, assignment
    //   statement, or any other expression evaluated for side-effects.
    |   expression[side_effects_allowed] SEMI!

    // If-else statement
    |   "if"^ LPAREN! expression[side_effects_allowed] RPAREN!
        statement[in_model_prog]
        (
            // CONFLICT: the old "dangling-else" problem...
            //           ANTLR generates proper code matching
            //       as soon as possible.  Hush warning.
            options {
                warnWhenFollowAmbig = false;
            }
        :
            "else"! statement[in_model_prog]
        )?

        // the "else" part above is ambiguous.  The intent
        // is to keep it as close to the corresponding "if"
        // as possible.  The generated code will do this,
        // so we can live with the ambiguity.  We could do
        //      (   ("else")=> "else" statement 
        //      |   // no else clause
        //      )
        // instead, but that's less efficient...

    // loop statements
    |!  lm:loop_assignable_clause_seq_opt /// added by LB
        li:loop_invariant_seq_opt     // added for JML
        ls:loop_signals_clause_seq_opt     // added by LB
        vf:variant_function_seq_opt   // added for JML
        ( w:"while" LPAREN! we:expression[side_effects_allowed] RPAREN!
          ws:statement[in_model_prog]
            { #statement = #(w, lm, li, ls, vf, we, ws); }
        | d:"do" ds:statement[in_model_prog] "while" LPAREN!
          de:expression[side_effects_allowed] RPAREN! SEMI!
            { #statement = #(d, lm, li, ls, vf, ds, de); }
        | f:"for"
            LPAREN finit:for_init SEMI
                   ftest:for_test SEMI
                   fupdater:for_updater
            RPAREN
            fstat:statement[in_model_prog]
            { #statement = #(f, finit, ftest, fupdater, lm, li, ls, vf, fstat); }
        )

    // get out of a loop (or switch)
    |   "break"^ (IDENT)? SEMI!

    // do next iteration of a loop
    |   "continue"^ (IDENT)? SEMI!

    // Return an expression
    |   "return"^ (expression[side_effects_allowed])? SEMI!

    // switch/case statement
    |   switch_statement[in_model_prog]

    // exception try-catch block
    |   try_block[in_model_prog]

    // throw an exception
    |   "throw"^ expression[side_effects_allowed] SEMI!

    // synchronize a statement
    |   "synchronized"^ LPAREN! expression[side_effects_allowed] RPAREN!
         compound_statement[in_model_prog]

    // empty statement
    |   SEMI

    //  assert statement (new in JDK 1.4)
    |   assert_statement

    // statements added for JACK (LB)
    |   label_statement
   
    // statements added for JML, but available always
    |   hence_by_statement
    |   assert_redundantly_statement
    |   assume_statement
    |   set_statement            // added from ESC/Java (JML)
    |   unreachable_statement    // added from ESC/Java (JML)

    // statements only available in model programs
    |   mps:model_prog_statement
        {
            if (!in_model_prog) {
                reportError("model-program-statements can only be used in model programs",
                            ((LineAST)#mps).line, ((LineAST)#mps).column);
            }
        }
    ;

// inherited from grammar JmlParser
for_init :(local_declaration)=> local_declaration
        { #for_init = #([FOR_INIT, "for_init"], #for_init); }
    |   expression_list[side_effects_allowed]
        { #for_init = #([FOR_INIT, "for_init"], #for_init); }
    |   /* nothing */
        { #for_init = #([FOR_INIT, "for_init"], #for_init); }
    ;

// inherited from grammar JmlParser
for_test :expression[side_effects_allowed]
        { #for_test = #([FOR_TEST, "for_test"], #for_test); }
    |   /* nothing */
        { #for_test = #([FOR_TEST, "for_test"], #for_test); }
    ;

// inherited from grammar JmlParser
for_updater :expression_list[side_effects_allowed]
        { #for_updater = #([FOR_UPDATER, "for_updater"], #for_updater); }
    |   /* nothing */
        { #for_updater = #([FOR_UPDATER, "for_updater"], #for_updater); }
    ;

// inherited from grammar JmlParser
local_modifier :MODEL 
    | GHOST
    | "final"
    | NON_NULL
    ;

// inherited from grammar JmlParser
local_modifiers :( local_modifier )*
    ;

// inherited from grammar JmlParser
local_declaration :local_modifiers
      /* [[[make it a specification decl if model or ghost modifier]]] */
      variable_decls[side_effects_allowed]
    ;

// inherited from grammar JmlParser
switch_statement[boolean in_model_prog] :"switch"^ LPAREN! expression[side_effects_allowed] RPAREN!
            LCURLY!
                (switch_body[in_model_prog])*
            RCURLY!
    ;

// inherited from grammar JmlParser
switch_body[boolean in_model_prog] :switch_label_seq  (statement[in_model_prog])*
        // The CASE token eliminates the ambiguity in the AST.
        { #switch_body = #( [CASE], #switch_body ); }
    ;

// inherited from grammar JmlParser
switch_label_seq :(
            // CONFLICT: to which "cases" does the statement bind?
            //           ANTLR generates proper code: it groups the
            //           many "case"/"default" labels together then
            //           follows them with the statements
            options {
                warnWhenFollowAmbig = false;
            }
        :   switch_label
        )+
        // ambiguous but proper code will be generated...
    ;

// inherited from grammar JmlParser
switch_label :"case" expression[side_effects_allowed] COLON!
    |   "default" COLON!
    ;

// inherited from grammar JmlParser
try_block[boolean in_model_prog] :"try" compound_statement[in_model_prog]
        (handler[in_model_prog])*
        ( "finally" compound_statement[in_model_prog] )?
    ;

// inherited from grammar JmlParser
handler[boolean in_model_prog] :"catch"^ LPAREN! param_declaration RPAREN!
        compound_statement[in_model_prog]
    ;

// inherited from grammar JmlParser
assert_statement {
    boolean in_JML = lexer.SL_Jml_state || lexer.ML_Jml_state
                       || lexer.JML_reading_JML_file;
}
:"assert"^ expression[in_JML ? no_side_effects : side_effects_allowed]
        (COLON! expression[side_effects_allowed])?
        SEMI!
        {   
            // change to "affirm" internally if in JML mode
            if (in_JML) { #assert_statement.setType(AFFIRM_KEYWORD); }
        }
    ;

// inherited from grammar JmlParser
hence_by_statement :( HENCE_BY^
      | HENCE_BY_REDUNDANTLY^
      )
      predicate SEMI!
            { #hence_by_statement.setType(HENCE_BY_KEYWORD); }
    ;

// inherited from grammar JmlParser
assert_redundantly_statement :ASSERT_REDUNDANTLY^ predicate
        (COLON! expression[side_effects_allowed])?
        SEMI!
        { #assert_redundantly_statement.setType(AFFIRM_KEYWORD); }
    ;

// inherited from grammar JmlParser
assume_statement :( ASSUME^
        | ASSUME_REDUNDANTLY^
        )
        predicate
        (COLON! expression[side_effects_allowed])?
        SEMI!
            { #assume_statement.setType(ASSUME_KEYWORD); }
    ;

// inherited from grammar JmlParser
set_statement :SET^ spec_assignment_expr SEMI!
    ;

// inherited from grammar JmlParser
spec_assignment_expr :conditional_expr[no_side_effects]
        (   ( ASSIGN^
            | ( PLUS_ASSIGN^ | MINUS_ASSIGN^)
                { #spec_assignment_expr.setType(ADDITIVE_ASSIGNMENT_OP); }
            | ( STAR_ASSIGN^ | DIV_ASSIGN^ | MOD_ASSIGN^ )
                { #spec_assignment_expr.setType(MULTIPLICATIVE_ASSIGNMENT_OP); }
            | ( SR_ASSIGN^ | BSR_ASSIGN^ | SL_ASSIGN^ )
                { #spec_assignment_expr.setType(SHIFT_ASSIGNMENT_OP); }
            | ( BAND_ASSIGN^ | BOR_ASSIGN^ | BXOR_ASSIGN^ )
                { #spec_assignment_expr.setType(BITWISE_ASSIGNMENT_OP); }
            )
            spec_assignment_expr
        )?
    ;

// inherited from grammar JmlParser
unreachable_statement :UNREACHABLE^ SEMI!
    ;

// inherited from grammar JmlParser
model_prog_statement :nondeterministic_choice
    |   nondeterministic_if
    |   spec_statement
    |   invariant
    ;

// inherited from grammar JmlParser
nondeterministic_choice :CHOOSE^ alternative_statements
    ;

// inherited from grammar JmlParser
alternative_statements :compound_statement[with_jml] (OR^ compound_statement[with_jml])*
    ;

// inherited from grammar JmlParser
nondeterministic_if :CHOOSE_IF^ guarded_statements
        (
            // CONFLICT: the old "dangling-else" problem...
            //           ANTLR generates proper code matching
            //           as soon as possible.  Hush warning.
            options {
                warnWhenFollowAmbig = false;
            }
        :
            ELSE! compound_statement[with_jml]
        )?
    ;

// inherited from grammar JmlParser
guarded_statements :guarded_statement (OR^ guarded_statement)*
    ;

// inherited from grammar JmlParser
guarded_statement :LCURLY assume_statement (statement[with_jml])* RCURLY
    ;

// inherited from grammar JmlParser
spec_statement :BEHAVIOR generic_spec_statement_case
    | EXCEPTIONAL_BEHAVIOR exceptional_spec_case
    | NORMAL_BEHAVIOR normal_spec_case
    | ABRUPT_BEHAVIOR abrupt_spec_case
    ;

// inherited from grammar JmlParser
generic_spec_statement_case :(spec_var_decls)? 
      ( spec_header (generic_spec_statement_body)?
      | generic_spec_statement_body
      )
      { #generic_spec_statement_case =
            #([SPEC_CASE, "generic_spec_statement_case"],
                          #generic_spec_statement_case);
      }
    ;

// inherited from grammar JmlParser
generic_spec_statement_body :simple_spec_statement_body
    | LCURLY_VBAR generic_spec_statement_case_seq VBAR_RCURLY
    ;

// inherited from grammar JmlParser
generic_spec_statement_case_seq :generic_spec_statement_case (ALSO^ generic_spec_statement_case)*
    ;

// inherited from grammar JmlParser
simple_spec_statement_body :assignable_clause_seq ensures_clause_seq_opt signals_clause_seq_opt
      diverges_clause_seq_opt
      continues_clause_seq_opt breaks_clause_seq_opt returns_clause_seq_opt
    | ensures_clause_seq signals_clause_seq_opt diverges_clause_seq_opt
      continues_clause_seq_opt breaks_clause_seq_opt returns_clause_seq_opt
    | signals_clause_seq diverges_clause_seq_opt
      continues_clause_seq_opt breaks_clause_seq_opt returns_clause_seq_opt
    | diverges_clause_seq
      continues_clause_seq_opt breaks_clause_seq_opt returns_clause_seq_opt
    | continues_clause_seq breaks_clause_seq_opt returns_clause_seq_opt
    | breaks_clause_seq returns_clause_seq_opt
    | returns_clause_seq
    ;

// inherited from grammar JmlParser
spec_statement_jack :requires_clause_seq assignable_clause_seq_opt ensures_clause_seq_opt signals_clause_seq_opt
    | assignable_clause_seq ensures_clause_seq_opt signals_clause_seq_opt
    | ensures_clause_seq signals_clause_seq_opt 
    | signals_clause_seq 
    ;

// inherited from grammar JmlParser
abrupt_spec_case :(spec_var_decls)?
      ( spec_header (abrupt_spec_case_body)?
      | abrupt_spec_case_body
      )
      { #abrupt_spec_case = #([SPEC_CASE, "abrupt_spec_case"],
                              #abrupt_spec_case); }
    ;

// inherited from grammar JmlParser
abrupt_spec_case_body :assignable_clause_seq diverges_clause_seq_opt
      continues_clause_seq_opt breaks_clause_seq_opt returns_clause_seq_opt
    | diverges_clause_seq
      continues_clause_seq_opt breaks_clause_seq_opt returns_clause_seq_opt
    | continues_clause_seq breaks_clause_seq_opt returns_clause_seq_opt
    | breaks_clause_seq returns_clause_seq_opt
    | returns_clause_seq
    | LCURLY_VBAR abrupt_spec_case_seq VBAR_RCURLY
    ;

// inherited from grammar JmlParser
abrupt_spec_case_seq :abrupt_spec_case (ALSO^ abrupt_spec_case)*
    ;

// inherited from grammar JmlParser
continues_clause_seq_opt :(continues_clause)*
      {
        #continues_clause_seq_opt = #([CONT_SEQ,"continues_seq"],
                                      #continues_clause_seq_opt);
      }
    ;

// inherited from grammar JmlParser
continues_clause_seq :(continues_clause)+
      {
        #continues_clause_seq = #([CONT_SEQ,"continues_seq"],
                                      #continues_clause_seq);
      }
    ;

// inherited from grammar JmlParser
continues_clause :(CONTINUES^ | CONTINUES_REDUNDANTLY^)
      (target_label)? (T_NOT_SPECIFIED | predicate)? SEMI!
            { #continues_clause.setType(CONTINUES_KEYWORD); }
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToJmlSpecKeyword();
    }

// inherited from grammar JmlParser
target_label :R_ARROW^ LPAREN! IDENT RPAREN!
    ;

// inherited from grammar JmlParser
breaks_clause_seq_opt :(breaks_clause)*
      {
        #breaks_clause_seq_opt = #([BREAKS_SEQ,"breaks_seq"],
                                   #breaks_clause_seq_opt);
      }
    ;

// inherited from grammar JmlParser
breaks_clause_seq :(breaks_clause)+
      {
        #breaks_clause_seq = #([BREAKS_SEQ,"breaks_seq"],
                                #breaks_clause_seq);
      }
    ;

// inherited from grammar JmlParser
breaks_clause :(BREAKS^ | BREAKS_REDUNDANTLY^)
      (target_label)? (T_NOT_SPECIFIED | predicate)? SEMI!
            { #breaks_clause.setType(BREAKS_KEYWORD); }
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToJmlSpecKeyword();
    }

// inherited from grammar JmlParser
returns_clause_seq_opt :(returns_clause)*
      {
        #returns_clause_seq_opt = #([RETURNS_SEQ,"returns_seq"],
                                   #returns_clause_seq_opt);
      }
    ;

// inherited from grammar JmlParser
returns_clause_seq :(returns_clause)+
      {
        #returns_clause_seq = #([RETURNS_SEQ,"returns_seq"],
                                #returns_clause_seq);
      }
    ;

// inherited from grammar JmlParser
returns_clause :(RETURNS^ | RETURNS_REDUNDANTLY^)
      (T_NOT_SPECIFIED | predicate)? SEMI!
            { #returns_clause.setType(RETURNS_KEYWORD); }
    ;
exception 
catch [RecognitionException err] {
        reportError(err);
        consumeToJmlSpecKeyword();
    }

// inherited from grammar JmlParser
loop_invariant_seq_opt :(loop_invariant)*
        { #loop_invariant_seq_opt = #([LOOP_INV_SEQ, "loop_invariant_seq"],
                                      #loop_invariant_seq_opt);
        }
    ;

// inherited from grammar JmlParser
loop_invariant {
  String kw = "";
}
:( MAINTAINING^
      | MAINTAINING_REDUNDANTLY^
      | LOOP_INVARIANT^
      | LOOP_INVARIANT_REDUNDANTLY^
      )
      predicate SEMI!
            { #loop_invariant.setType(MAINTAINING_KEYWORD); }
    ;

// inherited from grammar JmlParser
variant_function_seq_opt :(variant_function)*
        { #variant_function_seq_opt = #([VF_SEQ, "variant_function_seq"],
                                        #variant_function_seq_opt);
        }
    ;

// inherited from grammar JmlParser
variant_function {
  String kw = "";
}
:( DECREASING^
      | DECREASING_REDUNDANTLY^
      | DECREASES^
      | DECREASES_REDUNDANTLY^
      )
      spec_expression SEMI!
            { #variant_function.setType(DECREASING_KEYWORD); }
    ;

// inherited from grammar JmlParser
expression_list[boolean in_spec] :expression[in_spec] (COMMA^ expression[in_spec])*
    ;

// inherited from grammar JmlParser
expression[boolean in_spec] :assignment_expr[in_spec]
    ;

// inherited from grammar JmlParser
assignment_expr[boolean in_spec] {
    int line = 0, col = 0;
}
:conditional_expr[in_spec]
        (   (   a:ASSIGN^
                    { line = a.getLine(); col = a.getColumn(); }
            |   ( b:PLUS_ASSIGN^
                    { line = b.getLine(); col = b.getColumn(); }
                | c:MINUS_ASSIGN^
                    { line = c.getLine(); col = c.getColumn(); }
                )
                { #assignment_expr.setType(ADDITIVE_ASSIGNMENT_OP); }
            |   ( d:STAR_ASSIGN^
                    { line = d.getLine(); col = d.getColumn(); }
                | e:DIV_ASSIGN^
                    { line = e.getLine(); col = e.getColumn(); }
                | f:MOD_ASSIGN^
                    { line = f.getLine(); col = f.getColumn(); }
                )
                { #assignment_expr.setType(MULTIPLICATIVE_ASSIGNMENT_OP); }
            |   ( g:SR_ASSIGN^
                    { line = g.getLine(); col = g.getColumn(); }
                | h:BSR_ASSIGN^
                    { line = h.getLine(); col = h.getColumn(); }
                | i:SL_ASSIGN^
                    { line = i.getLine(); col = i.getColumn(); }
                )
                { #assignment_expr.setType(SHIFT_ASSIGNMENT_OP); }
            |   ( j:BAND_ASSIGN^
                    { line = j.getLine(); col = j.getColumn(); }
                | k:BOR_ASSIGN^
                    { line = k.getLine(); col = k.getColumn(); }
                | l:BXOR_ASSIGN^
                    { line = l.getLine(); col = l.getColumn(); }
                )
                { #assignment_expr.setType(BITWISE_ASSIGNMENT_OP); }
            )
            assignment_expr[in_spec]
            {
                if (in_spec) {
                    reportError("assignment operators are not allowed in JML specification expressions",
                                line, col);
                }
            }
        )?
    ;

// inherited from grammar JmlParser
conditional_expr[boolean in_spec] :equivalence_expr[in_spec]
        ( QUESTION^ conditional_expr[in_spec] COLON! conditional_expr[in_spec] )?
    ;

// inherited from grammar JmlParser
equivalence_expr[boolean in_spec] {
    int line = 0, col = 0;
}
:implies_expr[in_spec]
          ( ( e:EQUIV^
                { line = e.getLine(); col = e.getColumn(); }
            | n:NOT_EQUIV^
                { line = n.getLine(); col = n.getColumn(); }
            )
            implies_expr[in_spec]
            {   #equivalence_expr.setType(EQUIVALENCE_OP);
                if (!in_spec) {
                    reportError("<==> and <=!=> can only be used in JML specification expressions",
                                line, col);
                }
            }
          )*
    ;

// inherited from grammar JmlParser
implies_expr[boolean in_spec] :logical_or_expr[in_spec]
        ( ( li:LIMPLIES^
            implies_non_backward_expr[in_spec]
            {
                #implies_expr.setType(IMPLICATION_OP);
                if (!in_spec) {
                    reportError("==> can only be used in JML specification expressions",
                                li.getLine(), li.getColumn());
                }
            }
          )?
        | ( bi:BACKWARD_IMPLIES^
            logical_or_expr[in_spec]
            {
                #implies_expr.setType(IMPLICATION_OP);
                if (!in_spec) {
                    reportError("<== can only be used in JML specification expressions",
                                bi.getLine(), bi.getColumn());
                }
            }
          )+ 
        )
    ;

// inherited from grammar JmlParser
implies_non_backward_expr[boolean in_spec] :logical_or_expr[in_spec]
          ( li:LIMPLIES^
            implies_non_backward_expr[in_spec]
            {   
                #implies_non_backward_expr.setType(IMPLICATION_OP);
                if (!in_spec) {
                    reportError("==> can only be used in JML specification expressions",
                                li.getLine(), li.getColumn());
                }
            }
          )?
    ;

// inherited from grammar JmlParser
logical_or_expr[boolean in_spec] :logical_and_expr[in_spec]
        ( LOR^
            logical_and_expr[in_spec]
            { #logical_or_expr.setType(LOGICAL_OP); }
        )*
    ;

// inherited from grammar JmlParser
logical_and_expr[boolean in_spec] :inclusive_or_expr[in_spec]
        ( LAND^
            inclusive_or_expr[in_spec]
            { #logical_and_expr.setType(LOGICAL_OP); }
        )*
    ;

// inherited from grammar JmlParser
inclusive_or_expr[boolean in_spec] :exclusive_or_expr[in_spec]
        ( BOR^
            exclusive_or_expr[in_spec]
            { #inclusive_or_expr.setType(BITWISE_OP); }
        )*
    ;

// inherited from grammar JmlParser
exclusive_or_expr[boolean in_spec] :and_expr[in_spec]
        ( BXOR^
            and_expr[in_spec]
            { #exclusive_or_expr.setType(BITWISE_OP); }
        )*
    ;

// inherited from grammar JmlParser
and_expr[boolean in_spec] :equality_expr[in_spec]
        ( BAND^
            equality_expr[in_spec]
            { #and_expr.setType(BITWISE_OP); }
        )*
    ;

// inherited from grammar JmlParser
equality_expr[boolean in_spec] :relational_expr[in_spec]
        ( ( NOT_EQUAL^ | EQUAL^ )
            relational_expr[in_spec]
            { #equality_expr.setType(EQUALITY_OP); }
        )*
    ;

// inherited from grammar JmlParser
relational_expr[boolean in_spec] :shift_expr[in_spec]
        ( ( ( ( LT^ | GT^ | LE^ | GE^ )
                { #relational_expr.setType(RELATIONAL_OP); }
            | iso:IS_SUBTYPE_OF^     // from ESC/Java
                {   if (!in_spec) {
                       reportError("<: can only be used in JML specification expressions",
                                iso.getLine(), iso.getColumn());
                    }
                }
            )
            shift_expr[in_spec]
            )*
        | "instanceof"^ type_spec
        )
    ;

// inherited from grammar JmlParser
shift_expr[boolean in_spec] :additive_expr[in_spec]
        ( (SL^ | SR^ | BSR^ )
            additive_expr[in_spec]
            { #shift_expr.setType(SHIFT_OP); }
        )*
    ;

// inherited from grammar JmlParser
additive_expr[boolean in_spec] :mult_expr[in_spec]
        ( ( PLUS^ | MINUS^ )
            mult_expr[in_spec]
            { #additive_expr.setType(ADDITIVE_OP); }
        )*
    ;

// inherited from grammar JmlParser
mult_expr[boolean in_spec] :unary_expr[in_spec]
        ( (STAR^ | DIV^ | MOD^ )
            unary_expr[in_spec]
            { #mult_expr.setType(MULTIPLICATIVE_OP); }
        )*
    ;

// inherited from grammar JmlParser
unary_expr[boolean in_spec] {
    int line = 0, col = 0;
}
:( i:INC^
          { line = i.getLine(); col = i.getColumn(); }
      | d:DEC^
          { line = d.getLine(); col = d.getColumn(); }
      ) unary_expr[in_spec]
        {
            #unary_expr.setType(PRE_INCREMENT_OP);
            if (in_spec) {
                reportError("++ and -- are not allowed in JML specification expressions",
                            line, col);
            }
        }
    | ( PLUS^ | MINUS^ ) unary_expr[in_spec]
        { #unary_expr.setType(UNARY_NUMERIC_OP); }
    | unaryExpressionNotPlusMinus[in_spec]
    ;

// inherited from grammar JmlParser
unaryExpressionNotPlusMinus[boolean in_spec] :BNOT^ unary_expr[in_spec]
            { #unaryExpressionNotPlusMinus.setType(UNARY_NUMERIC_OP); }
    | LNOT^ unary_expr[in_spec]
    | ( // subrule allows option to shut off warnings
            options {
                // "(int" ambig with postfixExpr due to lack of sequence
                // info in linear approximate LL(k).  It's ok.  Shut up.
                generateAmbigWarnings=false;
            }
        :! // If typecast is built in type, must be numeric operand
           // Also, no reason to backtrack if type keyword like int, float...
           LPAREN t:builtInType_spec RPAREN c:unary_expr[in_spec]
            { #unaryExpressionNotPlusMinus = #([CAST, "cast"], t, c);}
        |! // if it _looks_ like a cast, it _is_ a cast; else it's a "(expr)"
          ( LPAREN reference_type_spec RPAREN
                unaryExpressionNotPlusMinus[in_spec] )=>
          LPAREN t2:reference_type_spec RPAREN
          c2:unaryExpressionNotPlusMinus[in_spec]
            { #unaryExpressionNotPlusMinus = #([CAST, "cast"], t2, c2 ); }
        | postfix_expr[in_spec]
        )
    ;

// inherited from grammar JmlParser
builtInType_spec :builtInType (dims)?
    ;

// inherited from grammar JmlParser
reference_type_spec :reference_type (dims)?
    ;

// inherited from grammar JmlParser
postfix_expr[boolean in_spec] :primary_expr[in_spec] // start with a primary
        (   
            // qualified id (id.id.id.id...) -- build the name
            DOT^ ( IDENT
                 | "this"
                 | "class"
                 | new_expr[in_spec]
                 | "super" LPAREN^ ( expression_list[in_spec] )? RPAREN
                )
            // the above line needs a semantic check to make sure "class"
            //   is the _last_ qualifier.

            // allow ClassName[].class
        |   ( lbc:LBRACK^
                { #lbc.setType(ARRAY_DECLARATOR);
                  #lbc.setText("array_declarator");
                }
            RBRACK! )+
            DOT^ "class"

        // an array indexing operation
        |   LBRACK^ expression[in_spec] RBRACK!

        // method invocation
        // The next line is not strictly proper; it allows x(3)(4) or
        //   x[2](4) which are not valid in Java.  If this grammar were used
        //   to validate a Java program a semantic check would be needed, or
        //   this rule would get really ugly...
        |   LPAREN^
                ( expression_list[in_spec] )?
            RPAREN!
        )*

        // possibly add on a post-increment or post-decrement
        (   in:INC^
            {   #in.setType(POST_INCREMENT_OP);
                if (in_spec) {
                    reportError("++ is not allowed in JML specification expressions",
                                in.getLine(), in.getColumn());
                }
            }
        | de:DEC^
            {   #de.setType(POST_INCREMENT_OP);
                if (in_spec) {
                    reportError("-- is not allowed in JML specification expressions",
                                de.getLine(), de.getColumn());
                }
            }
        | //nothing
        )

        // look for int.class and int[].class
    |   builtInType 
        ( lbt:LBRACK^
            { #lbt.setType(ARRAY_DECLARATOR);
              #lbt.setText("array_declarator");
            }
          RBRACK! )*
        DOT^ "class"
    ;

// inherited from grammar JmlParser
primary_expr[boolean in_spec] :id:IDENT
    |   new_expr[in_spec]
    |   constant
    |   "super"
    |   "true"
    |   "false"
    |   "this"
    |   "null"
    |   jmlp:jml_primary
        {   
            if (!in_spec) {
                reportError("Can't use a jml-primary outside a specification",
                            ((LineAST)#jmlp).line, ((LineAST)#jmlp).column);
            }
        }
    |   LPAREN!
            ( expression[in_spec]
            | sqe:spec_quantified_expr       // added for JML
              { if (!in_spec) {
                    reportError("Can't use a quantifier outside a specification",
                                 ((LineAST)#sqe).line, ((LineAST)#sqe).column);
                }
              }
            | lbln:T_LBLNEG^ IDENT spec_expression  // added from ESC/Java
              { if (!in_spec) {
                    reportError("Can't use \\lblneg outside a specification",
                                 lbln.getLine(), lbln.getColumn());
                }
              }
            | lblp:T_LBLPOS^ IDENT spec_expression  // added from ESC/Java
              { if (!in_spec) {
                    reportError("Can't use \\lblpos outside a specification",
                                 lblp.getLine(), lblp.getColumn());
                }
              }
            )
        RPAREN!
    ;

// inherited from grammar JmlParser
jml_primary :T_RESULT
    |   T_OLD^ LPAREN! spec_expression RPAREN!
    |   T_NOT_MODIFIED^ LPAREN! store_references RPAREN!
    |   T_FRESH^ LPAREN! spec_expression_list RPAREN!
    |   T_REACH^ LPAREN! spec_expression
                      ( COMMA! reference_type (COMMA! store_ref_expression)? )?
               RPAREN!
    |   informal_desc
    |   T_NONNULLELEMENTS^ LPAREN! spec_expression RPAREN!
    |   T_TYPEOF^ LPAREN! spec_expression RPAREN!
    |   T_ELEMTYPE^ LPAREN! spec_expression RPAREN!
    |   T_TYPE^ LPAREN! type RPAREN!
    |   T_LOCKSET
    |   T_IS_INITIALIZED^ LPAREN! reference_type RPAREN!
    |   T_INVARIANT_FOR^ LPAREN! spec_expression RPAREN!
    ;

// inherited from grammar JmlParser
informal_desc {
  boolean in_ML_JML = lexer.ML_Jml_state;
}
:!  id1:INFORMAL_DESCRIPTION
        { if (in_ML_JML) {
            #id1.setText(remove_ats_after_newlines(#id1.getText()));
          }
          #informal_desc = #( [DINFORMALLY, "#informally#"], #id1);
        }
    ;

// inherited from grammar JmlParser
builtInType :( "void"
      | "boolean"
      | "byte"
      | "char"
      | "short"
      | "int"
      | "long"
      | "float"
      | "double"
      )
      { #builtInType.setType(JAVA_BUILTIN_TYPE); }
    ;

// inherited from grammar JmlParser
new_expr[boolean in_spec] :"new"^  type  new_suffix[in_spec]
    ;

// inherited from grammar JmlParser
new_suffix[boolean in_spec] :LPAREN!
            ( expression_list[in_spec] )?
        RPAREN! 
        // java 1.1
        ( class_block[in_spec, no_jml_stmts] )?

        //java 1.1
        // Note: This will allow bad constructs like
        //    new int[4][][3] {exp,exp}.
        //    There needs to be a semantic check here...
        // to make sure:
        //   a) [ expr ] and [ ] are not mixed
        //   b) [ expr ] and an init are not used together
    |   array_decl[in_spec] (array_initializer[in_spec])?

     // comprehension rule added for JML
    |   sce:set_comprehension
        {
            if (!in_spec) {
                reportError("cannot use set-comprehension outside specification",
                                 ((LineAST)#sce).line, ((LineAST)#sce).column);
            }
        }
    ;

// inherited from grammar JmlParser
array_decl[boolean in_spec] :(
            options {
                warnWhenFollowAmbig = false;
            }
        :
            // CONFLICT:
            // new_expression is a primary_expression which can be
            // followed by an array index reference.  This is ok,
            // as the generated code will stay in this loop as
            // long as it sees an LBRACK (proper behavior)
            dim_exprs[in_spec]
        |   dims
        )+
    ;

// inherited from grammar JmlParser
dim_exprs[boolean in_spec] :(
            options {
                warnWhenFollowAmbig = false;
            }
        :   LBRACK expression[in_spec] RBRACK!
        )+
        { #dim_exprs = #( [DIM_EXPRS, "#dim_exprs#"], dim_exprs ); }
    ;

// inherited from grammar JmlParser
dims :(
            options {
                warnWhenFollowAmbig = false;
            }
        :   LBRACK RBRACK!
        )+
        { #dims = #( [DIMS, "#dims#"], dims ); }
    ;

// inherited from grammar JmlParser
constant :NUM_INT
    |   CHAR_LITERAL
    |   STRING_LITERAL
    |   NUM_FLOAT
    ;

// inherited from grammar JmlParser
set_comprehension :LCURLY!
        type_spec quantified_var_declarator BOR! set_comprehension_pred
        RCURLY!
        { #set_comprehension = 
            #( [SET_COMPR, "#set_compr#"], #set_comprehension ); }
    ;

// inherited from grammar JmlParser
set_comprehension_pred :has_expression LAND^ predicate
        { #set_comprehension_pred.setType(LOGICAL_OP); }
    ;

// inherited from grammar JmlParser
has_expression :primary_expr[no_side_effects] ( DOT^  IDENT )+
        LPAREN^ ( IDENT ) RPAREN!
    ;

// inherited from grammar JmlParser
spec_quantified_expr :quantifier 
       wrap_quantified_var_decl SEMI! 
       ( spec_expression (SEMI! spec_expression)?
       | SEMI! spec_expression
       )
       { #spec_quantified_expr = #([QUANTIFIED_EXPR, "quantified_exp"],
                                   #spec_quantified_expr);
       }
    ;

// inherited from grammar JmlParser
quantifier :( T_FORALL | T_EXISTS | T_MAX | T_MIN | T_SUM | T_PRODUCT | T_NUM_OF )
      { #quantifier.setType(QUANTIFIER_TOKEN);
      }
    ;

// inherited from grammar JmlParser
wrap_quantified_var_decl :quantified_var_decl
      { #wrap_quantified_var_decl = #([QUANT_VARS, "quantified_vars"],
                                       #wrap_quantified_var_decl);
      }
    ;

// inherited from grammar JmlParser
quantified_var_decl :type_spec quantified_var_declarators
      { #quantified_var_decl = #([QUANT_VARS, "quantified_var_decl"],
                       #quantified_var_decl); }
    ;

// inherited from grammar JmlParser
quantified_var_declarators :quantified_var_declarator (COMMA^ quantified_var_declarator)*
    ;

// inherited from grammar JmlParser
quantified_var_declarator :IDENT (dims)?
    ;


