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

// import other things we need
{
import java.io.*;
import antlr.*;
//LB import edu.iastate.cs.jml.checker.attributes.*;
}

class JmlDeclParser extends JmlParser;


// A type definition in a file is either a class or interface definition.
type_definition
// added doc_comment for JML
    :   (doc_comment!)? modifiers class_or_interface_def
    |!  SEMI
    ;
    exception // for rule
    catch [RecognitionException err] {
        reportError(err);
        consumeToTopLevelKeyword();
    }


field[boolean in_spec, boolean in_model_prog]
{
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
    exception // for rule
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

method_spec_first_decl[AST m, boolean in_model_prog]
    :!   mspec:method_specification[m]
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

method_decl[boolean in_model_prog]
    :!  t:type_spec mh:method_head
        (mods:modifiers method_specification[#mods]!)?
        method_body[in_model_prog]!
        { #method_decl = #( [METH, "#meth#"], #t, #mh, [SEMI, ";"] ); }
    |!  ch:method_head
        (mds:modifiers method_specification[#mds]!)?  // constructor
        method_body[in_model_prog]!
        { #method_decl = #( [CONSTRUCTOR, "#constr#"], #ch, [SEMI, ";"] ); }
    ;

variable_declarator[boolean in_spec]
    :   IDENT (dims)? ( ASSIGN! initializer[in_spec]! )?
    ;

// A declaration is the creation of a reference or primitive-type variable
variable_decls[boolean in_spec]
    :   type_spec variable_declarators[in_spec] ( jml_var_assertion! )?
        { #variable_decls = #( [VAR_DECL, "#vardecl#"], variable_decls ); }
    ;
