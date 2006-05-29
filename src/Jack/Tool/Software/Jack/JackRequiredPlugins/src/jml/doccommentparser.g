header {
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
}

// import other things we need
{
import java.io.*;
import antlr.*;
//import edu.iastate.cs.jml.checker.util.Debug;
}

class DocCommentParser extends Parser;
options {
    k = 1;
    importVocab=Java;
    codeGenMakeSwitchThreshold = 2;  // Some optimizations
    codeGenBitsetTestThreshold = 3;
    defaultErrorHandler = true;     // Don't generate parser error handlers
    buildAST = true;
}

// Define some methods and variables to use in the generated parser.
{
    // an initializer, to set the tree type
    {
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
}


// This is the start rule for this parser.
documentationCommentBody
{
	//    Debug.msg(debugOn, "entering documentationCommentBody ");
}
    : (description)* 
        (taggedParagraph)* 
        (j:jml_specs)? 
        EOF!
    ;
    // Some error handling.. has to be improved
    exception
    catch[RecognitionException e]
    {
        System.err.println(currentFile.getPath() + ":" 
            + LT(1).getLine() + ": " + e.toString());
    }
    catch[TokenStreamException err]
    {
        
        System.err.println(currentFile.getPath() + ":" + LT(1).getLine() + ": Error in Documentation Comment");
    }

description
{
//LB    Debug.msg(debugOn, "entering description ");
}
    : dc:DOC_NON_EMPTY_TEXTLINE 
    ;

taggedParagraph
{
    //LB Debug.msg(debugOn, "entering tagged paragraph ");
}
    : paragraph_tag (DOC_ATSIGN)* ( description )*
    ;

paragraph_tag
{
    //LB Debug.msg(debugOn, "entering paragraph_tag ");
}
    : DOC_AUTHOR
    | DOC_DEPRECATED
    | DOC_EXCEPTION
    | DOC_PARAM
    | DOC_RETURN
    | DOC_SEE
    | DOC_SERIALDATA
    | DOC_SERIAL
    | DOC_SERIALFIELD
    | DOC_SINCE
    | DOC_THROWS
    | DOC_VERSION
    | DOC_UNKNOWN_KEYWORD
    ;

jml_specs
{
    String r = "";
    //LB Debug.msg(debugOn, "entering jml_spec ");
}
    : ( pjtok:DOC_PRE_JML 
            (d:description
                {
                    r = r + "\n" + #d.getText(); // add NON_NL_WS       
                }
            )* 
            jptok:DOC_JML_PRE
            {
                if (!pjtok.getText()
                        .regionMatches(true,6,jptok.getText(),2,3)) {
                    // <JML> ended by </ESC> or vice versa
                    reportWarning(pjtok.getText() + " ended by "
                        + jptok.getText());
                }
            }
        )+
        {
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
                #jml_specs = #([DOC_JML_SPECS,"#doc_jml_specs#"]);
            } else {
                #jml_specs = #([DOC_JML_SPECS,"#doc_jml_specs#"], jp.getAST());
            }
            
            warnings += jp.warnings;    
            
        } 
        exception
        catch[RecognitionException e]
        {
            System.err.println(currentFile.getPath() + ":" 
                + e.toString());
            System.err.println("skipping to the end of this documentation comment");        
        }
    ;
