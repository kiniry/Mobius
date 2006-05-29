header
{
// @(#)$Id: doccommentlexer.g,v 1.10 2001/08/02 18:36:20 leavens Exp $

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

//----------------------------------------------------------------------------
// The Documentation Comment scanner
//----------------------------------------------------------------------------

    package jml;
}

class DocCommentLexer extends Lexer;

options {
    k = 3;
    charVocabulary = '\3'..'\377';
    importVocab=DocCommentParser;
    testLiterals=false;     // don't automatically test for literals
}

// Define some methods and variables to use in the generated lexer.
{
    // an initializer, to set the token type
    {
        setTokenObjectClass("jml.LineToken");
    }
    
    private DocLiteralsTable atsignKeywords = new DocLiteralsTable();
    
    public void tab() {
        int c = getColumn();
        int nc = c + 8 - (c % 8);
        setColumn( nc );
    }
}

protected
DOC_NON_NL_WS
    : (' ' | '\t' | '\f')
    ;

DOC_NL_WS
    : ( "\r\n"  // Evil DOS
        |   '\r'    // Macintosh
        |   '\n'    // Unix (the right way)
        )
        { newline(); }
        (DOC_NON_NL_WS)*
        (('*')+ (DOC_NON_NL_WS)*)?
        { newline(); _ttype = Token.SKIP; }
    ;

protected
DOC_PRE_JML
    : ("<PRE>"|"<pre>")
        (DOC_NON_NL_WS)*
        ("<JML>"|"<jml>"|"<ESC>"|"<esc>")
    ;

protected
DOC_JML_PRE
    : ("</JML>"|"</jml>"|"</ESC>"|"</esc>")
        (DOC_NON_NL_WS)*
        ("</PRE>"|"</pre>")
    ;


DOC_ATSIGN
    : '@'
    ;

DOC_ATSIGN_KEYWORD
    : DOC_ATSIGN ('a' .. 'z' | 'A' .. 'Z')+
        {  _ttype = atsignKeywords.lookup(text, DOC_UNKNOWN_KEYWORD);
        }
        (DOC_NON_NL_WS)*
    ;

DOC_NON_EMPTY_TEXTLINE
    : (DOC_PRE_JML) => DOC_PRE_JML
        {  _ttype =  DOC_PRE_JML;
        }
    | (DOC_JML_PRE) => DOC_JML_PRE
        {  _ttype =  DOC_JML_PRE;
        }
    | { LA(1) != '@' && LA(1) != '\r' && LA(1) != '\n'
        && LA(1) != '\t' && LA(1) != '\f'
        && LA(1) != EOF_CHAR  }?
        ~('@'|'\r'|'\n')
        ( { LA(1) != '\r' && LA(1) != '\n' && LA(1) != EOF_CHAR }?
            ~('\r'|'\n') )*
    ;
