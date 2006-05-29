// @(#)$Id: LineAST.java,v 1.18 2001/07/23 20:51:44 cheon Exp $

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


package jml;

import antlr.*;
import antlr.collections.*;
//import jml.attributes.*;
//import edu.iastate.cs.jml.models.*;

/** abstract syntax trees that track a line and column. */
public class LineAST extends CommonAST implements java.io.Serializable
{
    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	public int line;
    public int column;
    public TypeAttrib type;
    public Object etc;
    
    public void initialize (Token tok)
    {
	super.initialize(tok);
        if (tok instanceof LineToken) {
            LineToken lt = (LineToken)tok;
            line = lt.getLine();
            column = lt.getColumn();
	    etc = null;
        }
    }

    public void initialize (AST t)
    {
	super.initialize(t);
        if (t instanceof LineAST) {
            LineAST lt = (LineAST) t;
            line = lt.line;
            column = lt.column;
            type = lt.type;
	    etc = lt.etc;
        }
    }

    //[[[ use getNextSibling ]]]
    public void addSibling(LineAST node)
    {
    	LineAST t = (LineAST) this.right;
	if ( t!=null ) {
	    while ( t.right!=null ) {
		t = (LineAST) t.right;
	    }
	    t.right = node;
	}
	else {
	    this.right = node;
	}
     }

    // for XML serialization
    public static String encode(String text)
    {
	char c;
	StringBuffer n = new StringBuffer();
	if( text != null )
	{
	   for (int i=0; i < text.length(); i++)
	     {
		c = text.charAt(i);
		switch (c) {
		case '&' : { n.append("&amp;"); break; }
		case '<' : { n.append("&lt;"); break; }
		case '>' : { n.append("&gt;"); break; }
		case '"' : { n.append("&quot;"); break; }
		case '\'' : { n.append("&apos;"); break; }
		default : { n.append(c); break; }
		}
	     }
	}
	return new String(n);
    }

    public boolean equals(Object o) 
    {
        if (o instanceof LineAST) {
            LineAST oth = (LineAST)o;
            return super.equals(oth)
                && line == oth.line && column == oth.column
                && (type == null || type.equals(oth.type))
		&& (etc == null || etc.equals(oth.etc));
        } else {
            return false;
        }
    }

}



