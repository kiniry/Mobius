// @(#)$Id: Modifiers.java,v 1.2 2001/02/22 02:59:40 leavens Exp $

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

/** an attribute for the AST which represents a set of modifiers **/
public class Modifiers extends MTypeAttrib 
{
    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public Modifiers ()
    {
        modifiers = new ModifierSet();
    }

    public Modifiers (ModifierSet ms)
    {
        modifiers = ms;  // ModifierSet is a pure type
    }

    public Modifiers (Modifier m)
    {
        modifiers = new ModifierSet(m);
    }

    public Object clone () 
    {
        Modifiers t = new Modifiers ();
        t.setModifiers(modifiers);
        return t;
    }

    public boolean equals (Object o) 
    {
        return (o instanceof Modifiers) 
            && modifiers.equals(((Modifiers)o).modifiers);
    }

    public String toString () 
    {
        return modifiers.toString();
    }
}





