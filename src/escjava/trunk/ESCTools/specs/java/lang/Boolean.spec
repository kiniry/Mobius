// @(#)$Id$

// Copyright (C) 2002 Iowa State University

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


package java.lang;

/** JML's specification of java.lang.Boolean.
 * @version $Revision$
 * @author Brandon Shilling
 * @author Gary T. Leavens
 * @author David R. Cok
 */
//-@ immutable
public final /*@ pure @*/ class Boolean implements java.io.Serializable {

    public static final Boolean TRUE;

    public static final Boolean FALSE;

    public static final Class	TYPE;

    //@ public model boolean theBoolean;
    //  represents theBoolean <- booleanValue();

    /*@ public normal_behavior
      @   assignable theBoolean;
      @   ensures theBoolean == value;
      @*/
    public Boolean(boolean value);

    /*@ public normal_behavior
      @   {|
      @     requires s != null && s.equalsIgnoreCase("true");
      @     ensures theBoolean;
      @   also
      @     requires s == null || !(s.equalsIgnoreCase("true"));
      @     ensures !theBoolean;
      @   |}
      @*/
    public /*@ pure @*/ Boolean(String s);
    
    /*@ public normal_behavior
      @   ensures \result == theBoolean;
      @*/
    public /*@ pure @*/ boolean booleanValue();

    /*@ public normal_behavior
      @   ensures \result != null && \result.equals(new Boolean(b));
      @   ensures_redundantly \result != null && \result.booleanValue() == b;
      @*/
    public static /*@ pure @*/ Boolean valueOf(boolean b);


    /*@ public normal_behavior
      @   {|
      @     requires s != null && s.equalsIgnoreCase("true");
      @     ensures \fresh(\result) && \result.booleanValue();
      @   also
      @     requires s == null || !(s.equalsIgnoreCase("true"));
      @     ensures \fresh(\result) && !\result.booleanValue();
      @   |}
      @*/
    public static /*@ pure @*/ Boolean valueOf(String s);

    /*@ public normal_behavior
      @   ensures valueOf(\result).booleanValue() == b;
      @*/
    public static /*@ pure @*/ String toString(boolean b);

    /*@ also
      @ public normal_behavior
      @   ensures valueOf(\result).booleanValue() == theBoolean;
      @*/
    public String toString();

    // inherited specification
    public int hashCode();

    /*@ also
      @ public normal_behavior
      @ {|
      @   requires obj != null && (obj instanceof Boolean);
      @   ensures \result == (theBoolean == ((Boolean) obj).booleanValue());
      @ also
      @   requires obj == null || !(obj instanceof Boolean);
      @   ensures !\result;
      @ |}
      @*/
    public /*@ pure @*/ boolean equals(Object obj);
    
    // FIXME - check if getPRoperty is case-insensitive; getBoolean is supposed to be
    /*@ public normal_behavior
      @   requires name != null && !name.equals("")
      @         && System.getProperty(name) != null;
      @   ensures \result == valueOf(System.getProperty(name)).booleanValue();
      @*/
    public static /*@ pure @*/ boolean getBoolean(String name);
}
