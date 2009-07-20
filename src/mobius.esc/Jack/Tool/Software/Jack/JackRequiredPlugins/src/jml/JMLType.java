// @(#)$Id: JMLType.java,v 1.42 2001/02/22 03:00:34 leavens Exp $

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

/** Objects with a clone and equals method.
    JMLObjectType and JMLValueType are refinements
    for object and value containers (respectively).
    @see JMLObjectType
    @see JMLValueType
 **/
public interface JMLType extends Cloneable, java.io.Serializable {

  /*@ also
    @   public normal_behavior
    @     ensures \result instanceof JMLType
    @           && ((JMLType)\result).equals(this);
    @*/
  public /*@ pure @*/ Object clone();    

  /*@ also
    @   public normal_behavior
    @     ensures \result <==>
    @             (* ob2 is not distinguishable from this,
    @                except by using mutation or == *);
    @ implies_that
    @   public normal_behavior
    @   {|
    @      requires ob2 instanceof JMLType;
    @      ensures ob2.equals(this) == \result;
    @    also
    @      requires ob2 == this;
    @      ensures \result <==> true;
    @   |}
    @*/
  public /*@ pure @*/ boolean equals(Object ob2);    
}
