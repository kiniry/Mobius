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

/** JML's specification of java.lang.CharSequence.
 * @version $Revision$
 * @author Gary T. Leavens
 */
public /*+@ pure @+*/ interface CharSequence {

    //+@ public normal_behavior
    //@    ensures \result >= 0;
    //@ pure
    int length();

    /*+@   public normal_behavior
      @      requires 0 <= index && index < length();
      @      ensures (* \result is the character at the given index *);
      @  also
      @    public exceptional_behavior
      @      requires !(0 <= index && index < length());
      @      signals (IndexOutOfBoundsException);
      @+*/
    //+@ implies_that public normal_behavior
    //@    requires 0 <= index;
    char charAt(int index) throws IndexOutOfBoundsException;

    /*+@   public normal_behavior
      @      requires 0 <= start && start <= end && end <= length();
      @      ensures (* \result is the subsequence from start to end,
      @               not including the character at index end, if any *);
      @  also
      @    public exceptional_behavior
      @      requires start < 0 || end < 0 || end > length() || start > end;
      @      signals (IndexOutOfBoundsException);
      @+*/
    CharSequence subSequence(int start, int end)
        throws IndexOutOfBoundsException;

    /*+@ also
      @    public normal_behavior
      @      ensures \result != null
      @           && (* result is this sequence of characters *);
      @+*/
    public String toString();

    /** According to the javadocs, the equals method should not be called. */
    // +@ also
    // +@    requires false;
    //public boolean equals(Object obj);

    /** According to the javadocs, the hashCode method should not be called. */
    // +@ also
    // +@    requires false;
    //public int hashCode();
}
