// @(#)$Id$

// Copyright (C) 2004 Iowa State University

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

package java.util;

/** JML's specification of ArrayList.
 *  @author Ajani Thomas
 *  @author Gary T. Leavens
 */
public class ArrayList extends AbstractList
    implements List, RandomAccess, Cloneable, java.io.Serializable
{

    /** This represents the size of the array used to store the elements 
     *  in the ArrayList.
     **/
    /*@ public model int capacity; in objectState;
      @*/

    // METHODS AND CONSTRUCTORS
    /*@  public normal_behavior
      @   requires 0 <= initialCapacity;
      @   assignable objectState;
      @   ensures capacity == initialCapacity;
      @   ensures this.isEmpty();
      @ also
      @  public exceptional_behavior
      @   requires initialCapacity < 0;
      @   assignable \nothing;
      @   signals (IllegalArgumentException) initialCapacity < 0;
      @*/
    /*@ pure @*/ public ArrayList(int initialCapacity);

    /*@  public normal_behavior
      @   assignable objectState;
      @   ensures capacity == 10;
      @   ensures this.isEmpty();
      @*/
    /*@ pure @*/ public ArrayList();

    /*@  public normal_behavior
      @   requires c != null;
      @   requires c.size()*1.1 <= Integer.MAX_VALUE;
      @   assignable objectState;
      @   ensures this.size() == c.size();
      @   ensures (\forall int i; 0 <= i && i < c.size();
      @                     this.get(i).equals(c.iterator().nthNextElement(i)));
      @   ensures capacity == c.size()*1.1;
      @ also
      @  public exceptional_behavior
      @   requires c == null;
      @   assignable \nothing;
      @   signals (NullPointerException) c == null;
      @*/
    /*@ pure @*/ public ArrayList(Collection c);

    /*@  public normal_behavior
      @   assignable objectState;
      @   ensures capacity == this.size();
      @*/
    public void trimToSize();

    /*@  public normal_behavior
      @   assignable objectState;
      @   ensures capacity >= minCapacity;
      @*/
    public void ensureCapacity(int minCapacity);

    // specification inherited from List
    public /*@ pure @*/ int size();

    // specification inherited from List
    public /*@ pure @*/ boolean isEmpty();

    // specification inherited from List
    public /*@ pure @*/ boolean contains(Object elem);

    // specification inherited from List
    public /*@ pure @*/ int indexOf(Object elem);

    // specification inherited from List
    public /*@ pure @*/ int lastIndexOf(Object elem);

    // specification inherited from Object
    /*@ also
      @  public normal_behavior
      @   ensures \result != this;
      @   ensures \result.getClass() == this.getClass();
      @   ensures \result.equals(this);
      @   ensures \result != null;
      @   ensures ((ArrayList)\result).size() == this.size();
      @   ensures (\forall int i; 0 <= i && i < this.size();
      @             ((ArrayList)\result).get(i) == this.get(i));
      @*/
    public /*@ pure @*/ Object clone();

    // specification inherited from List
    public /*@ pure @*/ Object[] toArray();

    // specification inherited from List
    /*@ also
      @  public exceptional_behavior
      @   requires elementType <: \elemtype(\typeof(a));
      @   assignable \nothing;
      @   signals (ArrayStoreException);
      @*/
    public Object[] toArray(Object[] a) throws ArrayStoreException;

    // specification inherited from List
    /*@ also
      @  public exceptional_behavior
      @   requires index < 0 || index >= this.size();
      @   signals (IndexOutOfBoundsException);
      @*/
    public /*@ pure @*/ Object get(int index) throws ArrayStoreException;

    // specification inherited from List
    /*@ also
      @  public exceptional_behavior
      @   requires index < 0 || index >= this.size();
      @   assignable \nothing;
      @   signals (IndexOutOfBoundsException);
      @*/
    public Object set(int index, Object element) throws IndexOutOfBoundsException;

    // specification inherited from List
    public boolean add(Object o);

    // specification inherited from List
    /*@ also
      @  public exceptional_behavior
      @   requires index < 0 || index >= this.size();
      @   assignable \nothing;
      @   signals (IndexOutOfBoundsException);
      @*/
    public void add(int index, Object element) throws IndexOutOfBoundsException;

    // specification inherited from List
    /*@ also
      @  public exceptional_behavior
      @   requires index < 0 || index >= this.size();
      @   assignable \nothing;
      @   signals (IndexOutOfBoundsException);
      @*/
    public Object remove(int index) throws IndexOutOfBoundsException;

    // specification inherited from List
    public void clear();

    // specification inherited from List
    public boolean addAll(Collection c);

    // specification inherited from List
    /*@ also
      @  public exceptional_behavior
      @   requires index < 0 || index >= this.size() || c == null;
      @   assignable \nothing;
      @   signals (IndexOutOfBoundsException) index < 0 || index >= this.size();
      @   signals (NullPointerException) c == null;
      @*/
    public boolean addAll(int index, Collection c) throws IndexOutOfBoundsException;

    // specification inherited from AbstractList
    protected void removeRange(int fromIndex, int toIndex) throws IndexOutOfBoundsException;
} 
