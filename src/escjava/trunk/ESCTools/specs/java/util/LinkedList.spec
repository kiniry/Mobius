// Copyright (C) 2003 Iowa State University

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
// along with GNU Emacs; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

package java.util;


/** JML's specification of java.util.LinkedList.
 * @author Katie Becker
 * @author Gary T. Leavens
 * @author Erik Poll
 */

public class LinkedList extends AbstractSequentialList
    implements List, Cloneable, java.io.Serializable
{
	
    /*@ public normal_behavior
      @   ensures isEmpty();
      @*/
    /*@ pure @*/ public LinkedList();
          
    /*@   public normal_behavior
      @     requires c != null;
      @     assignable objectState;
      @ also
      @   public exceptional_behavior
      @     requires c == null;
      @     signals (Exception e) e instanceof NullPointerException;
      @*/
    /*@ pure @*/ public LinkedList(Collection c);
    
    /*@  public normal_behavior
      @    requires !isEmpty();
      @    ensures (\result == null) || \typeof(\result) <: elementType;
      @ also
      @  public exceptional_behavior
      @    requires isEmpty();
      @    signals (Exception e) e instanceof NoSuchElementException;
      @*/
    public /*@ pure @*/ Object getFirst();
    
    /*@  public normal_behavior
      @    requires !isEmpty();
      @    ensures (\result == null) || \typeof(\result) <: elementType;
      @ also
      @  public exceptional_behavior
      @    requires isEmpty();
      @    signals (Exception e) e instanceof NoSuchElementException; 
      @*/
    public /*@ pure @*/ Object getLast();

    /*@  public normal_behavior
      @    requires !isEmpty();
      @     assignable objectState;
      @    ensures ((\result == null) || \typeof(\result) <: elementType);
      @ also
      @  public exceptional_behavior
      @    requires isEmpty();
      @    assignable \nothing;
      @    signals (Exception e) e instanceof NoSuchElementException;
      @*/    
    public Object removeFirst();
 
    /*@  public behavior
      @    requires !isEmpty();
      @     assignable objectState;
      @    ensures ((\result == null) || \typeof(\result) <: elementType);
      @ also 
      @  public exceptional_behavior
      @    requires isEmpty();
      @    assignable \nothing;
      @    signals (Exception e) e instanceof NoSuchElementException;
      @*/     
    public Object removeLast();
  
    /*@ public normal_behavior
      @     assignable objectState;
      @*/    
    public void addFirst(Object o);

    /*@ public normal_behavior
      @     assignable objectState;
      @*/     
    public void addLast(Object o);
    
    // -- all other methods are specified by List --
    //@ pure
    public boolean contains(Object o);
    
    //@ pure
    public int size();
    
    public boolean add(Object o);

    public boolean remove(Object o);
    
    public boolean addAll(Collection c);
    
    public boolean addAll(int index, Collection c);
    
    public void clear();
    
    //@ pure
    public Object get(int index);
    
    public Object set(int index, Object element);
    
    public void add(int index, Object element);
    
    public Object remove(int index);
    
    //@ pure
    public int indexOf(Object o);
    
    //@ pure
    public int lastIndexOf(Object o);
    
    //@ pure
    public ListIterator listIterator(int index);
    
    /*@ also
      @   public normal_behavior
      @       ensures \result instanceof LinkedList && \fresh(\result)
      @          && ((LinkedList)\result).equals(this);
      @       ensures_redundantly \result != this;
      @*/
    public /*@ pure @*/ Object clone();

    //@ pure
    public Object[] toArray();
    
    public Object[] toArray(Object[] a);
}
