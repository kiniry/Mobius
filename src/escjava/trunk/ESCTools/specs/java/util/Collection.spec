// @(#)$Id$

// Adapted in part from Compaq SRC's specification for ESC/Java

// Copyright (C) 2000, 2002 Iowa State University

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

/** JML's specification of java.util.Collection.
 * Part of this specification is adapted from ESC/Java.
 * @version $Revision$
 * @author Gary T. Leavens
 * @author Brandon Shilling
 */
public interface Collection {
    
    //@ public model instance non_null Object[] _theCollection;

    // Subclasses may not support some operations.  The following
    // model variables should be given a representation that indicates
    // whether or not the associated operation is supported. 
    // Note that nullElementSupported is different than containsNull.
    // If nullElementSupported is false, an exception is thrown by the
    // implementation; if containsNull is false, that indicates that the
    // user has stated that the collection  is not allowed to contain null
    // (by the user's choice) even though the implementation supports it.
    // Clearly !nullElementSupported ==> !containsNull;

    //@ public model instance boolean addOperationSupported;
    //@ public model instance boolean removeOperationSupported;
    //@ public model instance boolean nullElementsSupported;

    /**
     * The (more specific) type of our elements (set by the user of the
     * object to state what is allowed to be added to the collection, and
     * hence what is guaranteed to be retrieved from the collection).  It is
     * not adjusted based on the content of the collection.
     **/
    //@ instance ghost public \TYPE elementType;

    /**
     * True iff we are allowed to contain null (not whether we do in fact
     * contain null).
     **/
    //@ instance ghost public boolean containsNull;
    //@ public instance invariant !nullElementsSupported ==> !containsNull;

    // Note: size() returns the smaller of Integer.MAX_VALUE and
    // the number of elements in the Collection 
    // FIXME - that condition is not in the javadoc specs.
    // Need \bigint returned from theCollection.size()?
    /*@ public normal_behavior
          ensures \result == _theCollection.length;
          ensures \result >= 0;
      @*/
    /*@ pure @*/ int size();

    /*@ public normal_behavior
          ensures \result == (size()==0);
      @*/
    /*@ pure @*/ boolean isEmpty();

    /*@ public behavior
      @   ensures !containsNull && o == null ==> !\result;
      @   ensures (o == null) || \typeof(o) <: elementType || !\result;
      @   ensures \result <==> (\exists int i; 0<=i && i<_theCollection.length;
                                 _theCollection[i] == o);
      @*/
    /*@ pure @*/ public boolean contains(Object o);

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result != null;
      @   ensures \result.elementType == elementType;
      @   ensures containsNull == \result.returnsNull;
      @*/
    /* FIXME +@ also public normal_behavior
      @   ensures (\forall int i; 0 <= i && i < size();
      @                 theCollection.has(\result.nthNextElement(i)));
      @   ensures (\forall Object o; theCollection.has(o) ==>
      @              (\exists int i; 0 <= i && i < size(); 
      @                 o == \result.nthNextElement(i)));
      @   ensures size() > 0 ==> \result.hasNext((int)(size()-1));
      @   ensures !\result.hasNext((int)(size()));
      @   ensures_redundantly
      @           (\forall int i; 0 <= i && i < size();
      @                 this.contains(\result.nthNextElement(i)));
      @   ensures_redundantly size() != 0 ==> \result.moreElements;
      @*/
    // FIXME - need specs for escjava case
    /*@ non_null @*/ /*@ pure @*/ Iterator iterator();

    /*@ public normal_behavior
      @   requires size() < Integer.MAX_VALUE;
      @   assignable \nothing;
      @   ensures \result != null;
      @   ensures containsNull || \nonnullelements(\result);
      @   ensures \result.length == size();
      @*/
    /* FIXME +@ also public normal_behavior
      @   ensures (\forall int i; 0 <= i && i < size();
      @                 theCollection.count(\result[i])
      @                 == JMLArrayOps.valueEqualsCount(\result, \result[i]));
      @*/
    // FIXME - need specs for escjava case
    /*@ pure @*/ Object[] toArray();
       
    /* FIXME +@ public normal_behavior
      @   old int colSize = theCollection.int_size();
      @   old int arrSize = a.length;
      @   requires a!= null && colSize < Integer.MAX_VALUE;
      @   requires elementType <: \elemtype(\typeof(a));
      @   requires (\forall Object o; contains(o); \typeof(o) <: \elemtype(\typeof(a)));
      @   {|
      @     requires colSize <= arrSize;
      @     assignable a[*];
      @     ensures \result == a;
      @     ensures (\forall int k; 0 <= k && k < colSize;
      @                  theCollection.count(\result[k])
      @                  == JMLArrayOps.valueEqualsCount(\result,
      @                                                  \result[k], colSize));
      @     ensures (\forall int i; colSize <= i && i < arrSize;
      @                             \result[i] == null);
      @     ensures_redundantly \typeof(\result) == \typeof(a);
      @   also
      @     requires colSize > arrSize;
      @     assignable \nothing;
      @     ensures \fresh(\result) && \result.length == colSize;
      @     ensures (\forall int k; 0 <= k && k < colSize;
      @        theCollection.count(\result[k])
      @        == JMLArrayOps.valueEqualsCount(\result, \result[k], colSize));
      @     ensures (\forall int k; 0 <= k && k < colSize;
      @                \result[k] == null || 
      @                \typeof(\result[k]) <: \elemtype(\typeof(\result)));
      @     ensures \typeof(\result) == \typeof(a);
      @   |}
      @*/
    /*@
      @ public exceptional_behavior
      @   requires a == null;
      @   assignable \nothing;
      @   signals (Exception e) (e instanceof NullPointerException) ;
      @ also
      @ public behavior
      @   requires a != null;
      @   requires !(\forall Object o; o != null && contains(o);
      @                                \typeof(o) <: \elemtype(\typeof(a)));
      @   assignable a[*];
      @   signals (Exception e) (e instanceof ArrayStoreException) ;
      @*/
    // FIXME - need specs for escjava case
    /*@ non_null @*/
    Object[] toArray(Object[] a);

    /*@ public behavior
      @   requires !containsNull ==> o != null;
      @   requires  (o == null) || \typeof(o) <: elementType;
      @*/
    //@  assignable _theCollection;
    /* FIXME +@
      @   assignable theCollection;
      @   ensures \result
      @         ==> theCollection.equals(\old(theCollection.insert(o)));
      @   ensures \result && \old(size() < Integer.MAX_VALUE)
      @           ==> size() == \old(size()+1);
	// FIXME - The above limitation to MAX_VALUE is just because
	// the arithmetic is not valid otherwise. Would \bigint 
	// arithmetic fix this?
      @   ensures !\result ==> size() == \old(size());
      @   ensures contains(o);
      @   signals (UnsupportedOperationException)
      @             (* this does not support add *);
      @   signals (NullPointerException)
      @             (* not allowed to add null *);
      @   signals (ClassCastException)
      @             (* class of specified element prevents it 
      @                from being added to this *);
      @   signals (IllegalArgumentException)
      @             (* some aspect of this element 
      @                prevents it from being added to this *);
      @   
      @*/
    // FIXME - need specs for escjava case
    boolean add(Object o);

    /*@ public behavior
      @   requires !containsNull ==> o != null;
      @   requires  (o == null) || \typeof(o) <: elementType;
      @*/
    //@  assignable _theCollection;
    /* FIXME +@
      @   assignable theCollection;
      @   ensures \result
      @         ==> theCollection.equals(\old(theCollection.remove(o)));
      @   ensures \result && \old(size() <= Integer.MAX_VALUE)
      @           ==> size() == \old(size()-1) && size() < Integer.MAX_VALUE
      @               && size() >= 0;
      @   ensures !\result || \old(size() == Integer.MAX_VALUE)
      @           ==> size() == \old(size());
      @   signals (UnsupportedOperationException)
      @            (* this does not support remove *);
      @   signals (ClassCastException)
      @            (* the type of this element is not 
      @               compatible with this *);
      @*/
    // FIXME - need specs for escjava case
    boolean remove(Object o);

    /* FIXME +@ public behavior
      @   requires c != null;
      @   requires c.elementType <: elementType;
      @   requires !containsNull ==> !c.containsNull;
      @   assignable \nothing;
          ensures \result <==> (\forall Object o; c.contains(o) ==> contains(o));
      @*/
    /* FIXME +@
      @   ensures \result <==> theCollection.containsAll(c);
      @   signals (ClassCastException)
      @           (* class of specified element prevents it 
      @              from being added to this *);
      @   signals (NullPointerException)
      @           (* argument contains null elements and this does not support 
      @              null elements *);
      @*/
    /*@
      @ public exceptional_behavior
      @  requires c == null;
      @  signals (NullPointerException);
      @*/
    /*@ pure @*/ boolean containsAll(Collection c);

    /* FIXME +@ public behavior
      @   requires c != null;
      @   requires c.elementType <: elementType;
      @   requires !containsNull ==> !c.containsNull;
      @   assignable theCollection;
      @   ensures theCollection
      @           .equals(\old(theCollection).union(c.theCollection));
      @   signals (UnsupportedOperationException)
      @           (* this does not support addAll *);
      @   signals (ClassCastException)
      @           (* class of specified element prevents it 
      @              from being added to this *);
      @   signals (IllegalArgumentException)
      @           (* some aspect of this element 
      @              prevents it from being added to this *);
      @   signals (NullPointerException)
      @           (* argument contains null elements and this does not support 
      @              null elements *);
      @ also public exceptional_behavior
      @  requires c == null;
      @  assignable \nothing;
      @  signals (NullPointerException);
      @*/
    boolean addAll(Collection c);

    /* FIXME +@ public behavior
      @   requires c != null;
      @   requires elementType <: c.elementType;
      @   requires !c.containsNull ==> !containsNull;
      @  assignable theCollection;
      @   ensures theCollection
      @           .equals(\old(theCollection).difference(c.theCollection));
      @   signals (UnsupportedOperationException)
      @               (* this does not support removeAll *);
      @   signals (ClassCastException)
      @             (* the type of one or more of the elements
      @                in c is not supported by this *);
      @   signals (NullPointerException)
      @           (* argument contains null elements and this does not support 
      @              null elements *);
      @ also public exceptional_behavior
      @  requires c == null;
      @  assignable \nothing;
      @  signals (NullPointerException);
      @*/
    boolean removeAll(Collection c);

    /* FIXME +@ public behavior
      @   requires c != null;
      @   requires elementType <: c.elementType;
      @   requires !c.containsNull ==> !containsNull;
      @  assignable theCollection;
      @   ensures theCollection
      @           .equals(\old(theCollection).intersection(c.theCollection));
      @   signals (UnsupportedOperationException)
      @            (* this does not support retainAll *);
      @   signals (ClassCastException)
      @            (* the type of one or more of the elements
      @               in c is not supported by this *);
      @   signals (NullPointerException)
      @           (* argument contains null elements and this does not support 
      @              null elements *);
      @ also public exceptional_behavior
      @  requires c == null;
      @  assignable \nothing;
      @  signals (NullPointerException);
      @*/
    boolean retainAll(Collection c);

    /* FIXME +@ public behavior
      @   assignable theCollection;
      @   ensures theCollection.isEmpty();
      @   ensures_redundantly size() == 0;
      @   signals (UnsupportedOperationException)
      @           (* clear is not supported by this *);
      @*/
    void clear();

    boolean equals(Object o);

    int hashCode();

    //@ public model int hashValue();
}
