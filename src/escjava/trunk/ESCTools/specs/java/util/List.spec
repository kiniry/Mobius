// @(#)$Id$

// Copyright (C) 2000 Iowa State University

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

/** JML's specification of java.util.List.
 * @version $Revision$
 * @author Brandon Shilling
 * @author Gary T. Leavens
 * @author Erik Poll
 */
public interface List extends Collection {

    // specification inherited
    //@ pure
    int size();

    // specification inherited
    //@ pure
    boolean isEmpty();

    // specification inherited
    //@ pure
    boolean contains(Object o);

    /*@ also
      @ public behavior
      @   ensures \result != null;
      @   ensures size() < Integer.MAX_VALUE
      @       ==> (\forall int i; 0 <= i && i < size();
      @                \result.hasNext(i) && \result.nthNextElement(i)
      @                 == toArray()[i]);
      @*/
    /*@ pure @*/ Iterator iterator();

    /*@ also
      @  public normal_behavior
      @   requires size() < Integer.MAX_VALUE;
      @   ensures \result != null;
      @   ensures \result.length == size();
      @*/
    //@ pure
    Object[] toArray();

    /*@ also
      @ public normal_behavior
      @   old int arrSize = a.length;
      @   old int colSize = size();
      @   requires a!= null; 
      @   requires elementType <: \elemtype(\typeof(a));
      @   requires (\forall Object o; contains(o); \typeof(o) <: \elemtype(\typeof(a)));
      @   {|
      @     requires colSize <= arrSize;
      @     assignable a[*];
      @     ensures \result == a;
      @     ensures (\forall int k; 0 <= k && k < colSize;
      @                 get(k) == \result[k]);
      @     ensures (\forall int i; colSize <= i && i < arrSize;
      @                            \result[i] == null);
      @   also
      @     requires colSize > arrSize;
      @     assignable \nothing;
      @     ensures \fresh(\result) && \result.length == colSize;
      @     ensures (\forall int k; 0 <= k && k < colSize;
      @                            get(k) == \result[k]);
      @   |}
      @*/
    Object[] toArray(Object[] a);

    boolean add(Object o);

    boolean remove(Object o);

    // specification inherited
    //@ pure
    boolean containsAll(Collection c);

    // specification inherited
    boolean addAll(Collection c);

    /*@   public behavior
      @     requires c != null;
      @     requires 0 <= index && index <= size();
      @     requires c.elementType <: elementType;
      @     requires !containsNull ==> !c.containsNull;
      @     assignable objectState;
      @     signals (UnsupportedOperationException)
      @              (* if this operation is not supported *);
      @     signals (IllegalArgumentException)
      @              (* if some aspect of c prevents
      @                 its elements from being added to the list *);
      @ also
      @   public exceptional_behavior
      @     requires c == null || !(0 <= index && index <= size())
      @             || !(c.elementType <: elementType)
      @             || (!containsNull && c.containsNull);
      @     assignable \nothing;
      @     signals (ClassCastException)
      @             c != null && !(c.elementType <: elementType);
      @     signals (NullPointerException) c == null;
      @     signals (IndexOutOfBoundsException)
      @             !(0 <= index && index <= size());
      @*/
    boolean addAll(int index, Collection c);

    // specification inherited
    boolean removeAll(Collection c);

    // specification inherited
    boolean retainAll(Collection c);

    // specification inherited
    void clear();

    /*@ also
      @ public normal_behavior
      @   requires o instanceof List && size() == ((List) o).size();
      @  ensures \result == (\forall int i; 0 <= i && i < size(); 
      @               (get(i) == null
      @                && ((List) o).get(i) == null) 
      @            || (get(i).equals(((List) o).get(i))));
      @  ensures \result == (\forall int i; 0 <= i && i < size(); 
      @               (get(i) == null
      @                && ((List) o).get(i) == null) 
      @            || (get(i).equals(((List) o).get(i))));
      @ also public normal_behavior
      @   requires !(o instanceof List && size() == ((List) o).size());
      @   ensures !\result;
      @*/
    /*@ pure @*/ boolean equals(Object o);

    // specification inherited
    int hashCode();

    /*@ public normal_behavior
      @   requires 0 <= index && index < size();
      @ also
      @ public exceptional_behavior
      @   requires !(0 <= index && index < size());
      @   signals (IndexOutOfBoundsException);
      @
      @ implies_that
      @   public normal_behavior
      @     requires index >= 0;
      @     ensures (\result == null) || \typeof(\result) <: elementType;
      @     ensures !containsNull ==> \result != null;
      @*/
    /*@ pure @*/ Object get(int index);

    /*@
      @ public behavior
      @ requires !containsNull ==> element != null;
      @ requires (element == null) || \typeof(element) <: elementType;
      @ {|
      @   requires 0 <= index && index < size();
      @   assignable objectState;
      @   ensures \result == (\old(get(index)));
      @   signals (UnsupportedOperationException)
      @           (* set method not supported by list *);
      @   signals (ClassCastException)
      @           (* class of specified element prevents it
      @              from being added to this *);
      @   signals (NullPointerException)
      @            (* element is null and null elements
      @               not supported by this *);
      @   signals (IllegalArgumentException)
      @            (* some aspect of element prevents it
      @               from being added to this *);
      @ also
      @   requires !(0 <= index && index < size());
      @   assignable \nothing;
      @   ensures false;
      @   signals (IndexOutOfBoundsException);
      @ |}
      @*/
    Object set(int index, Object element);
    
    /*@ public behavior
      @   requires !containsNull ==> element != null;
      @   requires (element == null) || \typeof(element) <: elementType;
      @   {|
      @     requires  0 <= index && index < size();
      @     assignable objectState;
      @     ensures (element == null && get(index) == null)
      @          || (get(index).equals(element))
      @          && (\forall int i; 0 <= i && i < index;
      @                     (get(i) == null
      @                      && \old(this.get(i)) == null)    
      @                  || get(i).equals(\old(this.get(i))))
      @          && (\forall int i; index <= i && i < \old(size());
      @                     (get((int)(i+1)) == null
      @                      && \old(this.get(i)) == null)    
      @                  || get((int)(i+1))
      @                                    .equals(\old(this.get(i))));

      @     signals (UnsupportedOperationException)
      @             (* add method not supported by list *);
      @     signals (ClassCastException)
      @             (* class of specified element prevents it
      @                from being added to this *);
      @     signals (NullPointerException)
      @             (* element is null and null elements are not
      @                supported by this *);
      @     signals (IllegalArgumentException)
      @             (* some aspect of element
      @                prevents it from being added to this *);
      @ also
      @   requires !(0 <= index && index < size());
      @   assignable \nothing;
      @   ensures false;
      @   signals (IndexOutOfBoundsException);
      @ |}
      @*/
    void add(int index, Object element);

    /*@ public behavior
      @ {|
      @   requires  0 <= index && index < size();
      @   assignable objectState;
      @   ensures \result == (\old(get(index))) ;
      @   ensures (\forall int i; 0 <= i && i < index;
      @                   (get(i) == null
      @                    && \old(this.get(i)) == null)    
      @                || get(i) == (\old(this.get(i))))
      @        && (\forall \bigint i; index <= i && i < (\old(size() - 1) );
      @                   (get((int)i) == null
      @                    && \old(this.get((int)(i+1))) == null)    
      @                || get((int)i) == (\old(this.get((int)(i+1)))));
      @   signals (UnsupportedOperationException)
      @            (* remove method not supported by list *);
      @ also
      @   requires  0 <= index && index < size();
      @   assignable objectState;
      @   ensures (\result == null) || \typeof(\result) <: elementType;
      @   ensures !containsNull ==> \result != null;
      @ also
      @   requires !(0 <= index && index < size());
      @   assignable \nothing;
      @   ensures false;
      @   signals (IndexOutOfBoundsException);
      @ |}
      @*/
    Object remove(int index);

    /*@ public behavior
      @   requires !containsNull ==> o != null;
      @   requires (o == null) || \typeof(o) <: elementType;
      @   ensures \result != -1 && get(\result) == null
      @           ==> o == null;
      @   ensures \result != -1 && get(\result) != null
      @           ==> get(\result).equals(o)
      @               && indexOf(o) == \result;
      @   signals (ClassCastException)
      @           (* class of specified element is incompatible with this *);
      @   signals (NullPointerException)
      @            (* element is null and null elements are not
      @               supported by this *);
      @ implies_that
      @   ensures \result != -1
      @       ==> (\forall int i; 0 <= i && i < \result;
      @                 (get(i) == null && o != null)
      @              || (get(i) != null && !get(i).equals(o)));
      @*/
    /*@ pure @*/ int indexOf(Object o);

    /*@ public behavior
      @   requires !containsNull ==> o != null;
      @   requires (o == null) || \typeof(o) <: elementType;
      @   ensures \result != -1 && get(\result) == null
      @           ==> o == null;
      @   ensures \result != -1 && get(\result) != null 
      @            ==> get(\result).equals(o);
      @   signals (ClassCastException)
      @           (* class of specified element is incompatible with this *);
      @   signals (NullPointerException)
      @           (* element is null and null elements are not
      @              supported by this *);
      @ implies_that
      @   ensures \result != -1
      @       ==> (\forall int i; \result < i && i < size();
      @                 (get(i) == null && o != null)
      @              || (get(i) != null && !get(i).equals(o)));
      @*/
    /*@ pure @*/ int lastIndexOf(Object o);

    /*@ 
      @ public normal_behavior
      @   ensures \result != null && size() < Integer.MAX_VALUE
      @       ==> (\forall int i; 0 <= i && i < size();
      @                \result.hasNext(i) && \result.nthNextElement(i)
      @                 == toArray()[i]);
      @   ensures \result.elementType == elementType;
      @   ensures containsNull == \result.returnsNull;
      @*/
    /*@ pure @*/ /*@ non_null @*/ ListIterator listIterator();

    /*@ 
      @ public normal_behavior
      @   requires 0 <= index && index < size();
      @   ensures \result != null && size() < Integer.MAX_VALUE
      @       ==> (\forall int i; index <= i && i < size();
      @                \result.hasNext(i) && \result.nthNextElement(i)
      @                 == toArray()[i]);
      @ also
      @ public exceptional_behavior
      @   requires index < 0 && size() <= index;
      @   signals (IndexOutOfBoundsException);
      @
      @  implies_that
      @     ensures \result.elementType == elementType;
      @     ensures containsNull == \result.returnsNull;
      @*/
    /*@ pure @*/ /*@ non_null @*/ ListIterator listIterator(int index);

    /*@ public normal_behavior
      @   requires 0 <= fromIndex && fromIndex <= size() 
      @         && 0 <= toIndex && toIndex <= size()
      @         && fromIndex <= toIndex;
      @ also
      @ public exceptional_behavior
      @   requires !(0 <= fromIndex && fromIndex <= size())
      @         || !( 0 <= toIndex && toIndex <= size())
      @         || !(fromIndex <= toIndex);
      @   signals (IndexOutOfBoundsException);
      @
      @ implies_that
      @   public normal_behavior
      @     requires 0 <= fromIndex && fromIndex <= toIndex;
      @*/
    /*@ pure @*/ List subList(int fromIndex, int toIndex);
}
