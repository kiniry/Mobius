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

    //@ also public behavior
    //@   ensures \result <==> (\exists int i; 0<=i && i<size(); nullequals(o,get(i)));
    //@ pure
    boolean contains(Object o);

    /*@ also
      @ public behavior
      @   ensures \result != null;
      @*/
    /* FIXME
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
      @   ensures (\forall int i; 0<=i && i < size(); \result[i] == _theCollection[i]);
      @*/
    //@ pure
    Object[] toArray();

    /*@ also
      @ public normal_behavior
      @   old int arrSize = a.length;
      @   old int colSize = size();
      @   requires a!= null; 
      @   requires elementType <: \elemtype(\typeof(a));
      @   requires (\forall Object o; contains(o); \typeof(o) <: \elemtype(\typeof(a))); // FIXME - implied by the precondition above
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
              // FIXME - spec the exceptions
      @*/
    Object[] toArray(Object[] a);

    //@ also public normal_behavior
    //@   requires \typeof(o) <: elementType;
    //@   requires !containsNull ==> o != null;
    //@   assignable _theCollection;
    //@   ensures size() == \old(size()+1);
    //@   ensures get(size()-1) == o;
    //@   ensures (\forall int i; 0<=i && i <size(); _theCollection[i] == \old(_theCollection[i]));
    boolean add(Object o);


    // FIXME
    //@ also public normal_behavior
    //@   requires contains(o);
    //@   assignable _theCollection;
    //@   ensures size() == \old(size()-1);
            // FIXME - spec what is missing
    //@ also public normal_behavior
    //@   requires !contains(o);
    //@   assignable \nothing;
    // FIXME - watch out for optional exceptions
    boolean remove(Object o);

    // specification inherited
    //@ pure
    boolean containsAll(Collection c);

    // FIXME
    boolean addAll(Collection c);

    // FIXME - spec the contents of the new list
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

    // FIXME
    boolean removeAll(Collection c);

    // FIXME
    boolean retainAll(Collection c);

    // specification inherited
    void clear();

    /*@ also
      @ public normal_behavior
      @   requires o instanceof List && size() == ((List) o).size();
      @   ensures \result <==> (\forall int i; 0<=i && i <size(); 
                           _theCollection[i] == \old(_theCollection[i]));
      @ also public normal_behavior
      @   requires !(o instanceof List && size() == ((List) o).size());
      @   ensures !\result;
      @*/
    /*@ pure @*/ boolean equals(Object o);

    // specification inherited
    int hashCode();

    /*@ public normal_behavior
      @   requires 0 <= index && index < size();
      @   ensures \result == _theCollection[index];
      @   ensures (\result == null) || \typeof(\result) <: elementType;
      @   ensures !containsNull ==> \result != null;
      @ also
      @ public exceptional_behavior
      @   requires !(0 <= index && index < size());
      @   signals_only IndexOutOfBoundsException;
      @
      @ implies_that
      @   public normal_behavior
      @     requires index >= 0;
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
      @   ensures get(index) == element;
      @   ensures (\forall int i; 0<=i && i<size() && i != index;
                             get(i) == \old(get(i)));
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
      @     ensures (get(index) == (element))
      @          && (\forall int i; 0 <= i && i < index;
      @                     get(i) == \old(get(i)))
      @          && (\forall int i; index <= i && i < \old(size());
      @                     \old(get(i)) == get(i+1));

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
      @                get(i) == (\old(this.get(i))))
      @        && (\forall \bigint i; index <= i && i < (\old(size() - 1) );
      @                 get((int)i) == (\old(this.get((int)(i+1)))));
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
      @   signals_only IndexOutOfBoundsException;
      @ |}
      @*/
    Object remove(int index);

    /*@ public behavior
      @   ensures \result >= -1 && \result < size();
      @   ensures \result != -1 ==> nullequals(o,get(\result));
      @   ensures (\forall int i; 0<=i && i < \result; !nullequals(o,get(i)));
      @   ensures \result == -1 <==> !contains(o);
      @   signals (ClassCastException)
      @           (* class of specified element is incompatible with this *);
      @   signals (NullPointerException)
      @            (* element is null and null elements are not
      @               supported by this *);
      @*/
    /*@ pure @*/ int indexOf(Object o);

    /*@ public behavior
      @   ensures \result >= -1 && \result < size();
      @   ensures \result != -1 ==> nullequals(o,get(\result));
      @   ensures (\forall int i; \result<i && i < size(); !nullequals(o,get(i)));
      @   ensures \result == -1 <==> !contains(o);
      @   signals (ClassCastException)
      @           (* class of specified element is incompatible with this *);
      @   signals (NullPointerException)
      @            (* element is null and null elements are not
      @               supported by this *);
      @*/
    /*@ pure @*/ int lastIndexOf(Object o);

    /* FIXME @ 
      @ public normal_behavior
      @   ensures \result != null && size() < Integer.MAX_VALUE
      @       ==> (\forall int i; 0 <= i && i < size();
      @                \result.hasNext(i) && \result.nthNextElement(i)
      @                 == toArray()[i]);
      @   ensures \result.elementType == elementType;
      @   ensures containsNull == \result.returnsNull;
      @*/
    /*@ pure @*/ /*@ non_null @*/ ListIterator listIterator();

    /* FIXME @ 
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

    // FIXME - changes to a sublist affect the list it is a sublist of!!!
    /*@ public normal_behavior
      @   requires 0 <= fromIndex && fromIndex <= size() 
      @         && 0 <= toIndex && toIndex <= size()
      @         && fromIndex <= toIndex;
      @   ensures \result.size() == toIndex - fromIndex;
      @   ensures (\forall int i; fromIndex <=i && i < toIndex;
                         \old(get(i)) == get(i-fromIndex));
      @ also
      @ public exceptional_behavior
      @   requires !(0 <= fromIndex && fromIndex <= size())
      @         || !( 0 <= toIndex && toIndex <= size())
      @         || !(fromIndex <= toIndex);
      @   signals_only IndexOutOfBoundsException;
      @
      @*/
    /*@ pure @*/ List subList(int fromIndex, int toIndex);
}
