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

/** JML's specification of java.util.Set.
 * @version $Revision$
 * @author Brandon Shilling
 * @author Gary T. Leavens
 */
public interface Set extends Collection {

    // specification inherited
    int size();

    // specification inherited
    boolean isEmpty();

    // specification inherited
    boolean contains(Object o);

    // specification inherited
    Iterator iterator();

    // specification inherited
    Object[] toArray();

    // specification inherited
    Object[] toArray(Object[] a);

    /* FIXME +@ also
       @ public behavior
       @   requires !theSet.has(o);
       @   assignable theCollection;
       @   ensures \result <==> !\old(theSet).has(o);
       @   ensures theSet.equals(\old(theSet).insert(o));
       @*/
    /*@ also
       @ public normal_behavior
       @   requires contains(o);
       @   assignable \nothing;
       @   ensures !\result;
       @   ensures (\forall Object oo; contains(oo) <==> \old(contains(oo)));
       @   ensures contains(null) <==> \old(contains(null));
       @ also public normal_behavior
       @   requires !contains(o);
       @   assignable _theCollection;
       @   ensures \result;
       @   ensures contains(o);
       @   ensures contains(null) <==> (\old(contains(null)) || o==null);
       @   ensures (\forall Object oo; contains(oo) <==> 
                                (\old(contains(oo)) || o == oo));
       @   ensures size() == \old(size()) + 1;
       @   // FIXME ensures equal(_theCollection,0,\old(_theCollection),0,
           //                        \old(_theCollection.length));
       @   ensures _theCollection[_theCollection.length-1] == o;
       @*/
    boolean add(Object o);

    /* FIXME +@ also
       @ implies_that
       @ public behavior
       @   assignable theCollection;
       @   assignable_redundantly theSet;
       @   ensures !theSet.has(o);
       @   ensures_redundantly !theCollection.has(o);
       @*/
    /*@ also
       @ public normal_behavior
       @   requires !contains(o);
       @   assignable \nothing;
       @   ensures \result;
       @   ensures (\forall Object oo; contains(oo) <==> \old(contains(oo)));
       @   ensures contains(null) <==> \old(contains(null));
       @ also public normal_behavior
       @   requires contains(o);
       @   assignable _theCollection;
       @   ensures !\result;
       @   ensures !contains(o);
       @   ensures \old(contains(null)) <==> (contains(null) || o==null);
       @   ensures (\forall Object oo; \old(contains(oo)) <==> 
                                (contains(oo) || o == oo));
       @   ensures size() == \old(size()) - 1;
       @*/
    boolean remove(Object o);

    // Bulk Operations

    /* FIXME +@ also
       @ public behavior
       @   requires c instanceof Set;
       @   ensures \result ==> ((Set) c).theSet.isSubset(theSet);
       @*/
    //@ pure
    boolean containsAll(Collection c);

    /* FIXME +@ also
       @ public behavior
       @   assignable theCollection;
       @   ensures 
       @        theSet.equals(\old(theSet).union(JMLEqualsSet.convertFrom(c)))
       @        && (\result ==> !theSet.equals(\old(theSet)));
       @*/
    /*@ also public normal_behavior
       @   assignable _theCollection;
       @   ensures contains(null) <==> (\old(contains(null)) || \old(c.contains(null)));
       @   ensures (\forall Object o; contains(o) <==>
                      (\old(contains(o)) || \old(c.contains(o))));
       @   ensures size() >= \old(size());
       @*/
    boolean addAll(Collection c);

    /* FIXME +@ also
       @ public behavior
       @   assignable theCollection;
       @   ensures theSet.equals(\old(theSet).intersection(
       @                                  JMLEqualsSet.convertFrom(c)))
       @        && (\result ==> !theSet.equals(\old(theSet)));
       @*/
    /*@ also public normal_behavior
       @   assignable _theCollection;
       @   ensures contains(null) <==> (\old(contains(null)) && \old(c.contains(null)));
       @   ensures (\forall Object o; contains(o) <==>
                      (\old(contains(o)) && \old(c.contains(o))));
       @   ensures size() <= \old(size());
       @*/
    boolean retainAll(Collection c);

    /* FIXME +@ also
       @ public behavior
       @   assignable theCollection;
       @   ensures theSet.equals(\old(theSet).difference(
       @                                  JMLEqualsSet.convertFrom(c)))
       @        && (\result ==> !theSet.equals(\old(theSet)));
       @*/
    /*@ also public normal_behavior
       @   assignable _theCollection;
       @   ensures contains(null) <==> (\old(contains(null)) && !\old(c.contains(null)));
       @   ensures (\forall Object o; contains(o) <==>
                      (\old(contains(o)) && !\old(c.contains(o))));
       @   ensures size() <= \old(size());
       @*/
    boolean removeAll(Collection c);

    // specification inherited
    void clear();

    // Comparison and hashing

    /* FIXME +@ also
       @ public normal_behavior
       @   requires o instanceof Set;
       @   ensures \result ==> theSet.equals(((Set)o).theSet);
       @*/
    /* FIXME @ also public normal_behavior
       @   requires o instanceof Set;
       @   ensures \result <==>
               ((\forall Object oo; contains(oo) <==> ((Set)o).contains(oo))
             && contains(null) <==> ((Set)o).contains(null));
       @   ensures_redundantly \result ==> (size == ((Set)o).size());
       @*/
    /*@ pure @*/ boolean equals(Object o);

    // specification inherited
    int hashCode();
}
