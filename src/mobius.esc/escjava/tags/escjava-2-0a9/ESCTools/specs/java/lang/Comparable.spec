// @(#)$Id$

// Copyright (C) 2001, 2002 Iowa State University

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

/** JML's specification of java.lang.Comparable.
 * These are objects with a total ordering that is an equivalence relation.
 * @version $Revision$
 * @author Gary T. Leavens
 */
public interface Comparable {

    /*@   public normal_behavior
      @     requires i < 0;
      @     ensures \result == -1;
      @ also
      @   public normal_behavior
      @     requires i == 0;
      @     ensures \result == 0;
      @ also
      @   public normal_behavior
      @     requires i > 0;
      @     ensures \result == 1;
      @ implies_that
      @   public model_program {
      @     return ((i < 0) ? -1 : ((i == 0) ? 0 : 1));
      @   }
      @ model static pure int sgn(int i);
      @*/

    /*@ public normal_behavior
      @    requires x != null && y != null;
      @    ensures !(x <: \type(Comparable)) ==> !\result;
      @    ensures !(y <: \type(Comparable)) ==> !\result;
      @    ensures \result == definedComparison(y,x);
      @ public static model pure boolean
      @ definedComparison(Class x, Class y);
      @*/

    /*$ public normal_behavior
      $   requires x != null && y != null;
      $ public static model pure boolean
      $		definedComparison(Object x, Object y);
      $*/

    /*@ 
      @ public exceptional_behavior
      @    requires o == null;
      @    signals_only NullPointerException;
      @ also public exceptional_behavior
      @    requires o != null;
      @    requires !definedComparison(this.getClass(), o.getClass());
      @    signals_only ClassCastException;
      @ also
      @   public behavior
      @    requires o != null; 
      @    requires definedComparison(getClass(), o.getClass());
      @    ensures o == this ==> \result == 0; // reflexive
      @    //ensures sgn(\result) == - sgn(((Comparable)o).compareTo(this)); // antisymmetric
      @*/
    /*@ pure @*/ int compareTo(Object o);

    // compareTo is reflexive
    /*+@ public instance invariant
      @   (\forall Comparable x; x != null; x.compareTo(x) == 0);
      @*/

    // compareTo is antisymmetric
    /*-$ public instance invariant
      $   (\forall Comparable x, y; x != null && y != null
      $                             && definedComparison(x, y)
      $                             && definedComparison(y, x);
      $                 sgn(x.compareTo(y)) == -sgn(y.compareTo(x)) );
      $*/

    // compareTo is transitive
    /*-$ public instance invariant
      $     (\forall int n; n == -1 || n == 1;
      $      (\forall Comparable x, y, z;
      $              x != null && y != null && z != null
      $               && definedComparison(x, y) && definedComparison(y, z)
      $               && definedComparison(x, z);
      $              sgn(x.compareTo(y)) == n && sgn(y.compareTo(z)) == n
      $                 ==> sgn(x.compareTo(z)) == n));
      $ public instance invariant
      $     (\forall int n; n == -1 || n == 1;
      $      (\forall Comparable x, y, z;
      $             x != null && y != null && z != null
      $              && definedComparison(x, y) && definedComparison(y, z)
      $              && definedComparison(x, z);
      $             (sgn(x.compareTo(y)) == 0 && sgn(y.compareTo(z)) == n
      $               || sgn(x.compareTo(y)) == n && sgn(y.compareTo(z)) == 0)
      $             ==> sgn(x.compareTo(z)) == n));
      $*/

    // compareTo returning 0 means the other argument
    // is in the same equivalence class
    /*-$ public instance invariant
      $    (\forall Comparable x, y, z;
      $             x != null && y != null && z != null
      $              && definedComparison(x, y) && definedComparison(x, z)
      $              && definedComparison(y, z);
      $             sgn(x.compareTo(y)) == 0
      $             ==> sgn(x.compareTo(z)) == sgn(y.compareTo(z)));
      $*/

}
