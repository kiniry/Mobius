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
import java.lang.reflect.Array;

/** JML's specification of java.lang.Object.
 *
 * @version $Revision$
 * @author Gary T. Leavens
 * @author Specifications from Compaq SRC's ESC/Java
 */
public class Object {

    /** A data group for the state of this object.  This is used to
     * allow side effects on unknown variables in methods such as
     * equals, clone, and toString. It also provides a convenient way
     * to talk about "the state" of an object in assignable
     * clauses.
     */
    //@ public non_null model JMLDataGroup objectState;

    /** The Object that has a field pointing to this Object.
     * Used to specify (among other things) injectivity (see
     * the ESC/Java User's Manual).
     */
    /*@ ghost public Object owner;
                           in objectState;
      @*/

    /*@ public normal_behavior
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Object();

    /** The Class of this object.  Needed to specify that invoking
      * getClass() on an object always produces the same result: no
      * methods include this model field in their assignable clause,
      * so no methods can alter the outcome of invoking getClass() on
      * some object.  This property is important when using ESC/Java
      * on specs that use getClass(), just knowing that getClass() is
      * pure is not enough.
      */
    //@ public model non_null Class _getClass;
    //@ public represents _getClass <- \typeof(this);

    /*@ public normal_behavior
      @   ensures \result == _getClass;
      @   ensures_redundantly \result != null;
      @*/
    public /*@ pure @*/ final Class getClass();

    /*@  public behavior
      @     assignable objectState; // for subclasses with benevolent side effects
      @     ensures (* \result is a hash code for this object *);
      @     //ensures \result == hashValue();
      @  also
      @   public normal_behavior
      @     requires \typeof(this) == \type(Object);
      @     assignable \nothing;
      @*/
    public int hashCode();

    // FIXME - use this (and the postcondition in hashCode), or some other
    // method of creating a pure value of hashCode?

    // The value produced by hashCode() but without any side-effects.
    // @ ensures (\forall Object o; equals(o) ==> \result == o.hashValue());
    //@ public pure model int hashValue();

    /*@  public normal_behavior
      @     requires obj != null;
      @     ensures (* \result is true when obj is "equal to" this object *);
      @  also
      @   public normal_behavior
      @     requires this == obj;
      @     ensures \result;
      @  also
      @   public normal_behavior
      @     requires obj != null && \typeof(this) == \type(Object);
      @     ensures \result <==> this == obj;
      @ also
      @    ensures obj == null ==> !\result;
      @ also
      @    requires obj != null;
      @    ensures \result == obj.equals(this);
      @*/
    public /*@ pure @*/ boolean equals(/*+@ \readonly @+*/ Object obj);

    /*@ protected normal_behavior
      @   requires this instanceof Cloneable;
      @   assignable \nothing;
      @   ensures \result != null;
		// Note: clone is magic.  Object.clone ensures the following
		// strict equality when it is called, and subclasses are
		// expected to fulfill it by calling super.clone();
      @   ensures \typeof(\result) == \typeof(this);
      @   ensures (* \result is a clone of this *);
      @*/
    /*+@
      @ also protected normal_behavior
      @   requires this.getClass().isArray();
      @   assignable \nothing;
      @   ensures \elemtype(\typeof(\result)) == \elemtype(\typeof(this));
      @   ensures ((\peer \peer Object[])\result).length
      @            == ((\peer \peer Object[])this).length;
      @   ensures (\forall int i;
      @                0<=i && i < ((\peer \peer Object[])this).length;
      @                ((\peer \peer Object[])\result)[i]
      @                 == ((\peer \peer Object[])this)[i] );
      @+*/
    /*-@
      @ also protected normal_behavior
      @   requires this.getClass().isArray();
      @   assignable \nothing;
      @   ensures \elemtype(\typeof(\result)) == \elemtype(\typeof(this));
      @   ensures ((Object[])\result).length == ((Object[])this).length;
      @   ensures (\forall int i; 0<=i && i < ((Object[])this).length;
      @                ((Object[])\result)[i] == ((Object[])this)[i] );
      @*/
    /*@
      @ also
      @   requires this.getClass().isArray();
      @   // FIXME requires \elemtype(\typeof(this)).isPrimitive();
      @   assignable \nothing;
      @   ensures \elemtype(\typeof(\result)) == \elemtype(\typeof(this));
      @   ensures Array.getLength(\result) == Array.getLength(this);
      @   ensures (\forall int i; 0<=i && i < Array.getLength(this);
      @                Array.get(\result,i).equals(Array.get(this,i))  );
      @ also protected exceptional_behavior
      @   requires !(this instanceof Cloneable);
      @   assignable \nothing;
      @   signals (CloneNotSupportedException) true;
      @*/
// FIXME - is it always true that \result != this
// FIXME - ifnot some derived classes will want to ensure this
/*
      @ also protected normal_behavior
      @   requires \elemtype(\typeof(this)) <: \type(Object);
      @   assignable \nothing;
      @   ensures \elemtype(\typeof(\result)) == \elemtype(\typeof(this));
      @   ensures ((Object[])\result).length == ((Object[])this).length;
      @   ensures (\forall int i; 0<=i && i < ((Object[])this).length;
      @                ((Object[])\result)[i] == ((Object[])this)[i] );
      @ also protected normal_behavior
      @   requires \elemtype(\typeof(this)) == \type(int);
      @   assignable \nothing;
      @   ensures \elemtype(\typeof(\result)) == \elemtype(\typeof(this));
      @   ensures ((int[])\result).length == ((int[])this).length;
      @   ensures (\forall int i; 0<=i && i < ((int[])this).length;
      @                ((int[])\result)[i] == ((int[])this)[i] );
      @ also protected normal_behavior
      @   requires \elemtype(\typeof(this)) == \type(byte);
      @   assignable \nothing;
      @   ensures \elemtype(\typeof(\result)) == \elemtype(\typeof(this));
      @   ensures ((byte[])\result).length == ((byte[])this).length;
      @   ensures (\forall int i; 0<=i && i < ((byte[])this).length;
      @                ((byte[])\result)[i] == ((byte[])this)[i] );
	// FIXME - needs the above replicated for each primitive type
*/
    protected Object clone() throws CloneNotSupportedException;

    /** Use theString as the (pure) model value of toString() */
    // This is not in objectState since it will not necessarily change just because
    // the state of the object changes (e.g. when there are benevolent side effects)
    //@ public model String theString;

    /*@   public normal_behavior
      @     assignable objectState;
      @     ensures \result != null;
      @     ensures \result == theString;
      @     ensures (* \result is a string representation of this object *);
      @ also
      @   public normal_behavior
      @     requires \typeof(this) == \type(Object);
      @     assignable \nothing;
      @     ensures \result != null
      @          && (* \result is the instance's class name, followed by an @,
      @		       followed by the instance's hashcode in hex *);
      @ also
      @   public model_program {
      @       assume \typeof(this) == \type(Object);
      @       return getClass().getName()
      @              + '@' + Integer.toHexString(hashCode());
      @   }
      @ implies_that
      @    assignable objectState;
      @    ensures \result != null;
      @*/
    public String toString();

    public final void notify();

    public final void notifyAll();

    //@ requires timeout >= 0L;
    public final void wait(long timeout) throws InterruptedException;

    //@ requires timeout >= 0L && 0 <= nanos && nanos < 1000000;
    public final void wait(long timeout, int nanos)
        throws InterruptedException;

    public final void wait() throws InterruptedException;

    /*@ protected behavior
      @   requires objectTimesFinalized == 0 ; // FIXME && \lockset.isEmpty();
      @   assignable objectTimesFinalized, objectState;
      @   ensures objectTimesFinalized == 1;
      @   signals (Throwable) objectTimesFinalized == 1;
      @*/
    protected void finalize() throws Throwable;

    /** The number of times this object has been finalized.
     */
    //@ protected ghost int objectTimesFinalized;
}
