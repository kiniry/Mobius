/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents a Name that occurs in an Expression position. 
 *  These are name-resolved to VariableAccess,
 *  ExprFieldAccess or TypeFieldAccess.
 */

public class AmbiguousVariableAccess extends Expr {
  public /*@non_null*/ Name name;

  public int getStartLoc() { return name.getStartLoc(); }
  public int getEndLoc() { return name.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw AmbiguousVariableAccess whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected AmbiguousVariableAccess() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     return 1;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.name;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[AmbiguousVariableAccess"
        + " name = " + this.name
        + "]";
  }

  public final int getTag() {
     return TagConstants.AMBIGUOUSVARIABLEACCESS;
  }

  public final void accept(Visitor v) { v.visitAmbiguousVariableAccess(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitAmbiguousVariableAccess(this, o); }

  public void check() {
     super.check();
     this.name.check();
  }

  //@ ensures \result!=null
  public static AmbiguousVariableAccess make(/*@non_null*/ Name name) {
     //@ set I_will_establish_invariants_afterwards = true
     AmbiguousVariableAccess result = new AmbiguousVariableAccess();
     result.name = name;
     return result;
  }
}
