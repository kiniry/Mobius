/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class InstanceOfExpr extends Expr {
  public /*@non_null*/ Expr expr;

  //@ invariant type.syntax
  public /*@non_null*/ Type type;

  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;

  public int getStartLoc() { return expr.getStartLoc(); }
  public int getEndLoc() { return type.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw InstanceOfExpr whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected InstanceOfExpr() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     return 2;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.expr;
     else index--;

     if (index == 0) return this.type;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[InstanceOfExpr"
        + " expr = " + this.expr
        + " type = " + this.type
        + " loc = " + this.loc
        + "]";
  }

  public final int getTag() {
     return TagConstants.INSTANCEOFEXPR;
  }

  public final void accept(Visitor v) { v.visitInstanceOfExpr(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitInstanceOfExpr(this, o); }

  public void check() {
     super.check();
     this.expr.check();
     this.type.check();
  }

  //@ requires type.syntax
  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static InstanceOfExpr make(/*@non_null*/ Expr expr, /*@non_null*/ Type type, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     InstanceOfExpr result = new InstanceOfExpr();
     result.expr = expr;
     result.type = type;
     result.loc = loc;
     return result;
  }
}
