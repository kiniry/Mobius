/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class ThrowStmt extends Stmt {
  public /*@non_null*/ Expr expr;

  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return expr.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw ThrowStmt whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected ThrowStmt() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.expr;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[ThrowStmt"
        + " expr = " + this.expr
        + " loc = " + this.loc
        + "]";
  }

  public final int getTag() {
     return TagConstants.THROWSTMT;
  }

  public final void accept(Visitor v) { v.visitThrowStmt(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitThrowStmt(this, o); }

  public void check() {
     super.check();
     this.expr.check();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static ThrowStmt make(/*@non_null*/ Expr expr, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     ThrowStmt result = new ThrowStmt();
     result.expr = expr;
     result.loc = loc;
     return result;
  }
}
