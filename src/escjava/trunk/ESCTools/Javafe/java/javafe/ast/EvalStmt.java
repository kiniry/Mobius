/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class EvalStmt extends Stmt {
  public /*@non_null*/ Expr expr;

  public int getStartLoc() { return expr.getStartLoc(); }
  public int getEndLoc() { return expr.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw EvalStmt whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected EvalStmt() {}    //@ nowarn Invariant,NonNullInit


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
     return "[EvalStmt"
        + " expr = " + this.expr
        + "]";
  }

  public final int getTag() {
     return TagConstants.EVALSTMT;
  }

  public final void accept(Visitor v) { v.visitEvalStmt(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitEvalStmt(this, o); }

  public void check() {
     super.check();
     this.expr.check();
  }

  //@ ensures \result!=null
  public static EvalStmt make(/*@non_null*/ Expr expr) {
     //@ set I_will_establish_invariants_afterwards = true
     EvalStmt result = new EvalStmt();
     result.expr = expr;
     return result;
  }
}
