/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class ParenExpr extends Expr {
  public /*@non_null*/ Expr expr;

  //@ invariant locOpenParen!=javafe.util.Location.NULL
  public int locOpenParen;

  //@ invariant locCloseParen!=javafe.util.Location.NULL
  public int locCloseParen;

  public int getStartLoc() { return locOpenParen; }
  public int getEndLoc() { return locCloseParen; }


// Generated boilerplate constructors:

  /**
   ** Construct a raw ParenExpr whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected ParenExpr() {}    //@ nowarn Invariant,NonNullInit


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
     return "[ParenExpr"
        + " expr = " + this.expr
        + " locOpenParen = " + this.locOpenParen
        + " locCloseParen = " + this.locCloseParen
        + "]";
  }

  public final int getTag() {
     return TagConstants.PARENEXPR;
  }

  public final void accept(Visitor v) { v.visitParenExpr(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitParenExpr(this, o); }

  public void check() {
     super.check();
     this.expr.check();
  }

  //@ requires locOpenParen!=javafe.util.Location.NULL
  //@ requires locCloseParen!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static ParenExpr make(/*@non_null*/ Expr expr, int locOpenParen, int locCloseParen) {
     //@ set I_will_establish_invariants_afterwards = true
     ParenExpr result = new ParenExpr();
     result.expr = expr;
     result.locOpenParen = locOpenParen;
     result.locCloseParen = locCloseParen;
     return result;
  }
}
