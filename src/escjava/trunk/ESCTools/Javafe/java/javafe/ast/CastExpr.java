/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class CastExpr extends Expr {
  public /*@non_null*/ Expr expr;

  //@ invariant type.syntax
  public /*@non_null*/ Type type;

  //@ invariant locOpenParen!=javafe.util.Location.NULL
  public int locOpenParen;

  //@ invariant locCloseParen!=javafe.util.Location.NULL
  public int locCloseParen;

  public int getStartLoc() { return locOpenParen; }
  public int getEndLoc() { return expr.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw CastExpr whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected CastExpr() {}    //@ nowarn Invariant,NonNullInit


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
     return "[CastExpr"
        + " expr = " + this.expr
        + " type = " + this.type
        + " locOpenParen = " + this.locOpenParen
        + " locCloseParen = " + this.locCloseParen
        + "]";
  }

  public final int getTag() {
     return TagConstants.CASTEXPR;
  }

  public final void accept(Visitor v) { v.visitCastExpr(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitCastExpr(this, o); }

  public void check() {
     super.check();
     this.expr.check();
     this.type.check();
  }

  //@ requires type.syntax
  //@ requires locOpenParen!=javafe.util.Location.NULL
  //@ requires locCloseParen!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static CastExpr make(/*@non_null*/ Expr expr, /*@non_null*/ Type type, int locOpenParen, int locCloseParen) {
     //@ set I_will_establish_invariants_afterwards = true
     CastExpr result = new CastExpr();
     result.expr = expr;
     result.type = type;
     result.locOpenParen = locOpenParen;
     result.locCloseParen = locCloseParen;
     return result;
  }
}
