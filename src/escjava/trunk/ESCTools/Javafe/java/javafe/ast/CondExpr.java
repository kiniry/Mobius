/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class CondExpr extends Expr {
  public /*@non_null*/ Expr test;

  public /*@non_null*/ Expr thn;

  public /*@non_null*/ Expr els;

  //@ invariant locQuestion!=javafe.util.Location.NULL
  public int locQuestion;

  //@ invariant locColon!=javafe.util.Location.NULL
  public int locColon;

  public int getStartLoc() { return test.getStartLoc(); }
  public int getEndLoc() { 
    int thenL = thn.getEndLoc();
    int elseL = els.getEndLoc();
    return Math.max(thenL, elseL);
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw CondExpr whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected CondExpr() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     return 3;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.test;
     else index--;

     if (index == 0) return this.thn;
     else index--;

     if (index == 0) return this.els;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[CondExpr"
        + " test = " + this.test
        + " thn = " + this.thn
        + " els = " + this.els
        + " locQuestion = " + this.locQuestion
        + " locColon = " + this.locColon
        + "]";
  }

  public final int getTag() {
     return TagConstants.CONDEXPR;
  }

  public final void accept(Visitor v) { v.visitCondExpr(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitCondExpr(this, o); }

  public void check() {
     super.check();
     this.test.check();
     this.thn.check();
     this.els.check();
  }

  //@ requires locQuestion!=javafe.util.Location.NULL
  //@ requires locColon!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static CondExpr make(/*@non_null*/ Expr test, /*@non_null*/ Expr thn, /*@non_null*/ Expr els, int locQuestion, int locColon) {
     //@ set I_will_establish_invariants_afterwards = true
     CondExpr result = new CondExpr();
     result.test = test;
     result.thn = thn;
     result.els = els;
     result.locQuestion = locQuestion;
     result.locColon = locColon;
     return result;
  }
}
