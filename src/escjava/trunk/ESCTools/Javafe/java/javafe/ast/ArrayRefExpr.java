/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class ArrayRefExpr extends Expr {
  public /*@non_null*/ Expr array;

  public /*@non_null*/ Expr index;

  //@ invariant locOpenBracket!=javafe.util.Location.NULL
  public int locOpenBracket;

  //@ invariant locCloseBracket!=javafe.util.Location.NULL
  public int locCloseBracket;

  public int getStartLoc() { return array.getStartLoc(); }
  public int getEndLoc() { return locCloseBracket; }


// Generated boilerplate constructors:

  /**
   ** Construct a raw ArrayRefExpr whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected ArrayRefExpr() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.array;
     else index--;

     if (index == 0) return this.index;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[ArrayRefExpr"
        + " array = " + this.array
        + " index = " + this.index
        + " locOpenBracket = " + this.locOpenBracket
        + " locCloseBracket = " + this.locCloseBracket
        + "]";
  }

  public final int getTag() {
     return TagConstants.ARRAYREFEXPR;
  }

  public final void accept(Visitor v) { v.visitArrayRefExpr(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitArrayRefExpr(this, o); }

  public void check() {
     super.check();
     this.array.check();
     this.index.check();
  }

  //@ requires locOpenBracket!=javafe.util.Location.NULL
  //@ requires locCloseBracket!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static ArrayRefExpr make(/*@non_null*/ Expr array, /*@non_null*/ Expr index, int locOpenBracket, int locCloseBracket) {
     //@ set I_will_establish_invariants_afterwards = true
     ArrayRefExpr result = new ArrayRefExpr();
     result.array = array;
     result.index = index;
     result.locOpenBracket = locOpenBracket;
     result.locCloseBracket = locCloseBracket;
     return result;
  }
}
