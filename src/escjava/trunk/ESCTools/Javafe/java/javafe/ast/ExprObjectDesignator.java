/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit



/** Represents an ObjectDesignator of the form "Expr . ".
 *
 *  Is created both by the parser (eg for "(x).y"),
 *  and by the name resolution code (eg for "x.y").
 */

public class ExprObjectDesignator extends ObjectDesignator {
  public /*@non_null*/ Expr expr;

  public int getStartLoc() { return expr.getStartLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw ExprObjectDesignator whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected ExprObjectDesignator() {}    //@ nowarn Invariant,NonNullInit


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
     return "[ExprObjectDesignator"
        + " locDot = " + this.locDot
        + " expr = " + this.expr
        + "]";
  }

  public final int getTag() {
     return TagConstants.EXPROBJECTDESIGNATOR;
  }

  public final void accept(Visitor v) { v.visitExprObjectDesignator(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitExprObjectDesignator(this, o); }

  public void check() {
     super.check();
     this.expr.check();
  }

  //@ requires locDot!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static ExprObjectDesignator make(int locDot, /*@non_null*/ Expr expr) {
     //@ set I_will_establish_invariants_afterwards = true
     ExprObjectDesignator result = new ExprObjectDesignator();
     result.locDot = locDot;
     result.expr = expr;
     return result;
  }
}
