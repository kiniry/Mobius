/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents various kinds of unary expressions.
 *  The tag is one of the constants:
 *       ADD SUB NOT BITNOT INC DEC POSTFIXINC POSTFIXDEC
 *  defined in OperatorTags.
 */

public class UnaryExpr extends Expr {

  /*@ invariant (op == TagConstants.UNARYADD || op == TagConstants.UNARYSUB
       || op == TagConstants.NOT || op == TagConstants.BITNOT
       || op == TagConstants.INC || op == TagConstants.DEC
       || op == TagConstants.POSTFIXINC || op == TagConstants.POSTFIXDEC) */
  public int op;


  public /*@non_null*/ Expr expr;

  //@ invariant locOp!=javafe.util.Location.NULL
  public int locOp;


  public final int getTag() { return op; }

  private void postCheck() {
    boolean goodtag =
      (op == TagConstants.UNARYADD || op == TagConstants.UNARYSUB
       || op == TagConstants.NOT || op == TagConstants.BITNOT
       || op == TagConstants.INC || op == TagConstants.DEC
       || op == TagConstants.POSTFIXINC || op == TagConstants.POSTFIXDEC);
    Assert.notFalse(goodtag);
  }
  public int getStartLoc() { 
    int le = expr.getStartLoc(); 
    return le < locOp ? le : locOp;
  }

  public int getEndLoc() { 
    int le = expr.getEndLoc(); 
    return le < locOp ? locOp : le;
  }

  /*@ requires (op == TagConstants.UNARYADD || op == TagConstants.UNARYSUB
       || op == TagConstants.NOT || op == TagConstants.BITNOT
       || op == TagConstants.INC || op == TagConstants.DEC
       || op == TagConstants.POSTFIXINC || op == TagConstants.POSTFIXDEC) */
  //
  //@ requires locOp!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static UnaryExpr make(int op, /*@non_null*/ Expr expr, int locOp) {
     //@ set I_will_establish_invariants_afterwards = true
     UnaryExpr result = new UnaryExpr();
     result.op = op;
     result.expr = expr;
     result.locOp = locOp;
     return result;
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw UnaryExpr whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected UnaryExpr() {}    //@ nowarn Invariant,NonNullInit


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
     return "[UnaryExpr"
        + " op = " + this.op
        + " expr = " + this.expr
        + " locOp = " + this.locOp
        + "]";
  }

  public final void accept(Visitor v) { v.visitUnaryExpr(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitUnaryExpr(this, o); }

  public void check() {
     super.check();
     this.expr.check();
     postCheck();
  }

}
