/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents various kinds of binary expressions (eg +,-,|,%=, etc).
 *  The tag is one of the binary operator tags or assignment operator
 *  tags defined in OperatorTags.
 */

public class BinaryExpr extends Expr {
  /*@ invariant (op == TagConstants.OR || op == TagConstants.AND
       || op == TagConstants.BITOR || op == TagConstants.BITXOR
       || op == TagConstants.BITAND
       || op == TagConstants.NE || op == TagConstants.EQ
       || op == TagConstants.GE || op == TagConstants.GT
       || op == TagConstants.LE || op == TagConstants.LT
       || op == TagConstants.LSHIFT || op == TagConstants.RSHIFT
       || op == TagConstants.URSHIFT || op == TagConstants.ADD
       || op == TagConstants.SUB || op == TagConstants.DIV
       || op == TagConstants.MOD || op == TagConstants.STAR
       || op == TagConstants.ASSIGN || op == TagConstants.ASGMUL
       || op == TagConstants.ASGDIV || op == TagConstants.ASGREM
       || op == TagConstants.ASGADD || op == TagConstants.ASGSUB
       || op == TagConstants.ASGLSHIFT || op == TagConstants.ASGRSHIFT
       || op == TagConstants.ASGURSHIFT || op == TagConstants.ASGBITAND) */
  public int op;


  public /*@non_null*/ Expr left;

  public /*@non_null*/ Expr right;

  //@ invariant locOp!=javafe.util.Location.NULL
  public int locOp;


  public final int getTag() { return op; }

  private void postCheck() {
    boolean goodtag =
      (op == TagConstants.OR || op == TagConstants.AND
       || op == TagConstants.BITOR || op == TagConstants.BITXOR
       || op == TagConstants.BITAND
       || op == TagConstants.NE || op == TagConstants.EQ
       || op == TagConstants.GE || op == TagConstants.GT
       || op == TagConstants.LE || op == TagConstants.LT
       || op == TagConstants.LSHIFT || op == TagConstants.RSHIFT
       || op == TagConstants.URSHIFT || op == TagConstants.ADD
       || op == TagConstants.SUB || op == TagConstants.DIV
       || op == TagConstants.MOD || op == TagConstants.STAR
       || op == TagConstants.ASSIGN || op == TagConstants.ASGMUL
       || op == TagConstants.ASGDIV || op == TagConstants.ASGREM
       || op == TagConstants.ASGADD || op == TagConstants.ASGSUB
       || op == TagConstants.ASGLSHIFT || op == TagConstants.ASGRSHIFT
       || op == TagConstants.ASGURSHIFT || op == TagConstants.ASGBITAND
       || op == TagConstants.ASGBITOR || op == TagConstants.ASGBITXOR);
    Assert.notFalse(goodtag);
  }
  public int getStartLoc() { return left.getStartLoc(); }
  public int getEndLoc() { return right.getEndLoc(); }


  /*@ requires (op == TagConstants.OR || op == TagConstants.AND
       || op == TagConstants.BITOR || op == TagConstants.BITXOR
       || op == TagConstants.BITAND
       || op == TagConstants.NE || op == TagConstants.EQ
       || op == TagConstants.GE || op == TagConstants.GT
       || op == TagConstants.LE || op == TagConstants.LT
       || op == TagConstants.LSHIFT || op == TagConstants.RSHIFT
       || op == TagConstants.URSHIFT || op == TagConstants.ADD
       || op == TagConstants.SUB || op == TagConstants.DIV
       || op == TagConstants.MOD || op == TagConstants.STAR
       || op == TagConstants.ASSIGN || op == TagConstants.ASGMUL
       || op == TagConstants.ASGDIV || op == TagConstants.ASGREM
       || op == TagConstants.ASGADD || op == TagConstants.ASGSUB
       || op == TagConstants.ASGLSHIFT || op == TagConstants.ASGRSHIFT
       || op == TagConstants.ASGURSHIFT || op == TagConstants.ASGBITAND) */
  //
  //@ requires locOp!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static BinaryExpr make(int op, /*@non_null*/ Expr left,
			        /*@non_null*/ Expr right, int locOp) {
     //@ set I_will_establish_invariants_afterwards = true
     BinaryExpr result = new BinaryExpr();
     result.op = op;
     result.left = left;
     result.right = right;
     result.locOp = locOp;
     return result;
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw BinaryExpr whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected BinaryExpr() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.left;
     else index--;

     if (index == 0) return this.right;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[BinaryExpr"
        + " op = " + this.op
        + " left = " + this.left
        + " right = " + this.right
        + " locOp = " + this.locOp
        + "]";
  }

  public final void accept(Visitor v) { v.visitBinaryExpr(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitBinaryExpr(this, o); }

  public void check() {
     super.check();
     this.left.check();
     this.right.check();
     postCheck();
  }

}
