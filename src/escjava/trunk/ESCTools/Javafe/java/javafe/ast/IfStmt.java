/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class IfStmt extends Stmt {
  public /*@non_null*/ Expr expr;

  public /*@non_null*/ Stmt thn;

  public /*@non_null*/ Stmt els;

  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;


  private void postCheck() {
    int t = thn.getTag();
    Assert.notFalse(t != TagConstants.SWITCHLABEL 	//@ nowarn Pre
		    && t != TagConstants.CONSTRUCTORINVOCATION
		    && t != TagConstants.VARDECLSTMT);
    t = els.getTag();
    Assert.notFalse(t != TagConstants.SWITCHLABEL	//@ nowarn Pre
		    && t != TagConstants.CONSTRUCTORINVOCATION
		    && t != TagConstants.VARDECLSTMT);
  }
  public int getStartLoc() { return loc; }
  public int getEndLoc() { 
    int thenL = thn.getEndLoc();
    int elseL = els.getEndLoc();
    return Math.max(thenL, elseL);
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw IfStmt whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected IfStmt() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.expr;
     else index--;

     if (index == 0) return this.thn;
     else index--;

     if (index == 0) return this.els;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[IfStmt"
        + " expr = " + this.expr
        + " thn = " + this.thn
        + " els = " + this.els
        + " loc = " + this.loc
        + "]";
  }

  public final int getTag() {
     return TagConstants.IFSTMT;
  }

  public final void accept(Visitor v) { v.visitIfStmt(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitIfStmt(this, o); }

  public void check() {
     super.check();
     this.expr.check();
     this.thn.check();
     this.els.check();
     postCheck();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static IfStmt make(/*@non_null*/ Expr expr, /*@non_null*/ Stmt thn, /*@non_null*/ Stmt els, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     IfStmt result = new IfStmt();
     result.expr = expr;
     result.thn = thn;
     result.els = els;
     result.loc = loc;
     return result;
  }
}
