/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class DoStmt extends Stmt {
  public /*@non_null*/ Expr expr;

  public /*@non_null*/ Stmt stmt;

  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;


  private void postCheck() {
    int t = stmt.getTag();
    Assert.notFalse(t != TagConstants.SWITCHLABEL	//@ nowarn Pre
		    && t != TagConstants.CONSTRUCTORINVOCATION
		    && t != TagConstants.VARDECLSTMT);
  }
  public int getStartLoc() { return loc; }
  public int getEndLoc() { return expr.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw DoStmt whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected DoStmt() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.stmt;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[DoStmt"
        + " expr = " + this.expr
        + " stmt = " + this.stmt
        + " loc = " + this.loc
        + "]";
  }

  public final int getTag() {
     return TagConstants.DOSTMT;
  }

  public final void accept(Visitor v) { v.visitDoStmt(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitDoStmt(this, o); }

  public void check() {
     super.check();
     this.expr.check();
     this.stmt.check();
     postCheck();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static DoStmt make(/*@non_null*/ Expr expr, /*@non_null*/ Stmt stmt, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     DoStmt result = new DoStmt();
     result.expr = expr;
     result.stmt = stmt;
     result.loc = loc;
     return result;
  }
}
