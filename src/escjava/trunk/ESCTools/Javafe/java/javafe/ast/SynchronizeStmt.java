/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class SynchronizeStmt extends Stmt {
  public /*@non_null*/ Expr expr;

  public /*@non_null*/ BlockStmt stmt;

  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;

  //@ invariant locOpenParen!=javafe.util.Location.NULL
  public int locOpenParen;


  public int getStartLoc() { return loc; }
  public int getEndLoc() { return stmt.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw SynchronizeStmt whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected SynchronizeStmt() {}    //@ nowarn Invariant,NonNullInit


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
     return "[SynchronizeStmt"
        + " expr = " + this.expr
        + " stmt = " + this.stmt
        + " loc = " + this.loc
        + " locOpenParen = " + this.locOpenParen
        + "]";
  }

  public final int getTag() {
     return TagConstants.SYNCHRONIZESTMT;
  }

  public final void accept(Visitor v) { v.visitSynchronizeStmt(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitSynchronizeStmt(this, o); }

  public void check() {
     super.check();
     this.expr.check();
     this.stmt.check();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ requires locOpenParen!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static SynchronizeStmt make(/*@non_null*/ Expr expr, /*@non_null*/ BlockStmt stmt, int loc, int locOpenParen) {
     //@ set I_will_establish_invariants_afterwards = true
     SynchronizeStmt result = new SynchronizeStmt();
     result.expr = expr;
     result.stmt = stmt;
     result.loc = loc;
     result.locOpenParen = locOpenParen;
     return result;
  }
}
