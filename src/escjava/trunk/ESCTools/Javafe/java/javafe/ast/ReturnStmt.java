/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class ReturnStmt extends Stmt {
  public Expr expr;

  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;

  public int getStartLoc() { return loc; }
  public int getEndLoc() {
    if (expr==null)
      return super.getEndLoc();

    return expr.getEndLoc();
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw ReturnStmt whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected ReturnStmt() {}    //@ nowarn Invariant,NonNullInit


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
     return "[ReturnStmt"
        + " expr = " + this.expr
        + " loc = " + this.loc
        + "]";
  }

  public final int getTag() {
     return TagConstants.RETURNSTMT;
  }

  public final void accept(Visitor v) { v.visitReturnStmt(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitReturnStmt(this, o); }

  public void check() {
     super.check();
     if (this.expr != null)
        this.expr.check();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static ReturnStmt make(Expr expr, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     ReturnStmt result = new ReturnStmt();
     result.expr = expr;
     result.loc = loc;
     return result;
  }
}
