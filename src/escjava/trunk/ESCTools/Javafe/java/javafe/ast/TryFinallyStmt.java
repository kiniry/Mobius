/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class TryFinallyStmt extends Stmt {
  // Note: locTry might will be shared with tryClause.locTry if
  // tryClause is a TryCatchStmt
  public /*@non_null*/ Stmt tryClause;

  public /*@non_null*/ Stmt finallyClause;

  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;

  //@ invariant locFinally!=javafe.util.Location.NULL
  public int locFinally;


  private void postCheck() {
    int t = tryClause.getTag();
    Assert.notFalse(t != TagConstants.SWITCHLABEL	//@ nowarn Pre
		    && t != TagConstants.CONSTRUCTORINVOCATION
		    && t != TagConstants.VARDECLSTMT);
    t = finallyClause.getTag();
    Assert.notFalse(t != TagConstants.SWITCHLABEL	//@ nowarn Pre
		    && t != TagConstants.CONSTRUCTORINVOCATION
		    && t != TagConstants.VARDECLSTMT);
  }
  public int getStartLoc() { return loc; }
  public int getEndLoc() { return finallyClause.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw TryFinallyStmt whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected TryFinallyStmt() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.tryClause;
     else index--;

     if (index == 0) return this.finallyClause;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[TryFinallyStmt"
        + " tryClause = " + this.tryClause
        + " finallyClause = " + this.finallyClause
        + " loc = " + this.loc
        + " locFinally = " + this.locFinally
        + "]";
  }

  public final int getTag() {
     return TagConstants.TRYFINALLYSTMT;
  }

  public final void accept(Visitor v) { v.visitTryFinallyStmt(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitTryFinallyStmt(this, o); }

  public void check() {
     super.check();
     this.tryClause.check();
     this.finallyClause.check();
     postCheck();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ requires locFinally!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static TryFinallyStmt make(/*@non_null*/ Stmt tryClause, /*@non_null*/ Stmt finallyClause, int loc, int locFinally) {
     //@ set I_will_establish_invariants_afterwards = true
     TryFinallyStmt result = new TryFinallyStmt();
     result.tryClause = tryClause;
     result.finallyClause = finallyClause;
     result.loc = loc;
     result.locFinally = locFinally;
     return result;
  }
}
