/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class LabelStmt extends Stmt {
  public /*@non_null*/ Identifier label;

  public /*@non_null*/ Stmt stmt;

  //@ invariant locId!=javafe.util.Location.NULL
  public int locId;


  private void postCheck() {
    int t = stmt.getTag();
    Assert.notFalse(t != TagConstants.SWITCHLABEL	//@ nowarn Pre
		    && t != TagConstants.CONSTRUCTORINVOCATION
		    && t != TagConstants.VARDECLSTMT);
  }
  public int getStartLoc() { return locId; }
  public int getEndLoc() { return stmt.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw LabelStmt whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected LabelStmt() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.label;
     else index--;

     if (index == 0) return this.stmt;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[LabelStmt"
        + " label = " + this.label
        + " stmt = " + this.stmt
        + " locId = " + this.locId
        + "]";
  }

  public final int getTag() {
     return TagConstants.LABELSTMT;
  }

  public final void accept(Visitor v) { v.visitLabelStmt(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitLabelStmt(this, o); }

  public void check() {
     super.check();
     if (this.label == null) throw new RuntimeException();
     this.stmt.check();
     postCheck();
  }

  //@ requires locId!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static LabelStmt make(/*@non_null*/ Identifier label, /*@non_null*/ Stmt stmt, int locId) {
     //@ set I_will_establish_invariants_afterwards = true
     LabelStmt result = new LabelStmt();
     result.label = label;
     result.stmt = stmt;
     result.locId = locId;
     return result;
  }
}
