/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class BlockStmt extends GenericBlockStmt {
  private void postCheck() {
    for(int i = 0; i < stmts.size(); i++) {
      int t = stmts.elementAt(i).getTag();
      Assert.notFalse(t != TagConstants.SWITCHLABEL);	//@ nowarn Pre
      Assert.notFalse(i == 0				//@ nowarn Pre
	|| t != TagConstants.CONSTRUCTORINVOCATION);
    }
  }
  public int getStartLoc() { return locOpenBrace; }


// Generated boilerplate constructors:

  /**
   ** Construct a raw BlockStmt whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected BlockStmt() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.stmts != null) sz += this.stmts.size();
     return sz + 0;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     sz = (this.stmts == null ? 0 : this.stmts.size());
     if (0 <= index && index < sz)
        return this.stmts.elementAt(index);
     else index -= sz;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[BlockStmt"
        + " stmts = " + this.stmts
        + " locOpenBrace = " + this.locOpenBrace
        + " locCloseBrace = " + this.locCloseBrace
        + "]";
  }

  public final int getTag() {
     return TagConstants.BLOCKSTMT;
  }

  public final void accept(Visitor v) { v.visitBlockStmt(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitBlockStmt(this, o); }

  public void check() {
     super.check();
     for(int i = 0; i < this.stmts.size(); i++)
        this.stmts.elementAt(i).check();
     postCheck();
  }

  //@ requires locOpenBrace!=javafe.util.Location.NULL
  //@ requires locCloseBrace!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static BlockStmt make(/*@non_null*/ StmtVec stmts, int locOpenBrace, int locCloseBrace) {
     //@ set I_will_establish_invariants_afterwards = true
     BlockStmt result = new BlockStmt();
     result.stmts = stmts;
     result.locOpenBrace = locOpenBrace;
     result.locCloseBrace = locCloseBrace;
     return result;
  }
}
