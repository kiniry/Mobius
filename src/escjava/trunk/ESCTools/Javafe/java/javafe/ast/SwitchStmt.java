/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class SwitchStmt extends GenericBlockStmt {
  public /*@non_null*/ Expr expr;

  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;

  public int getStartLoc() { return loc; }


// Generated boilerplate constructors:

  /**
   ** Construct a raw SwitchStmt whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected SwitchStmt() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.stmts != null) sz += this.stmts.size();
     return sz + 1;
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

     if (index == 0) return this.expr;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[SwitchStmt"
        + " stmts = " + this.stmts
        + " locOpenBrace = " + this.locOpenBrace
        + " locCloseBrace = " + this.locCloseBrace
        + " expr = " + this.expr
        + " loc = " + this.loc
        + "]";
  }

  public final int getTag() {
     return TagConstants.SWITCHSTMT;
  }

  public final void accept(Visitor v) { v.visitSwitchStmt(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitSwitchStmt(this, o); }

  public void check() {
     super.check();
     for(int i = 0; i < this.stmts.size(); i++)
        this.stmts.elementAt(i).check();
     this.expr.check();
  }

  //@ requires locOpenBrace!=javafe.util.Location.NULL
  //@ requires locCloseBrace!=javafe.util.Location.NULL
  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static SwitchStmt make(/*@non_null*/ StmtVec stmts, int locOpenBrace, int locCloseBrace, /*@non_null*/ Expr expr, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     SwitchStmt result = new SwitchStmt();
     result.stmts = stmts;
     result.locOpenBrace = locOpenBrace;
     result.locCloseBrace = locCloseBrace;
     result.expr = expr;
     result.loc = loc;
     return result;
  }
}
