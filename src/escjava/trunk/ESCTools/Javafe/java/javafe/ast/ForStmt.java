/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents a ForStatement.
 *
 *  The ForInit part of a ForStatement is either a StatementExpressionList
 *  or a LocalVariableDeclaration. Both alternatives are represented here
 *  by a Stmt sequence. 
 *  Note that our Stmt class corresponds to a BlockStatement syntactic unit, 
 *  so <code>forInit</code> can contain variable declarations.
 */

public class ForStmt extends Stmt {
  public /*@non_null*/ StmtVec forInit;

  public /*@non_null*/ Expr test;

  public /*@non_null*/ ExprVec forUpdate;

  public /*@non_null*/ Stmt body;

  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;

  //@ invariant locFirstSemi!=javafe.util.Location.NULL
  public int locFirstSemi;


  private void postCheck() {
    for(int i = 0; i < forInit.size(); i++) {
      int t = forInit.elementAt(i).getTag();
      Assert.notFalse(t != TagConstants.SWITCHLABEL	 //@ nowarn Pre
		    && t != TagConstants.CONSTRUCTORINVOCATION);
      // Could have a stronger invariant here...
    }
    // Invariants on forUpdate??...
    int t = body.getTag();
    Assert.notFalse(t != TagConstants.SWITCHLABEL	//@ nowarn Pre
		    && t != TagConstants.CONSTRUCTORINVOCATION
		    && t != TagConstants.VARDECLSTMT);
  }
  public int getStartLoc() { return loc; }
  public int getEndLoc() { return body.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw ForStmt whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected ForStmt() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.forInit != null) sz += this.forInit.size();
     if (this.forUpdate != null) sz += this.forUpdate.size();
     return sz + 2;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     sz = (this.forInit == null ? 0 : this.forInit.size());
     if (0 <= index && index < sz)
        return this.forInit.elementAt(index);
     else index -= sz;

     if (index == 0) return this.test;
     else index--;

     sz = (this.forUpdate == null ? 0 : this.forUpdate.size());
     if (0 <= index && index < sz)
        return this.forUpdate.elementAt(index);
     else index -= sz;

     if (index == 0) return this.body;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[ForStmt"
        + " forInit = " + this.forInit
        + " test = " + this.test
        + " forUpdate = " + this.forUpdate
        + " body = " + this.body
        + " loc = " + this.loc
        + " locFirstSemi = " + this.locFirstSemi
        + "]";
  }

  public final int getTag() {
     return TagConstants.FORSTMT;
  }

  public final void accept(Visitor v) { v.visitForStmt(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitForStmt(this, o); }

  public void check() {
     super.check();
     for(int i = 0; i < this.forInit.size(); i++)
        this.forInit.elementAt(i).check();
     this.test.check();
     for(int i = 0; i < this.forUpdate.size(); i++)
        this.forUpdate.elementAt(i).check();
     this.body.check();
     postCheck();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ requires locFirstSemi!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static ForStmt make(/*@non_null*/ StmtVec forInit, /*@non_null*/ Expr test, /*@non_null*/ ExprVec forUpdate, /*@non_null*/ Stmt body, int loc, int locFirstSemi) {
     //@ set I_will_establish_invariants_afterwards = true
     ForStmt result = new ForStmt();
     result.forInit = forInit;
     result.test = test;
     result.forUpdate = forUpdate;
     result.body = body;
     result.loc = loc;
     result.locFirstSemi = locFirstSemi;
     return result;
  }
}
