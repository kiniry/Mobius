// -*- mode: java -*-
/* Copyright 2000, 2001, Compaq Computer Corporation */

/* IF THIS IS A JAVA FILE, DO NOT EDIT IT!  

   Most Java files in this directory which are part of the Javafe AST
   are automatically generated using the astgen comment (see
   ESCTools/Javafe/astgen) from the input file 'hierarchy.h'.  If you
   wish to modify AST classes or introduce new ones, modify
   'hierarchy.j.'
 */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;
import javafe.tc.TagConstants;

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

public class ForStmt extends Stmt
{
  public /*@ non_null @*/ StmtVec forInit;

  public /*@ non_null @*/ Expr test;

  public /*@ non_null @*/ ExprVec forUpdate;

  public /*@ non_null @*/ Stmt body;

  //@ invariant loc != javafe.util.Location.NULL;
  public int loc;

  //@ invariant locFirstSemi != javafe.util.Location.NULL;
  public int locFirstSemi;


  private void postCheck() {
    for(int i = 0; i < forInit.size(); i++) {
      int t = forInit.elementAt(i).getTag();
      Assert.notFalse(t != TagConstants.SWITCHLABEL	 //@ nowarn Pre;
		    && t != TagConstants.CONSTRUCTORINVOCATION);
      // Could have a stronger invariant here...
    }
    // Invariants on forUpdate??...
    int t = body.getTag();
    Assert.notFalse(t != TagConstants.SWITCHLABEL	//@ nowarn Pre;
		    && t != TagConstants.CONSTRUCTORINVOCATION
		    && t != TagConstants.VARDECLSTMT);
  }
  //@ public represents startLoc <- loc;
  public /*@ pure @*/ int getStartLoc() { return loc; }
  //@ also public normal_behavior
  //@ ensures \result == body.getEndLoc();
  public /*@ pure @*/ int getEndLoc() { return body.getEndLoc(); }


// Generated boilerplate constructors:

  //@ ensures this.forInit == forInit;
  //@ ensures this.test == test;
  //@ ensures this.forUpdate == forUpdate;
  //@ ensures this.body == body;
  //@ ensures this.loc == loc;
  //@ ensures this.locFirstSemi == locFirstSemi;
  protected ForStmt(/*@ non_null @*/ StmtVec forInit, /*@ non_null @*/ Expr test, /*@ non_null @*/ ExprVec forUpdate, /*@ non_null @*/ Stmt body, int loc, int locFirstSemi) {
     super();
     this.forInit = forInit;
     this.test = test;
     this.forUpdate = forUpdate;
     this.body = body;
     this.loc = loc;
     this.locFirstSemi = locFirstSemi;
  }

// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.forInit != null) sz += this.forInit.size();
     if (this.forUpdate != null) sz += this.forUpdate.size();
     return sz + 2;
  }

  public final /*@ non_null */ Object childAt(int index) {
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
  }   //@ nowarn Exception;

  public final /*@non_null*/String toString() {
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

  public final void accept(/*@ non_null */ Visitor v) { v.visitForStmt(this); }

  public final /*@ non_null */ Object accept(/*@ non_null */ VisitorArgResult v, Object o) {return v.visitForStmt(this, o); }

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

  //@ requires loc != javafe.util.Location.NULL;
  //@ requires locFirstSemi != javafe.util.Location.NULL;
  //@ ensures \result != null;
  public static /*@ non_null */ ForStmt make(/*@ non_null @*/ StmtVec forInit, /*@ non_null @*/ Expr test, /*@ non_null @*/ ExprVec forUpdate, /*@ non_null @*/ Stmt body, int loc, int locFirstSemi) {
     ForStmt result = new ForStmt(forInit, test, forUpdate, body, loc, locFirstSemi);
     return result;
  }
}
