/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class VarDeclStmt extends Stmt {
  public /*@non_null*/ LocalVarDecl decl;

  public int getStartLoc() { return decl.getStartLoc(); }
  public int getEndLoc() { return decl.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw VarDeclStmt whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected VarDeclStmt() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.decl;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[VarDeclStmt"
        + " decl = " + this.decl
        + "]";
  }

  public final int getTag() {
     return TagConstants.VARDECLSTMT;
  }

  public final void accept(Visitor v) { v.visitVarDeclStmt(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitVarDeclStmt(this, o); }

  public void check() {
     super.check();
     this.decl.check();
  }

  //@ ensures \result!=null
  public static VarDeclStmt make(/*@non_null*/ LocalVarDecl decl) {
     //@ set I_will_establish_invariants_afterwards = true
     VarDeclStmt result = new VarDeclStmt();
     result.decl = decl;
     return result;
  }
}
