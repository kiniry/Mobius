/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class ClassDeclStmt extends Stmt {
  public /*@non_null*/ ClassDecl decl;


  private void postCheck() {
  // Awaiting information from Sun...
  }

  public int getStartLoc() { return decl.getStartLoc(); }
  public int getEndLoc() { return decl.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw ClassDeclStmt whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected ClassDeclStmt() {}    //@ nowarn Invariant,NonNullInit


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
     return "[ClassDeclStmt"
        + " decl = " + this.decl
        + "]";
  }

  public final int getTag() {
     return TagConstants.CLASSDECLSTMT;
  }

  public final void accept(Visitor v) { v.visitClassDeclStmt(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitClassDeclStmt(this, o); }

  public void check() {
     super.check();
     this.decl.check();
     postCheck();
  }

  //@ ensures \result!=null
  public static ClassDeclStmt make(/*@non_null*/ ClassDecl decl) {
     //@ set I_will_establish_invariants_afterwards = true
     ClassDeclStmt result = new ClassDeclStmt();
     result.decl = decl;
     return result;
  }
}
