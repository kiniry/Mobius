/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class SingleTypeImportDecl extends ImportDecl {
  public /*@non_null*/ TypeName typeName;



// Generated boilerplate constructors:

  /**
   ** Construct a raw SingleTypeImportDecl whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected SingleTypeImportDecl() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.typeName;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[SingleTypeImportDecl"
        + " loc = " + this.loc
        + " typeName = " + this.typeName
        + "]";
  }

  public final int getTag() {
     return TagConstants.SINGLETYPEIMPORTDECL;
  }

  public final void accept(Visitor v) { v.visitSingleTypeImportDecl(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitSingleTypeImportDecl(this, o); }

  public void check() {
     super.check();
     this.typeName.check();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static SingleTypeImportDecl make(int loc, /*@non_null*/ TypeName typeName) {
     //@ set I_will_establish_invariants_afterwards = true
     SingleTypeImportDecl result = new SingleTypeImportDecl();
     result.loc = loc;
     result.typeName = typeName;
     return result;
  }
}
