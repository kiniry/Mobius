/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class OnDemandImportDecl extends ImportDecl {
  public /*@non_null*/ Name pkgName;



// Generated boilerplate constructors:

  /**
   ** Construct a raw OnDemandImportDecl whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected OnDemandImportDecl() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.pkgName;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[OnDemandImportDecl"
        + " loc = " + this.loc
        + " pkgName = " + this.pkgName
        + "]";
  }

  public final int getTag() {
     return TagConstants.ONDEMANDIMPORTDECL;
  }

  public final void accept(Visitor v) { v.visitOnDemandImportDecl(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitOnDemandImportDecl(this, o); }

  public void check() {
     super.check();
     this.pkgName.check();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static OnDemandImportDecl make(int loc, /*@non_null*/ Name pkgName) {
     //@ set I_will_establish_invariants_afterwards = true
     OnDemandImportDecl result = new OnDemandImportDecl();
     result.loc = loc;
     result.pkgName = pkgName;
     return result;
  }
}
