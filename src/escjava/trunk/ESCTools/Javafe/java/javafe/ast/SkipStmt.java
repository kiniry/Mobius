/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class SkipStmt extends Stmt {
  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;

  
  public int getStartLoc() { return loc; }


// Generated boilerplate constructors:

  /**
   ** Construct a raw SkipStmt whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected SkipStmt() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     return 0;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[SkipStmt"
        + " loc = " + this.loc
        + "]";
  }

  public final int getTag() {
     return TagConstants.SKIPSTMT;
  }

  public final void accept(Visitor v) { v.visitSkipStmt(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitSkipStmt(this, o); }

  public void check() {
     super.check();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static SkipStmt make(int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     SkipStmt result = new SkipStmt();
     result.loc = loc;
     return result;
  }
}
