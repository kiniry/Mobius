/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/**
 ** Represents a class literal (Type . class)
 **/

public class ClassLiteral extends Expr {
  //@ invariant type.syntax
  public /*@non_null*/ Type type;

  //@ invariant locDot!=javafe.util.Location.NULL
  public int locDot;


  public int getStartLoc() {
    return type.getStartLoc();
  }

  public int getEndLoc() { 
    return locDot;
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw ClassLiteral whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected ClassLiteral() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.type;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[ClassLiteral"
        + " type = " + this.type
        + " locDot = " + this.locDot
        + "]";
  }

  public final int getTag() {
     return TagConstants.CLASSLITERAL;
  }

  public final void accept(Visitor v) { v.visitClassLiteral(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitClassLiteral(this, o); }

  public void check() {
     super.check();
     this.type.check();
  }

  //@ requires type.syntax
  //@ requires locDot!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static ClassLiteral make(/*@non_null*/ Type type, int locDot) {
     //@ set I_will_establish_invariants_afterwards = true
     ClassLiteral result = new ClassLiteral();
     result.type = type;
     result.locDot = locDot;
     return result;
  }
}
