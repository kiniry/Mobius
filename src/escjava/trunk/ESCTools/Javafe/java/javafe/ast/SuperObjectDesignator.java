/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents a ObjectDesignator of the form "super . ".
 *  Is created only by the parser, not by name resolution.
 */

public class SuperObjectDesignator extends ObjectDesignator {
  //@ invariant locSuper!=javafe.util.Location.NULL
  public int locSuper;

  public int getStartLoc() { return locSuper; }


// Generated boilerplate constructors:

  /**
   ** Construct a raw SuperObjectDesignator whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected SuperObjectDesignator() {}    //@ nowarn Invariant,NonNullInit


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
     return "[SuperObjectDesignator"
        + " locDot = " + this.locDot
        + " locSuper = " + this.locSuper
        + "]";
  }

  public final int getTag() {
     return TagConstants.SUPEROBJECTDESIGNATOR;
  }

  public final void accept(Visitor v) { v.visitSuperObjectDesignator(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitSuperObjectDesignator(this, o); }

  public void check() {
     super.check();
  }

  //@ requires locDot!=javafe.util.Location.NULL
  //@ requires locSuper!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static SuperObjectDesignator make(int locDot, int locSuper) {
     //@ set I_will_establish_invariants_afterwards = true
     SuperObjectDesignator result = new SuperObjectDesignator();
     result.locDot = locDot;
     result.locSuper = locSuper;
     return result;
  }
}
