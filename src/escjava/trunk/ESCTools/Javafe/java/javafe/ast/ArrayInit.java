/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents an ArrayInitializer. 
 */

public class ArrayInit extends VarInit {
  public /*@non_null*/ VarInitVec elems;

  //@ invariant locOpenBrace!=javafe.util.Location.NULL
  public int locOpenBrace;

  //@ invariant locCloseBrace!=javafe.util.Location.NULL
  public int locCloseBrace;

  public int getStartLoc() { return locOpenBrace; }
  public int getEndLoc() { return locCloseBrace; }


// Generated boilerplate constructors:

  /**
   ** Construct a raw ArrayInit whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected ArrayInit() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.elems != null) sz += this.elems.size();
     return sz + 0;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     sz = (this.elems == null ? 0 : this.elems.size());
     if (0 <= index && index < sz)
        return this.elems.elementAt(index);
     else index -= sz;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[ArrayInit"
        + " elems = " + this.elems
        + " locOpenBrace = " + this.locOpenBrace
        + " locCloseBrace = " + this.locCloseBrace
        + "]";
  }

  public final int getTag() {
     return TagConstants.ARRAYINIT;
  }

  public final void accept(Visitor v) { v.visitArrayInit(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitArrayInit(this, o); }

  public void check() {
     super.check();
     for(int i = 0; i < this.elems.size(); i++)
        this.elems.elementAt(i).check();
  }

  //@ requires locOpenBrace!=javafe.util.Location.NULL
  //@ requires locCloseBrace!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static ArrayInit make(/*@non_null*/ VarInitVec elems, int locOpenBrace, int locCloseBrace) {
     //@ set I_will_establish_invariants_afterwards = true
     ArrayInit result = new ArrayInit();
     result.elems = elems;
     result.locOpenBrace = locOpenBrace;
     result.locCloseBrace = locCloseBrace;
     return result;
  }
}
