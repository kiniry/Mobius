/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.ast;


import java.util.Hashtable;

import javafe.ast.*;
import escjava.ast.Visitor;      // Work around 1.0.2 compiler bug
import escjava.ast.TagConstants; // Work around 1.0.2 compiler bug
import escjava.ast.GeneratedTags;// Work around 1.0.2 compiler bug
import escjava.ast.AnOverview;   // Work around 1.0.2 compiler bug
import javafe.util.Assert;
import javafe.util.Location;


// Convention: unless otherwise noted, integer fields named "loc"g refer
// to the locaction of the first character of the syntactic unit

//# TagBase javafe.tc.TagConstants.LAST_TAG + 1
//# VisitorRoot javafe.ast.Visitor



public class SubSubGetsCmd extends AssignCmd {
  // denotes v[index][index] := rhs.  I expect that v will be "elems".
  public /*@non_null*/ Expr index1;

  public /*@non_null*/ Expr index2;



// Generated boilerplate constructors:

  /**
   ** Construct a raw SubSubGetsCmd whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected SubSubGetsCmd() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     return 4;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.v;
     else index--;

     if (index == 0) return this.rhs;
     else index--;

     if (index == 0) return this.index1;
     else index--;

     if (index == 0) return this.index2;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[SubSubGetsCmd"
        + " v = " + this.v
        + " rhs = " + this.rhs
        + " index1 = " + this.index1
        + " index2 = " + this.index2
        + "]";
  }

  public final int getTag() {
     return TagConstants.SUBSUBGETSCMD;
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitSubSubGetsCmd(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitSubSubGetsCmd(this, o); else return null;
  }

  public void check() {
     super.check();
     this.v.check();
     this.rhs.check();
     this.index1.check();
     this.index2.check();
  }

  //@ ensures \result!=null
  public static SubSubGetsCmd make(/*@non_null*/ VariableAccess v, /*@non_null*/ Expr rhs, /*@non_null*/ Expr index1, /*@non_null*/ Expr index2) {
     //@ set I_will_establish_invariants_afterwards = true
     SubSubGetsCmd result = new SubSubGetsCmd();
     result.v = v;
     result.rhs = rhs;
     result.index1 = index1;
     result.index2 = index2;
     return result;
  }
}
