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



public class SetStmtPragma extends StmtPragma {
  // set 'target' = 'value':

  public /*@non_null*/ Expr target;

  public int locOp;

  public /*@non_null*/ Expr value;

  public int loc;


  public int getStartLoc() { return loc; }
  public int getEndLoc() { return value.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw SetStmtPragma whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected SetStmtPragma() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     return 2;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.target;
     else index--;

     if (index == 0) return this.value;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[SetStmtPragma"
        + " target = " + this.target
        + " locOp = " + this.locOp
        + " value = " + this.value
        + " loc = " + this.loc
        + "]";
  }

  public final int getTag() {
     return TagConstants.SETSTMTPRAGMA;
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitSetStmtPragma(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitSetStmtPragma(this, o); else return null;
  }

  public void check() {
     this.target.check();
     this.value.check();
  }

  //@ ensures \result!=null
  public static SetStmtPragma make(/*@non_null*/ Expr target, int locOp, /*@non_null*/ Expr value, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     SetStmtPragma result = new SetStmtPragma();
     result.target = target;
     result.locOp = locOp;
     result.value = value;
     result.loc = loc;
     return result;
  }
}
