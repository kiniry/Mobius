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



public class GetsCmd extends AssignCmd {
  // denotes v := rhs


// Generated boilerplate constructors:

   /**
    ** Construct a raw GetsCmd whose class invariant(s) have not
    ** yet been established.  It is the caller's job to
    ** initialize the returned node's fields so that any
    ** class invariants hold.
    **/
   //@ requires I_will_establish_invariants_afterwards
   protected GetsCmd() {}    //@ nowarn Invariant,NonNullInit


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

      if (index == 0) return this.v;
      else index--;

      if (index == 0) return this.rhs;
      else index--;

      throw new IndexOutOfBoundsException("AST child index " + indexPre);
   }   //@ nowarn Exception

   public final String toString() {
      return "[GetsCmd"
         + " v = " + this.v
         + " rhs = " + this.rhs
         + "]";
   }

   public final int getTag() {
      return TagConstants.GETSCMD;
   }

   public final void accept(javafe.ast.Visitor v) { 
      if (v instanceof Visitor) ((Visitor)v).visitGetsCmd(this);
   }

   public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
      if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitGetsCmd(this, o); else return null;
   }

   public void check() {
      super.check();
      this.v.check();
      this.rhs.check();
   }

   //@ ensures \result!=null
   public static GetsCmd make(/*@non_null*/ VariableAccess v, /*@non_null*/ Expr rhs) {
      //@ set I_will_establish_invariants_afterwards = true
      GetsCmd result = new GetsCmd();
      result.v = v;
      result.rhs = rhs;
      return result;
   }
}
