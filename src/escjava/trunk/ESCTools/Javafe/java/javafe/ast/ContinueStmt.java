/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class ContinueStmt extends BranchStmt {


// Generated boilerplate constructors:

   /**
    ** Construct a raw ContinueStmt whose class invariant(s) have not
    ** yet been established.  It is the caller's job to
    ** initialize the returned node's fields so that any
    ** class invariants hold.
    **/
   //@ requires I_will_establish_invariants_afterwards
   protected ContinueStmt() {}    //@ nowarn Invariant,NonNullInit


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

      if (index == 0) return this.label;
      else index--;

      throw new IndexOutOfBoundsException("AST child index " + indexPre);
   }   //@ nowarn Exception

   public final String toString() {
      return "[ContinueStmt"
         + " label = " + this.label
         + " loc = " + this.loc
         + "]";
   }

   public final int getTag() {
      return TagConstants.CONTINUESTMT;
   }

   public final void accept(Visitor v) { v.visitContinueStmt(this); }

   public final Object accept(VisitorArgResult v, Object o) {return v.visitContinueStmt(this, o); }

   public void check() {
      super.check();
   }

   //@ requires loc!=javafe.util.Location.NULL
   //@ ensures \result!=null
   public static ContinueStmt make(Identifier label, int loc) {
      //@ set I_will_establish_invariants_afterwards = true
      ContinueStmt result = new ContinueStmt();
      result.label = label;
      result.loc = loc;
      return result;
   }
}
