/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class BreakStmt extends BranchStmt {


// Generated boilerplate constructors:

   /**
    ** Construct a raw BreakStmt whose class invariant(s) have not
    ** yet been established.  It is the caller's job to
    ** initialize the returned node's fields so that any
    ** class invariants hold.
    **/
   //@ requires I_will_establish_invariants_afterwards
   protected BreakStmt() {}    //@ nowarn Invariant,NonNullInit


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
      return "[BreakStmt"
         + " label = " + this.label
         + " loc = " + this.loc
         + "]";
   }

   public final int getTag() {
      return TagConstants.BREAKSTMT;
   }

   public final void accept(Visitor v) { v.visitBreakStmt(this); }

   public final Object accept(VisitorArgResult v, Object o) {return v.visitBreakStmt(this, o); }

   public void check() {
      super.check();
   }

   //@ requires loc!=javafe.util.Location.NULL
   //@ ensures \result!=null
   public static BreakStmt make(Identifier label, int loc) {
      //@ set I_will_establish_invariants_afterwards = true
      BreakStmt result = new BreakStmt();
      result.label = label;
      result.loc = loc;
      return result;
   }
}
