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



public class Call extends GuardedCmd {
  public /*@non_null*/ ExprVec args;

  public int scall;

  public int ecall;


    public boolean inlined;


  // This is a backedge, so it can't be a child:
  //@ invariant rd!=null
  public RoutineDecl rd;

  public Spec spec;
  public GuardedCmd desugared;

  public int getStartLoc() { return scall; }
  public int getEndLoc() { return ecall; }


// Generated boilerplate constructors:

  /**
   ** Construct a raw Call whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected Call() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.args != null) sz += this.args.size();
     return sz + 0;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     sz = (this.args == null ? 0 : this.args.size());
     if (0 <= index && index < sz)
        return this.args.elementAt(index);
     else index -= sz;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[Call"
        + " args = " + this.args
        + " scall = " + this.scall
        + " ecall = " + this.ecall
        + " inlined = " + this.inlined
        + "]";
  }

  public final int getTag() {
     return TagConstants.CALL;
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitCall(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitCall(this, o); else return null;
  }

  public void check() {
     super.check();
     for(int i = 0; i < this.args.size(); i++)
        this.args.elementAt(i).check();
  }

  //@ ensures \result!=null
  public static Call make(/*@non_null*/ ExprVec args, int scall, int ecall, boolean inlined) {
     //@ set I_will_establish_invariants_afterwards = true
     Call result = new Call();
     result.args = args;
     result.scall = scall;
     result.ecall = ecall;
     result.inlined = inlined;
     return result;
  }
}
