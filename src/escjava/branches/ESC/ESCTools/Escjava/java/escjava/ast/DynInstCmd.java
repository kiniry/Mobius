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



public class DynInstCmd extends GuardedCmd {
  // denotes DynamicInstanceCommand s IN g END.
  public /*@non_null*/ String s;

  public /*@non_null*/ GuardedCmd g;


  public int getStartLoc() { return g.getStartLoc(); }
  public int getEndLoc() { return g.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw DynInstCmd whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected DynInstCmd() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.s;
     else index--;

     if (index == 0) return this.g;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[DynInstCmd"
        + " s = " + this.s
        + " g = " + this.g
        + "]";
  }

  public final int getTag() {
     return TagConstants.DYNINSTCMD;
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitDynInstCmd(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitDynInstCmd(this, o); else return null;
  }

  public void check() {
     super.check();
     if (this.s == null) throw new RuntimeException();
     this.g.check();
  }

  //@ ensures \result!=null
  public static DynInstCmd make(/*@non_null*/ String s, /*@non_null*/ GuardedCmd g) {
     //@ set I_will_establish_invariants_afterwards = true
     DynInstCmd result = new DynInstCmd();
     result.s = s;
     result.g = g;
     return result;
  }
}
