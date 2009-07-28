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



public class VarInCmd extends GuardedCmd {
  // denotes VAR v IN g END.
  public /*@non_null*/ GenericVarDeclVec v;

  public /*@non_null*/ GuardedCmd g;


  public int getStartLoc() { return g.getStartLoc(); }
  public int getEndLoc() { return g.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw VarInCmd whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected VarInCmd() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.v != null) sz += this.v.size();
     return sz + 1;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     sz = (this.v == null ? 0 : this.v.size());
     if (0 <= index && index < sz)
        return this.v.elementAt(index);
     else index -= sz;

     if (index == 0) return this.g;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[VarInCmd"
        + " v = " + this.v
        + " g = " + this.g
        + "]";
  }

  public final int getTag() {
     return TagConstants.VARINCMD;
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitVarInCmd(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitVarInCmd(this, o); else return null;
  }

  public void check() {
     super.check();
     for(int i = 0; i < this.v.size(); i++)
        this.v.elementAt(i).check();
     this.g.check();
  }

  //@ ensures \result!=null
  public static VarInCmd make(/*@non_null*/ GenericVarDeclVec v, /*@non_null*/ GuardedCmd g) {
     //@ set I_will_establish_invariants_afterwards = true
     VarInCmd result = new VarInCmd();
     result.v = v;
     result.g = g;
     return result;
  }
}
