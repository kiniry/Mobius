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



public abstract class AssignCmd extends GuardedCmd {
  // denotes a subtype-dependent assignment to v
  // rhs must be pure
  public /*@non_null*/ VariableAccess v;

  public /*@non_null*/ Expr rhs;


  public int getStartLoc() { return v.getStartLoc(); }
  public int getEndLoc() { return rhs.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw AssignCmd whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected AssignCmd() {}    //@ nowarn Invariant,NonNullInit

  public void check() {
     super.check();
     this.v.check();
     this.rhs.check();
  }

}
