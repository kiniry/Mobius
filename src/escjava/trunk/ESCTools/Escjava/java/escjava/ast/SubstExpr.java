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



public class SubstExpr extends GCExpr {
  public /*@non_null*/ GenericVarDecl var;

  public /*@non_null*/ Expr val;

  public /*@non_null*/ Expr target;




// Generated boilerplate constructors:

  /**
   ** Construct a raw SubstExpr whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected SubstExpr() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     return 3;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.var;
     else index--;

     if (index == 0) return this.val;
     else index--;

     if (index == 0) return this.target;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[SubstExpr"
        + " sloc = " + this.sloc
        + " eloc = " + this.eloc
        + " var = " + this.var
        + " val = " + this.val
        + " target = " + this.target
        + "]";
  }

  public final int getTag() {
     return TagConstants.SUBSTEXPR;
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitSubstExpr(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitSubstExpr(this, o); else return null;
  }

  public void check() {
     super.check();
     this.var.check();
     this.val.check();
     this.target.check();
  }

  //@ ensures \result!=null
  public static SubstExpr make(int sloc, int eloc, /*@non_null*/ GenericVarDecl var, /*@non_null*/ Expr val, /*@non_null*/ Expr target) {
     //@ set I_will_establish_invariants_afterwards = true
     SubstExpr result = new SubstExpr();
     result.sloc = sloc;
     result.eloc = eloc;
     result.var = var;
     result.val = val;
     result.target = target;
     return result;
  }
}
