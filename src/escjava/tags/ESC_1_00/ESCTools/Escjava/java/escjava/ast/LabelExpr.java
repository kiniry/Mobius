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



public class LabelExpr extends GCExpr {
  public boolean positive;

  public /*@non_null*/ Identifier label;

  public /*@non_null*/ Expr expr;





// Generated boilerplate constructors:

  /**
   ** Construct a raw LabelExpr whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected LabelExpr() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.label;
     else index--;

     if (index == 0) return this.expr;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[LabelExpr"
        + " sloc = " + this.sloc
        + " eloc = " + this.eloc
        + " positive = " + this.positive
        + " label = " + this.label
        + " expr = " + this.expr
        + "]";
  }

  public final int getTag() {
     return TagConstants.LABELEXPR;
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitLabelExpr(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitLabelExpr(this, o); else return null;
  }

  public void check() {
     super.check();
     this.label.check();
     this.expr.check();
  }

  //@ ensures \result!=null
  public static LabelExpr make(int sloc, int eloc, boolean positive, /*@non_null*/ Identifier label, /*@non_null*/ Expr expr) {
     //@ set I_will_establish_invariants_afterwards = true
     LabelExpr result = new LabelExpr();
     result.sloc = sloc;
     result.eloc = eloc;
     result.positive = positive;
     result.label = label;
     result.expr = expr;
     return result;
  }
}
