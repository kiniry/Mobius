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



public class QuantifiedExpr extends GCExpr {
  public int quantifier;

  public /*@non_null*/ GenericVarDeclVec vars;

  public /*@non_null*/ Expr expr;

  public ExprVec nopats;


  public final int getTag() { return quantifier; }

  private void postCheck() {
    boolean goodtag =
      (quantifier == TagConstants.FORALL
       || quantifier == TagConstants.EXISTS);
    Assert.notFalse(goodtag);
  }



// Generated boilerplate constructors:

  /**
   ** Construct a raw QuantifiedExpr whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected QuantifiedExpr() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.vars != null) sz += this.vars.size();
     if (this.nopats != null) sz += this.nopats.size();
     return sz + 1;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     sz = (this.vars == null ? 0 : this.vars.size());
     if (0 <= index && index < sz)
        return this.vars.elementAt(index);
     else index -= sz;

     if (index == 0) return this.expr;
     else index--;

     sz = (this.nopats == null ? 0 : this.nopats.size());
     if (0 <= index && index < sz)
        return this.nopats.elementAt(index);
     else index -= sz;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[QuantifiedExpr"
        + " sloc = " + this.sloc
        + " eloc = " + this.eloc
        + " quantifier = " + this.quantifier
        + " vars = " + this.vars
        + " expr = " + this.expr
        + " nopats = " + this.nopats
        + "]";
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitQuantifiedExpr(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitQuantifiedExpr(this, o); else return null;
  }

  public void check() {
     super.check();
     for(int i = 0; i < this.vars.size(); i++)
        this.vars.elementAt(i).check();
     this.expr.check();
     if (this.nopats != null)
        for(int i = 0; i < this.nopats.size(); i++)
           this.nopats.elementAt(i).check();
     postCheck();
  }

  //@ ensures \result!=null
  public static QuantifiedExpr make(int sloc, int eloc, int quantifier, /*@non_null*/ GenericVarDeclVec vars, /*@non_null*/ Expr expr, ExprVec nopats) {
     //@ set I_will_establish_invariants_afterwards = true
     QuantifiedExpr result = new QuantifiedExpr();
     result.sloc = sloc;
     result.eloc = eloc;
     result.quantifier = quantifier;
     result.vars = vars;
     result.expr = expr;
     result.nopats = nopats;
     return result;
  }
}
