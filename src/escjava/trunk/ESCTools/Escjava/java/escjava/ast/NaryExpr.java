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



public class NaryExpr extends GCExpr {
  public int op;

  public /*@non_null*/ ExprVec exprs;

 
  public final int getTag() { return op; }

  private void postCheck() {
    boolean goodtag = 
      (op == TagConstants.CLASSLITERALFUNC
       || op == TagConstants.DTTFSA
       || op == TagConstants.ELEMTYPE
       || op == TagConstants.FRESH
       || op == TagConstants.MAX
       || op == TagConstants.TYPEOF
       || (TagConstants.FIRSTFUNCTIONTAG <= op 
	   && op <= TagConstants.LASTFUNCTIONTAG));
    Assert.notFalse(goodtag);
  }



// Generated boilerplate constructors:

  /**
   ** Construct a raw NaryExpr whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected NaryExpr() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.exprs != null) sz += this.exprs.size();
     return sz + 0;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     sz = (this.exprs == null ? 0 : this.exprs.size());
     if (0 <= index && index < sz)
        return this.exprs.elementAt(index);
     else index -= sz;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[NaryExpr"
        + " sloc = " + this.sloc
        + " eloc = " + this.eloc
        + " op = " + this.op
        + " exprs = " + this.exprs
        + "]";
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitNaryExpr(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitNaryExpr(this, o); else return null;
  }

  public void check() {
     super.check();
     for(int i = 0; i < this.exprs.size(); i++)
        this.exprs.elementAt(i).check();
     postCheck();
  }

  //@ ensures \result!=null
  public static NaryExpr make(int sloc, int eloc, int op, /*@non_null*/ ExprVec exprs) {
     //@ set I_will_establish_invariants_afterwards = true
     NaryExpr result = new NaryExpr();
     result.sloc = sloc;
     result.eloc = eloc;
     result.op = op;
     result.exprs = exprs;
     return result;
  }
}
