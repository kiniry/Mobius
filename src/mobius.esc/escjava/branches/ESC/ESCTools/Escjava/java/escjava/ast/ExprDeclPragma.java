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



//// Pragmas

public class ExprDeclPragma extends TypeDeclElemPragma {
  public int tag;

  public /*@non_null*/ Expr expr;

  public int loc;


  public final int getTag() { return tag; }

  private void postCheck() {
    boolean goodtag =
      (tag == TagConstants.AXIOM || tag == TagConstants.INVARIANT);
    Assert.notFalse(goodtag);
  }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return expr.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw ExprDeclPragma whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected ExprDeclPragma() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.expr;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[ExprDeclPragma"
        + " tag = " + this.tag
        + " expr = " + this.expr
        + " loc = " + this.loc
        + "]";
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitExprDeclPragma(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitExprDeclPragma(this, o); else return null;
  }

  public void check() {
     this.expr.check();
     postCheck();
  }

  //@ ensures \result!=null
  public static ExprDeclPragma make(int tag, /*@non_null*/ Expr expr, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     ExprDeclPragma result = new ExprDeclPragma();
     result.tag = tag;
     result.expr = expr;
     result.loc = loc;
     return result;
  }
}
