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



public class VarExprModifierPragma extends ModifierPragma {
  public int tag;

  public /*@non_null*/ GenericVarDecl arg;

  public /*@non_null*/ Expr expr;

  public int loc;


  public final int getTag() { return tag; }

  private void postCheck() {
    boolean goodtag =
      (tag == TagConstants.EXSURES || tag == TagConstants.ALSO_EXSURES);
    Assert.notFalse(goodtag);
  }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return expr.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw VarExprModifierPragma whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected VarExprModifierPragma() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.arg;
     else index--;

     if (index == 0) return this.expr;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[VarExprModifierPragma"
        + " tag = " + this.tag
        + " arg = " + this.arg
        + " expr = " + this.expr
        + " loc = " + this.loc
        + "]";
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitVarExprModifierPragma(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitVarExprModifierPragma(this, o); else return null;
  }

  public void check() {
     this.arg.check();
     this.expr.check();
     postCheck();
  }

  //@ ensures \result!=null
  public static VarExprModifierPragma make(int tag, /*@non_null*/ GenericVarDecl arg, /*@non_null*/ Expr expr, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     VarExprModifierPragma result = new VarExprModifierPragma();
     result.tag = tag;
     result.arg = arg;
     result.expr = expr;
     result.loc = loc;
     return result;
  }
}
