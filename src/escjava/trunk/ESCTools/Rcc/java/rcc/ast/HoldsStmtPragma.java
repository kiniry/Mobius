/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;


import java.util.Hashtable;

import javafe.ast.*;

import javafe.ast.Expr;
import rcc.ast.Visitor;      // Work around 1.0.2 compiler bug
import rcc.ast.VisitorArgResult;      // Work around 1.0.2 compiler bug
import rcc.ast.TagConstants; // Work around 1.0.2 compiler bug
import rcc.ast.GeneratedTags;// Work around 1.0.2 compiler bug
import rcc.ast.AnOverview;   // Work around 1.0.2 compiler bug
import javafe.util.Assert;
import javafe.util.Location;


// Convention: unless otherwise noted, integer fields named "loc"g refer
// to the locaction of the first character of the syntactic unit

//# TagBase javafe.tc.TagConstants.LAST_TAG + 1
//# VisitorRoot javafe.ast.Visitor
//# VisitorARRoot javafe.ast.VisitorArgResult


public class HoldsStmtPragma extends StmtPragma {
 public /*@ non_null @*/ ExprVec expressions;

  public int loc;

			
	public int getStartLoc() { return loc; }
	public int getEndLoc() { return expressions.elementAt(expressions.size()-1).getEndLoc(); }


// Generated boilerplate constructors:

 /**
  * Construct a raw HoldsStmtPragma whose class invariant(s) have not
  * yet been established.  It is the caller's job to
  * initialize the returned node's fields so that any
  * class invariants hold.
  */
 //@ requires I_will_establish_invariants_afterwards;
 protected HoldsStmtPragma() {}    //@ nowarn Invariant,NonNullInit;


// Generated boilerplate methods:

 public final int childCount() {
    int sz = 0;
    if (this.expressions != null) sz += this.expressions.size();
    return sz + 0;
 }

 public final Object childAt(int index) {
         /*throws IndexOutOfBoundsException*/
    if (index < 0)
       throw new IndexOutOfBoundsException("AST child index " + index);
    int indexPre = index;

    int sz;

    sz = (this.expressions == null ? 0 : this.expressions.size());
    if (0 <= index && index < sz)
       return this.expressions.elementAt(index);
    else index -= sz;

    throw new IndexOutOfBoundsException("AST child index " + indexPre);
 }   //@ nowarn Exception;

 public final String toString() {
    return "[HoldsStmtPragma"
       + " expressions = " + this.expressions
       + " loc = " + this.loc
       + "]";
 }

 public final int getTag() {
    return TagConstants.HOLDSSTMTPRAGMA;
 }

 public final void accept(javafe.ast.Visitor v) { 
  if (v instanceof Visitor) ((Visitor)v).visitHoldsStmtPragma(this);
 }

 public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
  if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitHoldsStmtPragma(this, o); else return null;
 }

 public void check() {
    for(int i = 0; i < this.expressions.size(); i++)
       this.expressions.elementAt(i).check();
 }

 //@ ensures \result != null;
 public static HoldsStmtPragma make(/*@ non_null @*/ ExprVec expressions, int loc) {
    //@ set I_will_establish_invariants_afterwards = true;
    HoldsStmtPragma result = new HoldsStmtPragma();
    result.expressions = expressions;
    result.loc = loc;
    return result;
 }
}
