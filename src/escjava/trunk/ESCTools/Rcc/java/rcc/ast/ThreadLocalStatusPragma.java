/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;


import java.util.Hashtable;

import javafe.ast.*;

import javafe.ast.Expr;
import javafe.util.Assert;
import javafe.util.Location;


// Convention: unless otherwise noted, integer fields named "loc"g refer
// to the locaction of the first character of the syntactic unit

//# TagBase javafe.tc.TagConstants.LAST_TAG + 1
//# VisitorRoot javafe.ast.Visitor
//# VisitorARRoot javafe.ast.VisitorArgResult


public class ThreadLocalStatusPragma extends ModifierPragma {
 public boolean local;

  public int loc;

                        
        public int getStartLoc() { return loc; }


// Generated boilerplate constructors:

 /**
  ** Construct a raw ThreadLocalStatusPragma whose class invariant(s) have not
  ** yet been established.  It is the caller's job to
  ** initialize the returned node's fields so that any
  ** class invariants hold.
  **/
 //@ requires I_will_establish_invariants_afterwards
 protected ThreadLocalStatusPragma() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

 public final int childCount() {
    return 0;
 }

 public final Object childAt(int index) {
         /*throws IndexOutOfBoundsException*/
    if (index < 0)
       throw new IndexOutOfBoundsException("AST child index " + index);
    int indexPre = index;

    int sz;

    throw new IndexOutOfBoundsException("AST child index " + indexPre);
 }   //@ nowarn Exception

 public final String toString() {
    return "[ThreadLocalStatusPragma"
       + " local = " + this.local
       + " loc = " + this.loc
       + "]";
 }

 public final int getTag() {
    return TagConstants.THREADLOCALSTATUSPRAGMA;
 }

 public final void accept(javafe.ast.Visitor v) { 
  if (v instanceof Visitor) ((Visitor)v).visitThreadLocalStatusPragma(this);
 }

 public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
  if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitThreadLocalStatusPragma(this, o); else return null;
 }

 public void check() {
 }

 //@ ensures \result!=null
 public static ThreadLocalStatusPragma make(boolean local, int loc) {
    //@ set I_will_establish_invariants_afterwards = true
    ThreadLocalStatusPragma result = new ThreadLocalStatusPragma();
    result.local = local;
    result.loc = loc;
    return result;
 }
}
