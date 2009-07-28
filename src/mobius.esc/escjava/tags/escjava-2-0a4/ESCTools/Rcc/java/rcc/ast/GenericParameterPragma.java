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




public class GenericParameterPragma extends TypeModifierPragma {
 public /*@non_null*/ FormalParaDeclVec args;

  public int loc;

			
	public int getStartLoc() { return loc; }
	public int getEndLoc() { 
		if (args.size()==0)
	    return super.getEndLoc();
		
		FormalParaDecl e= args.elementAt(args.size()-1);
		return e.getEndLoc();
	}


// Generated boilerplate constructors:

 /**
  ** Construct a raw GenericParameterPragma whose class invariant(s) have not
  ** yet been established.  It is the caller's job to
  ** initialize the returned node's fields so that any
  ** class invariants hold.
  **/
 //@ requires I_will_establish_invariants_afterwards
 protected GenericParameterPragma() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

 public final int childCount() {
    int sz = 0;
    if (this.args != null) sz += this.args.size();
    return sz + 0;
 }

 public final Object childAt(int index) {
         /*throws IndexOutOfBoundsException*/
    if (index < 0)
       throw new IndexOutOfBoundsException("AST child index " + index);
    int indexPre = index;

    int sz;

    sz = (this.args == null ? 0 : this.args.size());
    if (0 <= index && index < sz)
       return this.args.elementAt(index);
    else index -= sz;

    throw new IndexOutOfBoundsException("AST child index " + indexPre);
 }   //@ nowarn Exception

 public final String toString() {
    return "[GenericParameterPragma"
       + " args = " + this.args
       + " loc = " + this.loc
       + "]";
 }

 public final int getTag() {
    return TagConstants.GENERICPARAMETERPRAGMA;
 }

 public final void accept(javafe.ast.Visitor v) { 
  if (v instanceof Visitor) ((Visitor)v).visitGenericParameterPragma(this);
 }

 public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
  if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitGenericParameterPragma(this, o); else return null;
 }

 public void check() {
    for(int i = 0; i < this.args.size(); i++)
       this.args.elementAt(i).check();
 }

 //@ ensures \result!=null
 public static GenericParameterPragma make(/*@non_null*/ FormalParaDeclVec args, int loc) {
    //@ set I_will_establish_invariants_afterwards = true
    GenericParameterPragma result = new GenericParameterPragma();
    result.args = args;
    result.loc = loc;
    return result;
 }
}
