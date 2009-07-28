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



public class SkolemConstantPragma extends StmtPragma {
  public /*@non_null*/ LocalVarDeclVec decls;

  public int sloc;

  public int eloc;

  public int getStartLoc() { return sloc; }
  public int getEndLoc() { return eloc; }


// Generated boilerplate constructors:

  /**
   ** Construct a raw SkolemConstantPragma whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected SkolemConstantPragma() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.decls != null) sz += this.decls.size();
     return sz + 0;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     sz = (this.decls == null ? 0 : this.decls.size());
     if (0 <= index && index < sz)
        return this.decls.elementAt(index);
     else index -= sz;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[SkolemConstantPragma"
        + " decls = " + this.decls
        + " sloc = " + this.sloc
        + " eloc = " + this.eloc
        + "]";
  }

  public final int getTag() {
     return TagConstants.SKOLEMCONSTANTPRAGMA;
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitSkolemConstantPragma(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitSkolemConstantPragma(this, o); else return null;
  }

  public void check() {
     for(int i = 0; i < this.decls.size(); i++)
        this.decls.elementAt(i).check();
  }

  //@ ensures \result!=null
  public static SkolemConstantPragma make(/*@non_null*/ LocalVarDeclVec decls, int sloc, int eloc) {
     //@ set I_will_establish_invariants_afterwards = true
     SkolemConstantPragma result = new SkolemConstantPragma();
     result.decls = decls;
     result.sloc = sloc;
     result.eloc = eloc;
     return result;
  }
}
