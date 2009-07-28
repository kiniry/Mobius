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



/** Note: if <code>loc</code> is <code>Location.NULL</code>, then this
  node is <em>not</em> due to a source-level "type" construct in an
  annotation expression but rather was created during translations. */

public class TypeExpr extends GCExpr {
  public /*@non_null*/ Type type;




// Generated boilerplate constructors:

  /**
   ** Construct a raw TypeExpr whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected TypeExpr() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.type;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[TypeExpr"
        + " sloc = " + this.sloc
        + " eloc = " + this.eloc
        + " type = " + this.type
        + "]";
  }

  public final int getTag() {
     return TagConstants.TYPEEXPR;
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitTypeExpr(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitTypeExpr(this, o); else return null;
  }

  public void check() {
     super.check();
     this.type.check();
  }

  //@ ensures \result!=null
  public static TypeExpr make(int sloc, int eloc, /*@non_null*/ Type type) {
     //@ set I_will_establish_invariants_afterwards = true
     TypeExpr result = new TypeExpr();
     result.sloc = sloc;
     result.eloc = eloc;
     result.type = type;
     return result;
  }
}
