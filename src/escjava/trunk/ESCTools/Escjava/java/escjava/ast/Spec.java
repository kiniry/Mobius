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



public class Spec extends ASTNode {
  public /*@non_null*/ DerivedMethodDecl dmd;

  public /*@non_null*/ ExprVec targets;

  public /*@non_null*/ Hashtable preVarMap;

  public /*@non_null*/ ConditionVec pre;

  public /*@non_null*/ ConditionVec post;


  public int getStartLoc() { return dmd.original.getStartLoc(); }
  public int getEndLoc() { return dmd.original.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw Spec whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected Spec() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.targets != null) sz += this.targets.size();
     if (this.pre != null) sz += this.pre.size();
     if (this.post != null) sz += this.post.size();
     return sz + 2;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.dmd;
     else index--;

     sz = (this.targets == null ? 0 : this.targets.size());
     if (0 <= index && index < sz)
        return this.targets.elementAt(index);
     else index -= sz;

     if (index == 0) return this.preVarMap;
     else index--;

     sz = (this.pre == null ? 0 : this.pre.size());
     if (0 <= index && index < sz)
        return this.pre.elementAt(index);
     else index -= sz;

     sz = (this.post == null ? 0 : this.post.size());
     if (0 <= index && index < sz)
        return this.post.elementAt(index);
     else index -= sz;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[Spec"
        + " dmd = " + this.dmd
        + " targets = " + this.targets
        + " preVarMap = " + this.preVarMap
        + " pre = " + this.pre
        + " post = " + this.post
        + "]";
  }

  public final int getTag() {
     return TagConstants.SPEC;
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitSpec(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitSpec(this, o); else return null;
  }

  public void check() {
     if (this.dmd == null) throw new RuntimeException();
     for(int i = 0; i < this.targets.size(); i++)
        this.targets.elementAt(i).check();
     if (this.preVarMap == null) throw new RuntimeException();
     for(int i = 0; i < this.pre.size(); i++)
        this.pre.elementAt(i).check();
     for(int i = 0; i < this.post.size(); i++)
        this.post.elementAt(i).check();
  }

  //@ ensures \result!=null
  public static Spec make(/*@non_null*/ DerivedMethodDecl dmd, /*@non_null*/ ExprVec targets, /*@non_null*/ Hashtable preVarMap, /*@non_null*/ ConditionVec pre, /*@non_null*/ ConditionVec post) {
     //@ set I_will_establish_invariants_afterwards = true
     Spec result = new Spec();
     result.dmd = dmd;
     result.targets = targets;
     result.preVarMap = preVarMap;
     result.pre = pre;
     result.post = post;
     return result;
  }
}
