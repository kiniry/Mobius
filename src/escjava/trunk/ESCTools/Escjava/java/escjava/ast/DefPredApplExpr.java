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



public class DefPredApplExpr extends Expr {
    public /*@non_null*/ Identifier predId;

    public /*@non_null*/ ExprVec args;


    public int getStartLoc() { return Location.NULL; }


// Generated boilerplate constructors:

    /**
     ** Construct a raw DefPredApplExpr whose class invariant(s) have not
     ** yet been established.  It is the caller's job to
     ** initialize the returned node's fields so that any
     ** class invariants hold.
     **/
    //@ requires I_will_establish_invariants_afterwards
    protected DefPredApplExpr() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

    public final int childCount() {
       int sz = 0;
       if (this.args != null) sz += this.args.size();
       return sz + 1;
    }

    public final Object childAt(int index) {
            /*throws IndexOutOfBoundsException*/
       if (index < 0)
          throw new IndexOutOfBoundsException("AST child index " + index);
       int indexPre = index;

       int sz;

       if (index == 0) return this.predId;
       else index--;

       sz = (this.args == null ? 0 : this.args.size());
       if (0 <= index && index < sz)
          return this.args.elementAt(index);
       else index -= sz;

       throw new IndexOutOfBoundsException("AST child index " + indexPre);
    }   //@ nowarn Exception

    public final String toString() {
       return "[DefPredApplExpr"
          + " predId = " + this.predId
          + " args = " + this.args
          + "]";
    }

    public final int getTag() {
       return TagConstants.DEFPREDAPPLEXPR;
    }

    public final void accept(javafe.ast.Visitor v) { 
        if (v instanceof Visitor) ((Visitor)v).visitDefPredApplExpr(this);
    }

    public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
        if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitDefPredApplExpr(this, o); else return null;
    }

    public void check() {
       this.predId.check();
       for(int i = 0; i < this.args.size(); i++)
          this.args.elementAt(i).check();
    }

    //@ ensures \result!=null
    public static DefPredApplExpr make(/*@non_null*/ Identifier predId, /*@non_null*/ ExprVec args) {
       //@ set I_will_establish_invariants_afterwards = true
       DefPredApplExpr result = new DefPredApplExpr();
       result.predId = predId;
       result.args = args;
       return result;
    }
}
