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



public class DefPredLetExpr extends Expr {
    public /*@non_null*/ DefPredVec preds;

    public /*@non_null*/ Expr body;


    public int getStartLoc() { return body.getStartLoc(); }


// Generated boilerplate constructors:

    /**
     ** Construct a raw DefPredLetExpr whose class invariant(s) have not
     ** yet been established.  It is the caller's job to
     ** initialize the returned node's fields so that any
     ** class invariants hold.
     **/
    //@ requires I_will_establish_invariants_afterwards
    protected DefPredLetExpr() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

    public final int childCount() {
       int sz = 0;
       if (this.preds != null) sz += this.preds.size();
       return sz + 1;
    }

    public final Object childAt(int index) {
            /*throws IndexOutOfBoundsException*/
       if (index < 0)
          throw new IndexOutOfBoundsException("AST child index " + index);
       int indexPre = index;

       int sz;

       sz = (this.preds == null ? 0 : this.preds.size());
       if (0 <= index && index < sz)
          return this.preds.elementAt(index);
       else index -= sz;

       if (index == 0) return this.body;
       else index--;

       throw new IndexOutOfBoundsException("AST child index " + indexPre);
    }   //@ nowarn Exception

    public final String toString() {
       return "[DefPredLetExpr"
          + " preds = " + this.preds
          + " body = " + this.body
          + "]";
    }

    public final int getTag() {
       return TagConstants.DEFPREDLETEXPR;
    }

    public final void accept(javafe.ast.Visitor v) { 
        if (v instanceof Visitor) ((Visitor)v).visitDefPredLetExpr(this);
    }

    public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
        if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitDefPredLetExpr(this, o); else return null;
    }

    public void check() {
       for(int i = 0; i < this.preds.size(); i++)
          this.preds.elementAt(i).check();
       this.body.check();
    }

    //@ ensures \result!=null
    public static DefPredLetExpr make(/*@non_null*/ DefPredVec preds, /*@non_null*/ Expr body) {
       //@ set I_will_establish_invariants_afterwards = true
       DefPredLetExpr result = new DefPredLetExpr();
       result.preds = preds;
       result.body = body;
       return result;
    }
}
