/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/* ---------------------------------------------------------------------- */

public class CatchClause extends ASTNode {
  public /*@non_null*/ FormalParaDecl arg;

  public /*@non_null*/ BlockStmt body;

  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return body.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw CatchClause whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected CatchClause() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.body;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[CatchClause"
        + " arg = " + this.arg
        + " body = " + this.body
        + " loc = " + this.loc
        + "]";
  }

  public final int getTag() {
     return TagConstants.CATCHCLAUSE;
  }

  public final void accept(Visitor v) { v.visitCatchClause(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitCatchClause(this, o); }

  public void check() {
     super.check();
     this.arg.check();
     this.body.check();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static CatchClause make(/*@non_null*/ FormalParaDecl arg, /*@non_null*/ BlockStmt body, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     CatchClause result = new CatchClause();
     result.arg = arg;
     result.body = body;
     result.loc = loc;
     return result;
  }
}
