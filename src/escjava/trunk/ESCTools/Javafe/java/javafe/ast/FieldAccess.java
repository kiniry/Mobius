/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents various kinds of field access expressions. 
 *  The FieldDecl is filled in by the name resolution code.
 */

public class FieldAccess extends Expr {
  public /*@non_null*/ ObjectDesignator od;

  public /*@non_null*/ Identifier id;

  //@ invariant locId!=javafe.util.Location.NULL
  public int locId;


  //@ invariant decl==null || decl.id==id
  public FieldDecl decl;

  private void postCheck() {
    if (decl != null) {
      Assert.notFalse(id == decl.id);
      // Any other invariants here...???
    }
  }
  public int getStartLoc() { 
    int locOd = od.getStartLoc();
    if (locOd == Location.NULL) 
      return locId;
    else
      return locOd;
  }
  public int getEndLoc() { return locId; }

  //@ requires locId!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static FieldAccess make(/*@non_null*/ ObjectDesignator od, /*@non_null*/ Identifier id, int locId) {
     //@ set I_will_establish_invariants_afterwards = true
     FieldAccess result = new FieldAccess();
     result.od = od;
     result.id = id;
     result.locId = locId;
     result.decl = null;  // Easier than puting an ensures on constructor
     return result;
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw FieldAccess whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected FieldAccess() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.od;
     else index--;

     if (index == 0) return this.id;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[FieldAccess"
        + " od = " + this.od
        + " id = " + this.id
        + " locId = " + this.locId
        + "]";
  }

  public final int getTag() {
     return TagConstants.FIELDACCESS;
  }

  public final void accept(Visitor v) { v.visitFieldAccess(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitFieldAccess(this, o); }

  public void check() {
     super.check();
     this.od.check();
     if (this.id == null) throw new RuntimeException();
     postCheck();
  }

}
