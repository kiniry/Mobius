/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents a simple name that is bound to a local variable declaration.
 *  Is created only by the name resolution code, not by the parser.
 */

public class VariableAccess extends Expr {
  public /*@non_null*/ Identifier id;

  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;


  //@ invariant decl.id==id
  public /*@non_null*/ GenericVarDecl decl;

  private void postCheck() {
      Assert.notNull(decl);
      Assert.notFalse(id == decl.id);
      // Any other invariants here...???
  }
  public int getStartLoc() { return loc; }


  //@ requires decl.id == id
  //
  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static VariableAccess make(/*@non_null*/ Identifier id, int loc,
				    /*@non_null*/ GenericVarDecl decl) {
        //@ set I_will_establish_invariants_afterwards = true
	VariableAccess result = new VariableAccess();
	result.id = id;
	result.loc = loc;
	result.decl = decl;
	return result;
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw VariableAccess whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected VariableAccess() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.id;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[VariableAccess"
        + " id = " + this.id
        + " loc = " + this.loc
        + "]";
  }

  public final int getTag() {
     return TagConstants.VARIABLEACCESS;
  }

  public final void accept(Visitor v) { v.visitVariableAccess(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitVariableAccess(this, o); }

  public void check() {
     super.check();
     if (this.id == null) throw new RuntimeException();
     postCheck();
  }

}
