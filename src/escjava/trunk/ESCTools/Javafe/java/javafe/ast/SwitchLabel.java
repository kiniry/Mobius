/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents a SwitchLabel syntactic unit.
 *  If expr is null, then represents the "default" label, 
 *  otherwise represents a case label.<p>
 *
 *
 *  We infer a default: break at the end of each switch statement that
 *  does not contain a default case to simplify translation.  Such
 *  inferred cases will have their location equal to the location of the
 *  closing bracket of the switch statement they are contained in.
 */

public class SwitchLabel extends Stmt {
  public Expr expr;

  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;

  public int getStartLoc() { return loc; }


// Generated boilerplate constructors:

  /**
   ** Construct a raw SwitchLabel whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected SwitchLabel() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.expr;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[SwitchLabel"
        + " expr = " + this.expr
        + " loc = " + this.loc
        + "]";
  }

  public final int getTag() {
     return TagConstants.SWITCHLABEL;
  }

  public final void accept(Visitor v) { v.visitSwitchLabel(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitSwitchLabel(this, o); }

  public void check() {
     super.check();
     if (this.expr != null)
        this.expr.check();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static SwitchLabel make(Expr expr, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     SwitchLabel result = new SwitchLabel();
     result.expr = expr;
     result.loc = loc;
     return result;
  }
}
