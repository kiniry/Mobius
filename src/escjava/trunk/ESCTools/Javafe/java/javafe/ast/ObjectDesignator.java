/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit



/** Designates the object or type used for a field or method access.
 *  Subclasses represent "expr.", "type.", or "super."
 */

public abstract class ObjectDesignator extends ASTNode {
  //@ invariant locDot!=javafe.util.Location.NULL
  public int locDot;


    public int getEndLoc() { return locDot; }


// Generated boilerplate constructors:

  /**
   ** Construct a raw ObjectDesignator whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected ObjectDesignator() {}    //@ nowarn Invariant,NonNullInit

  public void check() {
     super.check();
  }

}
