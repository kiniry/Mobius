/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/* ---------------------------------------------------------------------- */

/** Represents a VariableInitializer. 
 */

public abstract class VarInit extends ASTNode {


// Generated boilerplate constructors:

   /**
    ** Construct a raw VarInit whose class invariant(s) have not
    ** yet been established.  It is the caller's job to
    ** initialize the returned node's fields so that any
    ** class invariants hold.
    **/
   //@ requires I_will_establish_invariants_afterwards
   protected VarInit() {}    //@ nowarn Invariant,NonNullInit

   public void check() {
      super.check();
   }

}
