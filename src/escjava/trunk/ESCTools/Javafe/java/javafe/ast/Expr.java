/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents an Expression.
 *
 *  We define Expr as a subclass of VarInit to yield a more compact
 *  representation. An alternative is for VarInit to contain a pointer to
 *  an Expr, which would result in a number of additional pointers, in
 *  particular for array initializers.
 */

public abstract class Expr extends VarInit {


// Generated boilerplate constructors:

   /**
    ** Construct a raw Expr whose class invariant(s) have not
    ** yet been established.  It is the caller's job to
    ** initialize the returned node's fields so that any
    ** class invariants hold.
    **/
   //@ requires I_will_establish_invariants_afterwards
   protected Expr() {}    //@ nowarn Invariant,NonNullInit

   public void check() {
      super.check();
   }

}
