/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/* ---------------------------------------------------------------------- */

/**
 ** Represents a Type syntactic unit. <p>
 **
 ** WARNING: unlike other AST nodes, Type and it's subtypes may
 ** not have associated locations!  Locations exist only if syntax is
 ** true.
 **/

public abstract class Type extends ASTNode {
    /**
     ** Does this AST Node have associated locations?  True if yes.
     **/
    //@ ghost public boolean syntax

    public TypeModifierPragmaVec tmodifiers;



// Generated boilerplate constructors:

    /**
     ** Construct a raw Type whose class invariant(s) have not
     ** yet been established.  It is the caller's job to
     ** initialize the returned node's fields so that any
     ** class invariants hold.
     **/
    //@ requires I_will_establish_invariants_afterwards
    protected Type() {}    //@ nowarn Invariant,NonNullInit

    public void check() {
       super.check();
       if (this.tmodifiers != null)
          for(int i = 0; i < this.tmodifiers.size(); i++)
             this.tmodifiers.elementAt(i).check();
    }

}
