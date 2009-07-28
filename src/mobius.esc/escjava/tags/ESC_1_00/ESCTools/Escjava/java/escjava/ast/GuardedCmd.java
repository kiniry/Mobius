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



//// Guarded commands

public abstract class GuardedCmd extends ASTNode { 

// Generated boilerplate constructors:

   /**
    ** Construct a raw GuardedCmd whose class invariant(s) have not
    ** yet been established.  It is the caller's job to
    ** initialize the returned node's fields so that any
    ** class invariants hold.
    **/

   

// Generated boilerplate methods:

   /** Return the number of children a node has. */
   public abstract int childCount();

   /** Return the first-but-ith child of a node. */
   public abstract Object childAt(int i);

   /** Return the tag of a node. */
   public abstract int getTag();

   /** Return a string representation of <code>this</code>.
   Meant for debugging use only, not for presentation. */
   public abstract String toString();

   /** Accept a visit from <code>v</code>.  This method simply
   calls the method of <code>v</code> corresponding to the
   allocated type of <code>this</code>, passing <code>this</code>
   as the argument.  See the design patterns book. */
   public abstract void accept(javafe.ast.Visitor v);

public abstract Object accept(javafe.ast.VisitorArgResult v, Object o);

   public void check() {
   }

}
