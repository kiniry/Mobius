/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit



/* ---------------------------------------------------------------------- */

/** Represents all variable declarations, including field declarations,
 *  local variables and formal arguments.
 *
 *  We 'unroll' field and variable decls, 
 *  so "<code>int x,y;</code>" becomes "<code>int x; int y;</code>".
 *  This unrolling can be detected by looking for sequential
 *  <code>VarDecl</code>s whose <code>Type</code> fields have the same
 *  starting location.
 */

public abstract class GenericVarDecl extends ASTNode {
  public int modifiers;

  public ModifierPragmaVec pmodifiers;

  public /*@non_null*/ Identifier id;

  //@ invariant type.syntax
  public /*@non_null*/ Type type;

  //@ invariant locId!=javafe.util.Location.NULL
  public int locId;

  public int getStartLoc() { return type.getStartLoc(); }
  public int getEndLoc() { return type.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw GenericVarDecl whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected GenericVarDecl() {}    //@ nowarn Invariant,NonNullInit

  public void check() {
     super.check();
     if (this.pmodifiers != null)
        for(int i = 0; i < this.pmodifiers.size(); i++)
           this.pmodifiers.elementAt(i).check();
     if (this.id == null) throw new RuntimeException();
     this.type.check();
  }

}
