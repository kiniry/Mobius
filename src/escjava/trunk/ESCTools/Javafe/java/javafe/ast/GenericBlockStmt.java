/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Abstract class containing common parts of Block and SwitchBlock
 *  syntactic units. 
 */

public abstract class GenericBlockStmt extends Stmt {
  public /*@non_null*/ StmtVec stmts;

  //@ invariant locOpenBrace!=javafe.util.Location.NULL
  public int locOpenBrace;

  //@ invariant locCloseBrace!=javafe.util.Location.NULL
  public int locCloseBrace;


  public int getEndLoc() { return locCloseBrace; }


// Generated boilerplate constructors:

  /**
   ** Construct a raw GenericBlockStmt whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected GenericBlockStmt() {}    //@ nowarn Invariant,NonNullInit

  public void check() {
     super.check();
     for(int i = 0; i < this.stmts.size(); i++)
        this.stmts.elementAt(i).check();
  }

}
