/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/* ---------------------------------------------------------------------- */

/** Represents both MethodDeclarations and ConstructorDeclarations.
 */

public abstract class RoutineDecl extends ASTNode implements TypeDeclElem {
  //@ invariant hasParent ==> parent!=null
  public TypeDecl parent;

  public boolean implicit = false;
  public int modifiers;

  public ModifierPragmaVec pmodifiers;

  public TypeModifierPragmaVec tmodifiers;

  public /*@non_null*/ FormalParaDeclVec args;

  public /*@non_null*/ TypeNameVec raises;

  public BlockStmt body;

  public int locOpenBrace;

  //@ invariant body != null ==> locOpenBrace != Location.NULL;
  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;

  //@ invariant locId!=javafe.util.Location.NULL
  public int locId;


  // The "locThrowsKeyword" field should be used only if "raises" denotes
  // a nonempty list, in which case "locThrowsKeyword" is not "Location.NULL"
  public int locThrowsKeyword;


  private void postCheck() {
    // Check invariants on modifiers...

    for(int i = 0; i < args.size(); i++)
      // Check invariants on modifiers...
      /*skip*/;
  }

  public TypeDecl getParent() { return parent; }
  public void setParent(TypeDecl p) { parent = p; }

  public int getStartLoc() { return loc; }

    public int getEndLoc() { 
	if (body==null)
	    return super.getEndLoc();

	return body.getEndLoc();
    }


// Generated boilerplate constructors:

  /**
   ** Construct a raw RoutineDecl whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected RoutineDecl() {}    //@ nowarn Invariant,NonNullInit

  public void check() {
     super.check();
     if (this.pmodifiers != null)
        for(int i = 0; i < this.pmodifiers.size(); i++)
           this.pmodifiers.elementAt(i).check();
     if (this.tmodifiers != null)
        for(int i = 0; i < this.tmodifiers.size(); i++)
           this.tmodifiers.elementAt(i).check();
     for(int i = 0; i < this.args.size(); i++)
        this.args.elementAt(i).check();
     for(int i = 0; i < this.raises.size(); i++)
        this.raises.elementAt(i).check();
     if (this.body != null)
        this.body.check();
     postCheck();
  }

}
