/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/* ---------------------------------------------------------------------- */

/** Represents a TypeDeclaration.
 *  Common fields of ClassDeclarations and InterfaceDeclarations are here.
 */

public abstract class TypeDecl extends ASTNode implements TypeDeclElem {
  /**
   ** if specOnly is true, then this is only a spec.  In particular,
   ** methods do not have non-empty bodies, no initializers are present
   ** for fields, and no static bodies are present.
   **/
  public boolean specOnly = false;

  public int modifiers;

  public ModifierPragmaVec pmodifiers;

  public /*@non_null*/ Identifier id;

  public /*@non_null*/ TypeNameVec superInterfaces;


  public TypeModifierPragmaVec tmodifiers;


  //* "invariant" elems.<each element>.hasParent is true
  public /*@non_null*/ TypeDeclElemVec elems;


  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;

  //@ invariant locId!=javafe.util.Location.NULL
  public int locId;

  //@ invariant locOpenBrace!=javafe.util.Location.NULL
  public int locOpenBrace;

  //@ invariant locCloseBrace!=javafe.util.Location.NULL
  public int locCloseBrace;



  //@ invariant hasParent ==> parent!=null
  public TypeDecl parent;

  public TypeDecl getParent() { return parent; }
  public void setParent(TypeDecl p) { parent = p; }


  private void postCheck() {
    // check invariants on modifiers...
    for(int i = 0; i < elems.size(); i++) {
      Assert.notFalse(elems.elementAt(i).getParent() == this);	//@ nowarn Pre
      for(int j = i+1; j < elems.size(); j++)
	Assert.notFalse(elems.elementAt(i) != elems.elementAt(j));  //@ nowarn Pre
    }
  }

    /**
     ** Return true iff this TypeDecl was created from a .class
     ** file. <p>
     **
     ** Precondition: we have already been associated with a TypeSig.<p>
     **/
    public boolean isBinary() {
        javafe.tc.TypeSig sig = javafe.tc.TypeSig.getSig(this);
	CompilationUnit cu = sig.getCompilationUnit();

	return cu.isBinary();
    }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return locCloseBrace; }


// Generated boilerplate constructors:

  /**
   ** Construct a raw TypeDecl whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected TypeDecl() {}    //@ nowarn Invariant,NonNullInit

  public void check() {
     super.check();
     if (this.pmodifiers != null)
        for(int i = 0; i < this.pmodifiers.size(); i++)
           this.pmodifiers.elementAt(i).check();
     if (this.id == null) throw new RuntimeException();
     for(int i = 0; i < this.superInterfaces.size(); i++)
        this.superInterfaces.elementAt(i).check();
     if (this.tmodifiers != null)
        for(int i = 0; i < this.tmodifiers.size(); i++)
           this.tmodifiers.elementAt(i).check();
     if (this.elems == null) throw new RuntimeException();
     postCheck();
  }

}
