/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents an initializing block of code as a class member
 *
 *  We include modifiers for later extensibility to JDK 1.1, where both
 *  static and dynamic initializer blocks are allowed.
 */

public class InitBlock extends ASTNode implements TypeDeclElem {
  //@ invariant hasParent ==> parent!=null
  public TypeDecl parent;

  public int modifiers;

  public ModifierPragmaVec pmodifiers;

  public /*@non_null*/ BlockStmt block;


  public TypeDecl getParent() { return parent; }
  public void setParent(TypeDecl p) { parent = p; }
  public int getStartLoc() { return block.getStartLoc(); }
  public int getEndLoc() { return block.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw InitBlock whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected InitBlock() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.pmodifiers != null) sz += this.pmodifiers.size();
     return sz + 1;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     sz = (this.pmodifiers == null ? 0 : this.pmodifiers.size());
     if (0 <= index && index < sz)
        return this.pmodifiers.elementAt(index);
     else index -= sz;

     if (index == 0) return this.block;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[InitBlock"
        + " modifiers = " + this.modifiers
        + " pmodifiers = " + this.pmodifiers
        + " block = " + this.block
        + "]";
  }

  public final int getTag() {
     return TagConstants.INITBLOCK;
  }

  public final void accept(Visitor v) { v.visitInitBlock(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitInitBlock(this, o); }

  public void check() {
     super.check();
     if (this.pmodifiers != null)
        for(int i = 0; i < this.pmodifiers.size(); i++)
           this.pmodifiers.elementAt(i).check();
     this.block.check();
  }

  //@ ensures \result!=null
  public static InitBlock make(int modifiers, ModifierPragmaVec pmodifiers, /*@non_null*/ BlockStmt block) {
     //@ set I_will_establish_invariants_afterwards = true
     InitBlock result = new InitBlock();
     result.modifiers = modifiers;
     result.pmodifiers = pmodifiers;
     result.block = block;
     return result;
  }
}
