/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class InterfaceDecl extends TypeDecl {

  /** Set the parent pointer of the <code>TypeDeclElems</code>s
    inside the <code>this</code>. */
  private void postMake() {
    for(int i = 0; i < elems.size(); i++)
      elems.elementAt(i).setParent(this);
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw InterfaceDecl whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected InterfaceDecl() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.pmodifiers != null) sz += this.pmodifiers.size();
     if (this.superInterfaces != null) sz += this.superInterfaces.size();
     if (this.tmodifiers != null) sz += this.tmodifiers.size();
     if (this.elems != null) sz += this.elems.size();
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

     if (index == 0) return this.id;
     else index--;

     sz = (this.superInterfaces == null ? 0 : this.superInterfaces.size());
     if (0 <= index && index < sz)
        return this.superInterfaces.elementAt(index);
     else index -= sz;

     sz = (this.tmodifiers == null ? 0 : this.tmodifiers.size());
     if (0 <= index && index < sz)
        return this.tmodifiers.elementAt(index);
     else index -= sz;

     sz = (this.elems == null ? 0 : this.elems.size());
     if (0 <= index && index < sz)
        return this.elems.elementAt(index);
     else index -= sz;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[InterfaceDecl"
        + " modifiers = " + this.modifiers
        + " pmodifiers = " + this.pmodifiers
        + " id = " + this.id
        + " superInterfaces = " + this.superInterfaces
        + " tmodifiers = " + this.tmodifiers
        + " elems = " + this.elems
        + " loc = " + this.loc
        + " locId = " + this.locId
        + " locOpenBrace = " + this.locOpenBrace
        + " locCloseBrace = " + this.locCloseBrace
        + "]";
  }

  public final int getTag() {
     return TagConstants.INTERFACEDECL;
  }

  public final void accept(Visitor v) { v.visitInterfaceDecl(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitInterfaceDecl(this, o); }

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
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ requires locId!=javafe.util.Location.NULL
  //@ requires locOpenBrace!=javafe.util.Location.NULL
  //@ requires locCloseBrace!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static InterfaceDecl make(int modifiers, ModifierPragmaVec pmodifiers, /*@non_null*/ Identifier id, /*@non_null*/ TypeNameVec superInterfaces, TypeModifierPragmaVec tmodifiers, /*@non_null*/ TypeDeclElemVec elems, int loc, int locId, int locOpenBrace, int locCloseBrace) {
     //@ set I_will_establish_invariants_afterwards = true
     InterfaceDecl result = new InterfaceDecl();
     result.modifiers = modifiers;
     result.pmodifiers = pmodifiers;
     result.id = id;
     result.superInterfaces = superInterfaces;
     result.tmodifiers = tmodifiers;
     result.elems = elems;
     result.loc = loc;
     result.locId = locId;
     result.locOpenBrace = locOpenBrace;
     result.locCloseBrace = locCloseBrace;
     result.postMake();
     return result;
  }
}
