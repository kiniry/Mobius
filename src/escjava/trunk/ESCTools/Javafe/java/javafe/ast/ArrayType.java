/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class ArrayType extends Type {
  // We have associated locations iff elemType does:
  //@ invariant elemType.syntax == syntax

  public /*@non_null*/ Type elemType;

  //@ invariant locOpenBracket!=javafe.util.Location.NULL
  public int locOpenBracket;

  public int getStartLoc() { return elemType.getStartLoc(); }
  public int getEndLoc() {
    return Location.inc(locOpenBracket,1);
  }

  // Generate this manually to add condition about syntax:
  //@ ensures elemType.syntax ==> \result.syntax
  //
  //@ requires locOpenBracket!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static ArrayType make(/*@non_null*/ Type elemType,
                               int locOpenBracket) {
     //@ set I_will_establish_invariants_afterwards = true
     ArrayType result = new ArrayType();
     // Can't fix this since elemType is *not* injective:
     //@ assume (\forall ArrayType a; a.elemType != result)
     result.elemType = elemType;
     result.locOpenBracket = locOpenBracket;
     //@ set result.syntax = elemType.syntax
     return result;
  }

  //@ ensures elemType.syntax ==> \result.syntax
  //
  //@ requires locOpenBracket!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static ArrayType make(TypeModifierPragmaVec tmodifiers,
			       /*@non_null*/ Type elemType,
                               int locOpenBracket) {
	ArrayType at = ArrayType.make(elemType, locOpenBracket);
	at.tmodifiers = tmodifiers;
	return at;
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw ArrayType whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected ArrayType() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.tmodifiers != null) sz += this.tmodifiers.size();
     return sz + 1;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     sz = (this.tmodifiers == null ? 0 : this.tmodifiers.size());
     if (0 <= index && index < sz)
        return this.tmodifiers.elementAt(index);
     else index -= sz;

     if (index == 0) return this.elemType;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[ArrayType"
        + " tmodifiers = " + this.tmodifiers
        + " elemType = " + this.elemType
        + " locOpenBracket = " + this.locOpenBracket
        + "]";
  }

  public final int getTag() {
     return TagConstants.ARRAYTYPE;
  }

  public final void accept(Visitor v) { v.visitArrayType(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitArrayType(this, o); }

  public void check() {
     super.check();
     if (this.tmodifiers != null)
        for(int i = 0; i < this.tmodifiers.size(); i++)
           this.tmodifiers.elementAt(i).check();
     this.elemType.check();
  }

}
