/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class TypeName extends Type {
  // We always have associated locations:
  //@ invariant syntax

  public /*@non_null*/ Name name;

  public int getStartLoc() { return name.getStartLoc(); }
  public int getEndLoc() { return name.getEndLoc(); }

  // overloaded constructor for type names that
  // do not have any type modifiers
  //@ ensures \result!=null
  static public TypeName make(/*@non_null*/ Name name) {
    return TypeName.make(null, name);
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw TypeName whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected TypeName() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.name;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[TypeName"
        + " tmodifiers = " + this.tmodifiers
        + " name = " + this.name
        + "]";
  }

  public final int getTag() {
     return TagConstants.TYPENAME;
  }

  public final void accept(Visitor v) { v.visitTypeName(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitTypeName(this, o); }

  public void check() {
     super.check();
     if (this.tmodifiers != null)
        for(int i = 0; i < this.tmodifiers.size(); i++)
           this.tmodifiers.elementAt(i).check();
     this.name.check();
  }

  //@ ensures \result!=null
  public static TypeName make(TypeModifierPragmaVec tmodifiers, /*@non_null*/ Name name) {
     //@ set I_will_establish_invariants_afterwards = true
     TypeName result = new TypeName();
     result.tmodifiers = tmodifiers;
     result.name = name;
     return result;
  }
}
