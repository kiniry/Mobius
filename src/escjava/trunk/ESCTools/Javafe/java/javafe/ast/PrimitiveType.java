/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/**
 ** Represents a PrimitiveType syntactic unit. 
 ** The tag should be one of the *TYPE constants defined in TagConstants
 **  (eg INTTYPE).<p>
 **
 ** WARNING: this AST node has associated locations only if syntax is
 ** true.
 **/

public class PrimitiveType extends Type {

  /*@ invariant (tag == TagConstants.BOOLEANTYPE || tag == TagConstants.INTTYPE
       || tag == TagConstants.LONGTYPE || tag == TagConstants.CHARTYPE
       || tag == TagConstants.FLOATTYPE || tag == TagConstants.DOUBLETYPE
       || tag == TagConstants.VOIDTYPE || tag == TagConstants.NULLTYPE
       || tag == TagConstants.BYTETYPE || tag == TagConstants.SHORTTYPE) */
  public int tag;



  //@ invariant syntax ==> loc!=Location.NULL
  public int loc;


  public int getStartLoc() { return loc; }


  public final int getTag() { return this.tag; }


  /**
   ** Normal maker that produces syntax, but requires a non-NULL location.
   **/
  /*@ requires (tag == TagConstants.BOOLEANTYPE || tag == TagConstants.INTTYPE
       || tag == TagConstants.LONGTYPE || tag == TagConstants.CHARTYPE
       || tag == TagConstants.FLOATTYPE || tag == TagConstants.DOUBLETYPE
       || tag == TagConstants.VOIDTYPE || tag == TagConstants.NULLTYPE
       || tag == TagConstants.BYTETYPE || tag == TagConstants.SHORTTYPE) */
  //@ ensures \result.syntax
  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static PrimitiveType make(TypeModifierPragmaVec tmodifiers,
				   int tag, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     PrimitiveType result = new PrimitiveType();
     result.tag = tag;
     result.loc = loc;
     result.tmodifiers = tmodifiers;
     //@ set result.syntax = true
     return result;
  }

  /**
   ** Special maker for producing non-syntax, which does not require a
   ** location.
   **/
  /*@ requires (tag == TagConstants.BOOLEANTYPE || tag == TagConstants.INTTYPE
       || tag == TagConstants.LONGTYPE || tag == TagConstants.CHARTYPE
       || tag == TagConstants.FLOATTYPE || tag == TagConstants.DOUBLETYPE
       || tag == TagConstants.VOIDTYPE || tag == TagConstants.NULLTYPE
       || tag == TagConstants.BYTETYPE || tag == TagConstants.SHORTTYPE) */
  //@ ensures !\result.syntax
  //@ ensures \result!=null
  public static PrimitiveType makeNonSyntax(int tag) {
     //@ set I_will_establish_invariants_afterwards = true
     PrimitiveType result = new PrimitiveType();
     result.tag = tag;
     result.loc = Location.NULL;
     result.tmodifiers = null;
     //@ set result.syntax = false
     return result;
  }


  private void postCheck() {
    boolean goodtag =
      (tag == TagConstants.BOOLEANTYPE || tag == TagConstants.INTTYPE
       || tag == TagConstants.LONGTYPE || tag == TagConstants.CHARTYPE
       || tag == TagConstants.FLOATTYPE || tag == TagConstants.DOUBLETYPE
       || tag == TagConstants.VOIDTYPE || tag == TagConstants.NULLTYPE
       || tag == TagConstants.BYTETYPE || tag == TagConstants.SHORTTYPE);
    Assert.notFalse(goodtag); 
  }
 
 
  // manual override for backwards compatibility
  /*@ requires (tag == TagConstants.BOOLEANTYPE || tag == TagConstants.INTTYPE
       || tag == TagConstants.LONGTYPE || tag == TagConstants.CHARTYPE
       || tag == TagConstants.FLOATTYPE || tag == TagConstants.DOUBLETYPE
       || tag == TagConstants.VOIDTYPE || tag == TagConstants.NULLTYPE
       || tag == TagConstants.BYTETYPE || tag == TagConstants.SHORTTYPE) */
  //@ ensures \result.syntax
  //@ ensures \result!=null
  //@ requires loc!=javafe.util.Location.NULL
  static public PrimitiveType make(int tag, int loc) {
    return PrimitiveType.make(null, tag, loc);
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw PrimitiveType whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected PrimitiveType() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.tmodifiers != null) sz += this.tmodifiers.size();
     return sz + 0;
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

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[PrimitiveType"
        + " tmodifiers = " + this.tmodifiers
        + " tag = " + this.tag
        + " loc = " + this.loc
        + "]";
  }

  public final void accept(Visitor v) { v.visitPrimitiveType(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitPrimitiveType(this, o); }

  public void check() {
     super.check();
     if (this.tmodifiers != null)
        for(int i = 0; i < this.tmodifiers.size(); i++)
           this.tmodifiers.elementAt(i).check();
     postCheck();
  }

}
