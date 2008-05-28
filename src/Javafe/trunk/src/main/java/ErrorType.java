// -*- mode: java -*-
/* Copyright 2000, 2001, Compaq Computer Corporation */

/* IF THIS IS A JAVA FILE, DO NOT EDIT IT!  

   Most Java files in this directory which are part of the Javafe AST
   are automatically generated using the astgen comment (see
   ESCTools/Javafe/astgen) from the input file 'hierarchy.h'.  If you
   wish to modify AST classes or introduce new ones, modify
   'hierarchy.j.'
 */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;
import javafe.tc.TagConstants;

// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit



/** 
 * Used to indicate the type of an illegal operation, so that error messages
 * do not unnecessarily propagate; should only be used if the error has
 * already been reported.
 */
public class ErrorType extends Type
{
  //@ invariant_redundantly isInternal;

  //@ public represents startLoc <- Location.NULL;
  public /*@ pure @*/ int getStartLoc() { return Location.NULL; }

  protected ErrorType() {}

  public static /*@ non_null */ ErrorType make() {
    ErrorType result = new ErrorType();
    return result;
  }


// Generated boilerplate constructors:

   //@ ensures this.tmodifiers == tmodifiers;
   protected ErrorType(TypeModifierPragmaVec tmodifiers) {
      super(tmodifiers);
   }

// Generated boilerplate methods:

   public final int childCount() {
      int sz = 0;
      if (this.tmodifiers != null) sz += this.tmodifiers.size();
      return sz + 0;
   }

   public final /*@ non_null */ Object childAt(int index) {
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
   }   //@ nowarn Exception;

   public final /*@non_null*/String toString() {
      return "[ErrorType"
         + " tmodifiers = " + this.tmodifiers
         + "]";
   }

   public final int getTag() {
      return TagConstants.ERRORTYPE;
   }

   public final void accept(/*@ non_null */ Visitor v) { v.visitErrorType(this); }

   public final /*@ non_null */ Object accept(/*@ non_null */ VisitorArgResult v, Object o) {return v.visitErrorType(this, o); }

   public void check() {
      super.check();
      if (this.tmodifiers != null)
         for(int i = 0; i < this.tmodifiers.size(); i++)
            this.tmodifiers.elementAt(i).check();
   }

   //@ ensures \result != null;
   public static /*@ non_null */ ErrorType make(TypeModifierPragmaVec tmodifiers) {
      ErrorType result = new ErrorType(tmodifiers);
      return result;
   }
}
