/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents a ObjectDesignator of the form "TypeName . " 
 *
 *  <p> Is created from AmbiguousVariableAccess/AmbiguousMethodInvocation
 *  by the name resolution code.  
 *  The <code>type</code> must be an instance of either <code>TypeName</code>
 *  or <code>TypeSig</code>  (found in <code>javafe.tc</code>).
 *  If <code>type</code> is a <code>TypeName</code>, then an explicit
 *  type name was given in the program text; if <code>type</code> 
 *  is a <code>TypeSig</code>, then the type was inferred.
 */

public class TypeObjectDesignator extends ObjectDesignator {
  //@ invariant type instanceof TypeName || type instanceof javafe.tc.TypeSig
  public /*@non_null*/ Type type;


  private void postCheck() {
    Assert.notNull(type);	
  }

    public int getStartLoc() {
        if (!(type instanceof javafe.tc.TypeSig))
	    return type.getStartLoc();

	return locDot;
    }

  //* Manual maker to ensure invariant on type satisfied
  //@ requires type instanceof TypeName || type instanceof javafe.tc.TypeSig
  //
  //@ requires locDot!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static TypeObjectDesignator make(int locDot, /*@non_null*/ Type type) {
     //@ set I_will_establish_invariants_afterwards = true
     TypeObjectDesignator result = new TypeObjectDesignator();
     result.locDot = locDot;
     result.type = type;
     return result;
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw TypeObjectDesignator whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected TypeObjectDesignator() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     return 1;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.type;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[TypeObjectDesignator"
        + " locDot = " + this.locDot
        + " type = " + this.type
        + "]";
  }

  public final int getTag() {
     return TagConstants.TYPEOBJECTDESIGNATOR;
  }

  public final void accept(Visitor v) { v.visitTypeObjectDesignator(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitTypeObjectDesignator(this, o); }

  public void check() {
     super.check();
     this.type.check();
     postCheck();
  }

}
