/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/**
 ** We represent [C.]this. <p>
 **
 ** classPrefix holds C if present, and null otherwise.<p>
 **
 ** Note: classPrefix will hold a **TypeSig** instead of a TypeName if
 ** we have been inferred.  (The inferred field specifies whether or
 ** not we have been inferred).<p>
 **/

public class ThisExpr extends Expr {
  public Type classPrefix;


  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;


  //* Were we inferred by the disambiguation code?
  public boolean inferred = false;

    public int getStartLoc() {
        if (classPrefix!=null && classPrefix instanceof TypeName)
	    return classPrefix.getStartLoc();
	return loc;
    }

  public int getEndLoc() { return Location.inc(loc,3); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw ThisExpr whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected ThisExpr() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.classPrefix;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[ThisExpr"
        + " classPrefix = " + this.classPrefix
        + " loc = " + this.loc
        + "]";
  }

  public final int getTag() {
     return TagConstants.THISEXPR;
  }

  public final void accept(Visitor v) { v.visitThisExpr(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitThisExpr(this, o); }

  public void check() {
     super.check();
     if (this.classPrefix != null)
        this.classPrefix.check();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static ThisExpr make(Type classPrefix, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     ThisExpr result = new ThisExpr();
     result.classPrefix = classPrefix;
     result.loc = loc;
     return result;
  }
}
