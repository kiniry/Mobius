/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class NewArrayExpr extends Expr {
  /**
   ** The type of the elements being given zero-default values, or (if
   ** an array initializer is present), the type of the array
   ** initializer elements.<p>
   **
   ** E.g., new int[4][3][] yields a type of int[] and new int[][][]{a, b}
   ** yields a type of int[][].
   **/
  //@ invariant type.syntax
  public /*@non_null*/ Type type;


  /**
   ** The array initializer, if any.  If it is present then dims will
   ** contain exactly 1 element, the inferred size of the array
   ** initializer.<p>
   **
   ** E.g., new int[][]{7, 5} will generate a dims of {INTLIT(2)}.
   **/
  //@ invariant init!=null ==> dims.count==1
  public ArrayInit init;


  /**
   ** If init is null, then holds Expr's between []'s in order.  If init
   ** is not null, then holds the inferred array size.  (cf. init).
   **
   ** E.g., new int[x+y][z][] will generate a dims of {<x+y>, <z>}.
   **/
  //@ invariant dims.count >= 1
  public /*@non_null*/ ExprVec dims;


  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;


  /**
   ** The locations of the open brackets for each Expr (possibly
   ** inferred if init!=null) in dims.<p>
   **
   ** the open bracket in front of dims[i] is located at
   ** locOpenBrackets[i].<p>
   **
   ** Note: locOpenBrackets may contain junk after the first
   ** dims.size() entries.
   **/
  //@ invariant locOpenBrackets.length >= dims.count
  /*@ invariant (\forall int i; (0<=i && i<dims.count) ==> 
			locOpenBrackets[i]!=Location.NULL) */
  public /*@non_null*/ int[] locOpenBrackets;


  public int getStartLoc() { return loc; }

  public int getEndLoc() { 
    if (init == null) {
      if (dims.size()<1)
        Assert.fail("Invariant failure: NewArrayExpr with init & dims>0");
      return dims.elementAt(dims.size()-1).getEndLoc();
    } else return init.locCloseBrace;
  }

  private void postCheck() {
    Assert.notFalse(dims.size()>=1);
    if (init!=null)
        Assert.notFalse(dims.size()==1);
  }


  //@ requires init!=null ==> dims.count==1
  //@ requires dims.count >= 1
  //@ requires locOpenBrackets.length >= dims.count
  /*@ requires (\forall int i; (0<=i && i<dims.count) ==> 
			locOpenBrackets[i]!=Location.NULL) */
  //
  //@ requires type.syntax
  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static NewArrayExpr make(/*@non_null*/ Type type, /*@non_null*/ ExprVec dims, ArrayInit init, int loc, /*@non_null*/ int[] locOpenBrackets) {
     //@ set I_will_establish_invariants_afterwards = true
     NewArrayExpr result = new NewArrayExpr();
     result.type = type;
     result.dims = dims;
     result.init = init;
     result.loc = loc;
     result.locOpenBrackets = locOpenBrackets;
     return result;
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw NewArrayExpr whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected NewArrayExpr() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.dims != null) sz += this.dims.size();
     return sz + 3;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.type;
     else index--;

     if (index == 0) return this.init;
     else index--;

     sz = (this.dims == null ? 0 : this.dims.size());
     if (0 <= index && index < sz)
        return this.dims.elementAt(index);
     else index -= sz;

     if (index == 0) return this.locOpenBrackets;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[NewArrayExpr"
        + " type = " + this.type
        + " init = " + this.init
        + " dims = " + this.dims
        + " loc = " + this.loc
        + " locOpenBrackets = " + this.locOpenBrackets
        + "]";
  }

  public final int getTag() {
     return TagConstants.NEWARRAYEXPR;
  }

  public final void accept(Visitor v) { v.visitNewArrayExpr(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitNewArrayExpr(this, o); }

  public void check() {
     super.check();
     this.type.check();
     if (this.init != null)
        this.init.check();
     for(int i = 0; i < this.dims.size(); i++)
        this.dims.elementAt(i).check();
     if (this.locOpenBrackets == null) throw new RuntimeException();
     postCheck();
  }

}
