/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit



public class SimpleName extends Name {
  public /*@non_null*/ Identifier id;


  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;



  //@ invariant length == 1


  /** Return a String representation of <code>this</code> in Java's
    syntax.
   */
  public String printName() {
    return id.toString();
  }

    public boolean equals(Object other) {
	if (other instanceof SimpleName)
	    return id == ((SimpleName)other).id;
	else
	    return false;
    }

  public Name prefix(int len) {
    Assert.precondition(len == 1);
    return make(id, loc);
  }

  /** Return a hash code for <code>this</code> such that two
    <code>Name</code>s that are <code>equals</code> have the same hash
    code.
   */
  public int hashCode() {
    return id.hashCode();
  }

    /**
     ** Return the first <code>len</code> identifiers in
     ** <code>this</code> in an array.  Requires that <code>len</code>
     ** be between 0 and length of <code>this</code> inclusive.
     **/
  public String[] toStrings(int len) {
    Assert.precondition(len == 0 || len == 1);
    if (len == 0) return emptyStringArray;
    String[] result = { id.toString() };
    return result;
  }

  /** Return the number of identifiers in <code>this</code>. */
  public int size() { return 1; }

  /** Return the ith identifier of <code>this</code>. */
  public Identifier identifierAt(int i) {
    if (i != 0) throw new ArrayIndexOutOfBoundsException();
    return id;
  }

  /** Return the location of the ith identifier of <code>this</code>. */
  public int locIdAt(int i) {
    if (i != 0) throw new ArrayIndexOutOfBoundsException();
    return loc;
  }

  /** Return the location of the dot after the ith identifier of
    <code>this</code>.
   */
  public int locDotAfter(int i) {
    throw new ArrayIndexOutOfBoundsException();
  }

  public int getStartLoc() { return loc; }


// Generated boilerplate constructors:

  /**
   ** Construct a raw SimpleName whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected SimpleName() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.id;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[SimpleName"
        + " id = " + this.id
        + " loc = " + this.loc
        + "]";
  }

  public final int getTag() {
     return TagConstants.SIMPLENAME;
  }

  public final void accept(Visitor v) { v.visitSimpleName(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitSimpleName(this, o); }

  public void check() {
     super.check();
     if (this.id == null) throw new RuntimeException();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static SimpleName make(/*@non_null*/ Identifier id, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     SimpleName result = new SimpleName();
     result.id = id;
     result.loc = loc;
     return result;
  }
}
