/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents a Literal.
 *
 *  The tag of a LiteralExpr should be one of the *LIT (eg INTLIT)
 *  constants defined in TagConstants.  The value fields is a
 *  Character/String/Long/Double/Boolean/null, as appropriate.
 */

public class LiteralExpr extends Expr {
  /*@ invariant (
	(tag==TagConstants.BOOLEANLIT) ||
	(tag==TagConstants.INTLIT) ||
	(tag==TagConstants.LONGLIT) ||
	(tag==TagConstants.FLOATLIT) ||
	(tag==TagConstants.DOUBLELIT) ||
	(tag==TagConstants.STRINGLIT) ||
	(tag==TagConstants.NULLLIT) ||
	(tag==TagConstants.CHARLIT)
      ) */
  public int tag;


  /*@ invariant (
	((tag==TagConstants.BOOLEANLIT) ==> (value instanceof Boolean)) &&
	((tag==TagConstants.NULLLIT) ==> (value==null)) &&
	((tag==TagConstants.INTLIT) ==> (value instanceof Integer)) &&
	((tag==TagConstants.LONGLIT) ==> (value instanceof Long)) &&
	((tag==TagConstants.FLOATLIT) ==> (value instanceof Float)) &&
	((tag==TagConstants.DOUBLELIT) ==> (value instanceof Double)) &&
	((tag==TagConstants.STRINGLIT) ==> (value instanceof String)) &&
	((tag==TagConstants.CHARLIT) ==> (value instanceof Integer))
      ) */
  public Object value;



  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;

  public final int getTag() { return this.tag; }

  private void postCheck() {
    boolean goodtag =
      (tag == TagConstants.BOOLEANLIT || tag == TagConstants.INTLIT
       || tag == TagConstants.LONGLIT || tag == TagConstants.CHARLIT
       || tag == TagConstants.FLOATLIT || tag == TagConstants.DOUBLELIT
       || tag == TagConstants.STRINGLIT 
       || tag == TagConstants.NULLLIT);
    Assert.notFalse(goodtag);
    if (tag == TagConstants.BOOLEANLIT && value != null)
      Assert.notFalse(value instanceof Boolean);
    if (tag == TagConstants.INTLIT && value != null)
      Assert.notFalse(value instanceof Integer);
    if (tag == TagConstants.LONGLIT && value != null)
      Assert.notFalse(value instanceof Long);
    if (tag == TagConstants.CHARLIT && value != null)
      Assert.notFalse(value instanceof Integer);
    if (tag == TagConstants.FLOATLIT && value != null)
      Assert.notFalse(value instanceof Float);
    if (tag == TagConstants.DOUBLELIT && value != null)
      Assert.notFalse(value instanceof Double);
    if (tag == TagConstants.STRINGLIT && value != null)
      Assert.notFalse(value instanceof String);
    if (tag == TagConstants.NULLLIT) Assert.notFalse(value == null);
  }
  public int getStartLoc() { return loc; }
  public int getEndLoc() { return loc; }


  /*@ requires (
	(tag==TagConstants.BOOLEANLIT) ||
	(tag==TagConstants.INTLIT) ||
	(tag==TagConstants.LONGLIT) ||
	(tag==TagConstants.FLOATLIT) ||
	(tag==TagConstants.DOUBLELIT) ||
	(tag==TagConstants.STRINGLIT) ||
	(tag==TagConstants.NULLLIT) ||
	(tag==TagConstants.CHARLIT)
      ) */
  /*@ requires (
	((tag==TagConstants.BOOLEANLIT) ==> (value instanceof Boolean)) &&
	((tag==TagConstants.NULLLIT) ==> (value==null)) &&
	((tag==TagConstants.INTLIT) ==> (value instanceof Integer)) &&
	((tag==TagConstants.LONGLIT) ==> (value instanceof Long)) &&
	((tag==TagConstants.FLOATLIT) ==> (value instanceof Float)) &&
	((tag==TagConstants.DOUBLELIT) ==> (value instanceof Double)) &&
	((tag==TagConstants.STRINGLIT) ==> (value instanceof String)) &&
	((tag==TagConstants.CHARLIT) ==> (value instanceof Integer))
      ) */
  //
  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static LiteralExpr make(int tag, Object value, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     LiteralExpr result = new LiteralExpr();
     result.tag = tag;
     result.value = value;
     result.loc = loc;
     return result;
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw LiteralExpr whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected LiteralExpr() {}    //@ nowarn Invariant,NonNullInit


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

     if (index == 0) return this.value;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[LiteralExpr"
        + " tag = " + this.tag
        + " value = " + this.value
        + " loc = " + this.loc
        + "]";
  }

  public final void accept(Visitor v) { v.visitLiteralExpr(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitLiteralExpr(this, o); }

  public void check() {
     super.check();
     postCheck();
  }

}
