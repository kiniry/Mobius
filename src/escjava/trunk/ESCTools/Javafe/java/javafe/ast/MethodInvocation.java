/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents a MethodInvocation. 
 */

public class MethodInvocation extends Expr {
  public /*@non_null*/ ObjectDesignator od;

  public /*@non_null*/ Identifier id;

  public TypeModifierPragmaVec tmodifiers;

  //@ invariant locId!=javafe.util.Location.NULL
  public int locId;

  //@ invariant locOpenParen!=javafe.util.Location.NULL
  public int locOpenParen;

  public /*@non_null*/ ExprVec args;


  //@ invariant decl==null || decl.id==id
  public MethodDecl decl;

  private void postCheck() {
    if (decl != null) {
      Assert.notFalse(id == decl.id);
      // Any other invariants here...???
    }
  }
  public int getStartLoc() {
    int loc = od.getStartLoc();
    if (loc != Location.NULL)
      return loc;
    else
      return locId;
  }
  public int getEndLoc() { 
    if (args.size()<1)
      return locId;

    return args.elementAt(args.size()-1).getEndLoc();
  }


  //@ requires locId!=javafe.util.Location.NULL
  //@ requires locOpenParen!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static MethodInvocation make(/*@non_null*/ ObjectDesignator od, /*@non_null*/ Identifier id, TypeModifierPragmaVec tmodifiers, int locId, int locOpenParen, /*@non_null*/ ExprVec args) {
     //@ set I_will_establish_invariants_afterwards = true
     MethodInvocation result = new MethodInvocation();
     result.od = od;
     result.id = id;
     result.locId = locId;
     result.locOpenParen = locOpenParen;
     result.args = args;
     result.decl = null;  // Easier than puting an ensures on constructor
     result.tmodifiers = tmodifiers;
     return result;
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw MethodInvocation whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected MethodInvocation() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.tmodifiers != null) sz += this.tmodifiers.size();
     if (this.args != null) sz += this.args.size();
     return sz + 2;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.od;
     else index--;

     if (index == 0) return this.id;
     else index--;

     sz = (this.tmodifiers == null ? 0 : this.tmodifiers.size());
     if (0 <= index && index < sz)
        return this.tmodifiers.elementAt(index);
     else index -= sz;

     sz = (this.args == null ? 0 : this.args.size());
     if (0 <= index && index < sz)
        return this.args.elementAt(index);
     else index -= sz;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[MethodInvocation"
        + " od = " + this.od
        + " id = " + this.id
        + " tmodifiers = " + this.tmodifiers
        + " locId = " + this.locId
        + " locOpenParen = " + this.locOpenParen
        + " args = " + this.args
        + "]";
  }

  public final int getTag() {
     return TagConstants.METHODINVOCATION;
  }

  public final void accept(Visitor v) { v.visitMethodInvocation(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitMethodInvocation(this, o); }

  public void check() {
     super.check();
     this.od.check();
     if (this.id == null) throw new RuntimeException();
     if (this.tmodifiers != null)
        for(int i = 0; i < this.tmodifiers.size(); i++)
           this.tmodifiers.elementAt(i).check();
     for(int i = 0; i < this.args.size(); i++)
        this.args.elementAt(i).check();
     postCheck();
  }

}
