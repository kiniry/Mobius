/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents an ExplicitConstructorInvocation. 
 *  <p> Only occurs as the first Stmt in a ConstructorDecl. 
 *  <p> Name resolution sets the decl field to the callee.
 */

public class ConstructorInvocation extends Stmt {
  /**
   ** superCall is true implies call is "super(...)",
   ** superCall is false implies call is "this(...)".
   **/
  public boolean superCall;


  /**
   ** The enclosing instance is the object expression before a super
   ** call ( <enclosingInstance>.super(...) ).  This field may be null
   ** if there is no such expression.<p>
   **
   ** Note: if the supertype in question is an inner class, then the
   ** type checker will infer a [<C>.]this expression if no expression
   ** is present and place it in this slot.  (See ThisExpr for how to
   ** distinguish inferred this expressions.)<p>
   **/
  public Expr enclosingInstance;


  //@ invariant enclosingInstance!=null && superCall ==> locDot!=Location.NULL
  public int locDot;


  //@ invariant locKeyword!=javafe.util.Location.NULL
  public int locKeyword;

  //@ invariant locOpenParen!=javafe.util.Location.NULL
  public int locOpenParen;


  public /*@non_null*/ ExprVec args;


  public ConstructorDecl decl;

  private void postCheck() {
    if (decl != null) {
      // Any invariants here...???
    }
  }

  public int getStartLoc() {
    if (enclosingInstance == null) return locKeyword;
    else return enclosingInstance.getStartLoc();
  }

  public int getEndLoc() { 
    if (args.size()<1)
      return super.getEndLoc();

    return args.elementAt(args.size()-1).getEndLoc();
  }


  //@ requires enclosingInstance!=null && superCall ==> locDot!=Location.NULL
  //
  //@ requires locKeyword!=javafe.util.Location.NULL
  //@ requires locOpenParen!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static ConstructorInvocation make(boolean superCall, Expr enclosingInstance, int locDot, int locKeyword, int locOpenParen, /*@non_null*/ ExprVec args) {
     //@ set I_will_establish_invariants_afterwards = true
     ConstructorInvocation result = new ConstructorInvocation();
     result.superCall = superCall;
     result.enclosingInstance = enclosingInstance;
     result.locDot = locDot;
     result.locKeyword = locKeyword;
     result.locOpenParen = locOpenParen;
     result.args = args;
     return result;
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw ConstructorInvocation whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected ConstructorInvocation() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.args != null) sz += this.args.size();
     return sz + 1;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.enclosingInstance;
     else index--;

     sz = (this.args == null ? 0 : this.args.size());
     if (0 <= index && index < sz)
        return this.args.elementAt(index);
     else index -= sz;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[ConstructorInvocation"
        + " superCall = " + this.superCall
        + " enclosingInstance = " + this.enclosingInstance
        + " locDot = " + this.locDot
        + " locKeyword = " + this.locKeyword
        + " locOpenParen = " + this.locOpenParen
        + " args = " + this.args
        + "]";
  }

  public final int getTag() {
     return TagConstants.CONSTRUCTORINVOCATION;
  }

  public final void accept(Visitor v) { v.visitConstructorInvocation(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitConstructorInvocation(this, o); }

  public void check() {
     super.check();
     if (this.enclosingInstance != null)
        this.enclosingInstance.check();
     for(int i = 0; i < this.args.size(); i++)
        this.args.elementAt(i).check();
     postCheck();
  }

}
