/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class NewInstanceExpr extends Expr {
  /**
   ** The enclosing instance is the object expression before a new
   ** call ( <enclosingInstance>.new T(...) ).  This field may be null
   ** if there is no such expression.<p>
   **
   ** Note: if the type in question is an inner class, then the
   ** type checker will infer a [<C>.]this expression if no expression
   ** is present and place it in this slot.  (See ThisExpr for how to
   ** distinguish inferred this expressions.)<p>
   **/
  public Expr enclosingInstance;


  //@ invariant (enclosingInstance==null) == (locDot==Location.NULL)
  public int locDot;


  public /*@non_null*/ TypeName type;

  public /*@non_null*/ ExprVec args;


  /**
   ** If the new expression includes a declaration of an inner class,
   ** then "anonDecl" will be non-null.  In this case, the
   ** "superclass" field of "ananDecl" will be null and
   ** "superinterfaces" list of "anonDecl" will be empty.  One of
   ** these fields needs to be modified during type checking depending
   ** on whether "type" is a class or an interface.
   **/
  public ClassDecl anonDecl;


  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;

  //@ invariant locOpenParen!=javafe.util.Location.NULL
  public int locOpenParen;


  public ConstructorDecl decl;

  public int getStartLoc() {
    if (enclosingInstance == null) return loc;
    else return enclosingInstance.getStartLoc();
  }

  public int getEndLoc() {
    if (decl == null) {
      if (args.size()==0) return type.getEndLoc();
      return args.elementAt(args.size()-1).getEndLoc();
    } else return decl.getEndLoc();
  }


  //@ requires (enclosingInstance==null) == (locDot==Location.NULL)
  //
  //@ requires loc!=javafe.util.Location.NULL
  //@ requires locOpenParen!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static NewInstanceExpr make(Expr enclosingInstance, int locDot, /*@non_null*/ TypeName type, /*@non_null*/ ExprVec args, ClassDecl anonDecl, int loc, int locOpenParen) {
     //@ set I_will_establish_invariants_afterwards = true
     NewInstanceExpr result = new NewInstanceExpr();
     result.enclosingInstance = enclosingInstance;
     result.locDot = locDot;
     result.type = type;
     result.args = args;
     result.anonDecl = anonDecl;
     result.loc = loc;
     result.locOpenParen = locOpenParen;
     return result;
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw NewInstanceExpr whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected NewInstanceExpr() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.args != null) sz += this.args.size();
     return sz + 3;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.enclosingInstance;
     else index--;

     if (index == 0) return this.type;
     else index--;

     sz = (this.args == null ? 0 : this.args.size());
     if (0 <= index && index < sz)
        return this.args.elementAt(index);
     else index -= sz;

     if (index == 0) return this.anonDecl;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[NewInstanceExpr"
        + " enclosingInstance = " + this.enclosingInstance
        + " locDot = " + this.locDot
        + " type = " + this.type
        + " args = " + this.args
        + " anonDecl = " + this.anonDecl
        + " loc = " + this.loc
        + " locOpenParen = " + this.locOpenParen
        + "]";
  }

  public final int getTag() {
     return TagConstants.NEWINSTANCEEXPR;
  }

  public final void accept(Visitor v) { v.visitNewInstanceExpr(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitNewInstanceExpr(this, o); }

  public void check() {
     super.check();
     if (this.enclosingInstance != null)
        this.enclosingInstance.check();
     this.type.check();
     for(int i = 0; i < this.args.size(); i++)
        this.args.elementAt(i).check();
     if (this.anonDecl != null)
        this.anonDecl.check();
  }

}
