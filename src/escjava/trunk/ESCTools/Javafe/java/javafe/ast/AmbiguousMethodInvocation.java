/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents a Name occuring before an argument list.
 *  Is created by the parser, and then resolved to either an
 *  InstanceMethodAccess or ClassMethodAccess by the name resolution code.
 *
 *  <p> Thus for the method call "x.y()", the "x.y" part is initially 
 *  represented as a MethodName, 
 *  and then resolved to a InstanceMethodAccess if "x" is a variable, 
 *  or resolved to a ClassMethodAccess if "x" is a type name.
 */

public class AmbiguousMethodInvocation extends Expr {
  public /*@non_null*/ Name name;

  public TypeModifierPragmaVec tmodifiers;

  //@ invariant locOpenParen!=javafe.util.Location.NULL
  public int locOpenParen;

  public /*@non_null*/ ExprVec args;

  public int getStartLoc() { return name.getStartLoc(); }
  public int getEndLoc() { 
    if (args.size()<1)
      return name.getEndLoc();

    return args.elementAt(args.size()-1).getEndLoc();
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw AmbiguousMethodInvocation whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected AmbiguousMethodInvocation() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.tmodifiers != null) sz += this.tmodifiers.size();
     if (this.args != null) sz += this.args.size();
     return sz + 1;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.name;
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
     return "[AmbiguousMethodInvocation"
        + " name = " + this.name
        + " tmodifiers = " + this.tmodifiers
        + " locOpenParen = " + this.locOpenParen
        + " args = " + this.args
        + "]";
  }

  public final int getTag() {
     return TagConstants.AMBIGUOUSMETHODINVOCATION;
  }

  public final void accept(Visitor v) { v.visitAmbiguousMethodInvocation(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitAmbiguousMethodInvocation(this, o); }

  public void check() {
     super.check();
     this.name.check();
     if (this.tmodifiers != null)
        for(int i = 0; i < this.tmodifiers.size(); i++)
           this.tmodifiers.elementAt(i).check();
     for(int i = 0; i < this.args.size(); i++)
        this.args.elementAt(i).check();
  }

  //@ requires locOpenParen!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static AmbiguousMethodInvocation make(/*@non_null*/ Name name, TypeModifierPragmaVec tmodifiers, int locOpenParen, /*@non_null*/ ExprVec args) {
     //@ set I_will_establish_invariants_afterwards = true
     AmbiguousMethodInvocation result = new AmbiguousMethodInvocation();
     result.name = name;
     result.tmodifiers = tmodifiers;
     result.locOpenParen = locOpenParen;
     result.args = args;
     return result;
  }
}
