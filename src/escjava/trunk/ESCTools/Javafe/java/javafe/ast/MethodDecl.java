/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


public class MethodDecl extends RoutineDecl {
  public /*@non_null*/ Identifier id;

  //@ invariant returnType.syntax
  public /*@non_null*/ Type returnType;

  //@ invariant locType!=javafe.util.Location.NULL
  public int locType;




// Generated boilerplate constructors:

  /**
   ** Construct a raw MethodDecl whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected MethodDecl() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.pmodifiers != null) sz += this.pmodifiers.size();
     if (this.tmodifiers != null) sz += this.tmodifiers.size();
     if (this.args != null) sz += this.args.size();
     if (this.raises != null) sz += this.raises.size();
     return sz + 3;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     sz = (this.pmodifiers == null ? 0 : this.pmodifiers.size());
     if (0 <= index && index < sz)
        return this.pmodifiers.elementAt(index);
     else index -= sz;

     sz = (this.tmodifiers == null ? 0 : this.tmodifiers.size());
     if (0 <= index && index < sz)
        return this.tmodifiers.elementAt(index);
     else index -= sz;

     sz = (this.args == null ? 0 : this.args.size());
     if (0 <= index && index < sz)
        return this.args.elementAt(index);
     else index -= sz;

     sz = (this.raises == null ? 0 : this.raises.size());
     if (0 <= index && index < sz)
        return this.raises.elementAt(index);
     else index -= sz;

     if (index == 0) return this.body;
     else index--;

     if (index == 0) return this.id;
     else index--;

     if (index == 0) return this.returnType;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[MethodDecl"
        + " modifiers = " + this.modifiers
        + " pmodifiers = " + this.pmodifiers
        + " tmodifiers = " + this.tmodifiers
        + " args = " + this.args
        + " raises = " + this.raises
        + " body = " + this.body
        + " locOpenBrace = " + this.locOpenBrace
        + " loc = " + this.loc
        + " locId = " + this.locId
        + " locThrowsKeyword = " + this.locThrowsKeyword
        + " id = " + this.id
        + " returnType = " + this.returnType
        + " locType = " + this.locType
        + "]";
  }

  public final int getTag() {
     return TagConstants.METHODDECL;
  }

  public final void accept(Visitor v) { v.visitMethodDecl(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitMethodDecl(this, o); }

  public void check() {
     super.check();
     if (this.pmodifiers != null)
        for(int i = 0; i < this.pmodifiers.size(); i++)
           this.pmodifiers.elementAt(i).check();
     if (this.tmodifiers != null)
        for(int i = 0; i < this.tmodifiers.size(); i++)
           this.tmodifiers.elementAt(i).check();
     for(int i = 0; i < this.args.size(); i++)
        this.args.elementAt(i).check();
     for(int i = 0; i < this.raises.size(); i++)
        this.raises.elementAt(i).check();
     if (this.body != null)
        this.body.check();
     if (this.id == null) throw new RuntimeException();
     this.returnType.check();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ requires locId!=javafe.util.Location.NULL
  //@ requires returnType.syntax
  //@ requires locType!=javafe.util.Location.NULL
  //@ requires body != null ==> locOpenBrace != Location.NULL;
  //@ ensures \result!=null
  public static MethodDecl make(int modifiers, ModifierPragmaVec pmodifiers, TypeModifierPragmaVec tmodifiers, /*@non_null*/ FormalParaDeclVec args, /*@non_null*/ TypeNameVec raises, BlockStmt body, int locOpenBrace, int loc, int locId, int locThrowsKeyword, /*@non_null*/ Identifier id, /*@non_null*/ Type returnType, int locType) {
     //@ set I_will_establish_invariants_afterwards = true
     MethodDecl result = new MethodDecl();
     result.modifiers = modifiers;
     result.pmodifiers = pmodifiers;
     result.tmodifiers = tmodifiers;
     result.args = args;
     result.raises = raises;
     result.body = body;
     result.locOpenBrace = locOpenBrace;
     result.loc = loc;
     result.locId = locId;
     result.locThrowsKeyword = locThrowsKeyword;
     result.id = id;
     result.returnType = returnType;
     result.locType = locType;
     return result;
  }
}
