// -*- mode: java -*-
/* Copyright 2000, 2001, Compaq Computer Corporation */

/* IF THIS IS A JAVA FILE, DO NOT EDIT IT!  

   Most Java files in this directory which are part of the Javafe AST
   are automatically generated using the astgen comment (see
   ESCTools/Javafe/astgen) from the input file 'hierarchy.h'.  If you
   wish to modify AST classes or introduce new ones, modify
   'hierarchy.j.'
 */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;
import javafe.tc.TagConstants;

// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents a ConstructorDeclaration.
 *
 *  The first Stmt in the body field should be a ConstructorInvocation. If
 *  the source code does not contain a constructor invocation, it is
 *  inserted by the parser.
 */

public class ConstructorDecl extends RoutineDecl
{

  public Identifier id() { return parent != null ? parent.id : Identifier.intern("<constructor>"); }


// Generated boilerplate constructors:

  //@ ensures this.modifiers == modifiers;
  //@ ensures this.pmodifiers == pmodifiers;
  //@ ensures this.tmodifiers == tmodifiers;
  //@ ensures this.args == args;
  //@ ensures this.raises == raises;
  //@ ensures this.body == body;
  //@ ensures this.locOpenBrace == locOpenBrace;
  //@ ensures this.loc == loc;
  //@ ensures this.locId == locId;
  //@ ensures this.locThrowsKeyword == locThrowsKeyword;
  protected ConstructorDecl(int modifiers, ModifierPragmaVec pmodifiers, TypeModifierPragmaVec tmodifiers, /*@ non_null @*/ FormalParaDeclVec args, /*@ non_null @*/ TypeNameVec raises, BlockStmt body, int locOpenBrace, int loc, int locId, int locThrowsKeyword) {
     super(modifiers, pmodifiers, tmodifiers, args, raises, body, locOpenBrace, loc, locId, locThrowsKeyword);
  }

// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.pmodifiers != null) sz += this.pmodifiers.size();
     if (this.tmodifiers != null) sz += this.tmodifiers.size();
     if (this.args != null) sz += this.args.size();
     if (this.raises != null) sz += this.raises.size();
     return sz + 1;
  }

  public final /*@ non_null */ Object childAt(int index) {
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

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception;

  public final /*@non_null*/String toString() {
     return "[ConstructorDecl"
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
        + "]";
  }

  public final int getTag() {
     return TagConstants.CONSTRUCTORDECL;
  }

  public final void accept(/*@ non_null */ Visitor v) { v.visitConstructorDecl(this); }

  public final /*@ non_null */ Object accept(/*@ non_null */ VisitorArgResult v, Object o) {return v.visitConstructorDecl(this, o); }

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
  }

  //@ requires loc != javafe.util.Location.NULL;
  //@ requires locId != javafe.util.Location.NULL;
  //@ requires body != null ==> locOpenBrace != Location.NULL;
  //@ ensures \result != null;
  public static /*@ non_null */ ConstructorDecl make(int modifiers, ModifierPragmaVec pmodifiers, TypeModifierPragmaVec tmodifiers, /*@ non_null @*/ FormalParaDeclVec args, /*@ non_null @*/ TypeNameVec raises, BlockStmt body, int locOpenBrace, int loc, int locId, int locThrowsKeyword) {
     ConstructorDecl result = new ConstructorDecl(modifiers, pmodifiers, tmodifiers, args, raises, body, locOpenBrace, loc, locId, locThrowsKeyword);
     return result;
  }
}
