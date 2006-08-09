/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;


import java.util.Hashtable;

import javafe.ast.*;

import javafe.ast.Expr;
import rcc.ast.Visitor;      // Work around 1.0.2 compiler bug
import rcc.ast.VisitorArgResult;      // Work around 1.0.2 compiler bug
import rcc.ast.TagConstants; // Work around 1.0.2 compiler bug
import rcc.ast.GeneratedTags;// Work around 1.0.2 compiler bug
import rcc.ast.AnOverview;   // Work around 1.0.2 compiler bug
import javafe.util.Assert;
import javafe.util.Location;


// Convention: unless otherwise noted, integer fields named "loc"g refer
// to the locaction of the first character of the syntactic unit

//# TagBase javafe.tc.TagConstants.LAST_TAG + 1
//# VisitorRoot javafe.ast.Visitor
//# VisitorARRoot javafe.ast.VisitorArgResult




public class GhostDeclPragma extends TypeDeclElemPragma {
  public /*@ non_null @*/ FieldDecl decl;

  public int loc;


  public void setParent(TypeDecl p) {
    super.setParent(p);
    if (decl!=null)
	decl.setParent(p);
  }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return decl.getEndLoc(); }


// Generated boilerplate constructors:

  //@ ensures this.decl == decl;
  //@ ensures this.loc == loc;
  protected GhostDeclPragma(/*@ non_null @*/ FieldDecl decl, int loc) {
     this.decl = decl;
     this.loc = loc;
  }

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

     if (index == 0) return this.decl;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception;

  public final /*@non_null*/String toString() {
     return "[GhostDeclPragma"
        + " decl = " + this.decl
        + " loc = " + this.loc
        + "]";
  }

  public final int getTag() {
     return TagConstants.GHOSTDECLPRAGMA;
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitGhostDeclPragma(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitGhostDeclPragma(this, o); else return null;
  }

  public void check() {
     this.decl.check();
  }

  //@ ensures \result != null;
  public static GhostDeclPragma make(/*@ non_null @*/ FieldDecl decl, int loc) {
     GhostDeclPragma result = new GhostDeclPragma(decl, loc);
     return result;
  }
}
