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


/**
	
	The files in this package extend the AST classes defined in
	<code>javafe.ast</code>.  The following diagram shows how the new
	classes related to the old classes in the class hierarchy:
	
	* <PRE>
	* - ASTNode
	*    - Stmt ()
	*       - StmtPragma ()
	*         + HoldStmtPragma (Expr* locks) 
	*    - ModifierPragma ()
	*         + RequiresPragma (Expr* locks) 
	*         + GuardedByPragma (Expr* locks)
	*         + ThreadLocalStatusPragma (boolean local) 
	*         + ReadOnlyPragma (boolean local) 
	*    - LexicalPragma ()
	*      + NowarnPragma (Identifier* checks)
	*    - TypeModifierPragma ()
	*      + ArrayGuardModifierPragma (Expr* locks)
	* </PRE>
	
	(Classes with a <code>-</code> next to them are defined in
	<code>javafe.ast</code>; classes with a <code>+</code> are defined in
	this package.
	
	(P.S. Ignore the stuff that appears below; the only purpose of this class
	is to contain the above overview.)
	
	@see javafe.ast.AnOverview
	
	*/

public abstract class AnOverview extends ASTNode {


// Generated boilerplate constructors:

   protected AnOverview() {
   }
   

// Generated boilerplate methods:

   /** Return the number of children a node has. */
   //@ ensures \result >= 0;
   public abstract int childCount();

   /** Return the first-but-ith child of a node. */
   //@ requires 0 <= i;
   public abstract Object childAt(int i);

   /** Return the tag of a node. */
   public abstract int getTag();

   /** Return a string representation of <code>this</code>.
   Meant for debugging use only, not for presentation. */
   public abstract /*@non_null*/ String toString();

   /** Accept a visit from <code>v</code>.  This method simply
   calls the method of <code>v</code> corresponding to the
   allocated type of <code>this</code>, passing <code>this</code>
   as the argument.  See the design patterns book. */
   //@ requires v != null;
   public abstract void accept(javafe.ast.Visitor v);

   //@ requires v != null;
//@ ensures \result != null;
public abstract Object accept(javafe.ast.VisitorArgResult v, Object o);

   public void check() {
   }

}
