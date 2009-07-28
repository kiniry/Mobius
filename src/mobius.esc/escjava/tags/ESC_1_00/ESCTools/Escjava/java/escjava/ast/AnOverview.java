/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.ast;


import java.util.Hashtable;

import javafe.ast.*;
import escjava.ast.Visitor;      // Work around 1.0.2 compiler bug
import escjava.ast.TagConstants; // Work around 1.0.2 compiler bug
import escjava.ast.GeneratedTags;// Work around 1.0.2 compiler bug
import escjava.ast.AnOverview;   // Work around 1.0.2 compiler bug
import javafe.util.Assert;
import javafe.util.Location;


// Convention: unless otherwise noted, integer fields named "loc"g refer
// to the locaction of the first character of the syntactic unit

//# TagBase javafe.tc.TagConstants.LAST_TAG + 1
//# VisitorRoot javafe.ast.Visitor



/**

The files in this package extend the AST classes defined in
<code>javafe.ast</code>.  The following diagram shows how the new
classes related to the old classes in the class hierarchy:

  * <PRE>
  * - ASTNode
  *    - VarInit ()
  *       - Expr ()
  *         + GCExpr
  *           + LabelExpr (Identifier label, Expr expr)
  *           + NaryExpr (int op, Expr* exprs)
  *           + QuantifiedExpr (GenericVarDecl* vars, Expr expr)
  *           + SubstExpr (GenericVarDecl var, Expr val, Expr target)
  *           + TypeExpr (Type type)
  *         + LockSetExpr ()
  *         + ResExpr ()
  *         + WildRefExpr (Expr expr)
  *         + GuardExpr (Expr expr)
  *         + DefPredLetExpr (DefPred* preds, Expr body)
  *         + DefPredApplExpr (Identifier predId, Expr* args)
  *    + GuardedCmd
  *      + SimpleCmd (int cmd) // Skip, Raise
  *      + ExprCmd (int cmd, Expr pred) // Assert, Assume
  *      + AssignCmd (VariableAccess v, Expr rhs)
  *        + GetsCmd ()
  *        + SubGetsCmd (Expr index)
  *        + SubSubGetsCmd (Expr index1, Expr index2)
  *        + RestoreFromCmd ()
  *      + VarInCmd (GenericVarDecl v*, GuardedCmd g)
  *      + DynInstCmd (String s, GuardedCmd g)
  *      + SeqCmd (GuardedCmd cmds*)
  *      + LoopCmd (Condition invariants*, DecreasesInfo decreases*, LocalVarDecl skolemConstants*, Expr predicates*, GenericVarDecl tempVars*, GuardedCmd guard, GuardedCmd body)
  *      + CmdCmdCmd (int cmd, GuardedCmd g1, GuardedCmd g2)// Try, Choose
  *      + Call (RoutineDecl rd, Expr* args, TypeDecl scope)
  *    - TypeDeclElem ()
  *       - TypeDeclElemPragma ()
  *         + ExprDeclPragma (Expr expr) // Axiom, ObjectInvariant
  *	    + GhostDeclPragma (GhostFieldDecl decl)
  *         + StillDeferredDeclPragma (Identifier var)
  *    - Stmt ()
  *       - StmtPragma ()
  *         + SimpleStmtPragma () // Unreachable
  *         + ExprStmtPragma (Expr expr) // Assume, Assert, LoopInvariant, LoopPredicate
  *         + SetStmtPragma (Expr target, Expr value) 
  *         + SkolemConstantPragma (LocalVarDecl* decl)
  *    - ModifierPragma ()
  *         + SimpleModifierPragma () // Uninitialized, Monitored, Nonnull, WritableDeferred, Helper
  *         + ExprModifierPragma (Expr expr) // DefinedIf, Writable, Requires, Ensures, AlsoEnsures, MonitoredBy, Modifies, AlsoModifies
  *         + VarExprModifierPragma (GenericVarDecl arg, Expr expr) // Exsures, AlsoExsures
  *    - LexicalPragma ()
  *      + NowarnPragma (Identifier* checks)
  *    + Spec (MethodDecl md, Expr* targets, Hashtable preVarMap, Condition* pre, Condition* post)
  *    + Condition(int label, Expr pred)
  *    + DefPred (Identifier predId, GenericVarDecl* args, Expr body)
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

   /**
    ** Construct a raw AnOverview whose class invariant(s) have not
    ** yet been established.  It is the caller's job to
    ** initialize the returned node's fields so that any
    ** class invariants hold.
    **/

   

// Generated boilerplate methods:

   /** Return the number of children a node has. */
   public abstract int childCount();

   /** Return the first-but-ith child of a node. */
   public abstract Object childAt(int i);

   /** Return the tag of a node. */
   public abstract int getTag();

   /** Return a string representation of <code>this</code>.
   Meant for debugging use only, not for presentation. */
   public abstract String toString();

   /** Accept a visit from <code>v</code>.  This method simply
   calls the method of <code>v</code> corresponding to the
   allocated type of <code>this</code>, passing <code>this</code>
   as the argument.  See the design patterns book. */
   public abstract void accept(javafe.ast.Visitor v);

public abstract Object accept(javafe.ast.VisitorArgResult v, Object o);

   public void check() {
   }

}
