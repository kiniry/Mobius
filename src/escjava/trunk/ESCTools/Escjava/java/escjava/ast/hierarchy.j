/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.ast;

import java.util.Hashtable;
import java.util.Set;
import java.util.ArrayList;

import javafe.ast.*;
import javafe.util.Assert;
import javafe.util.Location;
import escjava.ParsedRoutineSpecs;

// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit

//# TagBase javafe.tc.TagConstants.LAST_TAG + 1
//# VisitorRoot javafe.ast.Visitor

//# EndHeader

/**
 * The files in this package extend the AST classes defined in
 * <code>javafe.ast</code>.  The following diagram shows how the new
 * classes related to the old classes in the class hierarchy:
 *
 * <pre>
 * - ASTNode
 *    - VarInit ()
 *       - Expr ()
 *         + GCExpr
 *           + LabelExpr (Identifier label, Expr expr)
 *           + NaryExpr (int op, Identifier methodName, Expr* exprs)
 *           + QuantifiedExpr (GenericVarDecl* vars, Expr expr)
 *           + GeneralizedQuantifiedExpr (GenericVarDecl* vars, Expr expr)
 *                // Sum, Product, Max, Min
 *           + NumericalQuantifiedExpr (GenericVarDecl* vars, Expr expr)
 *                // NumOf
 *           + SubstExpr (GenericVarDecl var, Expr val, Expr target)
 *           + TypeExpr (Type type)
 *         + EverythingExpr ()
 *         + LockSetExpr ()
 *         + NotSpecifiedExpr ()
 *         + NothingExpr ()
 *         + StoreRefExpr(Expr,Expr)
 *         + NotModifiedExpr(Expr)
 *         + ResExpr ()
 *	   + SetCompExpr(Type type, Type typeBound, Identifier id, Expr e)
 *         + WildRefExpr (Expr expr)
 *         + GuardExpr (Expr expr)
 *         + DefPredLetExpr (DefPred* preds, Expr body)
 *         + DefPredApplExpr (Identifier predId, Expr* args)
 *	   + ArrayRangeRefExpr(Expr, Expr, Expr)
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
 *	   + GhostDeclPragma (GhostFieldDecl decl)
 *	   + ModelDeclPragma (ModelFieldDecl decl)
 *         + ModelTypePragma (TypeDecl decl)
 *         + NamedExprDeclPragma (Expr target, Expr expr)
 *         + IdExprDeclPragma (Id target, Expr expr)
 *         + ModelMethodDeclPragma (MethodDecl decl)
 *         + ModelConstructorPragma (ConstructorDecl decl)
 *         + StillDeferredDeclPragma (Identifier var)
 *         + DependsPragma (Expr* exprs) // Depends clause
 *    - Stmt ()
 *       - StmtPragma ()
 *         + SimpleStmtPragma () // Unreachable
 *         + ExprStmtPragma (Expr expr, Expr label) 
 *             // Assume, Assert, LoopInvariant, LoopPredicate
 *         + SetStmtPragma (Expr target, Expr value) 
 *         + SkolemConstantPragma (LocalVarDecl* decl)
 *    - ModifierPragma ()
 *         + SimpleModifierPragma () 
 *                   // Uninitialized, Monitored, NonNull, WritableDeferred, Helper
 *	   + NestedModifierPragma (ArrayList list)
 *         + ExprModifierPragma (Expr expr) 
 *                   // DefinedIf, Writable, Requires, Pre, Ensures, Post, AlsoEnsures, 
 *                   // MonitoredBy, Constraint, InvariantFor, Space, 
 *                   // \Duration, \WorkingSpace
 *         + IdentifierModifierPramga (Identifier id)
 *                   // IsInitialized
 *         + ReachModifierPragma (Expr expr, Identifier id, StoreRefExpr)
 *                   // \Reach
 *	   + CondExprModifierPragma (Expr expr, Expr cond) 
 *                   // Modifiers, AlsoModifiers, Assignable, Modifiable
 *         + MapsExprModifierPragma (Identifier id, Expr mapsexpr, Expr expr) 
 *		     // maps
 *         + VarExprModifierPragma (GenericVarDecl arg, Expr expr)
 *                   // Exsures, AlsoExsures, Signals, AlsoSignals
 *         + ModelProgramModifierPragma()
 *	   + VarDeclModifierPragma (LocalVarDecl decl)
 *    - LexicalPragma ()
 *      + NowarnPragma (Identifier* checks)
 *      + ImportPragma (ImportDecl decl)
 *      + RefinePragma (String filename)
 *    + Spec (MethodDecl md, Expr* targets, Hashtable preVarMap, 
 *            Condition* pre, Condition* post)
 *    + Condition(int label, Expr pred)
 *    + DefPred (Identifier predId, GenericVarDecl* args, Expr body)
 * </pre>
 * 
 * <p> (Classes with a <code>-</code> next to them are defined in
 * <code>javafe.ast</code>; classes with a <code>+</code> are defined
 * in this package. </p>
 *
 * <p> (P.S. Ignore the stuff that appears below; the only purpose of
 * this class is to contain the above overview.) </p>
 *
 */

public abstract class AnOverview extends ASTNode
{ }

//// Spec expressions

public abstract class GCExpr extends Expr
{
  //# int sloc
  //# int eloc

  public int getStartLoc() { return sloc; }
  public int getEndLoc() { return eloc; }
}

public class NaryExpr extends GCExpr
{
  //# int op
  //# Identifier methodName
  //# Expr* exprs

  //# ManualTag
  public final int getTag() { return op; }

  //# PostCheckCall
  private void postCheck() {
    boolean goodtag = 
      (op == TagConstants.CLASSLITERALFUNC
       || op == TagConstants.DTTFSA
       || op == TagConstants.ELEMTYPE
       || op == TagConstants.WACK_NOWARN
       || op == TagConstants.NOWARN_OP
       || op == TagConstants.WARN
       || op == TagConstants.WARN_OP
       || op == TagConstants.WACK_DURATION
       || op == TagConstants.WACK_WORKING_SPACE
       || op == TagConstants.FRESH
       || op == TagConstants.MAX
       || op == TagConstants.TYPEOF
       || (TagConstants.FIRSTFUNCTIONTAG <= op 
	   && op <= TagConstants.LASTFUNCTIONTAG));
    Assert.notFalse(goodtag);
  }

}

public class QuantifiedExpr extends GCExpr
{
  //# int quantifier
  //# GenericVarDecl* vars
  //# Expr expr
  //# Expr* nopats NullOK
  //# Expr* pats NullOK

  //# ManualTag
  public final int getTag() { return quantifier; }

  //# PostCheckCall
  private void postCheck() {
    boolean goodtag =
      (quantifier == TagConstants.FORALL
       || quantifier == TagConstants.EXISTS);
    Assert.notFalse(goodtag);
  }

}

public class GeneralizedQuantifiedExpr extends GCExpr
{
  // Sum, Product, Max, Min
  //# int quantifier
  //# GenericVarDecl* vars
  //# Expr expr
  //# Expr rangeExpr
  //# Expr* nopats NullOK

  //# ManualTag
  public final int getTag() { return quantifier; }

  //# PostCheckCall
  private void postCheck() {
    boolean goodtag =
      (quantifier == TagConstants.MIN
       || quantifier == TagConstants.PRODUCT
       || quantifier == TagConstants.MAXQUANT
       || quantifier == TagConstants.SUM);
    Assert.notFalse(goodtag);
  }
}

public class NumericalQuantifiedExpr extends GCExpr
{
  // NumOf
  //# int quantifier
  //# GenericVarDecl* vars
  //# Expr expr
  //# Expr* nopats NullOK

  //# ManualTag
  public final int getTag() { return quantifier; }

  //# PostCheckCall
  private void postCheck() {
    boolean goodtag =
      (quantifier == TagConstants.NUM_OF);
    Assert.notFalse(goodtag);
  }
}

public class SubstExpr extends GCExpr
{
  //# GenericVarDecl var
  //# Expr val
  //# Expr target

}

/** 
 * @note If <code>loc</code> is <code>Location.NULL</code>, then this
 * node is <em>not</em> due to a source-level "type" construct in an
 * annotation expression but rather was created during translations.
 */

public class TypeExpr extends GCExpr
{
  //# Type type

}

public class LabelExpr extends GCExpr
{
  //# boolean positive
  //# Identifier label
  //# Expr expr
}

public class WildRefExpr extends Expr
{
  //# Expr var
  //# ObjectDesignator od

  public int getStartLoc() { return od != null ? od.getStartLoc() : var.getStartLoc(); }
  public int getEndLoc() { return od != null ? od.getEndLoc() : var.getEndLoc(); }
}

public class GuardExpr extends Expr
{
  //# Expr expr
  //# int locPragmaDecl

  public int getStartLoc() { return expr.getStartLoc(); }
  public int getEndLoc() { return expr.getEndLoc(); }
}

public class ResExpr extends Expr
{
  //# int loc

  public int getStartLoc() { return loc; }
}

public class SetCompExpr extends Expr
{
  //# Type type
  //# FormalParaDecl fp
  //# Expr expr

  public int getStartLoc() { return fp.getStartLoc(); }
}
public class LockSetExpr extends Expr
{
  //# int loc

  public int getStartLoc() { return loc; }
}

public class EverythingExpr extends Expr
{
  //# int loc

  public int getStartLoc() { return loc; }
}

public class NothingExpr extends Expr
{
  //# int loc

  public int getStartLoc() { return loc; }
}

public class NotSpecifiedExpr extends Expr
{
  //# int loc

  public int getStartLoc() { return loc; }
}

public class NotModifiedExpr extends Expr
{
  //# int loc
  //# Expr expr
 
  public int getStartLoc() { return loc; }
}

public class ArrayRangeRefExpr extends Expr
{
  //# int locOpenBracket
  //# Expr array
  //# Expr lowIndex	NullOK
  //# Expr highIndex	NullOK

  public int getStartLoc() { return locOpenBracket; }
}

public class DefPredLetExpr extends Expr
{
    //# DefPred* preds
    //# Expr body

    public int getStartLoc() { return body.getStartLoc(); }
}

public class DefPredApplExpr extends Expr
{
    //# Identifier predId
    //# Expr* args

    public int getStartLoc() { return Location.NULL; }
}

//// Guarded commands

public abstract class GuardedCmd extends ASTNode
{ }

public class SimpleCmd extends GuardedCmd
{
  // Denotes skip or raise
  //# int cmd
  //# int loc

  //# ManualTag
  public final int getTag() { return cmd; }

  //# PostCheckCall
  private void postCheck() {
    boolean goodtag =
      (cmd == TagConstants.SKIPCMD || cmd == TagConstants.RAISECMD);
    Assert.notFalse(goodtag);
  }

  public int getStartLoc() { return loc; }
}

public class ExprCmd extends GuardedCmd
{
  // Denotes assert or assume
  //# int cmd
  //# Expr pred
  //# int loc

  //# ManualTag
  public final int getTag() { return cmd; }

  //# PostCheckCall
  private void postCheck() {
    boolean goodtag =
      (cmd == TagConstants.ASSERTCMD || cmd == TagConstants.ASSUMECMD);
    Assert.notFalse(goodtag);
  }

  public int getStartLoc() { return loc; }
}

public abstract class AssignCmd extends GuardedCmd
{
  // denotes a subtype-dependent assignment to v
  // rhs must be pure
  //# VariableAccess v
  //# Expr rhs

  public int getStartLoc() { return v.getStartLoc(); }
  public int getEndLoc() { return rhs.getEndLoc(); }
}

public class GetsCmd extends AssignCmd
{
  // denotes v := rhs
}

public class SubGetsCmd extends AssignCmd
{
  // denotes v[index] := rhs
  //# Expr index
}

public class SubSubGetsCmd extends AssignCmd
{
  // denotes v[index][index] := rhs.  I expect that v will be "elems".
  //# Expr index1
  //# Expr index2
}

public class RestoreFromCmd extends AssignCmd
{
  // denotes RESTORE v FROM rhs
  // which has the same effect as v := rhs
  // but does not count "v" as a target
}

public class VarInCmd extends GuardedCmd
{
  // denotes VAR v IN g END.
  //# GenericVarDecl* v
  //# GuardedCmd g

  public int getStartLoc() { return g.getStartLoc(); }
  public int getEndLoc() { return g.getEndLoc(); }
}

public class DynInstCmd extends GuardedCmd
{
  // denotes DynamicInstanceCommand s IN g END.
  //# String s NoCheck
  //# GuardedCmd g

  public int getStartLoc() { return g.getStartLoc(); }
  public int getEndLoc() { return g.getEndLoc(); }
}

public class SeqCmd extends GuardedCmd
{
  // denotes g1 ; g2 ; ... ; gn
  //# GuardedCmd* cmds

  //# PostCheckCall
  private void postCheck() {
    Assert.notFalse(1 < cmds.size());
  }

  public int getStartLoc() { return cmds.elementAt(0).getStartLoc(); }
  public int getEndLoc() { return cmds.elementAt(cmds.size()-1).getEndLoc(); }
}

public class LoopCmd extends GuardedCmd
{
  //# int locStart
  //# int locEnd
  //# int locHotspot
  //# Hashtable oldmap NoCheck
  //# Condition* invariants
  //# DecreasesInfo* decreases
  //# LocalVarDecl* skolemConstants
  //# Expr* predicates
  //# GenericVarDecl* tempVars
  //# GuardedCmd guard
  //# GuardedCmd body

  public GuardedCmd desugared;
  
  public int getStartLoc() { return locStart; }
  public int getEndLoc() { return locEnd; }
}
 

public class CmdCmdCmd extends GuardedCmd
{
  // denotes g1 ! g2  or  g1 [] g2
  //# int cmd
  //# GuardedCmd g1
  //# GuardedCmd g2

  //# ManualTag
  public final int getTag() { return cmd; }

  //# PostCheckCall
  private void postCheck() {
    boolean goodtag =
      (cmd == TagConstants.TRYCMD || cmd == TagConstants.CHOOSECMD);
    Assert.notFalse(goodtag);
  }

  public int getStartLoc() { return g1.getStartLoc(); }
  public int getEndLoc() { return g2.getEndLoc(); }
}

public class Call extends GuardedCmd
{
  //# Expr* args
  //# int scall
  //# int ecall

  //# boolean inlined

  // This is a backedge, so it can't be a child:
  //@ invariant rd != null
  public RoutineDecl rd;

  public Spec spec;
  public GuardedCmd desugared;

  public int getStartLoc() { return scall; }
  public int getEndLoc() { return ecall; }
}

//// Pragmas

public class ExprDeclPragma extends TypeDeclElemPragma
{
  //# int tag
  //# Expr expr
  //# int loc

  //# ManualTag
  public final int getTag() { return tag; }

  //# PostCheckCall
  private void postCheck() {
    boolean goodtag =
      (tag == TagConstants.AXIOM || 
       tag == TagConstants.INVARIANT );
    Assert.notFalse(goodtag);
  }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return expr.getEndLoc(); }
  public boolean isRedundant() { return redundant; }
  public void setRedundant(boolean v) { redundant = v; }
}

public class IdExprDeclPragma extends TypeDeclElemPragma
{
  //# int tag
  //# Identifier id      NoCheck
  //# Expr expr
  //# int loc
  //# int locId

  //# ManualTag
  public final int getTag() { return tag; }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return expr.getEndLoc(); }
}

public class NamedExprDeclPragma extends TypeDeclElemPragma 
{
  //# int tag
  //# Expr expr
  //# Expr target
  //# int loc

  //# ManualTag
  public final int getTag() { return tag; }

  //# PostCheckCall
  private void postCheck() {
    boolean goodtag =
      ( tag == TagConstants.REPRESENTS);
    Assert.notFalse(goodtag);
  }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return expr.getEndLoc(); }
  public boolean isRedundant() { return redundant; }
  public void setRedundant(boolean v) { redundant = v; }
}

public class ModelDeclPragma extends TypeDeclElemPragma
{
  //# FieldDecl decl
  //# int loc

  public void setParent(TypeDecl p) {
    super.setParent(p);
    if (decl != null)
	decl.setParent(p);
  }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return decl.getEndLoc(); }
  public void decorate(ModifierPragmaVec modifierPragmas) {
    if (decl.pmodifiers == null) {
	decl.pmodifiers = modifierPragmas;
    } else if (modifierPragmas != null) {
	// FIXME - should be prepen???
	decl.pmodifiers.append(modifierPragmas); 
    }
  }
}

public class DependsPragma extends TypeDeclElemPragma
{
  //# int tag
  //# Expr target
  //# Expr* exprs
  //# int loc

  //# ManualTag
  public final int getTag() { return tag; }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return exprs.elementAt(exprs.size()-1).getEndLoc(); }
}

public class ModelConstructorDeclPragma extends TypeDeclElemPragma
{
  //# ConstructorDecl decl
  //# int loc
  //# SimpleName id

  public void setParent(TypeDecl p) {
    super.setParent(p);
    if (decl != null) 
	decl.setParent(p);
  }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return decl.getEndLoc(); }
  public void decorate(ModifierPragmaVec modifierPragmas) {
    if (decl.pmodifiers == null) {
	decl.pmodifiers = modifierPragmas;
    } else if (modifierPragmas != null) {
	// FIXME - should be prepen???
	decl.pmodifiers.append(modifierPragmas); 
    }
  }
}

public class ModelTypePragma extends TypeDeclElemPragma
{
  //# TypeDecl decl
  //# int loc

  public void setParent(TypeDecl p) {
    super.setParent(p);
    if (decl != null) 
	decl.setParent(p);
  }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return decl.getEndLoc(); }
  public void decorate(ModifierPragmaVec modifierPragmas) {
    if (decl.pmodifiers == null) {
	decl.pmodifiers = modifierPragmas;
	// FIXME - should be prepen???
    } else if (modifierPragmas != null) {
	decl.pmodifiers.append(modifierPragmas); 
    }
  }
}

public class ModelMethodDeclPragma extends TypeDeclElemPragma
{
  //# MethodDecl decl
  //# int loc

  public void setParent(TypeDecl p) {
    super.setParent(p);
    if (decl != null) 
	decl.setParent(p);
  }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return decl.getEndLoc(); }
  public void decorate(ModifierPragmaVec modifierPragmas) {
    if (decl.pmodifiers == null) {
	decl.pmodifiers = modifierPragmas;
    } else if (modifierPragmas != null) {
	// FIXME - should be prepen???
	decl.pmodifiers.append(modifierPragmas); 
    }
  }
}
public class GhostDeclPragma extends TypeDeclElemPragma
{
  //# FieldDecl decl
  //# int loc

  public void setParent(TypeDecl p) {
    super.setParent(p);
    if (decl != null)
	decl.setParent(p);
  }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return decl.getEndLoc(); }
  public void decorate(ModifierPragmaVec modifierPragmas) {
    if (decl.pmodifiers == null) {
	decl.pmodifiers = modifierPragmas;
    } else if (modifierPragmas != null) {
	// FIXME - should be prepen???
	decl.pmodifiers.append(modifierPragmas); 
    }
  }
}

public class StillDeferredDeclPragma extends TypeDeclElemPragma
{
  //# Identifier var
  //# int loc
  //# int locId

  public int getStartLoc() { return loc; }
}

public class SimpleStmtPragma extends StmtPragma
{
  //# int tag
  //# int loc

  //# ManualTag
  public final int getTag() { return tag; }

  //# PostCheckCall
  private void postCheck() {
    boolean goodtag = (tag == TagConstants.UNREACHABLE);
    Assert.notFalse(goodtag);
  }

  public int getStartLoc() { return loc; }
}

public class IdentifierModifierPragma extends ModifierPragma
{
  //# int tag
  //# Identifier id
  //# int loc

  //# PostCheckCall
  private void postCheck() {
    boolean goodtag =
      (tag == TagConstants.IS_INITIALIZED);
    Assert.notFalse(goodtag);
  }

  public int getStartLoc() { return loc; }
}

public class ExprStmtPragma extends StmtPragma
{
  //# int tag
  //# Expr expr
  //# Expr label NullOK
  //# int loc

  //# ManualTag
  public final int getTag() { return tag; }

  //# PostCheckCall
  private void postCheck() {
    boolean goodtag = (tag == TagConstants.ASSERT || 
                       tag == TagConstants.ASSUME || 
                       tag == TagConstants.DECREASES ||
                       tag == TagConstants.DECREASING ||
                       tag == TagConstants.MAINTAINING || 
                       tag == TagConstants.LOOP_INVARIANT || 
                       tag == TagConstants.LOOP_PREDICATE);
    Assert.notFalse(goodtag);
  }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return expr.getEndLoc(); }
}

public class SetStmtPragma extends StmtPragma
{
  // set 'target' = 'value':

  //# Expr target
  //# int locOp
  //# Expr value
  //# int loc

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return value.getEndLoc(); }
}

public class SkolemConstantPragma extends StmtPragma
{
  //# LocalVarDecl* decls
  //# int sloc
  //# int eloc
  public int getStartLoc() { return sloc; }
  public int getEndLoc() { return eloc; }
}

public class ModelProgamModifierPragma extends ModifierPragma
{
  //# int tag
  //# int loc

  //# ManualTag
  public final int getTag() { return tag; }

  public int getStartLoc() { return loc; }
}

public class NestedModifierPragma extends ModifierPragma
{
	// This is a list of ModifierPragmaVec
  //# ArrayList list   NoCheck

  //# ManualTag
  public final int getTag() { return TagConstants.NESTEDMODIFIERPRAGMA; }

	// FIXME - need more robust settingn of this
  public int getStartLoc() { return ((ModifierPragmaVec)list.get(0)).elementAt(0).getStartLoc(); }
}

public class ParsedSpecs extends ModifierPragma
{
  //# RoutineDecl decl         NoCheck
  //# ParsedRoutineSpecs specs NoCheck

  //# ManualTag
  public final int getTag() { return TagConstants.PARSEDSPECS; }

  public int getStartLoc() { return decl.locId; }
}

public class SimpleModifierPragma extends ModifierPragma
{
  //# int tag
  //# int loc

  //# ManualTag
  public final int getTag() { return tag; }

  //# PostCheckCall
  private void postCheck() {
    boolean goodtag =
      (tag == TagConstants.UNINITIALIZED
       || tag == TagConstants.MONITORED
       || tag == TagConstants.NON_NULL
       || tag == TagConstants.SPEC_PUBLIC
       || tag == TagConstants.WRITABLE_DEFERRED
       || tag == TagConstants.HELPER);
    Assert.notFalse(goodtag);
  }

  public int getStartLoc() { return loc; }
}

public class ExprModifierPragma extends ModifierPragma
{
    // Extended to support JML

    //# int tag
    //# Expr expr
    //# int loc
    public int errorTag = 0;

    //# ManualTag
    public final int getTag() { return tag; }

    //# PostCheckCall
    private void postCheck() {
        boolean goodtag = (tag == TagConstants.READABLE_IF 
                           || tag == TagConstants.WRITABLE_IF
                           || tag == TagConstants.REQUIRES 
                           || tag == TagConstants.ALSO_REQUIRES
                           || tag == TagConstants.ENSURES 
                           || tag == TagConstants.ALSO_ENSURES
                           || tag == TagConstants.MONITORED_BY 
                           || tag == TagConstants.WACK_DURATION
                           || tag == TagConstants.WACK_WORKING_SPACE);
        boolean isJMLExprModifier = isJMLExprModifier();
        Assert.notFalse(goodtag || isJMLExprModifier);
    }

    private boolean isJMLExprModifier() {
        return tag == TagConstants.ALSO 
            || tag == TagConstants.PRECONDITION
            || tag == TagConstants.POSTCONDITION;
    }

    public int getStartLoc() { return loc; }
    public int getEndLoc() { return expr.getEndLoc(); }
}

public class CondExprModifierPragma  extends ModifierPragma {
    // Extended to support JML

    //# int tag
    //# Expr expr
    //# int loc
    //# Expr cond

    //# ManualTag
    public final int getTag() { return tag; }

    //# PostCheckCall
    private void postCheck() {
        boolean goodtag = (tag == TagConstants.ALSO_MODIFIES ||
                           tag == TagConstants.MODIFIES);
        boolean isJMLExprModifier = isJMLExprModifier();
        Assert.notFalse(goodtag || isJMLExprModifier);
    }

    private boolean isJMLExprModifier() {
        return (tag == TagConstants.ASSIGNABLE ||
                tag == TagConstants.MODIFIABLE);
    }

    public int getStartLoc() { return loc; }
    public int getEndLoc() { return cond.getEndLoc(); }
}
public class MapsExprModifierPragma  extends ModifierPragma implements javafe.ast.IdPragma {
    // Extended to support JML

    //# int tag
    //# Identifier id
    //# Expr mapsexpr
    //# int loc
    //# Expr expr

    //# ManualTag
    public final int getTag() { return tag; }

    //# PostCheckCall
    private void postCheck() {
        boolean goodtag = (tag == TagConstants.MAPS);
        Assert.notFalse(goodtag);
    }

    public Identifier id() { return id; }
    public int getStartLoc() { return loc; }
    public int getEndLoc() { return expr.getEndLoc(); }
}

public class ReachModifierPragma extends ModifierPragma
{
    //# Expr expr
    //# Identifier id
    //# Identifier* storerefs
    //# int loc

    public int getStartLoc() { return loc; }
}

public class VarDeclModifierPragma extends ModifierPragma
{
    //# int tag
    //# LocalVarDecl decl
    //# int loc
    //# int locId

    //# ManualTag
    public int getTag() { return tag; }

    public int getStartLoc() { return loc; }
}

public class VarExprModifierPragma extends ModifierPragma
{
    // Extended to support JML

    //# int tag
    //# GenericVarDecl arg
    //# Expr expr
    //# int loc

    //# ManualTag
    public final int getTag() { return tag; }

    //# PostCheckCall
    private void postCheck() {
        boolean goodtag =
            (tag == TagConstants.EXSURES 
             || tag == TagConstants.ALSO_EXSURES
             || tag == TagConstants.SIGNALS);
        Assert.notFalse(goodtag);
    }

    public int getStartLoc() { return loc; }
    public int getEndLoc() { return expr.getEndLoc(); }
}

public class NowarnPragma extends LexicalPragma
{
  //# Identifier* checks NoCheck
  //# int loc

  public int getStartLoc() { return loc; }
}

public class ImportPragma extends LexicalPragma
{
  //# ImportDecl decl
  //# int loc

  public int getStartLoc() { return loc; }
}

public class RefinePragma extends LexicalPragma
{
  //# String filename NoCheck
  //# int loc

  public int getStartLoc() { return loc; }
}

public class Spec extends ASTNode
{
  //# DerivedMethodDecl dmd NoCheck
  //# Expr* targets
  //# Hashtable preVarMap NoCheck
  //# Expr* preAssumptions
  //# Condition* pre
  //# Expr* postAssumptions
  //# Condition* post
  //# boolean modifiesEverything
  //# Set postconditionLocations  NoCheck

  public int getStartLoc() { return dmd.original.getStartLoc(); }
  public int getEndLoc() { return dmd.original.getEndLoc(); }
}

public class Condition extends ASTNode
{
  //# int label
  //# Expr pred
  //# int locPragmaDecl

  public int getStartLoc() { return locPragmaDecl; }

  public String prettyPrint() {
	return "Condition: label = " + TagConstants.toString(label) + "\n"
		+ "     loc = " + Location.toString(locPragmaDecl) + "\n"
		+ "     pred = " + pred;
  }
}

public class DefPred extends ASTNode
{
    //# Identifier predId
    //# GenericVarDecl* args
    //# Expr body

    public int getStartLoc() { return body.getStartLoc(); }
}
