/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.ast;


import java.util.Hashtable;

import javafe.ast.*;
//import escjava.ast.Visitor;      // Work around 1.0.2 compiler bug
//import escjava.ast.TagConstants; // Work around 1.0.2 compiler bug
//import escjava.ast.GeneratedTags;// Work around 1.0.2 compiler bug
//import escjava.ast.AnOverview;   // Work around 1.0.2 compiler bug
import javafe.util.Assert;
import javafe.util.Location;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the locaction of the first character of the syntactic unit

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
 *           + SubstExpr (GenericVarDecl var, Expr val, Expr target)
 *           + TypeExpr (Type type)
 *         + LockSetExpr ()
 *         + EverythingExpr ()
 *         + NothingExpr ()
 *         + NotSpecifiedExpr ()
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
 *	    + ModelDeclPragma (ModelFieldDecl decl)
 *         + ModelMethodDeclPragma (MethodDecl decl)
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
 *           // plus JML keywords: Also, Pre, Post, Assignable, Modifiable (kiniry)
 *         + VarExprModifierPragma (GenericVarDecl arg, Expr expr) // Exsures, AlsoExsures
 *           // plus JML keywords: Signals
 *    - LexicalPragma ()
 *      + NowarnPragma (Identifier* checks)
 *    + Spec (MethodDecl md, Expr* targets, Hashtable preVarMap, Condition* pre, Condition* post)
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
 * @see javafe.ast.AnOverview
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
  //# Expr expr
  //# int locOpenBracket
  //# int locCloseBracket

  public int getStartLoc() { return expr.getStartLoc(); }
  public int getEndLoc() { return expr.getEndLoc(); }
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
      (tag == TagConstants.AXIOM || tag == TagConstants.INVARIANT || tag == TagConstants.JML_REPRESENTS);
    Assert.notFalse(goodtag);
  }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return expr.getEndLoc(); }
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

public class ExprStmtPragma extends StmtPragma
{
  //# int tag
  //# Expr expr
  //# int loc

  //# ManualTag
  public final int getTag() { return tag; }

  //# PostCheckCall
  private void postCheck() {
    boolean goodtag =
      (tag == TagConstants.ASSUME 
       || tag == TagConstants.ASSERT
       || tag == TagConstants.LOOP_INVARIANT 
       || tag == TagConstants.JML_MAINTAINING 
       || tag == TagConstants.DECREASES
       || tag == TagConstants.JML_DECREASING);
    Assert.notFalse(goodtag);
  }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return expr.getEndLoc(); }
}

public class RepresentsPragma extends TypeDeclElemPragma
{
  // represents 'target' <- 'value':

  //# Expr target
  //# int locOp
  //# Expr value
  //# int loc

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return value.getEndLoc(); }
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

    //# ManualTag
    public final int getTag() { return tag; }

    //# PostCheckCall
    private void postCheck() {
        boolean goodtag =
            (tag == TagConstants.READABLE_IF || tag == TagConstants.WRITABLE_IF
             || tag == TagConstants.REQUIRES || tag == TagConstants.ALSO_REQUIRES
             || tag == TagConstants.ENSURES || tag == TagConstants.ALSO_ENSURES
             || tag == TagConstants.MONITORED_BY || tag == TagConstants.MODIFIES
             || tag == TagConstants.ALSO_MODIFIES);
        boolean isJMLExprModifier = isJMLExprModifier();
        Assert.notFalse(goodtag || isJMLExprModifier);
    }

    private boolean isJMLExprModifier() {
        return (tag == TagConstants.JML_ALSO 
                || tag == TagConstants.JML_PRE
                || tag == TagConstants.JML_POST
                || tag == TagConstants.JML_MODIFIABLE
                || tag == TagConstants.JML_ASSIGNABLE);
    }

    public int getStartLoc() { return loc; }
    public int getEndLoc() { return expr.getEndLoc(); }
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
             || tag == TagConstants.JML_SIGNALS);
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

public class Spec extends ASTNode
{
  //# DerivedMethodDecl dmd NoCheck
  //# Expr* targets
  //# Hashtable preVarMap NoCheck
  //# Condition* pre
  //# Condition* post

  public int getStartLoc() { return dmd.original.getStartLoc(); }
  public int getEndLoc() { return dmd.original.getEndLoc(); }
}

public class Condition extends ASTNode
{
  //# int label
  //# Expr pred
  //# int locPragmaDecl

  public int getStartLoc() { return locPragmaDecl; }
}

public class DefPred extends ASTNode
{
    //# Identifier predId
    //# GenericVarDecl* args
    //# Expr body

    public int getStartLoc() { return body.getStartLoc(); }
}

