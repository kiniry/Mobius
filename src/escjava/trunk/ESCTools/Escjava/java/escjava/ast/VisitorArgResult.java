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


public abstract class VisitorArgResult extends javafe.ast.VisitorArgResult {
  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitAnOverview(AnOverview x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitGCExpr(GCExpr x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitNaryExpr(NaryExpr x, Object o) {
    return visitGCExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitQuantifiedExpr(QuantifiedExpr x, Object o) {
    return visitGCExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitSubstExpr(SubstExpr x, Object o) {
    return visitGCExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitTypeExpr(TypeExpr x, Object o) {
    return visitGCExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitLabelExpr(LabelExpr x, Object o) {
    return visitGCExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitWildRefExpr(WildRefExpr x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitGuardExpr(GuardExpr x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitResExpr(ResExpr x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitLockSetExpr(LockSetExpr x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitDefPredLetExpr(DefPredLetExpr x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitDefPredApplExpr(DefPredApplExpr x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitGuardedCmd(GuardedCmd x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitSimpleCmd(SimpleCmd x, Object o) {
    return visitGuardedCmd(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitExprCmd(ExprCmd x, Object o) {
    return visitGuardedCmd(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitAssignCmd(AssignCmd x, Object o) {
    return visitGuardedCmd(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitGetsCmd(GetsCmd x, Object o) {
    return visitAssignCmd(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitSubGetsCmd(SubGetsCmd x, Object o) {
    return visitAssignCmd(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitSubSubGetsCmd(SubSubGetsCmd x, Object o) {
    return visitAssignCmd(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitRestoreFromCmd(RestoreFromCmd x, Object o) {
    return visitAssignCmd(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitVarInCmd(VarInCmd x, Object o) {
    return visitGuardedCmd(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitDynInstCmd(DynInstCmd x, Object o) {
    return visitGuardedCmd(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitSeqCmd(SeqCmd x, Object o) {
    return visitGuardedCmd(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitLoopCmd(LoopCmd x, Object o) {
    return visitGuardedCmd(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitCmdCmdCmd(CmdCmdCmd x, Object o) {
    return visitGuardedCmd(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitCall(Call x, Object o) {
    return visitGuardedCmd(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitExprDeclPragma(ExprDeclPragma x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitGhostDeclPragma(GhostDeclPragma x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitStillDeferredDeclPragma(StillDeferredDeclPragma x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitSimpleStmtPragma(SimpleStmtPragma x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitExprStmtPragma(ExprStmtPragma x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitSetStmtPragma(SetStmtPragma x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitSkolemConstantPragma(SkolemConstantPragma x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitSimpleModifierPragma(SimpleModifierPragma x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitExprModifierPragma(ExprModifierPragma x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitVarExprModifierPragma(VarExprModifierPragma x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitNowarnPragma(NowarnPragma x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitSpec(Spec x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitCondition(Condition x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitDefPred(DefPred x, Object o);

}
