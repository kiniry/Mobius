/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.ast;


import java.util.Hashtable;

import javafe.ast.*;
// import escjava.ast.Visitor;      // Work around 1.0.2 compiler bug
// import escjava.ast.TagConstants; // Work around 1.0.2 compiler bug
// import escjava.ast.GeneratedTags;// Work around 1.0.2 compiler bug
// import escjava.ast.AnOverview;   // Work around 1.0.2 compiler bug
import javafe.util.Assert;
import javafe.util.Location;


// Convention: unless otherwise noted, integer fields named "loc"g refer
// to the locaction of the first character of the syntactic unit

//# TagBase javafe.tc.TagConstants.LAST_TAG + 1
//# VisitorRoot javafe.ast.Visitor


public abstract class Visitor extends javafe.ast.Visitor {
  //@ requires x!=null
  public abstract void visitAnOverview(AnOverview x);

  //@ requires x!=null
  public abstract void visitGCExpr(GCExpr x);

  //@ requires x!=null
  public void visitNaryExpr(NaryExpr x) {
    visitGCExpr(x);
  }

  //@ requires x!=null
  public void visitQuantifiedExpr(QuantifiedExpr x) {
    visitGCExpr(x);
  }

  //@ requires x!=null
  public void visitSubstExpr(SubstExpr x) {
    visitGCExpr(x);
  }

  //@ requires x!=null
  public void visitTypeExpr(TypeExpr x) {
    visitGCExpr(x);
  }

  //@ requires x!=null
  public void visitLabelExpr(LabelExpr x) {
    visitGCExpr(x);
  }

  //@ requires x!=null
  public abstract void visitWildRefExpr(WildRefExpr x);

  //@ requires x!=null
  public abstract void visitGuardExpr(GuardExpr x);

  //@ requires x!=null
  public abstract void visitResExpr(ResExpr x);

  //@ requires x!=null
  public abstract void visitLockSetExpr(LockSetExpr x);

  //@ requires x!=null
  public abstract void visitDefPredLetExpr(DefPredLetExpr x);

  //@ requires x!=null
  public abstract void visitDefPredApplExpr(DefPredApplExpr x);

  //@ requires x!=null
  public abstract void visitGuardedCmd(GuardedCmd x);

  //@ requires x!=null
  public void visitSimpleCmd(SimpleCmd x) {
    visitGuardedCmd(x);
  }

  //@ requires x!=null
  public void visitExprCmd(ExprCmd x) {
    visitGuardedCmd(x);
  }

  //@ requires x!=null
  public void visitAssignCmd(AssignCmd x) {
    visitGuardedCmd(x);
  }

  //@ requires x!=null
  public void visitGetsCmd(GetsCmd x) {
    visitAssignCmd(x);
  }

  //@ requires x!=null
  public void visitSubGetsCmd(SubGetsCmd x) {
    visitAssignCmd(x);
  }

  //@ requires x!=null
  public void visitSubSubGetsCmd(SubSubGetsCmd x) {
    visitAssignCmd(x);
  }

  //@ requires x!=null
  public void visitRestoreFromCmd(RestoreFromCmd x) {
    visitAssignCmd(x);
  }

  //@ requires x!=null
  public void visitVarInCmd(VarInCmd x) {
    visitGuardedCmd(x);
  }

  //@ requires x!=null
  public void visitDynInstCmd(DynInstCmd x) {
    visitGuardedCmd(x);
  }

  //@ requires x!=null
  public void visitSeqCmd(SeqCmd x) {
    visitGuardedCmd(x);
  }

  //@ requires x!=null
  public void visitLoopCmd(LoopCmd x) {
    visitGuardedCmd(x);
  }

  //@ requires x!=null
  public void visitCmdCmdCmd(CmdCmdCmd x) {
    visitGuardedCmd(x);
  }

  //@ requires x!=null
  public void visitCall(Call x) {
    visitGuardedCmd(x);
  }

  //@ requires x!=null
  public abstract void visitExprDeclPragma(ExprDeclPragma x);

  //@ requires x!=null
  public abstract void visitGhostDeclPragma(GhostDeclPragma x);

  //@ requires x!=null
  public abstract void visitStillDeferredDeclPragma(StillDeferredDeclPragma x);

  //@ requires x!=null
  public abstract void visitSimpleStmtPragma(SimpleStmtPragma x);

  //@ requires x!=null
  public abstract void visitExprStmtPragma(ExprStmtPragma x);

  //@ requires x!=null
  public abstract void visitSetStmtPragma(SetStmtPragma x);

  //@ requires x!=null
  public abstract void visitSkolemConstantPragma(SkolemConstantPragma x);

  //@ requires x!=null
  public abstract void visitSimpleModifierPragma(SimpleModifierPragma x);

  //@ requires x!=null
  public abstract void visitExprModifierPragma(ExprModifierPragma x);

  //@ requires x!=null
  public abstract void visitVarExprModifierPragma(VarExprModifierPragma x);

  //@ requires x!=null
  public abstract void visitNowarnPragma(NowarnPragma x);

  //@ requires x!=null
  public abstract void visitSpec(Spec x);

  //@ requires x!=null
  public abstract void visitCondition(Condition x);

  //@ requires x!=null
  public abstract void visitDefPred(DefPred x);

}
