package mobius.directVCGen.formula.jmlTranslator;

import escjava.ast.Condition;
import escjava.ast.DecreasesInfo;
import escjava.ast.DefPred;
import escjava.ast.DefPredApplExpr;
import escjava.ast.DefPredLetExpr;
import escjava.ast.DependsPragma;
import escjava.ast.EscPrimitiveType;
import escjava.ast.GhostDeclPragma;
import escjava.ast.GuardExpr;
import escjava.ast.GuardedCmd;
import escjava.ast.IdExprDeclPragma;
import escjava.ast.IdentifierModifierPragma;
import escjava.ast.LockSetExpr;
import escjava.ast.MapsExprModifierPragma;
import escjava.ast.ModelConstructorDeclPragma;
import escjava.ast.ModelDeclPragma;
import escjava.ast.ModelMethodDeclPragma;
import escjava.ast.ModelProgamModifierPragma;
import escjava.ast.ModelTypePragma;
import escjava.ast.NamedExprDeclPragma;
import escjava.ast.NestedModifierPragma;
import escjava.ast.NotModifiedExpr;
import escjava.ast.NotSpecifiedExpr;
import escjava.ast.NothingExpr;
import escjava.ast.NowarnPragma;
import escjava.ast.ReachModifierPragma;
import escjava.ast.RefinePragma;
import escjava.ast.SetCompExpr;
import escjava.ast.SimpleModifierPragma;
import escjava.ast.SimpleStmtPragma;
import escjava.ast.SkolemConstantPragma;
import escjava.ast.Spec;
import escjava.ast.StillDeferredDeclPragma;
import escjava.ast.VarDeclModifierPragma;
import escjava.ast.WildRefExpr;
import mobius.directVCGen.vcgen.ABasicVisitor;

public class BasicJMLTranslator extends ABasicVisitor{
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSimpleModifierPragma(escjava.ast.SimpleModifierPragma, java.lang.Object)
   */
  public final Object visitSimpleModifierPragma(final /*@non_null*/ SimpleModifierPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSimpleStmtPragma(escjava.ast.SimpleStmtPragma, java.lang.Object)
   */
  public final Object visitSimpleStmtPragma(final /*@non_null*/ SimpleStmtPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSkolemConstantPragma(escjava.ast.SkolemConstantPragma, java.lang.Object)
   */
  public final Object visitSkolemConstantPragma(final /*@non_null*/ SkolemConstantPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSpec(escjava.ast.Spec, java.lang.Object)
   */
  public final Object visitSpec(final /*@non_null*/ Spec x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitStillDeferredDeclPragma(escjava.ast.StillDeferredDeclPragma, java.lang.Object)
   */
  public final Object visitStillDeferredDeclPragma(final /*@non_null*/ StillDeferredDeclPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitVarDeclModifierPragma(escjava.ast.VarDeclModifierPragma, java.lang.Object)
   */
  public final Object visitVarDeclModifierPragma(final /*@non_null*/ VarDeclModifierPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitWildRefExpr(escjava.ast.WildRefExpr, java.lang.Object)
   */
  public final Object visitWildRefExpr(final /*@non_null*/ WildRefExpr x, final Object o) {
    return null;
  }
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSetCompExpr(escjava.ast.SetCompExpr, java.lang.Object)
   */
  public final Object visitSetCompExpr(final /*@non_null*/ SetCompExpr x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitReachModifierPragma(escjava.ast.ReachModifierPragma, java.lang.Object)
   */
  public final Object visitReachModifierPragma(final /*@non_null*/ ReachModifierPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitRefinePragma(escjava.ast.RefinePragma, java.lang.Object)
   */
  public final Object visitRefinePragma(final /*@non_null*/ RefinePragma x, final Object o) {
    return null;
  }
  
  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNamedExprDeclPragma(escjava.ast.NamedExprDeclPragma, java.lang.Object)
   */
  @Override
  public final Object visitNamedExprDeclPragma(final /*@non_null*/ NamedExprDeclPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNestedModifierPragma(escjava.ast.NestedModifierPragma, java.lang.Object)
   */
  @Override
  public final Object visitNestedModifierPragma(final /*@non_null*/ NestedModifierPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNotModifiedExpr(escjava.ast.NotModifiedExpr, java.lang.Object)
   */
  @Override
  public final Object visitNotModifiedExpr(final /*@non_null*/ NotModifiedExpr x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNotSpecifiedExpr(escjava.ast.NotSpecifiedExpr, java.lang.Object)
   */
  @Override
  public final Object visitNotSpecifiedExpr(final /*@non_null*/ NotSpecifiedExpr x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNothingExpr(escjava.ast.NothingExpr, java.lang.Object)
   */
  @Override
  public final Object visitNothingExpr(final /*@non_null*/ NothingExpr x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNowarnPragma(escjava.ast.NowarnPragma, java.lang.Object)
   */
  @Override
  public final Object visitNowarnPragma(final /*@non_null*/ NowarnPragma x, final Object o) {
    return null;
  }
  
  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitLockSetExpr(escjava.ast.LockSetExpr, java.lang.Object)
   */
  @Override
  public final Object visitLockSetExpr(final /*@non_null*/ LockSetExpr x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitMapsExprModifierPragma(escjava.ast.MapsExprModifierPragma, java.lang.Object)
   */
  @Override
  public final Object visitMapsExprModifierPragma(final /*@non_null*/ MapsExprModifierPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelConstructorDeclPragma(escjava.ast.ModelConstructorDeclPragma, java.lang.Object)
   */
  @Override
  public final Object visitModelConstructorDeclPragma(final /*@non_null*/ ModelConstructorDeclPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelDeclPragma(escjava.ast.ModelDeclPragma, java.lang.Object)
   */
  @Override
  public final Object visitModelDeclPragma(final /*@non_null*/ ModelDeclPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelMethodDeclPragma(escjava.ast.ModelMethodDeclPragma, java.lang.Object)
   */
  @Override
  public final Object visitModelMethodDeclPragma(final /*@non_null*/ ModelMethodDeclPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelProgamModifierPragma(escjava.ast.ModelProgamModifierPragma, java.lang.Object)
   */
  @Override
  public final Object visitModelProgamModifierPragma(final /*@non_null*/ ModelProgamModifierPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelTypePragma(escjava.ast.ModelTypePragma, java.lang.Object)
   */
  @Override
  public final Object visitModelTypePragma(final /*@non_null*/ ModelTypePragma x, final Object o) {
    return null;
  }
  

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitGhostDeclPragma(escjava.ast.GhostDeclPragma, java.lang.Object)
   */
  @Override
  public final Object visitGhostDeclPragma(final /*@non_null*/ GhostDeclPragma x, final Object o) {
    //TODO: handle ghost fields
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitGuardExpr(escjava.ast.GuardExpr, java.lang.Object)
   */
  @Override
  public final Object visitGuardExpr(final /*@non_null*/ GuardExpr x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitGuardedCmd(escjava.ast.GuardedCmd, java.lang.Object)
   */
  @Override
  public final Object visitGuardedCmd(final /*@non_null*/ GuardedCmd x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitIdExprDeclPragma(escjava.ast.IdExprDeclPragma, java.lang.Object)
   */
  @Override
  public final Object visitIdExprDeclPragma(final /*@non_null*/ IdExprDeclPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitIdentifierModifierPragma(escjava.ast.IdentifierModifierPragma, java.lang.Object)
   */
  @Override
  public final Object visitIdentifierModifierPragma(final /*@non_null*/ IdentifierModifierPragma x, final Object o) {
    return null;
  }
  
  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitCondition(escjava.ast.Condition, java.lang.Object)
   */
  @Override
  public final Object visitCondition(final /*@non_null*/ Condition x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDecreasesInfo(escjava.ast.DecreasesInfo, java.lang.Object)
   */
  @Override
  public final Object visitDecreasesInfo(final /*@non_null*/ DecreasesInfo x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDefPred(escjava.ast.DefPred, java.lang.Object)
   */
  @Override
  public final Object visitDefPred(final /*@non_null*/ DefPred x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDefPredApplExpr(escjava.ast.DefPredApplExpr, java.lang.Object)
   */
  @Override
  public final Object visitDefPredApplExpr(final /*@non_null*/ DefPredApplExpr x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDefPredLetExpr(escjava.ast.DefPredLetExpr, java.lang.Object)
   */
  @Override
  public final Object visitDefPredLetExpr(final /*@non_null*/ DefPredLetExpr x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDependsPragma(escjava.ast.DependsPragma, java.lang.Object)
   */
  @Override
  public final Object visitDependsPragma(final /*@non_null*/ DependsPragma x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitEscPrimitiveType(escjava.ast.EscPrimitiveType, java.lang.Object)
   */
  @Override
  public final Object visitEscPrimitiveType(final /*@non_null*/ EscPrimitiveType x, final Object o) {
    return null;
  }

}
