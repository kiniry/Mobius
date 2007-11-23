package mobius.directVCGen.vcgen;

import javafe.ast.ASTNode;
import escjava.ast.AnOverview;
import escjava.ast.ArrayRangeRefExpr;
import escjava.ast.CondExprModifierPragma;
import escjava.ast.Condition;
import escjava.ast.DecreasesInfo;
import escjava.ast.DefPred;
import escjava.ast.DefPredApplExpr;
import escjava.ast.DefPredLetExpr;
import escjava.ast.DependsPragma;
import escjava.ast.EscPrimitiveType;
import escjava.ast.EverythingExpr;
import escjava.ast.ExprDeclPragma;
import escjava.ast.ExprModifierPragma;
import escjava.ast.ExprStmtPragma;
import escjava.ast.GCExpr;
import escjava.ast.GhostDeclPragma;
import escjava.ast.GuardExpr;
import escjava.ast.GuardedCmd;
import escjava.ast.IdExprDeclPragma;
import escjava.ast.IdentifierModifierPragma;
import escjava.ast.ImportPragma;
import escjava.ast.LockSetExpr;
import escjava.ast.MapsExprModifierPragma;
import escjava.ast.ModelConstructorDeclPragma;
import escjava.ast.ModelDeclPragma;
import escjava.ast.ModelMethodDeclPragma;
import escjava.ast.ModelProgamModifierPragma;
import escjava.ast.ModelTypePragma;
import escjava.ast.ModifiesGroupPragma;
import escjava.ast.NamedExprDeclPragma;
import escjava.ast.NestedModifierPragma;
import escjava.ast.NotModifiedExpr;
import escjava.ast.NotSpecifiedExpr;
import escjava.ast.NothingExpr;
import escjava.ast.NowarnPragma;
import escjava.ast.ParsedSpecs;
import escjava.ast.ReachModifierPragma;
import escjava.ast.RefinePragma;
import escjava.ast.ResExpr;
import escjava.ast.SetCompExpr;
import escjava.ast.SetStmtPragma;
import escjava.ast.SimpleModifierPragma;
import escjava.ast.SimpleStmtPragma;
import escjava.ast.SkolemConstantPragma;
import escjava.ast.Spec;
import escjava.ast.StillDeferredDeclPragma;
import escjava.ast.VarDeclModifierPragma;
import escjava.ast.VarExprModifierPragma;
import escjava.ast.VisitorArgResult;
import escjava.ast.WildRefExpr;

/**
 * A visitor that do all the basic handlings.
 * The only implemented method is {@link #visitASTNode(ASTNode, Object)}.
 * @author J. Charles (julien.charles@inria.fr)
 */
public abstract class ABasicVisitor extends VisitorArgResult {

  /**
   * Throws an exception which significate that we have reached an 
   * illegal expression.
   * @param x any node
   * @param o anything
   * @return nothing; throws a {@link java.lang.IllegalArgumentException}
   */
  public static Object illegalExpr(final ASTNode x, final Object o) {
    throw new IllegalArgumentException("Illegal Expression");
  }
  
  /**
   * Throws an exception which significate that we have reached an 
   * illegal statement.
   * @param x any node
   * @param o anything
   * @return nothing; throws a {@link java.lang.IllegalArgumentException}
   */
  public Object illegalStmt(final ASTNode x, final Object o) {
    throw new IllegalArgumentException("Illegal Statement");
  }


  /*
   * (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitASTNode(javafe.ast.ASTNode, java.lang.Object)
   */
  @Override
  public Object visitASTNode(final ASTNode x, final Object o) {
    final int max = x.childCount();
    Object res = o;
    for (int i = 0; i < max; i++) {
      final Object child = x.childAt(i);
      if ((child instanceof ASTNode) &&
          (child != x)) {
        res = ((ASTNode) child).accept(this, o);
      }
    }
    return res;
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitAnOverview(escjava.ast.AnOverview, java.lang.Object)
   */
  @Override
  public Object visitAnOverview(final AnOverview x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitArrayRangeRefExpr(escjava.ast.ArrayRangeRefExpr, java.lang.Object)
   */
  @Override
  public Object visitArrayRangeRefExpr(final ArrayRangeRefExpr x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitCondExprModifierPragma(escjava.ast.CondExprModifierPragma, java.lang.Object)
   */
  @Override
  public Object visitCondExprModifierPragma(final CondExprModifierPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitCondition(escjava.ast.Condition, java.lang.Object)
   */
  @Override
  public Object visitCondition(final Condition x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDecreasesInfo(escjava.ast.DecreasesInfo, java.lang.Object)
   */
  @Override
  public Object visitDecreasesInfo(final DecreasesInfo x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDefPred(escjava.ast.DefPred, java.lang.Object)
   */
  @Override
  public Object visitDefPred(final DefPred x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDefPredApplExpr(escjava.ast.DefPredApplExpr, java.lang.Object)
   */
  @Override
  public Object visitDefPredApplExpr(final DefPredApplExpr x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDefPredLetExpr(escjava.ast.DefPredLetExpr, java.lang.Object)
   */
  @Override
  public Object visitDefPredLetExpr(final DefPredLetExpr x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDependsPragma(escjava.ast.DependsPragma, java.lang.Object)
   */
  @Override
  public Object visitDependsPragma(final DependsPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitEscPrimitiveType(escjava.ast.EscPrimitiveType, java.lang.Object)
   */
  @Override
  public Object visitEscPrimitiveType(final EscPrimitiveType x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitEverythingExpr(escjava.ast.EverythingExpr, java.lang.Object)
   */
  @Override
  public Object visitEverythingExpr(final EverythingExpr x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitExprDeclPragma(escjava.ast.ExprDeclPragma, java.lang.Object)
   */
  @Override
  public Object visitExprDeclPragma(final ExprDeclPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitExprModifierPragma(escjava.ast.ExprModifierPragma, java.lang.Object)
   */
  @Override
  public Object visitExprModifierPragma(final ExprModifierPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitExprStmtPragma(escjava.ast.ExprStmtPragma, java.lang.Object)
   */
  @Override
  public Object visitExprStmtPragma(final ExprStmtPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitGCExpr(escjava.ast.GCExpr, java.lang.Object)
   */
  @Override
  public Object visitGCExpr(final GCExpr x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitGhostDeclPragma(escjava.ast.GhostDeclPragma, java.lang.Object)
   */
  @Override
  public Object visitGhostDeclPragma(final GhostDeclPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitGuardExpr(escjava.ast.GuardExpr, java.lang.Object)
   */
  @Override
  public Object visitGuardExpr(final GuardExpr x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitGuardedCmd(escjava.ast.GuardedCmd, java.lang.Object)
   */
  @Override
  public Object visitGuardedCmd(final GuardedCmd x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitIdExprDeclPragma(escjava.ast.IdExprDeclPragma, java.lang.Object)
   */
  @Override
  public Object visitIdExprDeclPragma(final IdExprDeclPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitIdentifierModifierPragma(escjava.ast.IdentifierModifierPragma, java.lang.Object)
   */
  @Override
  public Object visitIdentifierModifierPragma(final IdentifierModifierPragma x, 
                                              final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitImportPragma(escjava.ast.ImportPragma, java.lang.Object)
   */
  @Override
  public Object visitImportPragma(final ImportPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitLockSetExpr(escjava.ast.LockSetExpr, java.lang.Object)
   */
  @Override
  public Object visitLockSetExpr(final LockSetExpr x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitMapsExprModifierPragma(escjava.ast.MapsExprModifierPragma, java.lang.Object)
   */
  @Override
  public Object visitMapsExprModifierPragma(final MapsExprModifierPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelConstructorDeclPragma(escjava.ast.ModelConstructorDeclPragma, java.lang.Object)
   */
  @Override
  public Object visitModelConstructorDeclPragma(final ModelConstructorDeclPragma x, 
                                                final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelDeclPragma(escjava.ast.ModelDeclPragma, java.lang.Object)
   */
  @Override
  public Object visitModelDeclPragma(final ModelDeclPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelMethodDeclPragma(escjava.ast.ModelMethodDeclPragma, java.lang.Object)
   */
  @Override
  public Object visitModelMethodDeclPragma(final ModelMethodDeclPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelProgamModifierPragma(escjava.ast.ModelProgamModifierPragma, java.lang.Object)
   */
  @Override
  public Object visitModelProgamModifierPragma(final ModelProgamModifierPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelTypePragma(escjava.ast.ModelTypePragma, java.lang.Object)
   */
  @Override
  public Object visitModelTypePragma(final ModelTypePragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModifiesGroupPragma(escjava.ast.ModifiesGroupPragma, java.lang.Object)
   */
  @Override
  public Object visitModifiesGroupPragma(final ModifiesGroupPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNamedExprDeclPragma(escjava.ast.NamedExprDeclPragma, java.lang.Object)
   */
  @Override
  public Object visitNamedExprDeclPragma(final NamedExprDeclPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNestedModifierPragma(escjava.ast.NestedModifierPragma, java.lang.Object)
   */
  @Override
  public Object visitNestedModifierPragma(final NestedModifierPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNotModifiedExpr(escjava.ast.NotModifiedExpr, java.lang.Object)
   */
  @Override
  public Object visitNotModifiedExpr(final NotModifiedExpr x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNotSpecifiedExpr(escjava.ast.NotSpecifiedExpr, java.lang.Object)
   */
  @Override
  public Object visitNotSpecifiedExpr(final NotSpecifiedExpr x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNothingExpr(escjava.ast.NothingExpr, java.lang.Object)
   */
  @Override
  public Object visitNothingExpr(final NothingExpr x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNowarnPragma(escjava.ast.NowarnPragma, java.lang.Object)
   */
  @Override
  public Object visitNowarnPragma(final NowarnPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitParsedSpecs(escjava.ast.ParsedSpecs, java.lang.Object)
   */
  @Override
  public Object visitParsedSpecs(final ParsedSpecs x, final Object o) { 
    // there is a recursive dependency over child 0 of parsed spec
  
    return o;
    
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitReachModifierPragma(escjava.ast.ReachModifierPragma, java.lang.Object)
   */
  @Override
  public Object visitReachModifierPragma(final ReachModifierPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitRefinePragma(escjava.ast.RefinePragma, java.lang.Object)
   */
  @Override
  public Object visitRefinePragma(final RefinePragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitResExpr(escjava.ast.ResExpr, java.lang.Object)
   */
  @Override
  public Object visitResExpr(final ResExpr x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSetCompExpr(escjava.ast.SetCompExpr, java.lang.Object)
   */
  @Override
  public Object visitSetCompExpr(final SetCompExpr x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSetStmtPragma(escjava.ast.SetStmtPragma, java.lang.Object)
   */
  @Override
  public Object visitSetStmtPragma(final SetStmtPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSimpleModifierPragma(escjava.ast.SimpleModifierPragma, java.lang.Object)
   */
  @Override
  public Object visitSimpleModifierPragma(final SimpleModifierPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSimpleStmtPragma(escjava.ast.SimpleStmtPragma, java.lang.Object)
   */
  @Override
  public Object visitSimpleStmtPragma(final SimpleStmtPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSkolemConstantPragma(escjava.ast.SkolemConstantPragma, java.lang.Object)
   */
  @Override
  public Object visitSkolemConstantPragma(final SkolemConstantPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSpec(escjava.ast.Spec, java.lang.Object)
   */
  @Override
  public Object visitSpec(final Spec x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitStillDeferredDeclPragma(escjava.ast.StillDeferredDeclPragma, java.lang.Object)
   */
  @Override
  public Object visitStillDeferredDeclPragma(final StillDeferredDeclPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitVarDeclModifierPragma(escjava.ast.VarDeclModifierPragma, java.lang.Object)
   */
  @Override
  public Object visitVarDeclModifierPragma(final VarDeclModifierPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitVarExprModifierPragma(escjava.ast.VarExprModifierPragma, java.lang.Object)
   */
  @Override
  public Object visitVarExprModifierPragma(final VarExprModifierPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /*
   * (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitWildRefExpr(escjava.ast.WildRefExpr, java.lang.Object)
   */
  @Override
  public Object visitWildRefExpr(final WildRefExpr x, final Object o) {
    return visitASTNode(x, o);
  }
}
