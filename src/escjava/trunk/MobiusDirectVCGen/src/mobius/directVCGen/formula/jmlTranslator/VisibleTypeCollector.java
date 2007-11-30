package mobius.directVCGen.formula.jmlTranslator;

import java.util.HashSet;
import java.util.Set;

import javafe.ast.ASTNode;
import javafe.ast.BinaryExpr;
import javafe.ast.ClassDecl;
import javafe.ast.ConstructorDecl;
import javafe.ast.Expr;
import javafe.ast.FieldAccess;
import javafe.ast.FormalParaDecl;
import javafe.ast.InstanceOfExpr;
import javafe.ast.LiteralExpr;
import javafe.ast.MethodDecl;
import javafe.ast.MethodInvocation;
import javafe.ast.OperatorTags;
import javafe.ast.PrimitiveType;
import javafe.ast.RoutineDecl;
import javafe.ast.ThisExpr;
import javafe.ast.Type;
import javafe.ast.UnaryExpr;
import javafe.ast.VariableAccess;
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
import escjava.ast.NaryExpr;
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
import escjava.ast.TagConstants;
import escjava.ast.VarDeclModifierPragma;
import escjava.ast.VarExprModifierPragma;
import escjava.ast.VisitorArgResult;
import escjava.ast.WildRefExpr;
import escjava.tc.FlowInsensitiveChecks;
import escjava.tc.TypeSig;



/**
 * @author Claudia Brauchli (claudia@vis.ethz.ch)
 * @author Hermann Lehner (hermann.lehner@inf.ethz.ch)
 * @author Julien Charles (julien.charles@inria.fr)
 *
 */
public final class VisibleTypeCollector extends VisitorArgResult {

  private java.util.Set<Type> fTypeSet;

  private boolean fAssign;
  private boolean fEverything;

  private VisibleTypeCollector() {
    //fProperties = new Properties();
    //fProperties.put("old", Boolean.FALSE);
    //fProperties.put("everything", Boolean.FALSE);
    fTypeSet = new HashSet<Type>();
  }

  /** {@inheritDoc} */
  @Override
  public Object visitASTNode(final ASTNode x, final Object prop) {
    Object o = null;
    final int max = x.childCount();
    for (int i = 0; i < max; i++) {
      final Object child = x.childAt(i);
      if (child instanceof ASTNode) {
        o = ((ASTNode) child).accept(this, prop);
      }
    }
    return o;
  }

  @Override
  public Object visitClassDecl(final /*@non_null*/ ClassDecl x, final Object o) {
    fTypeSet.add(TypeSig.getSig(x));
    //should never be called
    return visitTypeDecl(x, null);
  }

  @Override
  public Object visitRoutineDecl(final /*@non_null*/ RoutineDecl x, final Object o) {

    fAssign = false;
    visitASTNode(x, o); 
    if (fEverything) {
      fTypeSet.clear();
    }
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitConstructorDecl(/*@non_null*/ final ConstructorDecl x, final Object o) {
    return visitRoutineDecl(x, o);
  }
  
  /** {@inheritDoc} */
  @Override
  public Object visitMethodDecl(final /*@non_null*/ MethodDecl x, final Object o) {
    return visitRoutineDecl(x, o);
  }
  
  /**
   * We also want to collect all assignable types of a method invocation.
   */
  public /*@non_null*/ Object visitMethodInvocation(
                                            final /*@non_null*/ MethodInvocation x, 
                                            final Object o) {
    //add assignable pragma types to fTypeSet   
    for (int i = 0; i < x.decl.pmodifiers.size(); i++) {
      if (x.decl.pmodifiers.elementAt(i).getTag() == TagConstants.MODIFIESGROUPPRAGMA) {
        final ModifiesGroupPragma modi = (ModifiesGroupPragma) x.decl.pmodifiers.elementAt(i);
        CondExprModifierPragma assigPragma = null;
        for (int j = 0; j < modi.items.size(); j++) {
          assigPragma = modi.items.elementAt(j);
          if (assigPragma.expr instanceof FieldAccess) {
            final javafe.ast.Type type2 = FlowInsensitiveChecks.getType(assigPragma.expr);
            fTypeSet.add(type2);
          }
          else if (assigPragma.expr instanceof EverythingExpr) {
            fEverything = true; 
            break;
          }
        }
      }
    }
    
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public Object visitFormalParaDecl(/*@non_null*/ final FormalParaDecl x, final Object o) {
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitAnOverview(final AnOverview x, final Object o) {
    
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public Object visitLiteralExpr(/*@non_null*/ final LiteralExpr x, final Object o) {
    return null;
  }


  @Override
  public Object visitVariableAccess(final /*@non_null*/ VariableAccess x, 
                                                  final Object o) {
    if (fAssign) {
      final javafe.ast.Type type = javafe.tc.FlowInsensitiveChecks.getType(x);
      if (!(type instanceof PrimitiveType)) {
        fTypeSet.add(type);
      }
    }
    return null;
  }

  @Override
  public Object visitFieldAccess(final /*@non_null*/ FieldAccess x, 
                                               final Object o) {

    final javafe.ast.Type type = x.od.type();
    if (!(type instanceof PrimitiveType) && fAssign) {
      fTypeSet.add(type);
    }

    fAssign = false;
    ((Expr)x.od.childAt(0)).accept(this, o);

    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitNaryExpr(/*@non_null*/ final NaryExpr x, final Object o) {
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitInstanceOfExpr(/*@non_null*/ final InstanceOfExpr x, final Object o) {
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object  visitThisExpr(final ThisExpr x, final Object o) {
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitArrayRangeRefExpr(final ArrayRangeRefExpr x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitCondExprModifierPragma(final CondExprModifierPragma x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitCondition(final Condition x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitDecreasesInfo(final DecreasesInfo x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitDefPred(final DefPred x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitDefPredApplExpr(final DefPredApplExpr x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitDefPredLetExpr(final DefPredLetExpr x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitDependsPragma(final DependsPragma x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitEscPrimitiveType(final EscPrimitiveType x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitEverythingExpr(final EverythingExpr x, final Object o) {
    
    //return null;
    return visitASTNode(x, o);
  }

  /** {@inheritDoc} */
  @Override
  public Object visitExprDeclPragma(final ExprDeclPragma x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitExprModifierPragma(final ExprModifierPragma x, final Object o) {
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitExprStmtPragma(final ExprStmtPragma x, final Object o) {
    
    return visitASTNode(x, o);
  }

  /** {@inheritDoc} */
  @Override
  public Object visitGCExpr(final GCExpr x, final Object o) {
    return visitASTNode(x, o);
  }

  /** {@inheritDoc} */
  @Override
  public Object visitGhostDeclPragma(final GhostDeclPragma x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitGuardExpr(final GuardExpr x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitGuardedCmd(final GuardedCmd x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitIdExprDeclPragma(final IdExprDeclPragma x, final Object o) {
    
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public Object visitIdentifierModifierPragma(final IdentifierModifierPragma x, 
                                              final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitImportPragma(final ImportPragma x, final Object o) {
    
    return visitASTNode(x, o);
  }

  /** {@inheritDoc} */
  @Override
  public Object visitLockSetExpr(final LockSetExpr x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitMapsExprModifierPragma(final MapsExprModifierPragma x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitModelConstructorDeclPragma(final ModelConstructorDeclPragma x,
                                                final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitModelDeclPragma(final ModelDeclPragma x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitModelMethodDeclPragma(final ModelMethodDeclPragma x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitModelProgamModifierPragma(final ModelProgamModifierPragma x, 
                                               final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitModelTypePragma(final ModelTypePragma x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitModifiesGroupPragma(final ModifiesGroupPragma x, final Object o) {
    //FIXME hel: Claudia, what's up here?
    //return null;
    return null; //visitASTNode(x, o);
  }

  /** {@inheritDoc} */
  @Override
  public Object visitNamedExprDeclPragma(final NamedExprDeclPragma x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitNestedModifierPragma(final NestedModifierPragma x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitNotModifiedExpr(final NotModifiedExpr x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitNotSpecifiedExpr(final NotSpecifiedExpr x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitNothingExpr(final NothingExpr x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitNowarnPragma(final NowarnPragma x, final Object o) {
    
    return null;
  }
  /** {@inheritDoc} */
  @Override
  public Object visitParsedSpecs(final ParsedSpecs x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitReachModifierPragma(final ReachModifierPragma x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitRefinePragma(final RefinePragma x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitResExpr(final ResExpr x, final Object o) {
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitSetCompExpr(final SetCompExpr x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitSetStmtPragma(final SetStmtPragma x, final Object o) {
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitSimpleModifierPragma(final SimpleModifierPragma x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitSimpleStmtPragma(final SimpleStmtPragma x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitSkolemConstantPragma(final SkolemConstantPragma x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitSpec(final Spec x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitStillDeferredDeclPragma(final StillDeferredDeclPragma x, final Object o) {
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitVarDeclModifierPragma(final VarDeclModifierPragma x, final Object o) {
    
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitVarExprModifierPragma(final VarExprModifierPragma x, final Object o) {
    
    return null; //visitASTNode(x, o); 
  }

  /** {@inheritDoc} */
  @Override
  public Object visitWildRefExpr(final WildRefExpr x, final Object o) {
    
    return null;
  }


  @Override
  public Object visitBinaryExpr(final BinaryExpr expr, final Object o) {
    if ((expr.op == OperatorTags.ASSIGN) | 
        (expr.op == OperatorTags.ASGMUL) |
        (expr.op == OperatorTags.ASGDIV) | 
        (expr.op == OperatorTags.ASGREM) |
        (expr.op == OperatorTags.ASGADD) | 
        (expr.op == OperatorTags.ASGSUB) |
        (expr.op == OperatorTags.ASGLSHIFT) | 
        (expr.op == OperatorTags.ASGRSHIFT) |
        (expr.op == OperatorTags.ASGURSHIFT) | 
        (expr.op == OperatorTags.ASGBITAND)) {
      fAssign = false;
      expr.right.accept(this, o); 
      fAssign = true;
      expr.left.accept(this, o);
      return null;
    }
    else {
      return visitExpr(expr, o);
    }
  }

  @Override
  public Object visitUnaryExpr(final /*@non_null*/ UnaryExpr x, final Object o) {
    fAssign = true;
    return visitExpr(x, o);
  }

  
  public static Set<Type> getVisibleTypeSet(RoutineDecl x) {
    final VisibleTypeCollector vtc = new VisibleTypeCollector();
    x.accept(vtc, null);
    return vtc.fTypeSet;
  }

}
