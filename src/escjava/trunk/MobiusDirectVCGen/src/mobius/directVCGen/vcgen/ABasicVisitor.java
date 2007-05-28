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
 * @author J. Charles
 */
public abstract class ABasicVisitor extends VisitorArgResult{

	/**
	 * Throws an exception which significate that we have reached an 
	 * illegal expression.
	 * @param x any node
	 * @param o anything
	 * @return nothing; throws a {@link java.lang.IllegalArgumentException}
	 */
	public static Object illegalExpr(ASTNode x, Object o){
		throw new IllegalArgumentException("Illegal Expression");
	}
	
	/*
	 * (non-Javadoc)
	 * @see javafe.ast.VisitorArgResult#visitASTNode(javafe.ast.ASTNode, java.lang.Object)
	 */
	@Override
	public Object visitASTNode(ASTNode x, Object o) {
		//System.out.println(x);
		int max = x.childCount();
		for(int i = 0; i < max; i++) {
			Object child = x.childAt(i);
			if(child instanceof ASTNode) {
				o = ((ASTNode) child).accept(this, o);
			}
		}
		return o;
	}
	
	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitAnOverview(escjava.ast.AnOverview, java.lang.Object)
	 */
	@Override
	public Object visitAnOverview(AnOverview x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitArrayRangeRefExpr(escjava.ast.ArrayRangeRefExpr, java.lang.Object)
	 */
	@Override
	public Object visitArrayRangeRefExpr(ArrayRangeRefExpr x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitCondExprModifierPragma(escjava.ast.CondExprModifierPragma, java.lang.Object)
	 */
	@Override
	public Object visitCondExprModifierPragma(CondExprModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitCondition(escjava.ast.Condition, java.lang.Object)
	 */
	@Override
	public Object visitCondition(Condition x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitDecreasesInfo(escjava.ast.DecreasesInfo, java.lang.Object)
	 */
	@Override
	public Object visitDecreasesInfo(DecreasesInfo x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitDefPred(escjava.ast.DefPred, java.lang.Object)
	 */
	@Override
	public Object visitDefPred(DefPred x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitDefPredApplExpr(escjava.ast.DefPredApplExpr, java.lang.Object)
	 */
	@Override
	public Object visitDefPredApplExpr(DefPredApplExpr x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitDefPredLetExpr(escjava.ast.DefPredLetExpr, java.lang.Object)
	 */
	@Override
	public Object visitDefPredLetExpr(DefPredLetExpr x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitDependsPragma(escjava.ast.DependsPragma, java.lang.Object)
	 */
	@Override
	public Object visitDependsPragma(DependsPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitEscPrimitiveType(escjava.ast.EscPrimitiveType, java.lang.Object)
	 */
	@Override
	public Object visitEscPrimitiveType(EscPrimitiveType x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitEverythingExpr(escjava.ast.EverythingExpr, java.lang.Object)
	 */
	@Override
	public Object visitEverythingExpr(EverythingExpr x, Object o) {
		return visitASTNode(x, o);
	}
	
	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitExprDeclPragma(escjava.ast.ExprDeclPragma, java.lang.Object)
	 */
	@Override
	public Object visitExprDeclPragma(ExprDeclPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitExprModifierPragma(escjava.ast.ExprModifierPragma, java.lang.Object)
	 */
	@Override
	public Object visitExprModifierPragma(ExprModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitExprStmtPragma(escjava.ast.ExprStmtPragma, java.lang.Object)
	 */
	@Override
	public Object visitExprStmtPragma(ExprStmtPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitGCExpr(escjava.ast.GCExpr, java.lang.Object)
	 */
	@Override
	public Object visitGCExpr(GCExpr x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitGhostDeclPragma(escjava.ast.GhostDeclPragma, java.lang.Object)
	 */
	@Override
	public Object visitGhostDeclPragma(GhostDeclPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitGuardExpr(escjava.ast.GuardExpr, java.lang.Object)
	 */
	@Override
	public Object visitGuardExpr(GuardExpr x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitGuardedCmd(escjava.ast.GuardedCmd, java.lang.Object)
	 */
	@Override
	public Object visitGuardedCmd(GuardedCmd x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitIdExprDeclPragma(escjava.ast.IdExprDeclPragma, java.lang.Object)
	 */
	@Override
	public Object visitIdExprDeclPragma(IdExprDeclPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitIdentifierModifierPragma(escjava.ast.IdentifierModifierPragma, java.lang.Object)
	 */
	@Override
	public Object visitIdentifierModifierPragma(IdentifierModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitImportPragma(escjava.ast.ImportPragma, java.lang.Object)
	 */
	@Override
	public Object visitImportPragma(ImportPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitLockSetExpr(escjava.ast.LockSetExpr, java.lang.Object)
	 */
	@Override
	public Object visitLockSetExpr(LockSetExpr x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitMapsExprModifierPragma(escjava.ast.MapsExprModifierPragma, java.lang.Object)
	 */
	@Override
	public Object visitMapsExprModifierPragma(MapsExprModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitModelConstructorDeclPragma(escjava.ast.ModelConstructorDeclPragma, java.lang.Object)
	 */
	@Override
	public Object visitModelConstructorDeclPragma(ModelConstructorDeclPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitModelDeclPragma(escjava.ast.ModelDeclPragma, java.lang.Object)
	 */
	@Override
	public Object visitModelDeclPragma(ModelDeclPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitModelMethodDeclPragma(escjava.ast.ModelMethodDeclPragma, java.lang.Object)
	 */
	@Override
	public Object visitModelMethodDeclPragma(ModelMethodDeclPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitModelProgamModifierPragma(escjava.ast.ModelProgamModifierPragma, java.lang.Object)
	 */
	@Override
	public Object visitModelProgamModifierPragma(ModelProgamModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitModelTypePragma(escjava.ast.ModelTypePragma, java.lang.Object)
	 */
	@Override
	public Object visitModelTypePragma(ModelTypePragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitModifiesGroupPragma(escjava.ast.ModifiesGroupPragma, java.lang.Object)
	 */
	@Override
	public Object visitModifiesGroupPragma(ModifiesGroupPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitNamedExprDeclPragma(escjava.ast.NamedExprDeclPragma, java.lang.Object)
	 */
	@Override
	public Object visitNamedExprDeclPragma(NamedExprDeclPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitNestedModifierPragma(escjava.ast.NestedModifierPragma, java.lang.Object)
	 */
	@Override
	public Object visitNestedModifierPragma(NestedModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitNotModifiedExpr(escjava.ast.NotModifiedExpr, java.lang.Object)
	 */
	@Override
	public Object visitNotModifiedExpr(NotModifiedExpr x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitNotSpecifiedExpr(escjava.ast.NotSpecifiedExpr, java.lang.Object)
	 */
	@Override
	public Object visitNotSpecifiedExpr(NotSpecifiedExpr x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitNothingExpr(escjava.ast.NothingExpr, java.lang.Object)
	 */
	@Override
	public Object visitNothingExpr(NothingExpr x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitNowarnPragma(escjava.ast.NowarnPragma, java.lang.Object)
	 */
	@Override
	public Object visitNowarnPragma(NowarnPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitParsedSpecs(escjava.ast.ParsedSpecs, java.lang.Object)
	 */
	@Override
	public Object visitParsedSpecs(ParsedSpecs x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitReachModifierPragma(escjava.ast.ReachModifierPragma, java.lang.Object)
	 */
	@Override
	public Object visitReachModifierPragma(ReachModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitRefinePragma(escjava.ast.RefinePragma, java.lang.Object)
	 */
	@Override
	public Object visitRefinePragma(RefinePragma x, Object o) {
		return visitASTNode(x, o);
	}
	
	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitResExpr(escjava.ast.ResExpr, java.lang.Object)
	 */
	@Override
	public Object visitResExpr(ResExpr x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitSetCompExpr(escjava.ast.SetCompExpr, java.lang.Object)
	 */
	@Override
	public Object visitSetCompExpr(SetCompExpr x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitSetStmtPragma(escjava.ast.SetStmtPragma, java.lang.Object)
	 */
	@Override
	public Object visitSetStmtPragma(SetStmtPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitSimpleModifierPragma(escjava.ast.SimpleModifierPragma, java.lang.Object)
	 */
	@Override
	public Object visitSimpleModifierPragma(SimpleModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitSimpleStmtPragma(escjava.ast.SimpleStmtPragma, java.lang.Object)
	 */
	@Override
	public Object visitSimpleStmtPragma(SimpleStmtPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitSkolemConstantPragma(escjava.ast.SkolemConstantPragma, java.lang.Object)
	 */
	@Override
	public Object visitSkolemConstantPragma(SkolemConstantPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitSpec(escjava.ast.Spec, java.lang.Object)
	 */
	@Override
	public Object visitSpec(Spec x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitStillDeferredDeclPragma(escjava.ast.StillDeferredDeclPragma, java.lang.Object)
	 */
	@Override
	public Object visitStillDeferredDeclPragma(StillDeferredDeclPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitVarDeclModifierPragma(escjava.ast.VarDeclModifierPragma, java.lang.Object)
	 */
	@Override
	public Object visitVarDeclModifierPragma(VarDeclModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitVarExprModifierPragma(escjava.ast.VarExprModifierPragma, java.lang.Object)
	 */
	@Override
	public Object visitVarExprModifierPragma(VarExprModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.ast.VisitorArgResult#visitWildRefExpr(escjava.ast.WildRefExpr, java.lang.Object)
	 */
	@Override
	public Object visitWildRefExpr(WildRefExpr x, Object o) {
		return visitASTNode(x, o);
	}
}
