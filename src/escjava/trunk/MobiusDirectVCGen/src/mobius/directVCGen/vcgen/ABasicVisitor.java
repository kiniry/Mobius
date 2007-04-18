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

public abstract class ABasicVisitor extends VisitorArgResult{

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
	@Override
	public Object visitAnOverview(AnOverview x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitArrayRangeRefExpr(ArrayRangeRefExpr x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitCondExprModifierPragma(CondExprModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitCondition(Condition x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitDecreasesInfo(DecreasesInfo x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitDefPred(DefPred x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitDefPredApplExpr(DefPredApplExpr x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitDefPredLetExpr(DefPredLetExpr x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitDependsPragma(DependsPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitEscPrimitiveType(EscPrimitiveType x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitEverythingExpr(EverythingExpr x, Object o) {
		return visitASTNode(x, o);
	}
	
	@Override
	public Object visitExprDeclPragma(ExprDeclPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitExprModifierPragma(ExprModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitExprStmtPragma(ExprStmtPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitGCExpr(GCExpr x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitGhostDeclPragma(GhostDeclPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitGuardExpr(GuardExpr x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitGuardedCmd(GuardedCmd x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitIdExprDeclPragma(IdExprDeclPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitIdentifierModifierPragma(IdentifierModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitImportPragma(ImportPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitLockSetExpr(LockSetExpr x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitMapsExprModifierPragma(MapsExprModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitModelConstructorDeclPragma(ModelConstructorDeclPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitModelDeclPragma(ModelDeclPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitModelMethodDeclPragma(ModelMethodDeclPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitModelProgamModifierPragma(ModelProgamModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitModelTypePragma(ModelTypePragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitModifiesGroupPragma(ModifiesGroupPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitNamedExprDeclPragma(NamedExprDeclPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitNestedModifierPragma(NestedModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitNotModifiedExpr(NotModifiedExpr x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitNotSpecifiedExpr(NotSpecifiedExpr x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitNothingExpr(NothingExpr x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitNowarnPragma(NowarnPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitParsedSpecs(ParsedSpecs x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitReachModifierPragma(ReachModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitRefinePragma(RefinePragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitResExpr(ResExpr x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitSetCompExpr(SetCompExpr x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitSetStmtPragma(SetStmtPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitSimpleModifierPragma(SimpleModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitSimpleStmtPragma(SimpleStmtPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitSkolemConstantPragma(SkolemConstantPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitSpec(Spec x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitStillDeferredDeclPragma(StillDeferredDeclPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitVarDeclModifierPragma(VarDeclModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitVarExprModifierPragma(VarExprModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitWildRefExpr(WildRefExpr x, Object o) {
		return visitASTNode(x, o);
	}



}
