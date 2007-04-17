package mobius.directVCGen.formula.jmlTranslator;

import javafe.ast.ASTNode;
import javafe.ast.BinaryExpr;
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
import escjava.ast.TagConstants;
import escjava.ast.VarDeclModifierPragma;
import escjava.ast.VarExprModifierPragma;
import escjava.ast.VisitorArgResult;
import escjava.ast.WildRefExpr;

public class JmlVisitor extends VisitorArgResult{

	JmlExprToFormula translator;
	
	public JmlVisitor(){
		translator = new JmlExprToFormula(this);
	}
	
	@Override
	public Object visitAnOverview(AnOverview x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitArrayRangeRefExpr(ArrayRangeRefExpr x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitCondExprModifierPragma(CondExprModifierPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitCondition(Condition x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitDecreasesInfo(DecreasesInfo x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitDefPred(DefPred x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitDefPredApplExpr(DefPredApplExpr x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitDefPredLetExpr(DefPredLetExpr x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitDependsPragma(DependsPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitEscPrimitiveType(EscPrimitiveType x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitEverythingExpr(EverythingExpr x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitExprDeclPragma(ExprDeclPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitExprModifierPragma(ExprModifierPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitExprStmtPragma(ExprStmtPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitGCExpr(GCExpr x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitGhostDeclPragma(GhostDeclPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitGuardExpr(GuardExpr x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitGuardedCmd(GuardedCmd x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitIdExprDeclPragma(IdExprDeclPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitIdentifierModifierPragma(IdentifierModifierPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitImportPragma(ImportPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitLockSetExpr(LockSetExpr x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitMapsExprModifierPragma(MapsExprModifierPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitModelConstructorDeclPragma(ModelConstructorDeclPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitModelDeclPragma(ModelDeclPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitModelMethodDeclPragma(ModelMethodDeclPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitModelProgamModifierPragma(ModelProgamModifierPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitModelTypePragma(ModelTypePragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitModifiesGroupPragma(ModifiesGroupPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitNamedExprDeclPragma(NamedExprDeclPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitNestedModifierPragma(NestedModifierPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitNotModifiedExpr(NotModifiedExpr x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitNotSpecifiedExpr(NotSpecifiedExpr x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitNothingExpr(NothingExpr x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitNowarnPragma(NowarnPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitParsedSpecs(ParsedSpecs x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitReachModifierPragma(ReachModifierPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitRefinePragma(RefinePragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitResExpr(ResExpr x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitSetCompExpr(SetCompExpr x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitSetStmtPragma(SetStmtPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitSimpleModifierPragma(SimpleModifierPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitSimpleStmtPragma(SimpleStmtPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitSkolemConstantPragma(SkolemConstantPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitSpec(Spec x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitStillDeferredDeclPragma(StillDeferredDeclPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitVarDeclModifierPragma(VarDeclModifierPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitVarExprModifierPragma(VarExprModifierPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitWildRefExpr(WildRefExpr x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitASTNode(ASTNode x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}
	
	public Object visitBinaryExpr(BinaryExpr expr, Object o){
	
		switch(expr.op) {
		case TagConstants.EQ:
		case TagConstants.OR:
		case TagConstants.AND:
		case TagConstants.NE:
		case TagConstants.GE:
		case TagConstants.GT:
		case TagConstants.LE:
		case TagConstants.LT:
		case TagConstants.BITOR:
		case TagConstants.BITXOR:
		case TagConstants.BITAND:
		case TagConstants.LSHIFT:
		case TagConstants.RSHIFT:
		case TagConstants.URSHIFT:
		case TagConstants.ADD:
			return translator.add(expr);
		case TagConstants.SUB:
		case TagConstants.DIV:
		case TagConstants.MOD:
		case TagConstants.STAR:

		case TagConstants.ASSIGN:

		case TagConstants.ASGMUL:
		case TagConstants.ASGDIV:
		case TagConstants.ASGREM:
		case TagConstants.ASGADD:
		case TagConstants.ASGSUB:
		case TagConstants.ASGLSHIFT:
		case TagConstants.ASGRSHIFT:
		case TagConstants.ASGURSHIFT:
		case TagConstants.ASGBITAND:
	// jml specific operators
		case TagConstants.IMPLIES:
		case TagConstants.EXPLIES:
		case TagConstants.IFF: // equivalence (equality)
		case TagConstants.NIFF:     // discrepance (xor)
		case TagConstants.SUBTYPE:
		case TagConstants.DOTDOT:

		default:
			throw new IllegalArgumentException("Unknown construct :" +
					TagConstants.toString(expr.op) +" " +  expr);
		}		
	}

}
