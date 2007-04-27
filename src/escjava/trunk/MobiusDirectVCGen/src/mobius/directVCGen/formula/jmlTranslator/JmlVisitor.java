package mobius.directVCGen.formula.jmlTranslator;

import mobius.directVCGen.formula.*;

import java.util.Properties;

import sun.misc.Sort;
import javafe.ast.ASTNode;
import javafe.ast.BinaryExpr;
import javafe.ast.FieldAccess;
import javafe.ast.InstanceOfExpr;
import javafe.ast.JavafePrimitiveType;
import javafe.ast.LiteralExpr;
import javafe.ast.ThisExpr;
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
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;


public class JmlVisitor extends VisitorArgResult{

	JmlExprToFormula translator;
	
	public JmlVisitor(){
		translator = new JmlExprToFormula(this);
	}
	
	
	public Object visitASTNode(ASTNode x, Object prop) {
		Object o = null;
		int max = x.childCount();
		for(int i = 0; i < max; i++) {
			Object child = x.childAt(i);
			if(child instanceof ASTNode) {
				o = ((ASTNode) child).accept(this, prop);
				if (o != null)
				{
					if (!o.equals(child))
					{
						System.out.println( o.toString());
						//System.out.println( o.toString() + " " + x.getClass().getName());
						
					}
				}
			}
			
		}
		return o;
	}
	
	@Override
	public Object visitAnOverview(AnOverview x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}
	
	 public /*@non_null*/ Object visitLiteralExpr(/*@non_null*/ LiteralExpr x, Object o) {
		return translator.lit(x,o);
	}
	 
	 
	 
	 public /*@non_null*/ Object visitVariableAccess(/*@non_null*/ VariableAccess x, Object o) {		 
		 Boolean oldProp = (Boolean) ((Properties) o).get("old");
		 Boolean predProp = (Boolean) ((Properties)o).get("pred");
		 String id = (String) x.id.toString();
		 int tag = ((JavafePrimitiveType) x.getDecorations()[1]).tag;
		 
		 if(oldProp.booleanValue())
		 {
			 id += "Pre"; 
		 }
		 
		 switch(tag)
		 {
		 case TagConstants.BOOLEANTYPE: 
			 if (predProp.booleanValue())
				 return Expression.rvar(id, Logic.sort);
			 else
				 return Expression.rvar(id, Bool.sort);
		 case TagConstants.CHARTYPE: 
		 case TagConstants.VOIDTYPE:
		 case TagConstants.NULLTYPE:
		 case TagConstants.BYTETYPE:
		 case TagConstants.SHORTTYPE:
		 case TagConstants.INTTYPE: return Expression.rvar(id, Num.sortInt); 
		 case TagConstants.LONGTYPE:
		 case TagConstants.FLOATTYPE:return Expression.rvar(id, Num.sortReal);
		 case TagConstants.DOUBLETYPE:
		 default: throw new IllegalArgumentException("The sort " + tag + " is illegal.");
		 }
	}
	 
	 
	 public /*@non_null*/ Object visitFieldAccess(/*@non_null*/ FieldAccess x, Object o) {		 
		 Boolean oldProp = (Boolean) ((Properties) o).get("old");
		 Boolean predProp = (Boolean) ((Properties)o).get("pred");
		 String idObj = x.decl.parent.id.toString(); 
		 String idVar = (String) x.id.toString(); 
		 QuantVariableRef heap = Heap.var;
		 QuantVariableRef obj;
		 QuantVariable var;
		 int tag = ((JavafePrimitiveType) x.getDecorations()[1]).tag;
		 
		 if(oldProp.booleanValue())
		 {
			 idObj += "Pre";
			 heap = Heap.varPre;
		 }
				 
		 switch(tag)
		 {
		 case TagConstants.BOOLEANTYPE: 
			 if (predProp.booleanValue())
				 var = Expression.var(idVar, Logic.sort);
			 else
				 var = Expression.var(idVar, Bool.sort);
			 break;
		 case TagConstants.CHARTYPE: 
		 case TagConstants.VOIDTYPE:
		 case TagConstants.NULLTYPE:
		 case TagConstants.BYTETYPE:
		 case TagConstants.SHORTTYPE:
		 case TagConstants.INTTYPE: 
			 var = Expression.var(idVar, Num.sortInt); break;
		 case TagConstants.LONGTYPE:
		 case TagConstants.FLOATTYPE:
			 var = Expression.var(idVar, Num.sortReal); break;
		 case TagConstants.DOUBLETYPE:
		 default: 
			 throw new IllegalArgumentException("The sort of " + tag + " is illegal.");
		 }
		 obj =  Expression.rvar(idObj, Ref.sort);
		 return Heap.select(heap, obj, var);
	}
	 
	 
	 
	 
	 public /*@non_null*/ Object visitNaryExpr(/*@non_null*/ NaryExpr x, Object o) {		 
		 if (x.op== TagConstants.PRE)
			 ((Properties) o).put("old",true); 
		 return visitGCExpr(x, o);
	}
	 

	 public /*@non_null*/ Object visitInstanceOfExpr(/*@non_null*/ InstanceOfExpr x, Object o) {
		return translator.instanceOfExpr(x, o);
	 }
	 
	 public Object  visitThisExpr(ThisExpr x, Object o) {
		return Ref.varthis;
		}
	 
	
	 
	@Override
	public Object visitArrayRangeRefExpr(ArrayRangeRefExpr x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitCondExprModifierPragma(CondExprModifierPragma x, Object o) {
		// TODO Auto-generated method stub
		//return null;
		return visitASTNode(x, o);
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
		//return null;
		return visitASTNode(x, o);
	}

	@Override
	public Object visitExprDeclPragma(ExprDeclPragma x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	
	public Object visitExprModifierPragma(ExprModifierPragma x, Object o) {
		return visitASTNode(x, o);
	}

	@Override
	public Object visitExprStmtPragma(ExprStmtPragma x, Object o) {
		// TODO Auto-generated method stub
		return visitASTNode(x, o);
	}

	public Object visitGCExpr(GCExpr x, Object o) {
		return visitASTNode(x, o);
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
		//return null;
		return visitASTNode(x, o);
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
		//return null;
		return visitASTNode(x, o);
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
		//return visitASTNode(x, o); //generates a stack overflow... but should be used
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
		return translator.res(x,o);
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
		return visitASTNode(x, o); 
	}

	@Override
	public Object visitWildRefExpr(WildRefExpr x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	
	
	public Object visitBinaryExpr(BinaryExpr expr, Object o){
	
		switch(expr.op) {
		case TagConstants.EQ: 
			return translator.eq(expr, o);
		case TagConstants.OR: 
			return translator.or(expr, o);
		case TagConstants.AND: 
			return translator.and(expr, o);
		case TagConstants.NE:
			return translator.ne(expr, o);
		case TagConstants.GE: 
			return translator.ge(expr, o);
		case TagConstants.GT: 
			return translator.gt(expr, o);
		case TagConstants.LE: 
			return translator.le(expr, o);
		case TagConstants.LT:  
			return translator.lt(expr, o);
		case TagConstants.BITOR: 
			return translator.bitor(expr, o);
		case TagConstants.BITXOR: 
			return translator.bitxor(expr, o);
		case TagConstants.BITAND: 
			return translator.bitand(expr, o);
		case TagConstants.LSHIFT:
			return translator.lshift(expr, o);
		case TagConstants.RSHIFT: 
			return translator.rshift(expr, o);
		case TagConstants.URSHIFT:
			return translator.urshift(expr, o);
		case TagConstants.ADD: 
			return translator.add(expr, o);
		case TagConstants.SUB: 
			return translator.sub(expr, o);
		case TagConstants.DIV: 
			return translator.div(expr, o);
		case TagConstants.MOD: 
			return translator.mod(expr, o);
		case TagConstants.STAR: 
			return translator.star(expr, o);
		case TagConstants.ASSIGN:
			return translator.assign(expr, o);
		case TagConstants.ASGMUL: 
			return translator.asgmul(expr, o);
		case TagConstants.ASGDIV: 
			return translator.asgdiv(expr, o);
		case TagConstants.ASGREM: 
			return translator.asgrem(expr, o);
		case TagConstants.ASGADD: 
			return translator.asgadd(expr, o);
		case TagConstants.ASGSUB: 
			return translator.asgsub(expr, o);
		case TagConstants.ASGLSHIFT: 
			return translator.asglshift(expr, o);
		case TagConstants.ASGRSHIFT: 
			return translator.asgrshift(expr, o);
		case TagConstants.ASGURSHIFT: 
			return translator.asgurshif(expr, o);
		case TagConstants.ASGBITAND: 
			return translator.asgbitand(expr, o);
	// jml specific operators 
		case TagConstants.IMPLIES: 
			return translator.implies(expr, o);
		case TagConstants.EXPLIES:
			return translator.explies(expr, o);
		case TagConstants.IFF: // equivalence (equality)
			return translator.iff(expr, o);
		case TagConstants.NIFF:    // discrepance (xor)
			return translator.niff(expr, o);
		case TagConstants.SUBTYPE: 
			return translator.subtype(expr, o);
		case TagConstants.DOTDOT: 
			return translator.dotdot(expr, o);

		default:
			throw new IllegalArgumentException("Unknown construct :" +
					TagConstants.toString(expr.op) +" " +  expr);
		}		
	}

}
