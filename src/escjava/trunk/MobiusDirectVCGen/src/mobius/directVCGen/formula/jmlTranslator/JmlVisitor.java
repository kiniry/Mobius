package mobius.directVCGen.formula.jmlTranslator;

import mobius.directVCGen.formula.*;
import mobius.directVCGen.formula.annotation.AAnnotation;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;
import mobius.directVCGen.formula.annotation.Assume;
import mobius.directVCGen.formula.annotation.Cut;
import mobius.directVCGen.formula.annotation.Set;
import mobius.directVCGen.vcgen.struct.Post;

import java.util.Properties;
import java.util.Vector;
import javafe.ast.ASTNode;
import javafe.ast.BinaryExpr;
import javafe.ast.BlockStmt;
import javafe.ast.ClassDecl;
import javafe.ast.ConstructorDecl;
import javafe.ast.DoStmt;
import javafe.ast.FieldAccess;
import javafe.ast.ForStmt;
import javafe.ast.FormalParaDecl;
import javafe.ast.IfStmt;
import javafe.ast.InstanceOfExpr;
import javafe.ast.LiteralExpr;
import javafe.ast.LocalVarDecl;
import javafe.ast.MethodDecl;
import javafe.ast.ModifierPragma;
import javafe.ast.RoutineDecl;
import javafe.ast.Stmt;
import javafe.ast.ThisExpr;
import javafe.ast.TryCatchStmt;
import javafe.ast.VarDeclStmt;
import javafe.ast.VariableAccess;
import javafe.ast.WhileStmt;
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
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;


public class JmlVisitor extends VisitorArgResult{

	JmlExprToFormula translator;
	Properties p;
	
	
	public JmlVisitor(){
		p = new Properties();
		p.put("pred", new Boolean(true));
		p.put("old", new Boolean(false));
		p.put("interesting", new Boolean(false));
		translator = new JmlExprToFormula(this);
	}
	
	@Override
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
	public /*@non_null*/ Object visitClassDecl(/*@non_null*/ ClassDecl x, Object o) {
		//Use default properties to start with.
		return visitTypeDecl(x, p);
	}
	
	@Override
	public /*@non_null*/ Object visitMethodDecl(/*@non_null*/ MethodDecl x, Object o) {
		((Properties) o).put("result", Expression.rvar(Expression.result,Type.getReturnType(x)));
		((Properties) o).put("method", x);
		((Properties) o).put("routinebegin", new Boolean(true));
		return visitRoutineDecl(x, o);
	}
	
	@Override
	public /*@non_null*/ Object visitConstructorDecl(/*@non_null*/ ConstructorDecl x, Object o) {
		((Properties) o).put("method", x);
		((Properties) o).put("routinebegin", new Boolean(true));
		return visitRoutineDecl(x, o);
	}
	
	@Override
	public /*@non_null*/ Object visitFormalParaDecl(/*@non_null*/ FormalParaDecl x, Object o) {
		return translator.genericVarDecl(x,o);
	}
	
	@Override
	public Object visitAnOverview(AnOverview x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	 public /*@non_null*/ Object visitLiteralExpr(/*@non_null*/ LiteralExpr x, Object o) {
		if (((Boolean) ((Properties) o).get("interesting")).booleanValue())
			return translator.literal(x,o);
		else
			return null;
	}
	 
	 
	 @Override
	 public /*@non_null*/ Object visitVariableAccess(/*@non_null*/ VariableAccess x, Object o) {		 
		if (((Boolean) ((Properties) o).get("interesting")).booleanValue())
			return translator.variableAccess(x,o);
		else 
			return null;
	}
	 
	 @Override
	 public /*@non_null*/ Object visitFieldAccess(/*@non_null*/ FieldAccess x, Object o) {		 
		if (((Boolean) ((Properties) o).get("interesting")).booleanValue())
			return translator.fieldAccess(x,o);
		else
			return null;
	}
	 
	 @Override
	 public /*@non_null*/ Object visitLocalVarDecl(/*@non_null*/ LocalVarDecl x, Object o) {
		 //TODO: do something meaningfull.
		 return null;
	 }
	 
	 @Override
	 public /*@non_null*/ Object visitNaryExpr(/*@non_null*/ NaryExpr x, Object o) {
		if (((Boolean) ((Properties) o).get("interesting")).booleanValue()){
			 if (x.op== TagConstants.PRE) {
				 return translator.naryExpr(x,o);
			 } else {
				 return visitGCExpr(x, o);
			 }
		} else
			return null;
	}
	 
	 @Override
	 public /*@non_null*/ Object visitInstanceOfExpr(/*@non_null*/ InstanceOfExpr x, Object o) {
		if (((Boolean) ((Properties) o).get("interesting")).booleanValue())
			return translator.instanceOfExpr(x, o);
		else
			return null;
	 }
	 
	 @Override
	 public Object  visitThisExpr(ThisExpr x, Object o) {
		if (((Boolean) ((Properties) o).get("interesting")).booleanValue())
			return translator.thisLiteral(x,o);
		else
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

	@Override
	public Object visitExprModifierPragma(ExprModifierPragma x, Object o) {
		((Properties) o).put("interesting", new Boolean(true));
		RoutineDecl rd = (RoutineDecl)((Properties) o).get("method");
		QuantVariableRef result = (QuantVariableRef)((Properties) o).get("result");
		Term t = (Term)visitASTNode(x, o);
		switch (x.getTag()){
		case TagConstants.REQUIRES:
			Lookup.preconditions.put(rd, t);
			break;
		case TagConstants.ENSURES:
			Lookup.postconditions.put(rd, new Post(result, t));
			break;
		}
		return null;
	}

	@Override
    public /*@non_null*/ Object visitBlockStmt(/*@non_null*/ BlockStmt x, Object o) {
	    Term t=null;
	    Term t1=null;
	    Term t2=null;
		Set  set=null;
		Set.Assignment assignment=null;
	    boolean interesting;
		Vector<AAnnotation> annos = new Vector<AAnnotation>();
		Term inv = null;
		
		//Save arguments values in prestate as ghosts.
		if (((Boolean)((Properties) o).get("routinebegin")).booleanValue()){
			((Properties) o).put("routinebegin", new Boolean(false));
			RoutineDecl m = (RoutineDecl) ((Properties) o).get("method");
			for(FormalParaDecl p: m.args.toArray()){
				 t1 = Expression.rvar(p);
				 t2 = Expression.old(p);
				 assignment = new Set.Assignment((QuantVariableRef) t2, t1);
				 annos.add(new Set((QuantVariableRef) t2, assignment)); 
			}
		}
		
		//
	    for(Stmt s: x.stmts.toArray()){
	    	interesting = false;
	    	//We are interested in Asserts, Assumes and Loop Invariants
	    	if (s instanceof ExprStmtPragma){
	    		interesting = true; 
	    		((Properties) o).put("interesting", new Boolean(true));
	    		t = (Term)s.accept(this, o);
	    		switch (s.getTag()){
	    		case TagConstants.ASSERT:
	    			annos.add(new Cut(t));
	    			break;
	    		case TagConstants.ASSUME:
	    			annos.add(new Assume(t));
	    			break;
	    		case TagConstants.LOOP_INVARIANT:
	    		case TagConstants.MAINTAINING:
	    			inv = t;
	    			break;
	    		}
	    	} else
	    	
	    	//We are also interested in ghost var declarations
	    	if (s instanceof VarDeclStmt){
	    		
	    		for (ModifierPragma p: ((VarDeclStmt) s).decl.pmodifiers.toArray()){
	    			if (p.getTag() == TagConstants.GHOST) {
	    				interesting = true;
	    				break;
	    			}
	    		}
	    		if (interesting){
	    			((Properties) o).put("interesting", new Boolean(true));
	    			t = (Term)s.accept(this, o);
	    			Set ghostVar = new Set();
	    			ghostVar.declaration = (QuantVariableRef) t;
	    			annos.add(ghostVar);
	    		}
	    	} else
	    	
	    	//Also set statements should be processed
	    	if (s instanceof SetStmtPragma) {
	    		interesting = true;
	    		((Properties) o).put("interesting", new Boolean(true));
	    		assignment = (Set.Assignment)s.accept(this, o);
	    		set = new Set();
	    		set.assignment = assignment;
	    		annos.add(set);
	    	}
	    	
	    	if (interesting){
    			x.stmts.removeElement(s);
	    	} else {
	    		((Properties) o).put("interesting", new Boolean(false));
	    		if (!annos.isEmpty()){
	    			AnnotationDecoration.inst.setAnnotPre(s, annos);
	    			annos.clear();
	    		}
	    		if (inv != null){
	    			if (s instanceof WhileStmt || 
	    					s instanceof ForStmt || 
	    					s instanceof DoStmt){
	    				AnnotationDecoration.inst.setInvariant(s, inv);
	    				inv = null;
	    			}
	    		}	
	    		if (s instanceof WhileStmt || 
    					s instanceof ForStmt || 
    					s instanceof DoStmt || 
    					s instanceof BlockStmt || 
    					s instanceof TryCatchStmt ||
    					s instanceof IfStmt){
    				s.accept(this,o);
    			}	
	    	}
	    }
		return null;
    }	

	@Override
	public /*@non_null*/ Object visitVarDeclStmt(/*@non_null*/ VarDeclStmt x, Object o) {
		//It's only called if we have a ghost variable declaration
		return Expression.rvar(x.decl);
	}	
	
	@Override
	public Object visitExprStmtPragma(ExprStmtPragma x, Object o) {
		// TODO Auto-generated method stub
		return visitASTNode(x, o);
	}

	@Override
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
		if (((Boolean) ((Properties) o).get("interesting")).booleanValue())
			return translator.resultLiteral(x,o);
		else
			return null;
	}

	@Override
	public Object visitSetCompExpr(SetCompExpr x, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object visitSetStmtPragma(SetStmtPragma x, Object o) {
		Set.Assignment res = new Set.Assignment();
		res.var = (QuantVariableRef) x.target.accept(this, o);
		res.expr = (Term) x.value.accept(this,0);
		return res;
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

	
	@Override
	public Object visitBinaryExpr(BinaryExpr expr, Object o){
		if (((Boolean) ((Properties) o).get("interesting")).booleanValue()){
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
		} else
			return null;
	}

}
