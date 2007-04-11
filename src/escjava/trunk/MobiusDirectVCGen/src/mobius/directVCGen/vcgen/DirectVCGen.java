package mobius.directVCGen.vcgen;

import java.util.Vector;

import javafe.ast.ASTNode;
import javafe.ast.BlockStmt;
import javafe.ast.EvalStmt;
import javafe.ast.LocalVarDecl;
import javafe.ast.VarDeclStmt;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.vcgen.intern.ExprResult;
import mobius.directVCGen.vcgen.intern.ExpressionVisitor;
import escjava.ast.ExprStmtPragma;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

public class DirectVCGen extends ExpressionVisitor {
	public final Vector<Term> vcs = new Vector<Term>();
	
	
	@Override
	public /*@non_null*/ Object visitBlockStmt(/*@non_null*/ BlockStmt x, Object o) {		
		int max = x.childCount();
		for(int i = max - 1; i >= 0; i--) {
			Object child = x.childAt(i);
			System.out.println(child);
			if(child instanceof ASTNode) {
				o = ((ASTNode) child).accept(this, o);
			}
		}
		return o;
	}
	
	public Object visitExprStmtPragma(ExprStmtPragma esp, Object o) {
		Term post = (Term) o;
		switch(esp.tag) {
			case TagConstants.ASSERT:
				return vcGenAssert(esp, post);
			default:
				throw new IllegalArgumentException("Unknown construct " + esp);
		}
	}
	public Object visitEvalStmt(EvalStmt esp, Object o) {
		Term post = (Term) o;
		ExprResult er = new ExprResult();
		er.post = post;
		er = (ExprResult)this.visitASTNode(esp, er);
		return er.post;
		
	}

	public Object visitVarDeclStmt(VarDeclStmt stmt, Object o) {
		Term post = (Lifter.Term ) o;
		LocalVarDecl decl = stmt.decl;
		QuantVariableRef v = Expression.var(decl.id.toString());
		
		ExprResult er = new ExprResult();
		er.post = post;
		ExprResult init = (ExprResult) decl.init.accept(this, er);
		
		return null; //init.post.subst(v, init.res);
	}
	
	
	
	


	public Term vcGenAssert(ExprStmtPragma stmtAssert, Term post) {
		ExprResult er = new ExprResult();
		er.post = post;
		ExprResult as = getAssert(stmtAssert, er);
		return null; //Logic.and(Logic.boolToProp(as.res), Logic.implies(Logic.boolToProp(as.res), as.post));
	}
	
	private ExprResult getAssert(ExprStmtPragma esp, ExprResult post) {
		return (ExprResult) visitASTNode(esp, post);
	}
}
