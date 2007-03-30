package mobius.directVCGen.vcgen;

import java.util.Vector;

import javafe.ast.ASTNode;
import javafe.ast.BlockStmt;
import javafe.ast.EvalStmt;
import javafe.ast.LocalVarDecl;
import javafe.ast.VarDeclStmt;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.expression.Expression;
import mobius.directVCGen.formula.expression.Variable;
import mobius.directVCGen.formula.logic.Logic;
import mobius.directVCGen.vcgen.intern.ExprResult;
import mobius.directVCGen.vcgen.intern.ExpressionVisitor;
import mobius.directVCGen.vcgen.intern.TypeVisitor;
import escjava.ast.ExprStmtPragma;
import escjava.ast.TagConstants;

public class DirectVCGen extends ExpressionVisitor {
	public final Vector<IFormula> vcs = new Vector<IFormula>();
	
	
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
		IFormula post = (IFormula) o;
		switch(esp.tag) {
			case TagConstants.ASSERT:
				return vcGenAssert(esp, post);
			default:
				throw new IllegalArgumentException("Unknown construct " + esp);
		}
	}
	public Object visitEvalStmt(EvalStmt esp, Object o) {
		IFormula post = (IFormula) o;
		ExprResult er = new ExprResult();
		er.post = post;
		er = (ExprResult)this.visitASTNode(esp, er);
		return er.post;
		
	}

	public Object visitVarDeclStmt(VarDeclStmt stmt, Object o) {
		IFormula post = (IFormula) o;
		LocalVarDecl decl = stmt.decl;
		Variable v = Expression.var(decl.id.toString(), TypeVisitor.convert2Type(decl.type));
		ExprResult er = new ExprResult();
		er.post = post;
		ExprResult init = (ExprResult) decl.init.accept(this, er);
		
		return init.post.subst(v, init.res);
	}
	
	
	
	


	public IFormula vcGenAssert(ExprStmtPragma stmtAssert, IFormula post) {
		ExprResult er = new ExprResult();
		er.post = post;
		ExprResult as = getAssert(stmtAssert, er);
		return Logic.and(Logic.boolToProp(as.res), Logic.implies(Logic.boolToProp(as.res), as.post));
	}
	
	private ExprResult getAssert(ExprStmtPragma esp, ExprResult post) {
		return (ExprResult) visitASTNode(esp, post);
	}
}
