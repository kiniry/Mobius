package mobius.directVCGen.vcgen;

import java.util.Vector;

import javafe.ast.ASTNode;
import javafe.ast.AssertStmt;
import javafe.ast.BlockStmt;
import javafe.ast.BranchStmt;
import javafe.ast.BreakStmt;
import javafe.ast.CatchClause;
import javafe.ast.ClassDeclStmt;
import javafe.ast.ConstructorInvocation;
import javafe.ast.ContinueStmt;
import javafe.ast.DoStmt;
import javafe.ast.EvalStmt;
import javafe.ast.ForStmt;
import javafe.ast.GenericBlockStmt;
import javafe.ast.IfStmt;
import javafe.ast.LabelStmt;
import javafe.ast.LocalVarDecl;
import javafe.ast.ReturnStmt;
import javafe.ast.SkipStmt;
import javafe.ast.Stmt;
import javafe.ast.StmtPragma;
import javafe.ast.SwitchLabel;
import javafe.ast.SwitchStmt;
import javafe.ast.SynchronizeStmt;
import javafe.ast.ThrowStmt;
import javafe.ast.TryCatchStmt;
import javafe.ast.TryFinallyStmt;
import javafe.ast.VarDeclStmt;
import javafe.ast.WhileStmt;
import javafe.ast.Stmt.Annotation;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.annotation.AAnnotation;
import mobius.directVCGen.vcgen.intern.VCEntry;
import mobius.directVCGen.vcgen.intern.ExpressionVisitor;
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
import escjava.ast.WildRefExpr;
import escjava.sortedProver.Lifter;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

public class DirectVCGen extends ExpressionVisitor {
	public final Vector<Term> vcs = new Vector<Term>();
	
	public Term treatAnnot(Term post, Annotation annot) {
		return post;
	}
	
	@Override
	public /*@non_null*/ Object visitBlockStmt(/*@non_null*/ BlockStmt x, Object o) {		
		int max = x.childCount();
		Term post = treatAnnot( (Term) o, x.annotPost);
		
		for(int i = max - 1; i >= 0; i--) {
			Object child = x.childAt(i);
			System.out.println(child);
			if(child instanceof ASTNode) {
				post = (Term) ((ASTNode) child).accept(this, post);
			}
		}
		post = treatAnnot( post, x.annotPre);
		return post;
	}	
	
	@Override
	public Object visitStmt(Stmt x, Object o){
		throw new IllegalArgumentException("Not yet implememented");
	}
	
	public /*@non_null*/ Object visitSwitchStmt(/*@non_null*/ SwitchStmt x, Object o) {
		return visitStmt(x, o);
	}	

	public /*@non_null*/ Object visitAssertStmt(/*@non_null*/ AssertStmt x, Object o) {
		return visitStmt(x, o);
	}

	public /*@non_null*/ Object visitVarDeclStmt(/*@non_null*/ VarDeclStmt x, Object o) {
		return visitStmt(x, o);
	}

	public /*@non_null*/ Object visitWhileStmt(/*@non_null*/ WhileStmt x, Object o) {
		Term post = treatAnnot( (Term) o, x.annotPost);
		AAnnotation annotPre = (AAnnotation)x.annotPre;
		Term inv = annotPre.formula;
		Term bodypre = (Term) x.stmt.accept(this, inv);
		VCEntry r = new VCEntry();
		QuantVariableRef v = Expression.var("bool");
//		r.var = v;
//		r.post = 
//		  Logic.and(Logic.implies(Logic.boolToProp(v), bodypre),
//				    Logic.implies(Logic.not(Logic.boolToProp(v)), post));
//		Term aux = ((VCEntry) x.expr.accept(this, r)).post;
//		vcs.add(Logic.implies(inv, aux));  
		return inv;
	}

	public /*@non_null*/ Object visitDoStmt(/*@non_null*/ DoStmt x, Object o) {
		return visitStmt(x, o);
	}

	public /*@non_null*/ Object visitSynchronizeStmt(/*@non_null*/ SynchronizeStmt x, Object o) {
		return visitStmt(x, o);
	}

	public /*@non_null*/ Object visitEvalStmt(/*@non_null*/ EvalStmt x, Object o) {
		Term post = treatAnnot( (Term) o, x.annotPost);
		VCEntry r = new VCEntry();
//		r.post = post;
//		post = ((VCEntry)x.expr.accept(this, r)).post;
		return treatAnnot(post, x.annotPre);
	}

	public /*@non_null*/ Object visitReturnStmt(/*@non_null*/ ReturnStmt x, Object o) {
		// Goog to ensure that x.annotPost == Null
		// and so remove this line
		Term post = treatAnnot((Term) o, x.annotPost);
		VCEntry r = new VCEntry();
//		r.post = post;
//		r.var = Expression.var("result");
//		post=((VCEntry) x.expr.accept(this, r)).post;
		return treatAnnot(post, x.annotPre);
	}	

		  public /*@non_null*/ Object visitThrowStmt(/*@non_null*/ ThrowStmt x, Object o) {
		    return visitStmt(x, o);
		  }

		  public /*@non_null*/ Object visitBranchStmt(/*@non_null*/ BranchStmt x, Object o) {
		    return visitStmt(x, o);
		  }

		  public /*@non_null*/ Object visitBreakStmt(/*@non_null*/ BreakStmt x, Object o) {
		    return visitBranchStmt(x, o);
		  }

		  public /*@non_null*/ Object visitContinueStmt(/*@non_null*/ ContinueStmt x, Object o) {
		    return visitBranchStmt(x, o);
		  }

		  public /*@non_null*/ Object visitLabelStmt(/*@non_null*/ LabelStmt x, Object o) {
		    return visitStmt(x, o);
		  }

		  public /*@non_null*/ Object visitIfStmt(/*@non_null*/ IfStmt x, Object o) {
		    return visitStmt(x, o);
		  }

		  public /*@non_null*/ Object visitForStmt(/*@non_null*/ ForStmt x, Object o) {
		    return visitStmt(x, o);
		  }

		  public /*@non_null*/ Object visitSkipStmt(/*@non_null*/ SkipStmt x, Object o) {
		    return visitStmt(x, o);
		  }

		  public /*@non_null*/ Object visitSwitchLabel(/*@non_null*/ SwitchLabel x, Object o) {
		    return visitStmt(x, o);
		  }

		  public /*@non_null*/ Object visitTryFinallyStmt(/*@non_null*/ TryFinallyStmt x, Object o) {
		    return visitStmt(x, o);
		  }

		  public /*@non_null*/ Object visitTryCatchStmt(/*@non_null*/ TryCatchStmt x, Object o) {
		    return visitStmt(x, o);
		  }

		  public /*@non_null*/ Object visitStmtPragma(/*@non_null*/ StmtPragma x, Object o) {
		    return visitStmt(x, o);
		  }

		  public /*@non_null*/ Object visitConstructorInvocation(/*@non_null*/ ConstructorInvocation x, Object o) {
		    return visitStmt(x, o);
		  }

		  public /*@non_null*/ Object visitCatchClause(/*@non_null*/ CatchClause x, Object o) {
		    return visitASTNode(x, o);
		  }
}
