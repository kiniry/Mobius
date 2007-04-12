package mobius.directVCGen.vcgen;

import java.util.Iterator;
import java.util.Vector;

import javafe.ast.ASTNode;
import javafe.ast.AssertStmt;
import javafe.ast.BlockStmt;
import javafe.ast.BranchStmt;
import javafe.ast.BreakStmt;
import javafe.ast.CatchClause;
import javafe.ast.ConstructorInvocation;
import javafe.ast.ContinueStmt;
import javafe.ast.DoStmt;
import javafe.ast.EvalStmt;
import javafe.ast.ForStmt;
import javafe.ast.IfStmt;
import javafe.ast.LabelStmt;
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
import javafe.ast.Type;
import javafe.ast.VarDeclStmt;
import javafe.ast.WhileStmt;
import javafe.ast.Stmt.Annotation;
import javafe.tc.FlowInsensitiveChecks;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.annotation.AAnnotation;
import mobius.directVCGen.vcgen.intern.ExpressionVisitor;
import mobius.directVCGen.vcgen.intern.VCEntry;
import mobius.directVCGen.vcgen.intern.VCEntry.ExcpPost;
import mobius.directVCGen.vcgen.intern.VCEntry.Post;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.tc.Types;

public class DirectVCGen extends ExpressionVisitor {
	/** the side conditions that were generated */
	public final Vector<Term> vcs = new Vector<Term>();
	/** the visitor to visit expressions */
	public final ExpressionVisitor exprVisitor = new ExpressionVisitor();
	
	/**
	 * The method to treat the annotations
	 * @param post the current post condition 
	 * @param annot the annotation to treat
	 * @return a postcondition computed from the annotation
	 */
	public VCEntry treatAnnot(VCEntry post, Annotation annot) {
		return post;
	}
	
	public /*@non_null*/ Object visitAssertStmt(/*@non_null*/ AssertStmt x, Object o) {
		return illegalStmt(x, o);
	}
	
	@Override
	public /*@non_null*/ Object visitBlockStmt(/*@non_null*/ BlockStmt x, Object o) {		
		int max = x.childCount();
		VCEntry post = treatAnnot( (VCEntry) o, x.annotPost);
		
		for(int i = max - 1; i >= 0; i--) {
			Object child = x.childAt(i);
			System.out.println(child);
			if(child instanceof ASTNode) {
				post = (VCEntry) ((ASTNode) child).accept(this, post);
			}
		}
		post = treatAnnot( post, x.annotPre);
		return post;
	}	
	
	@Override
	public Object visitStmt(Stmt x, Object o){
		throw new IllegalArgumentException("Not yet implememented");
	}
	
	public Object illegalStmt(Stmt x, Object o){
		throw new IllegalArgumentException("Illegal Statement");
	}
	
	public VCEntry mkEntryWhile(VCEntry ve, Post inv) {
		VCEntry res = new VCEntry(ve);
		res.brpost = ve.post;
		res.post = inv;
		res.contpost = inv;
		return res;
		
	}

	public /*@non_null*/ Object visitWhileStmt(/*@non_null*/ WhileStmt x, Object o) {
		VCEntry entryPost = treatAnnot( (VCEntry) o, x.annotPost);
		AAnnotation annotPre = (AAnnotation)x.annotPre;		
		assert (annotPre != null && annotPre.getID() == AAnnotation.annotAssert);
		Term inv = annotPre.formula;
		Term post = entryPost.post.post;
		VCEntry entryBody = mkEntryWhile(entryPost, new Post(inv));
		VCEntry bodypre = (VCEntry) x.stmt.accept(this, entryBody);
		QuantVariableRef v = Expression.var(Formula.getCurrentLifter().sortBool);
		entryPost.post = new Post(v,
				Logic.and(Logic.implies(Logic.boolToProp(v), bodypre.post.post),
						Logic.implies(Logic.not(Logic.boolToProp(v)), post)));
		// the only field that can be modified in a VCentry is post 
		Term aux = ((VCEntry) x.expr.accept(exprVisitor, entryPost)).post.post;
		vcs.add(Logic.implies(inv, aux));
		entryPost.post = new Post(inv);
		return entryPost;
	}


	public /*@non_null*/ Object visitEvalStmt(/*@non_null*/ EvalStmt x, Object o) {
		VCEntry post = treatAnnot( (VCEntry) o, x.annotPost);
		post = ((VCEntry) x.expr.accept(exprVisitor, post));
		return treatAnnot(post, x.annotPre);
	}

	public /*@non_null*/ Object visitReturnStmt(/*@non_null*/ ReturnStmt x, Object o) {
		// Goog to ensure that x.annotPost == Null
		// and so remove this line
		assert (x.annotPost == null); // if the method type is not void there should 
									  // also be the variable \result
		VCEntry post = (VCEntry) o;
		post = ((VCEntry) x.expr.accept(exprVisitor, post));
		return treatAnnot(post, x.annotPre);
	}	

	public Post getExcpPostExact(Type typ, VCEntry entry) {
		Iterator iter = entry.excpost.iterator();
		while(iter.hasNext()) {
			ExcpPost p = (ExcpPost)iter.next();
			if (Types.isSubClassOrEq(typ, p.excp)) {
				return p.post;
			}
		}
		return new Post(Logic.False());
	}
	
	public Post getExcpPost(Type typ, VCEntry entry) {
		Iterator iter = entry.excpost.iterator();
		Post res = entry.post;
		while(iter.hasNext()) {
			ExcpPost p = (ExcpPost)iter.next();
			if (Types.isSubClassOrEq(typ, p.excp)) {
				res = p.post;
			}
			else {
				Term var = Expression.var(Formula.getCurrentLifter().sortRef);
				
				Post typeof = new Post(Logic.typeLE(
								Expression.typeof(Expression.heap, var), 
								Formula.translate(p.excp)));
				res = Post.and(Post.implies(typeof, p.post), 
						Post.implies(Post.not(typeof), res));
			}
		}
		return new Post(Logic.False());
	}
	

	public /*@non_null*/ Object visitThrowStmt(/*@non_null*/ ThrowStmt x, Object curr) {
		
		Type typ = FlowInsensitiveChecks.getType(x.expr) ;
		Post p = getExcpPost(typ, (VCEntry) curr);
		VCEntry vce = (VCEntry) curr;
		vce.post = p;
		return vce;
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
	
	public /*@non_null*/ Object visitDoStmt(/*@non_null*/ DoStmt x, Object o) {
		return visitStmt(x, o);
	}

	public /*@non_null*/ Object visitSynchronizeStmt(/*@non_null*/ SynchronizeStmt x, Object o) {
		return visitStmt(x, o);
	}
	

	public /*@non_null*/ Object visitSwitchStmt(/*@non_null*/ SwitchStmt x, Object o) {
		return visitStmt(x, o);
	}	

	

	public /*@non_null*/ Object visitVarDeclStmt(/*@non_null*/ VarDeclStmt x, Object o) {
		return visitStmt(x, o);
	}
		
	public /*@non_null*/ Object visitBranchStmt(/*@non_null*/ BranchStmt x, Object o) {
		return visitStmt(x, o);
	}
}	
