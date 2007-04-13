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
import javafe.ast.Identifier;
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
import javafe.tc.FlowInsensitiveChecks;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.annotation.AAnnotation;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;
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
	public final AnnotationDecoration annot = AnnotationDecoration.inst;
	
	/**
	 * The method to treat the annotations
	 * @param post the current post condition 
	 * @param annot the annotation to treat
	 * @return a postcondition computed from the annotation
	 */
	public Post treatAnnot(VCEntry vce, Vector<AAnnotation> annot) {
		return vce.post;
	}
	
	public /*@non_null*/ Object visitAssertStmt(/*@non_null*/ AssertStmt x, Object o) {
		return illegalStmt(x, o);
	}
	
	public VCEntry mkEntryBlock (VCEntry vce) {
		VCEntry res = new VCEntry(vce);
		res.brpost = vce.post;
	    return res;	
		
	}
	@Override
	public /*@non_null*/ Object visitBlockStmt(/*@non_null*/ BlockStmt x, Object o) {		
		int max = x.childCount();
		VCEntry vce = (VCEntry) o;
		vce = mkEntryBlock(vce);
		vce.post = treatAnnot(vce, annot.getAnnotPost(x));
		
		for(int i = max - 1; i >= 0; i--) {
			Object child = x.childAt(i);
			if(child instanceof ASTNode) {
				vce.post = (Post) ((ASTNode) child).accept(this, vce);
			}
		}
		return treatAnnot( vce, annot.getAnnotPre(x));
	}	
	
	public Post visitWhileBlockStmt (/*@non_null*/ BlockStmt x, VCEntry vce) {		
		int max = x.childCount();
		assert (annot.getAnnotPost(x) == null && annot.getAnnotPre(x) == null);
		for(int i = max - 1; i >= 0; i--) {
			Object child = x.childAt(i);
			if(child instanceof ASTNode) {
				vce.post = (Post) ((ASTNode) child).accept(this, vce);
			}
		}
		return vce.post;
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
		VCEntry vce = (VCEntry)o;
		vce.post = treatAnnot( vce, annot.getAnnotPost(x));
		Term inv = annot.getInvariant(x);
		Term post = vce.post.post;
		Post pinv = new Post(inv);
		VCEntry vceBody = mkEntryWhile(vce, pinv);
		Post bodypre;
		if (x.stmt instanceof BlockStmt)
			bodypre = visitWhileBlockStmt((BlockStmt)x.stmt, vceBody);
		else 
			bodypre = (Post) x.stmt.accept(this, vceBody);
		
		QuantVariableRef v = Expression.var(Formula.getCurrentLifter().sortBool);
		vce.post = new Post(v,
				Logic.and(Logic.implies(Logic.boolToProp(v), bodypre.post),
						Logic.implies(Logic.not(Logic.boolToProp(v)), post)));
		// the only field that can be modified in a VCentry is post 
		Term aux = ((Post) x.expr.accept(exprVisitor, vce)).post;
		vcs.add(Logic.implies(inv, aux));
		
		vce.post = pinv;
		return treatAnnot(vce, annot.getAnnotPre(x));
	}


	public /*@non_null*/ Object visitEvalStmt(/*@non_null*/ EvalStmt x, Object o) {
		VCEntry vce = (VCEntry) o;
		vce.post = treatAnnot( vce, annot.getAnnotPost(x));
		vce.post = (Post)x.expr.accept(exprVisitor, vce);
		return treatAnnot(vce, annot.getAnnotPre(x));
	}

	public /*@non_null*/ Object visitReturnStmt(/*@non_null*/ ReturnStmt x, Object o) {
		// Goog to ensure that x.annotPost == Null
		// and so remove this line
		assert (annot.getAnnotPost(x) == null); // if the method type is not void there should 
									  // also be the variable \result
		VCEntry vce = (VCEntry) o;
		vce.post = (Post) x.expr.accept(exprVisitor, vce);
		return treatAnnot(vce, annot.getAnnotPre(x));
	}	

	public Post getExcpPostExact(Type typ, VCEntry vce) {
		Iterator iter = vce.lexcpost.iterator();
		while(iter.hasNext()) {
			ExcpPost p = (ExcpPost)iter.next();
			if (Types.isSubClassOrEq(typ, p.excp)) {
				return p.post;
			}
		}
		return vce.excpost;
		
	}
	
	public Post getExcpPost(Type typ, VCEntry vce) {
		Iterator iter = vce.lexcpost.iterator();
		Post res = vce.excpost;
		while(iter.hasNext()) {
			ExcpPost p = (ExcpPost)iter.next();
			if (Types.isSubClassOrEq(typ, p.excp)) {
				res = p.post;
			}
			else if (Types.isSubClassOrEq(p.excp,typ)) {
					Term var = Expression.var(Formula.getCurrentLifter().sortRef);
					Post typeof = new Post(Logic.typeLE(
							Expression.typeof(Expression.heap, var), 
							Formula.translate(p.excp)));
					res = Post.and(Post.implies(typeof, p.post), 
							Post.implies(Post.not(typeof), res));
			}	
		}
		return res;
	}
	

	public /*@non_null*/ Object visitThrowStmt(/*@non_null*/ ThrowStmt x, Object o) {
		VCEntry vce = (VCEntry)o;
		vce.post = treatAnnot( vce, annot.getAnnotPost(x));
		Type typ = FlowInsensitiveChecks.getType(x.expr) ;
		vce.post = getExcpPost(typ, vce);
		vce.post = ((Post)x.expr.accept(exprVisitor, vce));
		return treatAnnot(vce, annot.getAnnotPre(x));
	}
	
	public Post getBreakPost(Identifier label,VCEntry vce) {
		if (label == null) return vce.brpost; 
		return vce.lbrpost.get(label);
	}
	
	public /*@non_null*/ Object visitBreakStmt(/*@non_null*/ BreakStmt x, Object o) {
		VCEntry vce = (VCEntry) o;
		vce.post = getBreakPost(x.label, vce);
		return treatAnnot(vce, annot.getAnnotPre(x));
	}
	
	public Post getContinuePost(Identifier label,VCEntry vce) {
		if (label == null) return vce.contpost; 
		return vce.lcontpost.get(label);
	}
	
	public /*@non_null*/ Object visitContinueStmt(/*@non_null*/ ContinueStmt x, Object o) {
		VCEntry vce = (VCEntry) o;
		vce.post = getContinuePost(x.label, vce);
		return treatAnnot(vce, annot.getAnnotPre(x));
	}
	
	public VCEntry mkEntryLoopLabel(Identifier label, VCEntry ve, Post continu) {
		VCEntry res = new VCEntry(ve);
		res.brpost = ve.post;
		res.contpost = continu;
		res.lbrpost.put(label, ve.post);
		res.lcontpost.put(label, continu);
		return res;	
	}
	
	public /*@non_null*/ Object visitLabelStmt(/*@non_null*/ LabelStmt x, Object o) {
		Stmt s = x.stmt;
		VCEntry vce = (VCEntry)o;
		vce.post = treatAnnot(vce, annot.getAnnotPre(x));
		if (s instanceof WhileStmt || s instanceof DoStmt || s instanceof ForStmt ) {
			vce = mkEntryLoopLabel(x.label, vce, new Post(annot.getInvariant(s)));
		}
		return x.stmt.accept(this, vce);
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
