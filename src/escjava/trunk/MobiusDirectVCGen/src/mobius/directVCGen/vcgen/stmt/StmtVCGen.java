package mobius.directVCGen.vcgen.stmt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.Vector;

import javafe.ast.ASTNode;
import javafe.ast.ArrayInit;
import javafe.ast.AssertStmt;
import javafe.ast.BlockStmt;
import javafe.ast.BreakStmt;
import javafe.ast.CatchClause;
import javafe.ast.CatchClauseVec;
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
import javafe.ast.VarDeclStmt;
import javafe.ast.VarInit;
import javafe.ast.WhileStmt;
import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Type;
import mobius.directVCGen.formula.annotation.AAnnotation;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;
import mobius.directVCGen.vcgen.expression.ExpressionVisitor;
import mobius.directVCGen.vcgen.struct.ExcpPost;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;
import escjava.ast.ExprStmtPragma;
import escjava.ast.SetStmtPragma;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

/**
 * This class does the weakest precondition calculus for the statements.
 * @author B. Grégoire, J. Charles
 */
public class StmtVCGen extends ExpressionVisitor {
	/** the side conditions that were generated */
	public Vector<Term> vcs = new Vector<Term>();
	/** the list of variables declarations */
	public final Vector<Term> vardecl = new Vector<Term>();
	/** the visitor to visit expressions */
	public final ExpressionVisitor exprVisitor = new ExpressionVisitor();
	
	public final AnnotationDecoration annot = AnnotationDecoration.inst;
	
	
	
	/**
	 * The method to treat the annotations
	 * @param vce the current post condition 
	 * @param annot the annotation to treat
	 * @return a postcondition computed from the annotation
	 */
	public Post treatAnnot(VCEntry vce, Vector<AAnnotation> annot) {
		if(annot == null)
			return vce.post;
		Term post = vce.post.post;
		int len = annot.size();
		for(int i = len -1; i >= 0; i--) {
			AAnnotation aa =  annot.elementAt(i);		
			switch(aa.getID()) {
				case AAnnotation.annotAssert:
					vcs.add(Logic.safe.implies(aa.formula, post));
					post = aa.formula;
					break;
				case AAnnotation.annotCut:
					post = Logic.safe.and(aa.formula, Logic.safe.implies(aa.formula, post));
					break;
				case AAnnotation.annotAssume:
					post = Logic.safe.implies(aa.formula, post);
					break;
				case AAnnotation.annotSet: {
					mobius.directVCGen.formula.annotation.Set s = (mobius.directVCGen.formula.annotation.Set) aa;
					if(s.assignment != null) {
						post.subst(s.assignment.var, s.assignment.expr);
					}
					else if(s.declaration != null) {
						if(s.assignment == null) {
							post = Logic.forall(s.declaration.qvar, post);
						}						
						addVarDecl(s.declaration.qvar);
					}
					break;
				}
				
				case AAnnotation.undef:
				default:
					throw new UnsupportedOperationException(aa.toString());
			}
		}
		
		return new Post(post);
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
	
	public Post visitInnerBlockStmt (/*@non_null*/ Stmt x, VCEntry vce) {	
		if(!(x instanceof BlockStmt)) {
			return (Post)x.accept(this, vce);
		}
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
	
	public Object illegalStmt(ASTNode x, Object o){
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
			bodypre = visitInnerBlockStmt((BlockStmt)x.stmt, vceBody);
		else 
			bodypre = (Post) x.stmt.accept(this, vceBody);
		
		QuantVariableRef v = Expression.rvar(Bool.sort);
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
		Post p = vce.post;
		vce.post = new Post(Expression.rvar(Type.getSort(x.expr)),
							p.post);
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

	public static Post getExcpPostExact(Term typ, VCEntry vce) {
		Iterator iter = vce.lexcpost.iterator();
		while(iter.hasNext()) {
			ExcpPost p = (ExcpPost)iter.next();
			if (Type.isSubClassOrEq(typ, p.type)) {
				return p.post;
			}
		}
		return vce.excpost;
		
	}
	
	public static Post getExcpPost(Term typ, VCEntry vce) {
		Iterator iter = vce.lexcpost.iterator();
		Post res = vce.excpost;
		while(iter.hasNext()) {
			ExcpPost p = (ExcpPost)iter.next();
			if (Type.isSubClassOrEq(typ, p.type)) {
				res = p.post;
			}
			else if (Type.isSubClassOrEq(p.type,typ)) {
					Term var = Expression.rvar(Ref.sort);
					Post typeof = new Post(
							Logic.assignCompat(Heap.var, var, 
							p.type));
					res = Post.and(Post.implies(typeof, p.post), 
							Post.implies(Post.not(typeof), res));
			}	
		}
		return res;
	}
	

	public /*@non_null*/ Object visitThrowStmt(/*@non_null*/ ThrowStmt x, Object o) {
		VCEntry vce = (VCEntry)o;
		vce.post = treatAnnot( vce, annot.getAnnotPost(x));
		Term typ = Type.getTypeName(x.expr);
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
		if (label == null) {
			if(vce.contpost == null)
				throw new NullPointerException();
			return vce.contpost; 
		}
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
		vce.post = treatAnnot(vce, annot.getAnnotPost(x));
		if (s instanceof WhileStmt || s instanceof DoStmt || s instanceof ForStmt ) {
			vce = mkEntryLoopLabel(x.label, vce, new Post(annot.getInvariant(s)));
		}
		vce.post = (Post) x.stmt.accept(exprVisitor, vce);
		return treatAnnot(vce, annot.getAnnotPre(x));
	}
	
	public /*@non_null*/ Object visitIfStmt(/*@non_null*/ IfStmt x, Object o) {
		VCEntry vce = (VCEntry) o;
		Post postBranch = treatAnnot(vce, annot.getAnnotPost(x));
		vce.post = postBranch;
		Post preT = (Post) x.thn.accept(this, vce);
		vce.post = postBranch;
		Post preF = (Post) x.els.accept(this, vce);
		
		QuantVariableRef v = Expression.rvar(Bool.sort);
	
		vce.post = new Post(v,
				Logic.and(Logic.implies(Logic.boolToProp(v), preT.post),
						Logic.implies(Logic.not(Logic.boolToProp(v)), preF.post)));
		
	    vce.post = (Post) x.accept(exprVisitor, vce);	
		return treatAnnot(vce, annot.getAnnotPre(x));
	}
		
	public /*@non_null*/ Object visitSkipStmt(/*@non_null*/ SkipStmt x, Object o) {
		VCEntry vce = (VCEntry) o;
		vce.post = treatAnnot(vce, annot.getAnnotPost(x));
		return treatAnnot(vce, annot.getAnnotPre(x));
	}
		
	public /*@non_null*/ Object visitTryFinallyStmt(/*@non_null*/ TryFinallyStmt x, Object o) {
		VCEntry vce = (VCEntry) o;
		vce.post = treatAnnot(vce, annot.getAnnotPost(x));
		Stmt sTry = x.tryClause;
		Stmt sFinally = x.finallyClause;
		VCEntry vcetmp = new VCEntry(vce);
		Post post = visitInnerBlockStmt(sFinally,  vcetmp);
		
		// brpost
		vcetmp.post = vce.brpost;
		Post brpost = (Post) visitInnerBlockStmt(sFinally,  vcetmp);
		// lbrpost
		HashMap<Identifier, Post> lbrpost = new HashMap<Identifier, Post>();
		Set<Identifier> keys = vce.lbrpost.keySet();
		for(Identifier k : keys) {
			vcetmp.post = vce.lbrpost.get(k);
			Post p = visitInnerBlockStmt(sFinally,  vcetmp);
			lbrpost.put(k, p);
		}
		
		// contpost
		vcetmp.post = vce.contpost;
		Post contpost = visitInnerBlockStmt(sFinally,  vcetmp);
		//lcontpost
		HashMap<Identifier, Post> lcontpost = new HashMap<Identifier, Post>();
		keys = vce.lcontpost.keySet();
		for(Identifier k : keys) {
			vcetmp.post = vce.lcontpost.get(k);
			Post p = visitInnerBlockStmt(sFinally,  vcetmp);
			lcontpost.put(k, p);
		}
		
		//excpost
		vcetmp.post = vce.excpost;
		Post excpost = visitInnerBlockStmt(sFinally,  vcetmp);
		//lexcpost
		List<ExcpPost> lexcpost = new ArrayList<ExcpPost>();
		for(ExcpPost exc : vce.lexcpost) {
			vcetmp.post = exc.post;
			Post p = visitInnerBlockStmt(sFinally,  vcetmp);
			lexcpost.add(new ExcpPost(exc.type, p));
		}
		
		VCEntry entFinally = new VCEntry(post, excpost, brpost,contpost);
		entFinally.lbrpost.putAll(lbrpost);
		entFinally.lcontpost.putAll(lcontpost);
		entFinally.lexcpost.addAll(lexcpost);
		visitInnerBlockStmt(sTry,entFinally);
		return treatAnnot(vce, annot.getAnnotPre(x));
	}

	public /*@non_null*/ Object visitTryCatchStmt(/*@non_null*/ TryCatchStmt x, Object o) {
		VCEntry vce = (VCEntry) o;
		vce.post = treatAnnot(vce, annot.getAnnotPost(x));
		CatchClauseVec ccv= x.catchClauses;
		CatchClause[] catches = ccv.toArray();
		LinkedList<ExcpPost> l = new LinkedList<ExcpPost>();
		Post olpost = vce.post;
		for(CatchClause c: catches) {
			ExcpPost ep;
			Term t = Type.translate(c.arg.type);
			QuantVariableRef excp = Expression.rvar(c.arg);
			vce.post = olpost;
			Post epost = (Post)c.body.accept(this, vce);
			epost = new Post(excp, epost.post);
			ep = new ExcpPost(t, epost);
			l.addLast(ep);
		}
		VCEntry post = new VCEntry(vce);
		post.lexcpost.clear();
		post.lexcpost.addAll(l);
		post.lexcpost.addAll(vce.lexcpost);
		vce.post = visitInnerBlockStmt(x.tryClause, vce);
		return treatAnnot(vce, annot.getAnnotPre(x));
	}


	public /*@non_null*/ Object visitVarDeclStmt(/*@non_null*/ VarDeclStmt x, Object o) {
		VCEntry vce = (VCEntry) o;
		vce.post = treatAnnot(vce, annot.getAnnotPost(x));
		VarInit init = x.decl.init;
		QuantVariable qv = Expression.var(x.decl);
		if(init != null) {
			// the init value replaces the quantification
			QuantVariableRef qvr = Expression.rvar(qv);
			vce.post = new Post(qvr, vce.post.post);
			vce.post = (Post)init.accept(this, vce);
			if(init instanceof ArrayInit) {
				// FIXME should add the array new too
				vce.post = new Post(Logic.forall(qv, vce.post.post));
			}

		}
		else {
			// the quantification is preemptive
			vce.post = new Post(Logic.forall(qv, vce.post.post));
		}
		// we must anyway declare it for every vc:
		addVarDecl(qv);
		return treatAnnot(vce, annot.getAnnotPre(x));
	}
	
	private void addVarDecl(QuantVariable qv) {
		Vector<Term> oldvcs = vcs;
		vcs = new Vector<Term>();
		for (Term t: oldvcs) {
			vcs.add(Logic.forall(qv, t));
		}
		
	}


	// already treated in the try clause
	public /*@non_null*/ Object visitCatchClause(/*@non_null*/ CatchClause x, Object o) {
		return visitASTNode(x, o);
	}
	

	
	

	public /*@non_null*/ Object visitConstructorInvocation(/*@non_null*/ ConstructorInvocation x, Object o) {
		return visitStmt(x, o);
	}
	public /*@non_null*/ Object visitDoStmt(/*@non_null*/ DoStmt x, Object o) {
		return visitStmt(x, o);
	}

	
	public /*@non_null*/ Object visitForStmt(/*@non_null*/ ForStmt x, Object o) {
		
		VCEntry vce = (VCEntry)o;
		vce.post = treatAnnot( vce, annot.getAnnotPost(x));
		Term inv = annot.getInvariant(x);
		Term post = vce.post.post;
		Post pinv = new Post(inv);
		VCEntry vceBody = mkEntryWhile(vce, pinv);
		for(int i = x.forUpdate.size() -1; i >= 0; i --) {
			vceBody.post = (Post) x.forUpdate.elementAt(i).accept(this, vceBody);
		}
		Post bodypre;
		if (x.body instanceof BlockStmt)
			bodypre = visitInnerBlockStmt((BlockStmt)x.body, vceBody);
		else 
			bodypre = (Post) x.body.accept(this, vceBody);
		
		QuantVariableRef v = Expression.rvar(Bool.sort);
		vce.post = new Post(v,
				Logic.and(Logic.implies(Logic.boolToProp(v), bodypre.post),
						Logic.implies(Logic.not(Logic.boolToProp(v)), post)));
		// the only field that can be modified in a VCentry is post 
		Term aux = ((Post) x.test.accept(exprVisitor, vce)).post;
		Term vc = Logic.implies(inv, aux);
		// we add the for declared variables
		for(int i = x.forInit.size() -1; i >= 0; i --) {
			Stmt s =  (Stmt) x.forInit.elementAt(i);
			if(s instanceof VarDeclStmt) {
				VarDeclStmt decl = (VarDeclStmt) s;
				QuantVariable qv = Expression.var(decl.decl);
				vc = Logic.forall(qv, vc);
			}
		}
		vcs.add(vc);
		
		vce.post = pinv;
		for(int i = x.forInit.size() -1; i >= 0; i --) {
			Stmt s =  (Stmt) x.forInit.elementAt(i);
			vce.post = (Post)s.accept(this, vce);
		}
		return treatAnnot(vce, annot.getAnnotPre(x));
	}

	
	//pas implementer
	public /*@non_null*/ Object visitSwitchStmt(/*@non_null*/ SwitchStmt x, Object o) {
		return visitStmt(x, o);
	}	

	public /*@non_null*/ Object visitSwitchLabel(/*@non_null*/ SwitchLabel x, Object o) {
		return visitStmt(x, o);
	}

	public /*@non_null*/ Object visitStmtPragma(/*@non_null*/ StmtPragma x, Object o) {
		// just ignore it return illegalStmt(x, o);
		return ((VCEntry) o).post;
	}

	public /*@non_null*/ Object visitSynchronizeStmt(/*@non_null*/ SynchronizeStmt x, Object o) {
		return illegalStmt(x, o);
	}
	@Override
	public Object visitExprStmtPragma(ExprStmtPragma x, Object o) {
		return ((VCEntry) o).post;
	}

	@Override
	public Object visitSetStmtPragma(SetStmtPragma x, Object o) {
		return ((VCEntry) o).post;
	}

}	
