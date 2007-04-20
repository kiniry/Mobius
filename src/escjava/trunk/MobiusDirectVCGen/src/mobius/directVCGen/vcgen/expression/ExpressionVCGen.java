package mobius.directVCGen.vcgen.expression;

import java.util.Vector;

import javafe.ast.CastExpr;
import javafe.ast.CondExpr;
import javafe.ast.ExprVec;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.InstanceOfExpr;
import javafe.ast.MethodInvocation;
import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Type;
import mobius.directVCGen.vcgen.stmt.StmtVCGen;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;


public class ExpressionVCGen extends BinaryExpressionVCGen{

	public ExpressionVCGen(ExpressionVisitor vis) {
		super(vis);
	}

	public static Vector<QuantVariableRef> mkArguments(MethodInvocation mi) {
		Vector<QuantVariableRef> v = new Vector<QuantVariableRef>();
		FormalParaDeclVec fpdvec = mi.decl.args;
		FormalParaDecl[] args = fpdvec.toArray();
		for (FormalParaDecl fpd: args) {
			v.add(Expression.rvar(fpd));
		}
		return v;
	}
	public Post methodInvocation(MethodInvocation mi, VCEntry entry) {
		Post normalPost = Lookup.normalPostcondition(mi.decl);
		Post excpPost = Lookup.exceptionalPostcondition(mi.decl);
		Term pre = Lookup.precondition(mi.decl);
		QuantVariableRef exc = Expression.rvar(Ref.sort);
		Term tExcp = Logic.forall(exc.qvar, Logic.implies(excpPost.substWith(exc), 
				               		StmtVCGen.getExcpPost(Type.javaLangThrowable(), entry).substWith(exc)));
		Term tNormal = normalPost.substWith(entry.post.var);
		QuantVariableRef res = Expression.rvar(entry.post.var.getSort());
		tNormal = Logic.forall(res.qvar, Logic.implies(tNormal, entry.post.post));
		entry.post = new Post(Logic.and(pre, Logic.implies(pre, Logic.and(tNormal, tExcp))));
		Vector<QuantVariableRef> v = mkArguments(mi);
		ExprVec ev = mi.args;
		for (int i = ev.size() - 1; i >= 0; i--) {
			entry.post = new Post(v.elementAt(i), entry.post.post);
			entry.post = getPre(ev.elementAt(i), entry);
		}
		
		return entry.post;
	}

	public Post instanceOf(InstanceOfExpr x, VCEntry entry) {
		Post p = entry.post;
		
		QuantVariableRef r = Expression.rvar(Ref.sort);
		p = new Post(r,
			Logic.and(Logic.implies(Logic.typeLE(Type.of(Heap.var, r), 
												 Type.translate(x.type)),
								    p.substWith(Bool.value(true))), 
				      Logic.implies(Logic.not(Logic.typeLE(Type.of(Heap.var, r), 
						  								   Type.translate(x.type))),
						  			p.substWith(Bool.value(false)))));
		entry.post = p;
		Post pre = getPre(x.expr, entry);
		return pre;
	}

	public Post condExpr(CondExpr x, VCEntry e) {
		// of the form (cond ? st1 : st2 )
		QuantVariableRef cond = Expression.rvar(Bool.sort);


		QuantVariableRef st1 = Expression.rvar(Type.getSort(x.thn));		
		Post pthen = new Post(st1, e.post.substWith(st1));
		e.post = pthen;
		pthen = getPre(x.thn, e);

		
		QuantVariableRef st2 = Expression.rvar(Type.getSort(x.els));
		Post pelse = new Post(st1, e.post.substWith(st2));
		e.post = pelse;
		pelse = getPre(x.els, e);
		
		Post pcond = new Post(cond, Logic.and(Logic.implies(Logic.boolToProp(cond), pthen.post),
											  Logic.implies(Logic.not(Logic.boolToProp(cond)), pelse.post)));
		// now for the wp...
		e.post = pcond;
		pcond = getPre(x.test, e);
		return pcond;
	}

	public Post castExpr(CastExpr x, VCEntry e) {
		Post p = new Post(e.post.var, 
							Logic.implies(Logic.typeLE(Type.of(Heap.var, e.post.var), Type.translate(x.type)),
										  e.post.post));
		e.post = p;
		p = getPre(x.expr, e);
		return p;
	}
	
	
}
