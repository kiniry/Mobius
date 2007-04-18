package mobius.directVCGen.vcgen.expression;

import java.util.Vector;

import javafe.ast.ExprVec;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.MethodInvocation;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.vcgen.stmt.StmtVCGen;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.tc.Types;


public class ExpressionVCGen extends BinaryExpressionVCGen{

	

	
	public ExpressionVCGen(ExpressionVisitor vis) {
		super(vis);
	}

	public static Vector<QuantVariableRef> mkArguments(MethodInvocation mi) {
		Vector<QuantVariableRef> v = new Vector<QuantVariableRef>();
		FormalParaDeclVec fpdvec = mi.decl.args;
		FormalParaDecl[] args = fpdvec.toArray();
		for (FormalParaDecl fpd: args) {
			v.add(Expression.var(fpd));
		}
		return v;
	}
	public Object methodInvocation(MethodInvocation mi, VCEntry entry) {
		Post normalPost = Lookup.normalPostcondition(mi.decl);
		Post excpPost = Lookup.exceptionalPostcondition(mi.decl);
		Term pre = Lookup.precondition(mi.decl);
		QuantVariableRef exc = Expression.var(Ref.sort);
		Term tExcp = Logic.forall(exc.qvar, Logic.implies(excpPost.substWith(exc), 
				               		StmtVCGen.getExcpPost(Types.javaLangThrowable(), entry).substWith(exc)));
		Term tNormal = normalPost.substWith(entry.post.var);
		QuantVariableRef res = Expression.var(entry.post.var.getSort());
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

	
	
}
