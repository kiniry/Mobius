package mobius.directVCGen.vcgen.intern;

import javafe.ast.BinaryExpr;
import javafe.ast.Expr;
import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;
import escjava.sortedProver.Lifter.QuantVariableRef;

public class ExpressionVCGen {
	ExpressionVisitor visitor;
	public ExpressionVCGen(ExpressionVisitor vis) {
		visitor = vis;
	}
	
	public Post getPre(Expr e, VCEntry post) {
		return (Post)e.accept(visitor, post);
	}
	
	public Post equals(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.equals(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(right, post);
		return pre;
	}
	
}
