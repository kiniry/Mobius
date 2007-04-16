package mobius.directVCGen.vcgen.expression;

import javafe.ast.BinaryExpr;
import javafe.ast.Expr;
import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Num;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;
import escjava.sortedProver.Lifter.QuantVariableRef;

public class BinaryExpressionVCGen extends ABasicExpressionVCGEn{

	public BinaryExpressionVCGen(ExpressionVisitor vis) {
		super(vis);
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

	public Object or(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.or(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(right, post);
		return pre;
	}

	public Object and(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.and(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(right, post);
		return pre;
	}

	public Object ne(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.not(Bool.equals(lvar, rvar))));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(right, post);
		return pre;
	}

	public Object ge(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.ge(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(right, post);
		return pre;
	}

	public Object gt(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.gt(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(right, post);
		return pre;

	}

	public Object le(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.not(Bool.gt(lvar, rvar))));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(right, post);
		return pre;
	}

	public Object lt(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.not(Bool.ge(lvar, rvar))));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(right, post);
		return pre;
	}

	

	public Object add(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Num.add(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(right, post);
		return pre;
	}

	public Object sub(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Num.sub(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(right, post);
		return pre;
	}



	public Object star(BinaryExpr expr, VCEntry post) {
	
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Num.mul(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(right, post);
		return pre;
	}
	
	public Object bitor(BinaryExpr expr, VCEntry post) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object bitxor(BinaryExpr expr, VCEntry post) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object bitand(BinaryExpr expr, VCEntry post) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object lshift(BinaryExpr expr, VCEntry post) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object rshift(BinaryExpr expr, VCEntry post) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object urshift(BinaryExpr expr, VCEntry post) {
		// TODO Auto-generated method stub
		return null;
	}
	
	public Object div(BinaryExpr expr, VCEntry post) {
		// TODO: Handle the exceptional case
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Num.div(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(right, post);
		return pre;
	}

	public Object mod(BinaryExpr expr, VCEntry post) {
		// TODO: Handle the exceptional case
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Num.mod(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(right, post);
		return pre;
	}
}
