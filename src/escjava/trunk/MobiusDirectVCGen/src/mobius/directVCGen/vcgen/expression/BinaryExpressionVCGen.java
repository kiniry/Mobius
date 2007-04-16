package mobius.directVCGen.vcgen.expression;

import javafe.ast.BinaryExpr;
import javafe.ast.Expr;
import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Num;
import mobius.directVCGen.vcgen.DirectVCGen;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.tc.Types;

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
		pre = getPre(left, post);
		return pre;
	}

	public Post or(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.or(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}

	public Post and(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.and(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}

	public Post ne(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.not(Bool.equals(lvar, rvar))));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}

	public Post ge(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.ge(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}

	public Post gt(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.gt(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;

	}

	public Post le(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.not(Bool.gt(lvar, rvar))));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}

	public Post lt(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.not(Bool.ge(lvar, rvar))));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}

	

	public Post add(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Num.add(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}

	public Post sub(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Num.sub(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}



	public Post star(BinaryExpr expr, VCEntry post) {
	
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Num.mul(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}
	
	public Post bitor(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Expression.bitor(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}

	public Post bitxor(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Expression.bitxor(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}

	public Post bitand(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Expression.bitand(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}

	public Post lshift(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Num.lshift(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}

	public Post rshift(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Num.rshift(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}

	public Post urshift(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Num.urshift(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}
	
	public Post div(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		
		Post rPost = new Post(rvar, Logic.and(
				Logic.implies(Logic.not(Logic.equals(rvar, Num.value(0))), 
						      post.post.substWith(Num.div(lvar, rvar))),
				Logic.implies(Logic.equals(rvar, Num.value(0)),
						DirectVCGen.getExcpPost(Types.getJavaLang("ArithmeticException"), post).post)));
		
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}
	public Post assign(BinaryExpr expr, VCEntry post) {
		// TODO: Handle it
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.equals(lvar, rvar)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}
	public Post mod(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.var(Formula.getSort(right));
		QuantVariableRef lvar = Expression.var(Formula.getSort(left));
		Post rPost = new Post(rvar, Logic.and(
				Logic.implies(Logic.not(Logic.equalsZero(rvar)), 
						      post.post.substWith(Num.mod(lvar, rvar))),
				Logic.implies(Logic.equalsZero(rvar),
						DirectVCGen.getExcpPost(Types.getJavaLang("ArithmeticException"), post).post)));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}
}
