package mobius.directVCGen.vcgen.expression;

import javafe.ast.BinaryExpr;
import javafe.ast.Expr;
import javafe.ast.ExprObjectDesignator;
import javafe.ast.FieldAccess;
import javafe.ast.ObjectDesignator;
import javafe.ast.VariableAccess;
import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Num;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Type;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.NodeBuilder.Sort;

public class BinaryExpressionVCGen extends ABasicExpressionVCGEn{

	public BinaryExpressionVCGen(ExpressionVisitor vis) {
		super(vis);
	}
	public Post equals(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.not(Bool.lt(lvar, rvar))));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.not(Bool.le(lvar, rvar))));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.le(lvar, rvar)));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
		Post rPost = new Post(rvar, post.post.substWith(Bool.lt(lvar, rvar)));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
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
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
		
		Post rPost = new Post(rvar, Logic.and(
				Logic.implies(Logic.not(Logic.equals(rvar, Num.value(0))), 
						      post.post.substWith(Num.div(lvar, rvar))),
				Logic.implies(Logic.equals(rvar, Num.value(0)),
						getNewExcpPost(Type.javaLangArithmeticException(), post))));
		
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}

	
	
	public Post assign(BinaryExpr expr, VCEntry entry) {
		Expr right = expr.right;
		Expr left = expr.left;
		if(left instanceof VariableAccess) {
			VariableAccess va = (VariableAccess) left;
			QuantVariableRef var = Expression.rvar(va.decl);
			QuantVariableRef tmpvar = entry.post.var;
			Post newPost = new Post(tmpvar, entry.post.post.subst(var, tmpvar));
			entry.post = newPost;
			Post pre = getPre(right, entry);
			return pre;

		}
		else { // left instanceof FieldAccess
			FieldAccess field = (FieldAccess) left;
			ObjectDesignator od = field.od;
			switch(od.getTag()) {
				case TagConstants.EXPROBJECTDESIGNATOR: {
					// can be null
					//System.out.println(field.decl.parent);
					QuantVariable f = Expression.var(field.decl);
					Sort s = f.type;
					QuantVariableRef val = Expression.rvar(s);
					QuantVariableRef obj = Expression.rvar(Ref.sort);
					
					entry.post = new Post(val, entry.post.post.subst(Heap.var, 
														 Heap.store(Heap.var, obj, f, val)));
					Post pre = getPre(right, entry);
					entry.post = new Post(obj, pre.post);
					return getPre(od, entry);

				}
				case TagConstants.SUPEROBJECTDESIGNATOR:
					// TODO: the case for super
				case TagConstants.TYPEOBJECTDESIGNATOR: {
					// cannot be null
					//System.out.println(field);
					QuantVariable f = Expression.var(field.decl);
					Sort s = f.type;
					QuantVariableRef val = Expression.rvar(s);
					Post p = new Post(val, entry.post.post.subst(Heap.var, Heap.store(Heap.var, f, val)));
					entry.post = p;
					Post pre = getPre(right, entry);
					entry.post = pre;
					return getPre(od, entry);
				}
				default: 
					throw new IllegalArgumentException("Unknown object designator type ! " + od);
				
			}
			
		}
	}

	public Post mod(BinaryExpr expr, VCEntry post) {
		Expr right = expr.right;
		Expr left = expr.left;
		
		QuantVariableRef rvar = Expression.rvar(Type.getSort(right));
		QuantVariableRef lvar = Expression.rvar(Type.getSort(left));
		Post rPost = new Post(rvar, Logic.and(
				Logic.implies(Logic.not(Logic.equalsZero(rvar)), 
						      post.post.substWith(Num.mod(lvar, rvar))),
				Logic.implies(Logic.equalsZero(rvar),
						getNewExcpPost(Type.javaLangArithmeticException(), post))));
		post.post = rPost;
		Post pre = getPre(right, post);
		Post lPost = new Post(lvar, pre.post);
		post.post = lPost;
		pre = getPre(left, post);
		return pre;
	}
}
