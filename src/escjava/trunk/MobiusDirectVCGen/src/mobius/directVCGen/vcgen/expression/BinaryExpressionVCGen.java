package mobius.directVCGen.vcgen.expression;

import javafe.ast.BinaryExpr;
import javafe.ast.Expr;
import javafe.ast.FieldAccess;
import javafe.ast.FieldDecl;
import javafe.ast.GenericVarDecl;
import javafe.ast.LocalVarDecl;
import javafe.ast.ObjectDesignator;
import javafe.ast.VariableAccess;
import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Num;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.vcgen.DirectVCGen;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;
import escjava.ast.Modifiers;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;
import escjava.tc.Types;
import escjava.translate.UniqName;

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
	public Post visitVariableAccessForWrite(VariableAccess m, VCEntry post) {
		
		Sort s = null;
		String name = UniqName.variable(m.decl);
		
		GenericVarDecl decl = m.decl;
		if(((LocalVarDecl)decl).source != null)
			decl = ((LocalVarDecl)decl).source;	
		//assert(decl != null);
		
		switch (decl.getTag()) {
			case TagConstants.FIELDDECL: {
					FieldDecl d = (FieldDecl)decl;
					if (Modifiers.isStatic(d.getModifiers()))
						s = Formula.typeToSort(d.type);
					else
						s = Formula.getCurrentLifter().registerMapSort(Ref.sort, Formula.typeToSort(d.type));
					return post.post;
					// TODO: Treat correctly the fields
				}
			case TagConstants.LOCALVARDECL:
			case TagConstants.FORMALPARADECL: {
					GenericVarDecl g = (GenericVarDecl)decl;
					s = Formula.typeToSort(g.type);
					QuantVariableRef var = Expression.refFromVar(Expression.var(name, s));
					Post p = new Post(post.post.var, post.post.post.subst(var, post.post.var));
					return p;
				}
			default:
				throw new IllegalArgumentException("Unknown type of variable declaration: " + decl);
				
			
		}
		
		
	}

	public Post visitFieldAccessForWrite(FieldAccess field, VCEntry post) {
		
		

		return post.post;
	}
	
	public Post assign(BinaryExpr expr, VCEntry post) {
		// TODO: Handle it
		Expr right = expr.right;
		Expr left = expr.left;
		Post pr = post.post;
		if(left instanceof VariableAccess) {
			VariableAccess va = (VariableAccess) left;
			String name = UniqName.variable(va.decl);
			Sort s = Formula.typeToSort(va.decl.type);
			QuantVariableRef var = Expression.refFromVar(Expression.var(name, s));
			QuantVariableRef tmpvar = post.post.var;
			Post newPost = new Post(tmpvar, post.post.post.subst(var, tmpvar));
			post.post = newPost;
			Post pre = getPre(right, post);
			return pre;

		}
		else { // left instanceof FieldAccess
			FieldAccess field = (FieldAccess) left;
			ObjectDesignator od = field.od;
			switch(od.getTag()) {
				case TagConstants.EXPROBJECTDESIGNATOR: {
					// can be null
					System.out.println(field);
					break;
				}
				case TagConstants.SUPEROBJECTDESIGNATOR:
				case TagConstants.TYPEOBJECTDESIGNATOR: {
					// cannot be null
					System.out.println(field);
					String name = UniqName.variable(field.decl);
					Sort s = Formula.typeToSort(field.decl.type);
					QuantVariable f = Expression.var(name, s);
					Term val = null;
					Heap.store(Heap.var, f, val );
					break;
				}
				default: 
					throw new IllegalArgumentException("Unknown objec designator type ! " + od);
				
			}
			Post pre = getPre(right, post);
			return pre;
//			pre = visitFieldAccessForWrite((FieldAccess) left, post);
		}
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
