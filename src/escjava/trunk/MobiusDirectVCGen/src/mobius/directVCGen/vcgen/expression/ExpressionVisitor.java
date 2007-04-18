package mobius.directVCGen.vcgen.expression;

import javafe.ast.AmbiguousMethodInvocation;
import javafe.ast.AmbiguousVariableAccess;
import javafe.ast.ArrayInit;
import javafe.ast.ArrayRefExpr;
import javafe.ast.BinaryExpr;
import javafe.ast.CastExpr;
import javafe.ast.CondExpr;
import javafe.ast.Expr;
import javafe.ast.FieldAccess;
import javafe.ast.InstanceOfExpr;
import javafe.ast.LiteralExpr;
import javafe.ast.MethodInvocation;
import javafe.ast.NewArrayExpr;
import javafe.ast.NewInstanceExpr;
import javafe.ast.ParenExpr;
import javafe.ast.ThisExpr;
import javafe.ast.UnaryExpr;
import javafe.ast.VarInit;
import javafe.ast.VariableAccess;
import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Num;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.vcgen.ABasicVisitor;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.Term;

public class ExpressionVisitor extends ABasicVisitor {
	ExpressionVCGen vcg;
	public ExpressionVisitor() {
		vcg = new ExpressionVCGen(this);
	}
	public Object visitBinaryExpr(BinaryExpr expr, Object o) {
		
		//System.out.println(TagConstants.toString(expr.op));
		VCEntry post = (VCEntry) o;
		switch(expr.op) {
			case TagConstants.EQ:
				return vcg.equals(expr, post);
			case TagConstants.OR:
				return vcg.or(expr, post);
			case TagConstants.AND:
				return vcg.and(expr, post);
			case TagConstants.NE:
				return vcg.ne(expr, post);
			case TagConstants.GE:
				return vcg.ge(expr, post);
			case TagConstants.GT:
				return vcg.gt(expr, post);
			case TagConstants.LE:
				return vcg.le(expr, post);
			case TagConstants.LT:
				return vcg.lt(expr, post);
			case TagConstants.BITOR:
				return vcg.bitor(expr, post);
			case TagConstants.BITXOR:
				return vcg.bitxor(expr, post);
			case TagConstants.BITAND:
				return vcg.bitand(expr, post);
			case TagConstants.LSHIFT:
				return vcg.lshift(expr, post);
			case TagConstants.RSHIFT:
				return vcg.rshift(expr, post);
			case TagConstants.URSHIFT:
				return vcg.urshift(expr, post);
			case TagConstants.ADD:
				return vcg.add(expr, post);
			case TagConstants.SUB:
				return vcg.sub(expr, post);
			case TagConstants.DIV:
				return vcg.div(expr, post);
			case TagConstants.MOD:
				return vcg.mod(expr, post);
			case TagConstants.STAR:
				return vcg.star(expr, post);
			case TagConstants.ASSIGN:
				return vcg.assign(expr, post);
			case TagConstants.ASGMUL:
				// TODO: finish all these operators
			case TagConstants.ASGDIV:
			case TagConstants.ASGREM:
			case TagConstants.ASGADD:
			case TagConstants.ASGSUB:
			case TagConstants.ASGLSHIFT:
			case TagConstants.ASGRSHIFT:
			case TagConstants.ASGURSHIFT:
			case TagConstants.ASGBITAND:
				return post.post;
			
			// jml specific operators
			case TagConstants.IMPLIES:
			case TagConstants.EXPLIES:
			case TagConstants.IFF: 
			case TagConstants.NIFF:
			case TagConstants.SUBTYPE:
			case TagConstants.DOTDOT:
				throw new IllegalArgumentException("Unmanaged construct :" +
						TagConstants.toString(expr.op) +" " +  expr);
			default:
				throw new IllegalArgumentException("Unknown construct :" +
						TagConstants.toString(expr.op) +" " +  expr);
		}
	}
	


	public Object visitLiteralExpr(LiteralExpr expr,  Object o) {
		VCEntry vce = (VCEntry) o;
		Post result = vce.post;
		Term term = null;
		//System.out.println(TagConstants.toString(expr.tag));
		switch (expr.tag) {
			case TagConstants.BOOLEANLIT:
				term = result.substWith(Bool.value((Boolean)expr.value));
				break;
			case TagConstants.INTLIT:
				term = result.substWith(Num.value((Integer)expr.value));
				break;
			case TagConstants.LONGLIT:
				term = result.substWith(Num.value((Long)expr.value));
				break;
			case TagConstants.BYTELIT:
				result.substWith(Num.value((Byte)expr.value));
				break;
			case TagConstants.SHORTLIT: 
				term = result.substWith(Num.value((Short)expr.value));
				break;
			case TagConstants.FLOATLIT:
				term = result.substWith(Num.value((Float)expr.value));
				break;
			case TagConstants.CHARLIT:
				result.substWith(Num.value((Character)expr.value));
				break;
			case TagConstants.DOUBLELIT:
				term = result.substWith(Num.value((Double)expr.value));
				break;
			case TagConstants.STRINGLIT:
				term = result.substWith(Ref.strValue((String)expr.value));
				break;
			case TagConstants.NULLLIT:
				term = result.substWith(Ref.Null());
				break;
			default:
				throw new IllegalArgumentException("Unknown construct :" +
						TagConstants.toString(expr.tag) +" " +  expr);
		}
		return new Post(result.var, term);
	}

	public Object visitUnaryExpr(UnaryExpr expr, Object o) {
		// TODO: do the unary expressions
		VCEntry post = (VCEntry) o;
		switch(expr.op) {
			case TagConstants.POSTFIXINC:
				//return vcGenPostfixInc(expr, post);
			case TagConstants.INC:
				//return vcGenInc(expr, post);
			case TagConstants.POSTFIXDEC:
				//return vcGenPostfixDec(expr, post);
			case TagConstants.DEC:
				//return vcGenDec(expr, post);
				return post.post;
			case TagConstants.BITNOT:
			case TagConstants.UNARYADD:
			case TagConstants.UNARYSUB:
			case TagConstants.NOT:
			

				throw new IllegalArgumentException("Unmanaged construct :" +
						TagConstants.toString(expr.op) +" " +  expr);
			default:
				throw new IllegalArgumentException("Unknown construct :" +
						TagConstants.toString(expr.op) +" " +  expr);
		}
	}
	
	
	public /*@non_null*/ Object visitThisExpr(/*@non_null*/ ThisExpr x, Object o) {
		VCEntry vce = (VCEntry) o;
		return new Post(vce.post.substWith(Ref.varthis));// variable particuliere
	}
	
	public /*@non_null*/ Object visitParenExpr(/*@non_null*/ ParenExpr x, Object o) {
		// TODO: Check if a Paren Expr is as dumb as that
		return vcg.getPre(x.expr, (VCEntry) o);
	}
	
	public /*@non_null*/ Object visitMethodInvocation(/*@non_null*/ MethodInvocation x, Object o) {
		return vcg.methodInvocation(x, (VCEntry) o);
	}
	
	public /*@non_null*/ Object visitExpr(/*@non_null*/ Expr x, Object o) {
		throw new IllegalArgumentException("Illegal expr!!!!");
	}
	
	public /*@non_null*/ Object visitInstanceOfExpr(/*@non_null*/ InstanceOfExpr x, Object o) {
		return vcg.instanceOf(x, (VCEntry) o);
	}

	
	
	public Object visitVariableAccess(VariableAccess m, Object o) {
		VCEntry res = (VCEntry) o;
		
		
		return  res.post;
	}
	
	
	  public /*@non_null*/ Object visitVarInit(/*@non_null*/ VarInit x, Object o) {
	    return visitASTNode(x, o);
	  }

	  public /*@non_null*/ Object visitArrayInit(/*@non_null*/ ArrayInit x, Object o) {
	    return visitVarInit(x, o);
	  }

	  

	  

	  public /*@non_null*/ Object visitArrayRefExpr(/*@non_null*/ ArrayRefExpr x, Object o) {
	    return visitExpr(x, o);
	  }

	  public /*@non_null*/ Object visitNewInstanceExpr(/*@non_null*/ NewInstanceExpr x, Object o) {
	    return visitExpr(x, o);
	  }

	  public /*@non_null*/ Object visitNewArrayExpr(/*@non_null*/ NewArrayExpr x, Object o) {
	    return visitExpr(x, o);
	  }

	  public /*@non_null*/ Object visitCondExpr(/*@non_null*/ CondExpr x, Object o) {
	    return visitExpr(x, o);
	  }


	  public /*@non_null*/ Object visitCastExpr(/*@non_null*/ CastExpr x, Object o) {
	    return visitExpr(x, o);
	  }

	 

	  public /*@non_null*/ Object visitAmbiguousVariableAccess(/*@non_null*/ AmbiguousVariableAccess x, Object o) {
	    return visitExpr(x, o);
	  }


	  public /*@non_null*/ Object visitFieldAccess(/*@non_null*/ FieldAccess x, Object o) {
	    return visitExpr(x, o);
	  }

	  public /*@non_null*/ Object visitAmbiguousMethodInvocation(/*@non_null*/ AmbiguousMethodInvocation x, Object o) {
	    return visitExpr(x, o);
	  }

	  

}
