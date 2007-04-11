package mobius.directVCGen.vcgen.intern;

import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Num;
import javafe.ast.BinaryExpr;
import javafe.ast.FieldDecl;
import javafe.ast.FormalParaDecl;
import javafe.ast.GenericVarDecl;
import javafe.ast.LiteralExpr;
import javafe.ast.LocalVarDecl;
import javafe.ast.UnaryExpr;
import javafe.ast.VariableAccess;
import javafe.util.ErrorSet;
import escjava.ast.Modifiers;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;
import escjava.translate.UniqName;

public class ExpressionVisitor extends ABasicVisitor {
	public Object visitBinaryExpr(BinaryExpr expr, Object o) {
		
		//System.out.println(TagConstants.toString(expr.op));
		ExprResult post = (ExprResult) o;
		switch(expr.op) {
			case TagConstants.EQ:
				return vcGenEquals(expr, post);
				
			case TagConstants.OR:
			case TagConstants.AND:
			case TagConstants.BITOR:
			case TagConstants.BITXOR:
			case TagConstants.BITAND:
			case TagConstants.NE:

			case TagConstants.GE:
			case TagConstants.GT:
			case TagConstants.LE:
			case TagConstants.LT:
			case TagConstants.LSHIFT:
			case TagConstants.RSHIFT:
			case TagConstants.URSHIFT:
			case TagConstants.ADD:
			case TagConstants.SUB:
			case TagConstants.DIV:
			case TagConstants.MOD:
			case TagConstants.STAR:
		// jml specific operators
			case TagConstants.IMPLIES:
			case TagConstants.EXPLIES:
			case TagConstants.IFF: // equivalence (equality)
			case TagConstants.NIFF:     // discrepance (xor)
			case TagConstants.SUBTYPE:
			case TagConstants.DOTDOT:
				throw new IllegalArgumentException("Unmanaged construct :" +
						TagConstants.toString(expr.op) +" " +  expr);
			default:
				throw new IllegalArgumentException("Unknown construct :" +
						TagConstants.toString(expr.op) +" " +  expr);
		}
	}
	
	public ExprResult vcGenEquals(BinaryExpr expr, ExprResult post) {
		post = (ExprResult)expr.right.accept(this, post);
//		IFormula right = post.;
//		post = (ExprResult)expr.left.accept(this, post);
//		IFormula left = post.res;
//
//		
//		post.res = Formula.equals(left, right);
		return post;
	}

	public Object visitLiteralExpr(LiteralExpr expr,  Object o) {
		ExprResult result = (ExprResult) o;
		
		//System.out.println(TagConstants.toString(expr.tag));
		switch (expr.tag) {
			case TagConstants.BOOLEANLIT:
				result.substWith(Bool.value((Boolean)expr.value));
				break;
			case TagConstants.INTLIT:
				result.substWith(Num.value((Integer)expr.value));
				break;
			case TagConstants.LONGLIT:
				result.substWith(Num.value((Long)expr.value));
				break;
			case TagConstants.BYTELIT:
				result.substWith(Num.value((Byte)expr.value));
				break;
			case TagConstants.SHORTLIT: 
				result.substWith(Num.value((Short)expr.value));
				break;
			case TagConstants.FLOATLIT:;
			case TagConstants.CHARLIT:
			case TagConstants.DOUBLELIT:
			case TagConstants.STRINGLIT:
			case TagConstants.NULLLIT:
				throw new IllegalArgumentException("Unmanaged construct :" +
						TagConstants.toString(expr.tag) +" " +  expr);
			default:
				throw new IllegalArgumentException("Unknown construct :" +
						TagConstants.toString(expr.tag) +" " +  expr);
		}
		return result;
	}

	public Object visitUnaryExpr(UnaryExpr expr, Object o) {
		//System.out.println(TagConstants.toString(expr.op));
		ExprResult post = (ExprResult) o;
		switch(expr.op) {
			case TagConstants.POSTFIXINC:
				return vcGenPostfixInc(expr, post);
			case TagConstants.INC:
				return vcGenInc(expr, post);
			case TagConstants.POSTFIXDEC:
				return vcGenPostfixDec(expr, post);
			case TagConstants.DEC:
				return vcGenDec(expr, post);
				
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
	
	public Object visitVariableAccess(VariableAccess m, Object o) {
		ExprResult res = (ExprResult) o;
		
		Sort s = null;
		String name = UniqName.variable(m.decl);
			
		GenericVarDecl decl = m.decl;
			
		if (decl instanceof LocalVarDecl && ((LocalVarDecl)decl).source != null) {
			decl = ((LocalVarDecl)decl).source;				
			
			if (decl instanceof FieldDecl) {
				FieldDecl d = (FieldDecl)decl;
				if (Modifiers.isStatic(d.getModifiers()))
					s = Formula.getCurrentLifter().typeToSort(d.type);
				else
					s = Formula.getCurrentLifter().registerMapSort(Formula.getCurrentLifter().sortRef, Formula.getCurrentLifter().typeToSort(d.type));
				//ErrorSet.caution("VariableAccess " + name + " -> " + s);
			} else if (decl instanceof LocalVarDecl || decl instanceof FormalParaDecl) {
				GenericVarDecl g = (GenericVarDecl)decl;
				s = Formula.getCurrentLifter().typeToSort(g.type);
				//ErrorSet.caution("VariableAccess local " + name + " -> " + s);
			} else {
				ErrorSet.caution("unknown decl in VariableAccess " + m.decl.getClass());
			}
			
			
			
		}
		res.substWith(Expression.var(name, s));
		return  res;
	}
	public ExprResult vcGenPostfixInc(UnaryExpr expr, ExprResult r) {
		//ExprResult res = (ExprResult)visitASTNode(expr, r);
//		Variable v = (Variable)res.res;
//		res.post = res.post.subst(v, Num.add(v, Num.value(1)));
		return r;
	}

	public ExprResult vcGenInc(UnaryExpr expr, ExprResult r) {
		ExprResult res = (ExprResult)visitASTNode(expr, r);
//		Variable v = (Variable)res.res;
//		res.res = Num.add(v, Num.value(1));
//		res.post = res.post.subst(v, res.res);
		return res;
	}
	public ExprResult vcGenPostfixDec(UnaryExpr expr, ExprResult r) {
		ExprResult res = (ExprResult)visitASTNode(expr, r);
//		Variable v = (Variable)res.res;
//		res.post = res.post.subst(v, Num.sub(v, Num.value(1)));
		return res;
	}
	public ExprResult vcGenDec(UnaryExpr expr, ExprResult r) {
		ExprResult res = (ExprResult)visitASTNode(expr, r);
//		Variable v = (Variable)res.res;
//		res.res = Num.sub(v, Num.value(1));
//		res.post = res.post.subst(v, res.res);
		return res;
	}
}
