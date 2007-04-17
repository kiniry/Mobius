package mobius.directVCGen.formula.jmlTranslator;

import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Num;
import escjava.sortedProver.Lifter.Term;
import javafe.ast.BinaryExpr;

public class JmlExprToFormula {

	JmlVisitor v;
	
	public JmlExprToFormula(JmlVisitor visitor) {
		v = visitor;
	}

	public Term and(BinaryExpr expr) {
		Term t1 = (Term)expr.left.accept(v,null);
		Term t2 = (Term)expr.right.accept(v,null);
		return Logic.and(t1, t2);
	}
	
	public Term add(BinaryExpr expr) {
		Term t1 = (Term)expr.left.accept(v,null);
		Term t2 = (Term)expr.right.accept(v,null);
		return Num.add(t1, t2);
	}

	public Object eq(BinaryExpr expr) {
		Term t1 = (Term)expr.left.accept(v,null);
		Term t2 = (Term)expr.right.accept(v,null);
		return Logic.equals(t1,t2);
	}

	public Object ne(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object ge(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object gt(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object le(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object lt(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object bitor(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object bitxor(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object bitand(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object lshift(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object rshift(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object urshift(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object sub(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object div(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object mod(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object star(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object assign(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asgmul(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asgdiv(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asgrem(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asgadd(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asgsub(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asglshift(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asgrshift(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asgurshif(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object asgbitand(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object implies(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object explies(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}


	public Object iff(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object niff(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object subtype(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object dotdot(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object or(BinaryExpr expr) {
		// TODO Auto-generated method stub
		return null;
	}

	

}
