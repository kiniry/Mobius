package mobius.directVCGen.formula.expression.bool;

import java.util.Vector;

import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.expression.AExpression;
import mobius.directVCGen.formula.expression.Expression;
import mobius.directVCGen.formula.type.Type;


public class Bool {
	public final static AExpression TRUE = new BTrue();
	public final static AExpression FALSE = new BFalse();
	
	public static AExpression and(IFormula arg1, IFormula arg2) {
		Vector<IFormula> args = new Vector<IFormula>();
		args.add(arg1);
		args.add(arg2);
		return new BAnd(args);
	}
	
	public static AExpression equals(IFormula arg1, IFormula arg2) {
		Vector<IFormula> args = new Vector<IFormula>();
		args.add(arg1);
		args.add(arg2);
		if (arg1.getType().equals(Type.bool)) {
			return new BEqualBool(args);
		} else if (arg1.getType().equals(Type.refs)) {
			return new BEqualRef(args);	
		}
		else {
			return new BEqualNum(args);
		}
	}
	
	public static AExpression equalBool(IFormula arg1, IFormula arg2) {
		Vector<IFormula> args = new Vector<IFormula>();
		args.add(arg1);
		args.add(arg2);
		return new BEqualBool(args);
	}
	
	public static AExpression equalNum(IFormula arg1, IFormula arg2) {
		Vector<IFormula> args = new Vector<IFormula>();
		args.add(arg1);
		args.add(arg2);
		return new BEqualNum(args);
	}
	
	public static AExpression equalRef(IFormula arg1, IFormula arg2) {
		Vector<IFormula> args = new Vector<IFormula>();
		args.add(arg1);
		args.add(arg2);
		return new BEqualRef(args);
	}
	
	public static AExpression implies(IFormula arg1, IFormula arg2) {
		Vector<IFormula> args = new Vector<IFormula>();
		args.add(arg1);
		args.add(arg2);
		return new BImplies(args);
	}
	
	public static AExpression not(IFormula arg) {
		Vector<IFormula> args = new Vector<IFormula>();
		args.add(arg);
		return new BNot(args);
	}
	
	
	public static AExpression or(IFormula arg1, IFormula arg2) {
		Vector<IFormula> args = new Vector<IFormula>();
		args.add(arg1);
		args.add(arg2);
		return new BOr(args);
	}
	
	
	/**
	 * Main for testing purpose.
	 * @param args 
	 */
	public static void main(String [] args) {
		IFormula formula = 
			 Bool.implies(Bool.not(Bool.and(Bool.equals(Expression.var("vFirst", Type.bool),
				Bool.TRUE), Bool.FALSE)), Bool.TRUE);
		System.out.println(formula);
	}

	public static AExpression value(boolean b) {
		if(b)
			return TRUE;
		else
			return FALSE;
	}
}
