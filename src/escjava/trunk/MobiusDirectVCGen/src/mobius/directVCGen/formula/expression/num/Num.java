package mobius.directVCGen.formula.expression.num;

import java.util.Vector;

import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.expression.AExpression;
import mobius.directVCGen.formula.utils.NumSimplifierVisitor;


public class Num {
	public static AExpression add(IFormula arg1, IFormula arg2) {
		Vector<IFormula> args = new Vector<IFormula>();
		args.add(arg1);
		args.add(arg2);
		return new NAdd(args);
	}
	public static AExpression value(int i) {
		return new NInt(i);
	}
	public static AExpression value(long i) {
		return new NLong(i);
	}
	public static AExpression value(short i) {
		return new NShort(i);
	}
	public static AExpression value(byte i) {
		return new NByte(i);
	}
	public static AExpression minus(IFormula arg) {
		Vector<IFormula> args = new Vector<IFormula>();
		args.add(arg);
		return new NMinus(args);
	}
	/**
	 * Main for testing purpose.
	 * @param args 
	 */
	public static void main(String [] args) {
		IFormula f = 
			Num.minus(Num.add(Num.value(3), Num.add(Num.value(3), Num.value((long)2))));
		System.out.println(f);
		System.out.println(NumSimplifierVisitor.simplifyFormula(f));
	}
}
