package mobius.directVCGen.formula.expression;

import java.util.Iterator;
import java.util.Vector;

import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.type.FunType;
import mobius.directVCGen.formula.type.TypeErrorException;


public abstract class APrefixExpr extends AExpression {
	/** the name of the prefix expression */
	private final String fName;
	
	/**
	 * Create an expression using its name, its type, and giving it
	 * some arguments.
	 * @param name The name of the expression
	 * @param args Its arguments
	 * @param fType The type the arguments and the expression should have.
	 */
	public APrefixExpr(String name, Vector<IFormula> args, FunType fType) {
		super(fType.getReturnType(), args);
		fName = name;
		try {
			checkType(fType);
		} catch (TypeErrorException e) {
			throw new IllegalArgumentException("Bad typing for: " + name +"; " +
							e.getMessage());
		}
	}
	
	public String toString() {
		Iterator<IFormula> iter = this.iterator();
		String res = "(" + fName ;
		while(iter.hasNext()) {
			res += " " + iter.next();
		}
		return res + "):" + getType();
	}

}
