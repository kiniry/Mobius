package mobius.directVCGen.formula.expression;

import mobius.directVCGen.formula.type.Type;

public class Expression {
	/**
	 * Creates a variable.
	 * @param name The name of the variable
	 * @param t Its type.
	 * @return a newly created expression representing a variable.
	 */
	public static Variable var(String name, Type t) {
		if(name == null || t == null) {
			throw new IllegalArgumentException();
		}
		return new Variable(name, t);
	}
}
