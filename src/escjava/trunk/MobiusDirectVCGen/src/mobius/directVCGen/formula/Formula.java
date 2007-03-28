package mobius.directVCGen.formula;

import mobius.directVCGen.formula.expression.bool.Bool;

public class Formula {

	public static IFormula equals(IFormula f1, IFormula f2) {
		return Bool.equals(f1, f2);
	}
}
