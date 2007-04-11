package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;

public class Expression {
	public static QuantVariableRef var(String str) {
		QuantVariable v = null;
		return Formula.lf.mkQuantVariableRef(v);
	}
}
