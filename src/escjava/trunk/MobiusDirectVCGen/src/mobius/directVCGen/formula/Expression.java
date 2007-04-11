package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.NodeBuilder.Sort;

public class Expression {
	public static QuantVariableRef var(String str) {
		QuantVariable v = null;
		return Formula.lf.mkQuantVariableRef(v);
	}
	public static QuantVariableRef var(Sort s) {
		QuantVariable v =  Formula.lf.mkQuantVariable("x", s);
		return Formula.lf.mkQuantVariableRef(v);
	}
	public static FnTerm var(String name, Sort s) {
		return Formula.lf.symbolRef (name, s);
	}
}
