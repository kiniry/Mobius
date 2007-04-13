package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

public class Bool {

	public static Term value(Boolean b) {	
		return Formula.lf.mkBoolLiteral(b);
	}

	public static Term equals(Term l, Term r) {
		Term t = Formula.lf.mkFnTerm(Formula.lf.symAnyEQ, new Term[] {l, r});
		
		return t;
	}


	public static Sort sort = Formula.lf.sortBool;
}
