package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter.Term;

public class Bool {

	public static Term value(Boolean b) {	
		return Formula.lf.mkBoolLiteral(b);
	}

	public static Term equals(Term l, Term r) {
		
		return Formula.lf.mkFnTerm(Formula.lf.symAnyEQ, new Term[] {l, r});
	}

}
