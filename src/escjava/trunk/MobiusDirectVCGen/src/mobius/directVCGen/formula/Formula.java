package mobius.directVCGen.formula;

import javafe.ast.Type;
import escjava.sortedProver.Lifter;
import escjava.sortedProver.Lifter.Term;

public class Formula {
	static Lifter lf = new Lifter(null);
	
	public static Lifter getCurrentLifter() {
		return lf;
	}

	public static Term translate(Type type) {
		return lf.symbolRef(type.toString());
	}
	
}
