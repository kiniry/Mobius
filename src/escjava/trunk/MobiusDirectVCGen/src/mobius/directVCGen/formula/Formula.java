package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter;

public class Formula {
	static Lifter lf = new Lifter(null);
	public Lifter getCurrentLifter() {
		return lf;
	}
	
}
