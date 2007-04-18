package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter;
import escjava.sortedProver.NodeBuilder.Sort;

public class Formula {
	static Lifter lf = new Lifter(null);
	public static Sort sort = lf.sortAny;
	
	/**
	 * Every use of this function should be replaced by a 'proper'
	 * library call.
	 * @deprecated
	 */
    public static Lifter getCurrentLifter() {
		return lf;
	}

	
}
