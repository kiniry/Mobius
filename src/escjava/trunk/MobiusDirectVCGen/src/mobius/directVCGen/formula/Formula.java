package mobius.directVCGen.formula;

import mobius.directVCGen.formula.coq.CoqNodeBuilder;
import escjava.sortedProver.Lifter;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.STerm;
import escjava.sortedProver.NodeBuilder.Sort;

public class Formula {
	static Lifter lf = new Lifter(new CoqNodeBuilder());
	public static Sort sort = lf.sortAny;
	public static QuantVariable program = Expression.var("p");
	public static STerm generateFormulas(Term t) {
		lf.dumpBuilder = lf.builder;
		STerm st = t.dump();
		lf.dumpBuilder = null;
		return st;
	}
	
	/**
	 * Every use of this function should be replaced by a 'proper'
	 * library call.
	 * @deprecated
	 */
    public static Lifter getCurrentLifter() {
		return lf;
	}

	
}
