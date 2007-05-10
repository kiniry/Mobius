package mobius.directVCGen.formula;

import mobius.directVCGen.formula.coq.CoqNodeBuilder;
import escjava.sortedProver.Lifter;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.STerm;
import escjava.sortedProver.NodeBuilder.Sort;

// TODO: add comments
public class Formula {
	
	// TODO: add comments
	static Lifter lf = new Lifter(new CoqNodeBuilder());
	
	/** 
	 * the sort that represents any sort... should not be used 
	 * @deprecated use any other sort from any other library
	 */
	public static Sort sort = lf.sortAny;
	/**
	 * program is inner to Coq's representation: it is
	 * dubious that it should appear in formulas
	 * @deprecated use only at the Coq level
	 */
	public static QuantVariable program = Expression.var("p");
	
	
	// TODO: add comments
	public static STerm generateFormulas(Term t) {
		lf.dumpBuilder = lf.builder;
		STerm st = t.dump();
		lf.dumpBuilder = null;
		return st;
	}
	
	// TODO: add comments
	public static STerm [] generateTypes(Sort [] sorts) {
		STerm [] res = new STerm[sorts.length]; 
		lf.dumpBuilder = lf.builder;
		
		for(int i = 0; i < sorts.length; i++) {
			res[i] = lf.builder.buildSort(sorts[i]);
		}
		lf.dumpBuilder = null;
		return res;
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
