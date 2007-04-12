package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

public class Expression {
	public static Term preHeap = var("\\preHeap");
	public static Term heap = var("\\heap");
		
	public static QuantVariableRef var(String str) {
		QuantVariable v = null;
		return Formula.lf.mkQuantVariableRef(v);
	}
	private static int varCounter = 0;

	public static QuantVariableRef var(Sort s) {
		QuantVariable v =  Formula.lf.mkQuantVariable("x" + varCounter++, s);
		return Formula.lf.mkQuantVariableRef(v);
	}
	public static FnTerm var(String name, Sort s) {
		return Formula.lf.symbolRef (name, s);
	}
	
	public static FnTerm typeof(Term heap, Term var) {
		return Formula.lf.mkFnTerm(Formula.lf.symTypeOf, new Term[] {heap, var});
	}
}
