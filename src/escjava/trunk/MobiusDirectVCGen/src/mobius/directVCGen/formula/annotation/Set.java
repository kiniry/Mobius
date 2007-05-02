package mobius.directVCGen.formula.annotation;

import java.util.Vector;


import escjava.sortedProver.Lifter.Term;

public class Set extends AAnnotation {

	/**
	 * FOL-Terms  containing variable declarations. (Each Term is just a Variable)
	 * TODO: Could maybe be Vector<SortVar> instead
	 */
	public Term declaration;
	
	/**
	 * FOL-Terms translation of JML's set statement
	 */
	public Term assignment;

	@Override
	public int getID() {
		return annotSet;
	}
	
}
