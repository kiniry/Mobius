package mobius.directVCGen.formula.annotation;

import escjava.sortedProver.Lifter.Term;

// TODO: add comments
public class Assume extends AAnnotation {

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.annotation.AAnnotation#getID()
	 */
	@Override
	public int getID() {
		return annotAssume;
	}

	// TODO: add comments
	public Assume(Term t){
		super(t);
	}
	
}
