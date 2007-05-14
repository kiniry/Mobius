package mobius.directVCGen.formula.annotation;

import escjava.sortedProver.Lifter.Term;

// TODO: add comments
public class Cut extends AAnnotation {

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.annotation.AAnnotation#getID()
	 */
	@Override
	public int getID() {
		return annotCut;
	}

	// TODO: add comments
	public Cut(Term t){
		super(t);
	}
	
}
