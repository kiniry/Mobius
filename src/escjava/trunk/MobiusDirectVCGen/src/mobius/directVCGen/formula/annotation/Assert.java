package mobius.directVCGen.formula.annotation;

import escjava.sortedProver.Lifter.Term;

// TODO: add comments
public class Assert extends AAnnotation {

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.annotation.AAnnotation#getID()
	 */
	@Override
	public int getID() {
		return annotAssert;
	}

	// TODO: add comments
	public Assert(Term t){
		super(t);
	}
	
}
