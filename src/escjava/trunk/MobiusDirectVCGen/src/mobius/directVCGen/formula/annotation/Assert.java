package mobius.directVCGen.formula.annotation;

import escjava.sortedProver.Lifter.Term;

/**
 * Represents an assert; 
 * for instance like <code>assert t</code>
 * which is translated in the vcs as:  <code>t</code>, <code>t -> post</code>.
 */
public class Assert extends AAnnotation {

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.annotation.AAnnotation#getID()
	 */
	@Override
	public int getID() {
		return annotAssert;
	}

	/**
	 * Constructor that takes one argument, the term contained in the
	 * assert.
	 * @param t the term of the assert, should not be <code>null</code>
	 */
	public Assert(Term t){
		super(t);
		if(t == null) {
			throw new NullPointerException();
		}
	}
	
}
