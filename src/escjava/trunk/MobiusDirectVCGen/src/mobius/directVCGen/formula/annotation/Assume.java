package mobius.directVCGen.formula.annotation;

import escjava.sortedProver.Lifter.Term;


public class Assume extends AAnnotation {

	@Override
	public int getID() {
		return annotAssume;
	}

	public Assume(Term t){
		super(t);
	}
	
}
