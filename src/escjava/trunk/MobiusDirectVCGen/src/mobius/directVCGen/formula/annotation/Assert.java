package mobius.directVCGen.formula.annotation;

import escjava.sortedProver.Lifter.Term;


public class Assert extends AAnnotation {

	@Override
	public int getID() {
		return annotAssert;
	}

	public Assert(Term t){
		super(t);
	}
	
}
