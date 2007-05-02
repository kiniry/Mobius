package mobius.directVCGen.formula.annotation;

import escjava.sortedProver.Lifter.Term;


public class Cut extends AAnnotation {

	@Override
	public int getID() {
		return annotCut;
	}

	public Cut(Term t){
		super(t);
	}
	
}
