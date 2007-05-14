package mobius.directVCGen.formula.annotation;

import escjava.sortedProver.Lifter.Term;

public abstract class AAnnotation {
	/** an undefined id */
	public static final int undef = 0;
	/** the id of an assert class */
	public static final int annotAssert = undef + 1;
	/** the id of an assume class */
	public static final int annotAssume = annotAssert + 1;
	/** the id of a cut class */
	public static final int annotCut = annotAssume + 1;
	/** the id of a set class */
	public static final int annotSet = annotCut + 1;
	
	/**
	 * FOL-Term that represents the annotation at that point
	 */
	public Term formula;
	
	// TODO: add comments
	public AAnnotation(){
	}
	
	// TODO: add comments
	public AAnnotation(Term t){
		this.formula = t;
	}
	
	/**
	 * Return the ID of the class in order to do a switch
	 * @return an id precising which class the current object is from
	 */
	public abstract int getID();
	
	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return "" + formula;
	}
	
}
