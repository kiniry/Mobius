package mobius.directVCGen.formula.annotation;

import escjava.sortedProver.Lifter.Term;
import javafe.ast.Stmt.Annotation;

public abstract class AAnnotation implements Annotation {
	public static final int undef = 0;
	public static final int annotAssert = undef + 1;
	public static final int annotAssume = annotAssert + 1;
	public static final int annotCut = annotAssume + 1;
	public static final int annotSet = annotCut + 1;
	
	/**
	 * FOL-Term that represents the annotation at that point
	 */
	public Term formula;
	
	/**
	 * Annotations can be chained together
	 */
	public Annotation next;
	
	public abstract int getID();
	
}
