package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter.Term;
import javafe.ast.Stmt.Annotation;

public abstract class AAnnotation implements Annotation {

	/**
	 * FOL-Term that represents the annotation at that point
	 */
	public Term formula;
	
	/**
	 * Annotations can be chained together
	 */
	public Annotation next;
	
}
