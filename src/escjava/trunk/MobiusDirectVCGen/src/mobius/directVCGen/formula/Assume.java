package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter.Term;
import javafe.ast.Stmt.Annotation;

public class Assume implements Annotation {

	/**
	 * FOL-Term that should be assumed in the VCGen at this point
	 */
	public Term formula;
	
}
