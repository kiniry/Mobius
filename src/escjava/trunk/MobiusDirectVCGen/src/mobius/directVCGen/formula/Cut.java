package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter.Term;
import javafe.ast.Stmt.Annotation;


public class Cut implements Annotation {

	/**
	 * FOL-Term that should be 'cutted' in the VCGen at this point
	 */
	public Term formula;
	
}
