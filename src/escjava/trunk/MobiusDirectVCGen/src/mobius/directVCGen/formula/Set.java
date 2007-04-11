package mobius.directVCGen.formula;

import java.util.Vector;

import escjava.sortedProver.Lifter.Term;
import javafe.ast.Stmt.Annotation;

public class Set implements Annotation {

	/**
	 * FOL-Terms  containing variable declarations. (Each Term is just a Variable)
	 * TODO: Could maybe be Vector<SortVar> instead
	 */
	public Vector<Term> declarations;
	
	/**
	 * FOL-Terms translation of JML's set statement
	 */
	public Vector<Term> assignments;
	
}
