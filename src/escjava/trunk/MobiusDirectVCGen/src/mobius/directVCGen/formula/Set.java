package mobius.directVCGen.formula;

import java.util.Vector;

import escjava.sortedProver.Lifter.Term;
import javafe.ast.Stmt.Annotation;

public class Set implements Annotation {

	public Vector<Term> declarations;
	
	public Vector<Term> assignments;
	
}
