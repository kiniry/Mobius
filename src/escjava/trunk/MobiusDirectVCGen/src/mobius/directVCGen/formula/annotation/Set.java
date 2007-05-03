package mobius.directVCGen.formula.annotation;

import java.util.Vector;


import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

public class Set extends AAnnotation {

	/**
	 * FOL-Terms  containing variable declarations. (Each Term is just a Variable)
	 * TODO: Could maybe be Vector<SortVar> instead
	 */
	public QuantVariableRef declaration =null;
	
	/**
	 * FOL-Terms translation of JML's set statement
	 */
	public Assignment assignment =null;

	@Override
	public int getID() {
		return annotSet;
	}
	
	public static class Assignment{
		public QuantVariableRef var =null;
		public Term expr =null;
		public  /*@non_null*/String toString() {
			return var + " := " + expr;
		}
	}
	
	public String toString(){
		return "Declare " + declaration + ", Set " + assignment;
	}
	
}
