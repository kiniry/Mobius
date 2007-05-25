package mobius.directVCGen.formula.annotation;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

// TODO: add comments
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

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.annotation.AAnnotation#getID()
	 */
	@Override
	public int getID() {
		return annotSet;
	}
	
	/**
	 * Default constructor
	 */
	public Set(){
	}
	
	/**
	 * Build a new set from a variable and its assignment
	 * @param decl the variable to assign
	 * @param assign the JML assignment associated to this construct
	 */
	public Set(QuantVariableRef decl, Assignment assign){
		this.declaration= decl;
		this.assignment = assign;
	}
	
	/**
	 * Inner class that represents an JML assignment (set statement)
	 */
	public static class Assignment{
		// TODO: add comments
		public Assignment(){
			super();
		}
		
		// TODO: add comments
		public Assignment(QuantVariableRef var, Term expr){
			this.var = var;
			this.expr= expr;
		}
		
		// TODO: add comments
		public QuantVariableRef var =null;
		// TODO: add comments
		public Term expr =null;

		/*
		 * (non-Javadoc)
		 * @see java.lang.Object#toString()
		 */
		public String toString() {
			return var + " := " + expr;
		}
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.annotation.AAnnotation#toString()
	 */
	public String toString(){
		return "Declare " + declaration + ", Set " + assignment;
	}
	
}
