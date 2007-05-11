package mobius.directVCGen.formula.annotation;

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
	
	public Set(){
		super();
	}
	
	public Set(QuantVariableRef decl, Assignment assign){
		this.declaration= decl;
		this.assignment = assign;
	}
	
	/**
	 * Inner class that represents an JML assignment (set statement)
	 */
	public static class Assignment{
		public Assignment(){
			super();
		};
		public Assignment(QuantVariableRef var, Term expr){
			this.var = var;
			this.expr= expr;
		}
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
