/*
 * Created on Apr 28, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.branch;

import org.apache.bcel.generic.InstructionHandle;

import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.vm.Stack;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCIF_ICMPLE extends BCConditionalBranch {

	/**
	 * @param _branchInstruction
	 */
	public BCIF_ICMPLE(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
	}
	
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;

		/////////////////////////////////////////////	
		//top of the stack is not greater than the stack at level top-1
		// S(t-1) > S(t)
		Formula stackTop_minus_1_not_leq_stackTop =
			new Predicate2Ar(
				new Stack(Expression.getCOUNTER_MINUS_1()),
				new Stack(Expression.COUNTER),
				PredicateSymbol.GRT);

		//psi^n[t <-- t-2]
		Formula not_leq_branch =
		(Formula)_normal_Postcondition.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_MINUS_2());

		//!( S(t-1) > S(t))== > psi^n[t <-- t-2]
		wp =
			Formula.getFormula(
				stackTop_minus_1_not_leq_stackTop,
				not_leq_branch,
				Connector.IMPLIES);
		return wp;
	}

	/* (non-Javadoc)
	 * @see bytecode.branch.BCConditionalBranch#wpBranch(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public Formula wpBranch(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;
		
		// top of the stack is greater or equal than the stack at level top-1
		//S(t-1) <= S(t)
		Formula stackTop_minus_1_leq_stackTop =
			new Predicate2Ar(
				new Stack(Expression.getCOUNTER_MINUS_1()),
				new Stack(Expression.COUNTER),
				PredicateSymbol.LESSEQ);
		
		//getWPBranch[t<-- t-2]
		Formula leq_branch =
		(Formula)_normal_Postcondition.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_MINUS_2());
		//S(t-1) <= S(t) == >  getWPBranch[t<-- t-2]
		wp =
			Formula.getFormula(
				stackTop_minus_1_leq_stackTop,
				leq_branch,
				Connector.IMPLIES);

		return wp;
	}
}
