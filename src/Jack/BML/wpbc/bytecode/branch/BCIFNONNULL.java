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
public class BCIFNONNULL extends BCConditionalBranch {

	/**
	 * @param _branchInstruction
	 */
	public BCIFNONNULL(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.Exsures)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;

		// in case of executing next instruction
		Formula stackTop_eq_null =
			new Predicate2Ar(
				new Stack(Expression.COUNTER),
				Expression._NULL,
				PredicateSymbol.EQ);
		Formula eq_branch =
		(Formula)_normal_Postcondition.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_MINUS_1());
		wp =
			Formula.getFormula(stackTop_eq_null, eq_branch, Connector.IMPLIES);

		return wp;
	}

	/* (non-Javadoc)
	 * @see bytecode.branch.BCConditionalBranch#wpBranch(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public Formula wpBranch(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;

		//in case of jump
		Formula stackTop_noteq_null =
			Formula.getFormula( new Predicate2Ar(
				new Stack(Expression.COUNTER),
				Expression._NULL,
				PredicateSymbol.EQ), Connector.NOT);

		Formula noteq_branch  =
		(Formula)_normal_Postcondition.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_MINUS_1());

		wp =
			Formula.getFormula(
				stackTop_noteq_null,
				noteq_branch,
				Connector.IMPLIES);

		return wp;
	}

}
