/*
 * Created on Apr 29, 2004
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
public class BCIF_ICMPNE extends BCConditionalBranch {

	/**
	 * @param _branchInstruction
	 */
	public BCIF_ICMPNE(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
		// TODO Auto-generated constructor stub
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.Exsures)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;
		Stack stackTop = new Stack(Expression.COUNTER);
		Stack stackTop_minus_1 = new Stack(Expression.COUNTER_MINUS_1);

		///////////////////////////////////////////	
		// top two stack values are not equal - do a jump
		//S(t)== S(t-1)
		Formula stackTop_not_eq_stackTop_minus_1 =
			new Predicate2Ar(stackTop, stackTop_minus_1, PredicateSymbol.NOTEQ);
		//getWPBranch
		Formula not_eq_branch = getBranchWP();

		//getWPBranch[t<-- t-2]
		not_eq_branch =
			not_eq_branch.substitute(
				Expression.COUNTER,
				Expression.COUNTER_MINUS_2);
		//S(t)== S(t-1) == >  getWPBranch[t<-- t-2]
		Formula wp_not_eq_branch =
			new Formula(
				stackTop_not_eq_stackTop_minus_1,
				not_eq_branch,
				Connector.IMPLIES);

		/////////////////////////////////////////////	
		//top two stack values are  equal
		//S(t)== S(t-1)
		Formula stackTop_eq_stackTop_minus_1 =
			new Predicate2Ar(stackTop, stackTop_minus_1, PredicateSymbol.EQ);

		//psi^n[t <-- t-2]
		Formula eq_branch =
			_normal_Postcondition.substitute(
				Expression.COUNTER,
				Expression.COUNTER_MINUS_2);

		//S(t)== S(t-1) == > psi^n[t <-- t-2]
		Formula wp_eq_branch =
			new Formula(
				stackTop_eq_stackTop_minus_1,
				eq_branch,
				Connector.IMPLIES);

		wp = new Formula(wp_not_eq_branch, wp_eq_branch, Connector.AND);
		return wp;

	}

}
