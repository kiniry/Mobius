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
 * if_icmpeq - wp the same as for if_acmpeq
 */
public class BCIF_ICMPEQ extends BCConditionalBranch {

	/**
	 * @param _branchInstruction
	 */
	public BCIF_ICMPEQ(InstructionHandle _branchInstruction) {
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
		// top two stack values are equal 
		//S(t)== S(t-1)
		Formula stackTop_equals_stackTop_minus_1 =
			new Predicate2Ar(stackTop, stackTop_minus_1, PredicateSymbol.EQ);
		//getWPBranch
		Formula eq_branch = getBranchWP();

		//getWPBranch[t<-- t-2]
		eq_branch =
			eq_branch.substitute(
				Expression.COUNTER,
				Expression.COUNTER_MINUS_2);
		//S(t)== S(t-1) == >  getWPBranch[t<-- t-2]
		Formula wp_eq_branch =
			new Formula(
				stackTop_equals_stackTop_minus_1,
				eq_branch,
				Connector.IMPLIES);

		/////////////////////////////////////////////	
		//top two stack values are not equal
		//S(t)!= S(t-1)
		Formula stackTop_not_equals_stackTop_minus_1 =
			new Formula(stackTop_equals_stackTop_minus_1, Connector.NOT);

		//psi^n[t <-- t-2]
		Formula not_eq_branch =
			_normal_Postcondition.substitute(
				Expression.COUNTER,
				Expression.COUNTER_MINUS_2);

		//S(t)!= S(t-1) == > psi^n[t <-- t-2]
		Formula wp_not_eq_branch =
			new Formula(
				stackTop_not_equals_stackTop_minus_1,
				not_eq_branch,
				Connector.IMPLIES);

		wp = new Formula(wp_not_eq_branch, wp_eq_branch, Connector.AND);
		return wp;
	}

}
