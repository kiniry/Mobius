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
 * if_icmpge
 */
public class BCIF_ICMPGE extends BCConditionalBranch {

	/**
	 * @param _branchInstruction
	 */
	public BCIF_ICMPGE(InstructionHandle _branchInstruction) {
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
		// top of the stack is greater than the stack at level top-1
		//S(t-1) > S(t)
		Formula stackTop_minus_1_grteq_stackTop =
			new Predicate2Ar( stackTop_minus_1, stackTop,PredicateSymbol.GRTEQ);
		//getWPBranch
		Formula grteq_branch = getBranchWP();

		//getWPBranch[t<-- t-2]
		grteq_branch =
			grteq_branch.substitute(
				Expression.COUNTER,
				Expression.COUNTER_MINUS_2);
		//S(t-1) > S(t) == >  getWPBranch[t<-- t-2]
		Formula wp_grteq_branch =
			new Formula(
				stackTop_minus_1_grteq_stackTop,
				grteq_branch,
				Connector.IMPLIES);

		/////////////////////////////////////////////	
		//top of the stack is not greater than the stack at level top-1
		//!( S(t-1) > S(t))
		Formula stackTop_minus_1_not_grteq_stackTop =
			new Formula(stackTop_minus_1_grteq_stackTop, Connector.NOT);

		//psi^n[t <-- t-2]
		Formula not_grteq_branch =
			_normal_Postcondition.substitute(
				Expression.COUNTER,
				Expression.COUNTER_MINUS_2);

		//!( S(t-1) > S(t))== > psi^n[t <-- t-2]
		Formula wp_not_grteq_branch =
			new Formula(
				stackTop_minus_1_not_grteq_stackTop,
				not_grteq_branch,
				Connector.IMPLIES);

		wp = new Formula(wp_not_grteq_branch, wp_grteq_branch, Connector.AND);
		return wp;
	}

}
