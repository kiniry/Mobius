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
import bcexpression.NumberLiteral;
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
public class BCIFLT extends BCConditionalBranch {

	/**
	 * @param _branchInstruction
	 */
	public BCIFLT(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
		// TODO Auto-generated constructor stub
	}
	
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.Exsures)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		Stack stackTop = new Stack(Expression.COUNTER);

		//in case of jump
		Formula stackTop_less_0 = new Predicate2Ar(stackTop, new NumberLiteral(0), PredicateSymbol.LESS);
		Formula less_branch = getBranchWP();
		less_branch = less_branch.substitute(Expression.COUNTER, Expression.COUNTER_MINUS_1);
		Formula wp_stackTop_lesseq_0 = new Formula( stackTop_less_0, less_branch, Connector.IMPLIES);

		// in case of executing next instruction
		Formula stackTop_not_less_0 = new Formula( stackTop_less_0, Connector.NOT);
		Formula not_less_branch = _normal_Postcondition.substitute(Expression.COUNTER, Expression.COUNTER_MINUS_1);
		Formula wp_stackTop_not_less_0 = new Formula( stackTop_not_less_0, not_less_branch, Connector.IMPLIES);

		wp = new Formula(wp_stackTop_lesseq_0, wp_stackTop_not_less_0, Connector.AND);
		return wp;
	}

}
