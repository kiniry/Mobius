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
public class BCIFNULL extends BCConditionalBranch  {

	/**
	 * @param _branchInstruction
	 */
	public BCIFNULL(InstructionHandle _branchInstruction) {
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
		Formula stackTop_eq_null = new Predicate2Ar(stackTop, Expression.NULL, PredicateSymbol.EQ);
		Formula eq_branch = getBranchWP();
		eq_branch = eq_branch.substitute(Expression.COUNTER, Expression.COUNTER_MINUS_1);
		Formula wp_stackTop_eq_null = new Formula( stackTop_eq_null, eq_branch, Connector.IMPLIES);
		
		// in case of executing next instruction
		Formula stackTop_noteq_null = new Predicate2Ar( stackTop, Expression.NULL, PredicateSymbol.NOTEQ);
		Formula noteq_branch = _normal_Postcondition.substitute(Expression.COUNTER, Expression.COUNTER_MINUS_1);
		Formula wp_stackTop_noteq_null = new Formula( stackTop_noteq_null, noteq_branch, Connector.IMPLIES);
		
		wp = new Formula(wp_stackTop_eq_null, wp_stackTop_noteq_null, Connector.AND);
		return wp;
	}

}
