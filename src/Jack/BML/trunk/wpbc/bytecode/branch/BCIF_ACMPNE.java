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
 * if_acmpne - dual to if_acmpeq
 */
public class BCIF_ACMPNE extends BCConditionalBranch {

	/**
	 * @param _branchInstruction
	 */
	public BCIF_ACMPNE(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
		// TODO Auto-generated constructor stub
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.Exsures)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
//		Stack stackTop = new Stack(Expression.COUNTER);
//		Stack stackTop_minus_1 = new Stack( Expression.COUNTER_MINUS_1);
		
		////////////////////////////////////////////////////////
		// top two stack values are equal 
		Formula stackTop_equals_stackTop_minus_1 = new Predicate2Ar(new Stack(Expression.COUNTER), new Stack( Expression.COUNTER_MINUS_1), PredicateSymbol.EQ );
		Formula eq_branch = 	_normal_Postcondition.substitute(Expression.COUNTER, Expression.COUNTER_MINUS_2);
		Formula wp_eq_branch = Formula.getFormula(stackTop_equals_stackTop_minus_1, eq_branch, Connector.IMPLIES );
	
	
		////////////////////////////////////////////////////
		//top two stack values are not equal
		Formula stackTop_not_equals_stackTop_minus_1 = new Predicate2Ar(new Stack(Expression.COUNTER), new Stack( Expression.COUNTER_MINUS_1), PredicateSymbol.NOTEQ );
		Formula not_eq_branch = getBranchWP();
		not_eq_branch = not_eq_branch.substitute(Expression.COUNTER, Expression.COUNTER_MINUS_2);
		Formula wp_not_eq_branch = Formula.getFormula(stackTop_not_equals_stackTop_minus_1, not_eq_branch , Connector.IMPLIES );
		
		wp = Formula.getFormula(wp_not_eq_branch, wp_eq_branch, Connector.AND);
		return wp;
	}


}
