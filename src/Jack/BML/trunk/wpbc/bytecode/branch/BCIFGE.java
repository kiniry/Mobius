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
public class BCIFGE extends BCConditionalBranch {

	/**
	 * @param _branchInstruction
	 */
	public BCIFGE(InstructionHandle _branchInstruction) {
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
			Formula stackTop_geq_0 = new Predicate2Ar(stackTop, new NumberLiteral(0), PredicateSymbol.GRTEQ);
			Formula geq_branch = getBranchWP();
			geq_branch = geq_branch.substitute(Expression.COUNTER, Expression.COUNTER_MINUS_1);
			Formula wp_stackTop_geq_0 = new Formula( stackTop_geq_0, geq_branch, Connector.IMPLIES);
		
			// in case of executing next instruction
			Formula stackTop_not_geq_0 = new Formula( stackTop_geq_0, Connector.NOT);
			Formula not_geq_branch = _normal_Postcondition.substitute(Expression.COUNTER, Expression.COUNTER_MINUS_1);
			Formula wp_stackTop_not_geq_0 = new Formula( stackTop_not_geq_0, not_geq_branch, Connector.IMPLIES);
		
			wp = new Formula(wp_stackTop_geq_0, wp_stackTop_not_geq_0, Connector.AND);
			return wp;
		}


}
