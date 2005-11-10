/*
 * Created on Apr 20, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.stackinstruction;

import org.apache.bcel.generic.InstructionHandle;

import formula.Formula;
import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.vm.Stack;
import bytecode.BCInstruction;

/**
 * @author mpavlova
 * 
 * NB: should take off the part for long / computational type 2
 * 
 * Operation : Duplicate the top operand stack value and insert two values down
 *
 * Stack :  ..., value2, value1 ==> ..., value1, value2, value1
 * 
 * Description: Duplicate the top value on the operand stack and insert the duplicated value two values down in the operand stack. 
 *
 * psi^n = psi^n[t <-- t+1][S(t+1) <-- S(t)][S(t)<-- S(t-1)][S(t-1) <-- S(t )]
 */
public class BCDUP_X1 extends BCInstruction implements BCStackInstruction  {

	/**
	 * @param _instruction
	 */
	public BCDUP_X1(InstructionHandle _instruction) {
		super(_instruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;

		wp = (Formula)_normal_Postcondition.substitute(Expression.COUNTER, Expression.getCOUNTER_PLUS_1());
		wp = (Formula)wp.substitute(new Stack(Expression.getCOUNTER_PLUS_1()), new Stack(Expression.COUNTER));
		wp = (Formula)wp.substitute(new Stack(Expression.COUNTER), new Stack(Expression.getCOUNTER_MINUS_1()) );
		wp = (Formula)wp.substitute(new Stack(Expression.getCOUNTER_MINUS_1()) , new Stack(Expression.COUNTER));
		
		return wp;
	}

}
