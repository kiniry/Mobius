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
 * Operation:  Duplicate the top operand stack value
 * 
 * Format : dup 	
 * 
 * Operand Stack : ..., value  == >..., value, value
 * 
 * Description : Duplicate the top value on the operand stack and push the duplicated value onto the operand stack. 
 *  
 * wp = psi^n[t <-- t +1] [S(t+1) <-- S(t) ]
 */
public class BCDUP extends BCInstruction implements BCStackInstruction {

	/**
	 * @param _instruction
	 */
	public BCDUP(InstructionHandle _instruction) {
		super(_instruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		wp = _normal_Postcondition.substitute(Expression.COUNTER, Expression.COUNTER_PLUS_1);
		Stack topStack = new Stack(Expression.COUNTER);
		Stack topStack_plus_1 = new Stack(Expression.COUNTER_PLUS_1);
		wp = wp.substitute(topStack, topStack_plus_1);
		return wp;
	}
	

}
