/*
 * Created on Apr 21, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.stackinstruction;

import org.apache.bcel.generic.InstructionHandle;

import formula.Formula;
import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bytecode.BCInstruction;

/**
 * @author mpavlova
 *
 * pop
 * 
 * Operation:  Pop the top operand stack value
 *
 *  Format :  pop 	
 *
 *  Operand Stack : ..., value ==> ...
 *
 *  Description: Pop the top value from the operand stack. 
 *   The pop instruction must not be used unless value is a value of a category 1 computational type 
 *    (we consider only types of  computational type 1)
 * 
 *   wp = psi^n[t <-- t-1]
 */

public class BCPOP  extends BCInstruction implements BCStackInstruction{

	/**
	 * @param _instruction
	 */
	public BCPOP(InstructionHandle _instruction) {
		super(_instruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		wp = (Formula)_normal_Postcondition.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		
		return wp;
	}

}
