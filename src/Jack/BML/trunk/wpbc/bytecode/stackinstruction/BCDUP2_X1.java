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
import bcexpression.vm.Stack;
import bytecode.BCInstruction;

/**
 * @author mpavlova
 *
 * Operation: Duplicate the top one or two operand stack values and insert two or three values down
 * 
 *  Format : dup2_x1 	
 *  
 *  Operand Stack
 *
 *  Form 1:
 *
 *   ..., value3, value2, value1 ==> ..., value2, value1, value3, value2, value1
 *
 *   where value1, value2, and value3 are all values of a category 1 computational type 
 *
 *   Form 2:
 *
 *   ..., value2, value1 ==> ..., value1, value2, value1
 *
 *   where value1 is a value of a category 2 computational type and value2 is a value of a category 1 computational type
 * 
 * wp = value1, value2, and value3 of comp type 1 ==> psi^n[t <-- t+2][S(t+2) <-- S(t)][S(t+1) <-- S(t - 1)]
 */
public class BCDUP2_X1 extends BCInstruction implements BCStackInstruction {

	/**
	 * @param _instruction
	 */
	public BCDUP2_X1(InstructionHandle _instruction) {
		super(_instruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		
		Stack stackTop = new Stack(Expression.COUNTER);
		Stack stackTop_minus_1 = new Stack(Expression.getCOUNTER_MINUS_1());
	
		wp = (Formula)_normal_Postcondition.substitute(Expression.COUNTER, Expression.getCOUNTER_PLUS_2());
		wp = (Formula) wp.substitute(new Stack(Expression.getCOUNTER_PLUS_2()), stackTop );
		wp = (Formula)wp.substitute(Expression.getCOUNTER_PLUS_1(), stackTop_minus_1);
		return wp;
	}

}
