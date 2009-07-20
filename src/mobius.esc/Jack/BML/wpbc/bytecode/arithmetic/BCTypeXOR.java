/*
 * Created on Apr 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.arithmetic;

import org.apache.bcel.generic.IXOR;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LXOR;

import formula.Formula;

import bcclass.attributes.ExsuresTable;
import bcexpression.BitExpression;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;
import bytecode.BCConstants;
import bytecode.BCInstructionCodes;
/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCTypeXOR extends BCArithmeticInstruction {
	/*
	* 
	*/
	public BCTypeXOR(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		if (_instruction.getInstruction() instanceof IXOR) {
			setArithmeticOperation(BCConstants.XOR_INT);
			setInstructionCode(BCInstructionCodes.IXOR);
		} else if (_instruction.getInstruction() instanceof LXOR) {
			setArithmeticOperation(BCConstants.XOR_LONG);
			setInstructionCode(BCInstructionCodes.LXOR);
		}
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;
		Stack stackTop = new Stack(Expression.COUNTER);
		Stack stackTop_minus_1 = new Stack(Expression.getCOUNTER_MINUS_1());
		BitExpression xor =
			new BitExpression(
				stackTop,
				stackTop_minus_1,
				ExpressionConstants.BITWISEXOR);

		_normal_Postcondition.substitute(
			Expression.COUNTER,
			Expression.getCOUNTER_MINUS_1());
		_normal_Postcondition.substitute(stackTop_minus_1, xor);
		wp = _normal_Postcondition;
		return wp;
	}
}
