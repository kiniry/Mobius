package bytecode.arithmetic;

import org.apache.bcel.generic.IOR;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LOR;

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
public class BCTypeOR extends BCArithmeticInstruction {
	/*
	* 
	*/
	public BCTypeOR(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		if (_instruction.getInstruction() instanceof IOR) {
			setArithmeticOperation(BCConstants.OR_INT);
			setInstructionCode(BCInstructionCodes.IOR);
		} else if (_instruction.getInstruction() instanceof LOR) {
			setArithmeticOperation(BCConstants.OR_LONG);
			setInstructionCode(BCInstructionCodes.LOR);
		}
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;
		Stack stackTop = new Stack(Expression.COUNTER );
		Stack stackTop_minus_1 = new Stack(Expression.getCOUNTER_MINUS_1());
		BitExpression or =
			new BitExpression(
				stackTop,
				stackTop_minus_1,
				ExpressionConstants.BITWISEOR);

		_normal_Postcondition.substitute(
			Expression.COUNTER,
			Expression.getCOUNTER_MINUS_1());
		_normal_Postcondition.substitute(stackTop_minus_1, or);
		wp = _normal_Postcondition;
		return wp;
	}
}
