package bytecode.arithmetic;

import org.apache.bcel.generic.IAND;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LAND;


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
public class BCTypeAND extends BCArithmeticInstruction {
	/*
	* 
	*/
	public BCTypeAND(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		if (_instruction.getInstruction() instanceof IAND) {
			setArithmeticOperation(BCConstants.AND_INT);
			setInstructionCode(BCInstructionCodes.IAND);
		} else if (_instruction.getInstruction() instanceof LAND) {
			setArithmeticOperation(BCConstants.AND_LONG);
			setInstructionCode(BCInstructionCodes.LAND);
		}
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;
//		Stack stackTop = new Stack(Expression.COUNTER);
//		Stack stackTop_minus_1 = new Stack(Expression.COUNTER_MINUS_1);
		BitExpression and =
			new BitExpression(
				new Stack(Expression.COUNTER),
				new Stack(Expression.getCOUNTER_MINUS_1()),
				ExpressionConstants.BITWISEAND);

		_normal_Postcondition.substitute(
			Expression.COUNTER,
			Expression.getCOUNTER_MINUS_1());
		_normal_Postcondition.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), and);
		wp = _normal_Postcondition;
		return wp;
	}
}
