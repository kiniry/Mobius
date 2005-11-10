/*
 * Created on Apr 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.arithmetic;


import org.apache.bcel.generic.ISHR;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LSHR;

import formula.Formula;

import bcclass.attributes.ExsuresTable;
import bcexpression.BitExpression;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.NumberLiteral;
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
public class BCTypeSHR extends BCArithmeticInstruction {
	/**
		 * @param _instruction
		 */
	public BCTypeSHR(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		if (_instruction.getInstruction() instanceof ISHR) {
			setArithmeticOperation(BCConstants.SHR_INT);
			setInstructionCode(BCInstructionCodes.ISHR);
		} else if (_instruction.getInstruction() instanceof LSHR) {
			setArithmeticOperation(BCConstants.SHR_LONG);
			setInstructionCode(BCInstructionCodes.LSHR);
		}
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;
		Stack topStack = new Stack(Expression.COUNTER);
		Stack topStack_minus_1 = new Stack(Expression.getCOUNTER_MINUS_1());
		//S(t) && 0x1F
		BitExpression low5bitsofTopStack =
			new BitExpression(
				topStack,
				new NumberLiteral(0x1F),
				ExpressionConstants.BITWISEAND);
		BitExpression shift =
			new BitExpression(
				topStack_minus_1,
				low5bitsofTopStack,
				ExpressionConstants.SHR);
		_normal_Postcondition.substitute(
			Expression.COUNTER,
			Expression.getCOUNTER_MINUS_1());
		_normal_Postcondition.substitute(topStack_minus_1, shift);
		wp = _normal_Postcondition;
		return wp;
	}
}
