/*
 * Created on Apr 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.arithmetic;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.IUSHR;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LUSHR;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.BitExpression;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.ExpressionConstants;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCConstants;
import bytecode_wp.bytecode.BCInstructionCodes;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 *
 * Operand Stack
 *
 *   ..., value1, value2 ..., result
 *
 * Description
 *
 * Both value1 and value2 must be of type int. The values are popped from 
 * the operand stack. An int result is calculated by shifting value1 right by
 *  s bit positions, with zero extension, where s is the value of the low 5 bits of value2. 
 *  The result is pushed onto the operand stack.
 *
 * Notes
 * If value1 is positive and s is value2 & 0x1f, the result is
 * the same as that of value1 >> s; if value1 is negative, the result is equal to the value of
 * the expression (value1 >> s) + (2 << ~s). The addition of the (2 << ~s) term cancels out the
 * propagated sign bit. The shift distance actually used is always in the range 0 to 31, inclusive.
 */
public class BCTypeUSHR extends BCArithmeticInstruction {
	
	/**
	 * @param _instruction
	 * @param _type
	 */
	public BCTypeUSHR(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		if (_instruction.getInstruction() instanceof IUSHR) {
			setArithmeticOperation(BCConstants.USHR_INT);
			setInstructionCode(BCInstructionCodes.IUSHR);
		} else if (_instruction.getInstruction() instanceof LUSHR) {
			setArithmeticOperation(BCConstants.USHR_LONG);
			setInstructionCode(BCInstructionCodes.LUSHR);
		}
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		// TODO Auto-generated method stub
		return null;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
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
		vcs.substitute(
			Expression.COUNTER,
			Expression.getCOUNTER_MINUS_1());
		vcs.substitute(topStack_minus_1, shift);
		
		return vcs;
	}

}