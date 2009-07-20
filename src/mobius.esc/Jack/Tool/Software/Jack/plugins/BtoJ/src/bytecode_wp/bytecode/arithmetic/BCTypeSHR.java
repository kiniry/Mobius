/*
 * Created on Apr 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.arithmetic;


import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.ISHR;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LSHR;


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
 * 
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
		IJml2bConfiguration config,
		Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
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
