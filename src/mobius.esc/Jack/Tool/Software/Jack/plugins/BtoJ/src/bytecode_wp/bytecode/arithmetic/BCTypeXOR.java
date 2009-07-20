/*
 * Created on Apr 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.arithmetic;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.IXOR;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LXOR;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.BitExpression;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.ExpressionConstants;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCConstants;
import bytecode_wp.bytecode.BCInstructionCodes;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;
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
		IJml2bConfiguration config,
		Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
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

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		Stack stackTop = new Stack(Expression.COUNTER);
		Stack stackTop_minus_1 = new Stack(Expression.getCOUNTER_MINUS_1());
		BitExpression xor =
			new BitExpression(
				stackTop,
				stackTop_minus_1,
				ExpressionConstants.BITWISEXOR);

		vcs.substitute(
			Expression.COUNTER,
			Expression.getCOUNTER_MINUS_1());
		vcs.substitute(stackTop_minus_1, xor);
		
		return vcs;
	}
}
