package bytecode_wp.bytecode.arithmetic;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.IOR;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LOR;


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
		IJml2bConfiguration config,
		Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
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

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		Stack stackTop = new Stack(Expression.COUNTER );
		Stack stackTop_minus_1 = new Stack(Expression.getCOUNTER_MINUS_1());
		BitExpression or =
			new BitExpression(
				stackTop,
				stackTop_minus_1,
				ExpressionConstants.BITWISEOR);

		vcs.substitute(
			Expression.COUNTER,
			Expression.getCOUNTER_MINUS_1());
		vcs.substitute(stackTop_minus_1, or);
		
		return vcs;
	}
}
