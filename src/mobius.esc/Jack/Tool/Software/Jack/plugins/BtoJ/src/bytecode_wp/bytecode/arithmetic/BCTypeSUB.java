/*
 * Created on Apr 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.arithmetic;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.ISUB;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LSUB;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.ArithmeticExpression;
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
 *  Operation : Subtract type
 *
 * Operand Stack : ..., value1, value2 ==> ..., result
 *
 * Description : Both value1 and value2 must be of type int. The values are popped from the operand stack. The int result is value1 - value2. 
 * The result is pushed onto the operand stack.   For int subtraction, a - b produces the same result as a + (-b). For int values, subtraction from zero is the same as negation.
 * The result is the 32 low-order bits of the true mathematical result in a sufficiently wide two's-complement format, represented as a value of type int. 
 *  If overflow occurs, then the sign of the result may not be the same as the sign of the mathematical sum of the two values.
 *  Despite the fact that overflow may occur, execution of an isub instruction never throws a runtime exception.
 */
public class BCTypeSUB extends BCArithmeticInstruction {
	
	/**	
	 * @param _instruction
	 * @param _type
	 */
	public BCTypeSUB(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		if (_instruction.getInstruction() instanceof ISUB) {
			setArithmeticOperation(BCConstants.SUB_INT);
			setInstructionCode(BCInstructionCodes.ISUB);
		} else if (_instruction.getInstruction() instanceof LSUB) {
			setArithmeticOperation(BCConstants.SUB_LONG);
			setInstructionCode(BCInstructionCodes.LSUB);
		} 
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp = null;
			Stack stackTop = new Stack(Expression.COUNTER);
			Stack stackTop_minus_1 = new Stack(Expression.getCOUNTER_MINUS_1());
			ArithmeticExpression sub =
				(ArithmeticExpression)ArithmeticExpression.getArithmeticExpression(
					stackTop_minus_1,
					stackTop,
					ExpressionConstants.SUB);
			_normal_Postcondition.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
			_normal_Postcondition.substitute(stackTop_minus_1, sub);
			wp = _normal_Postcondition;
			return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		
		Stack stackTop = new Stack(Expression.COUNTER);
		Stack stackTop_minus_1 = new Stack(Expression.getCOUNTER_MINUS_1());
		ArithmeticExpression sub =
			(ArithmeticExpression)ArithmeticExpression.getArithmeticExpression(
				stackTop_minus_1,
				stackTop,
				ExpressionConstants.SUB);
		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		vcs.substitute(stackTop_minus_1, sub);
		return vcs;
	}
	

}
