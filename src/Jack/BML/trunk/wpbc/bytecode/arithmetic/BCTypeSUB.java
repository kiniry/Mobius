/*
 * Created on Apr 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.arithmetic;

import org.apache.bcel.generic.ISUB;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LSUB;

import bcclass.attributes.ExsuresTable;
import bcexpression.ArithmeticExpression;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;
import bytecode.BCConstants;
import bytecode.BCInstructionCodes;
import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
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
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp = null;
			Stack stackTop = new Stack(Expression.COUNTER);
			Stack stackTop_minus_1 = new Stack(Expression.COUNTER_MINUS_1);
			ArithmeticExpression sub =
				(ArithmeticExpression)ArithmeticExpression.getArithmeticExpression(
					stackTop,
					stackTop_minus_1,
					ExpressionConstants.SUB);
			_normal_Postcondition.substitute(Expression.COUNTER, Expression.COUNTER_MINUS_1);
			_normal_Postcondition.substitute(stackTop_minus_1, sub);
			wp = _normal_Postcondition;
			return wp;
	}
	

}
