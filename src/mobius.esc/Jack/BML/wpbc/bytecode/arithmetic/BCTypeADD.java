package bytecode.arithmetic;


import org.apache.bcel.generic.IADD;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LADD;

import formula.Formula;

import bcclass.attributes.ExsuresTable;
import bcexpression.ArithmeticExpression;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;
import bytecode.BCConstants;
import bytecode.BCInstructionCodes;


/**
 * @author Mariela
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class BCTypeADD extends BCArithmeticInstruction {
	/**
	 * @param _instruction
	 */
	public BCTypeADD(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		if (_instruction.getInstruction() instanceof IADD) {
			setArithmeticOperation(BCConstants.ADD_INT);
			setInstructionCode(BCInstructionCodes.IADD);
		} else if (_instruction.getInstruction() instanceof LADD) {
			setArithmeticOperation(BCConstants.ADD_LONG);
			setInstructionCode(BCInstructionCodes.LADD);
		} 
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		
		Formula wp = null;
//		Stack stackTop = new Stack(Expression.COUNTER);
//		Stack stackTop_minus_1 = new Stack(Expression.COUNTER_MINUS_1);
		ArithmeticExpression sum =
			(ArithmeticExpression)ArithmeticExpression.getArithmeticExpression(
				new Stack(Expression.COUNTER),
				new Stack(Expression.getCOUNTER_MINUS_1()),
				ExpressionConstants.ADD);
		_normal_Postcondition.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		_normal_Postcondition.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), sum);
		wp = _normal_Postcondition;
		return wp;
	}
}
