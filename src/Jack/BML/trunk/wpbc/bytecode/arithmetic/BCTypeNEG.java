package bytecode.arithmetic;

import org.apache.bcel.generic.INEG;
import org.apache.bcel.generic.InstructionHandle;

import org.apache.bcel.generic.LNEG;

import bcclass.attributes.ExsuresTable;
import bcexpression.javatype.JavaType;


import formula.Formula;

import bcexpression.ArithmeticExpression;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
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
public class BCTypeNEG extends BCArithmeticInstruction {
	/**
	 * @param _instruction
	 */
	public BCTypeNEG(InstructionHandle _instruction, JavaType _type) {
		super(_instruction,_type);
		if (_instruction.getInstruction() instanceof INEG) {
			setArithmeticOperation(BCConstants.NEG_INT);
			setInstructionCode(BCInstructionCodes.INEG);
		} else if (_instruction.getInstruction() instanceof LNEG) {
			setArithmeticOperation(BCConstants.NEG_LONG);
			setInstructionCode(BCInstructionCodes.LNEG);
		} 
	}
	
	/**
	 * @see bytecode.BCInstruction#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;

		Stack stackTop = new Stack(Expression.COUNTER);
		ArithmeticExpression neg = ArithmeticExpression.getArithmeticExpression(stackTop, ExpressionConstants.NEG);
		_normal_Postcondition.substitute(stackTop, neg);
		wp = _normal_Postcondition;
		return wp; 
	}
}
