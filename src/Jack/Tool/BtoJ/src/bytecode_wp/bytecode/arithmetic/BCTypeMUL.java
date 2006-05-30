package bytecode_wp.bytecode.arithmetic;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.IMUL;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LMUL;


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
 * @author Mariela
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class BCTypeMUL extends BCArithmeticInstruction {
	
	/**
	 * @param _instruction
	 */
	public BCTypeMUL(InstructionHandle _instruction, JavaType _type) {
		super(_instruction,_type);
		if (_instruction.getInstruction() instanceof IMUL ) {
			setArithmeticOperation(BCConstants.MUL_INT);
			setInstructionCode(BCInstructionCodes.IMUL);
		} else if (_instruction.getInstruction() instanceof LMUL ) {
			setArithmeticOperation(BCConstants.MUL_LONG);
			setInstructionCode(BCInstructionCodes.LMUL);
		} 
	}
	

	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		Stack stackTop = new Stack(Expression.COUNTER);
		Stack stackTop_minus_1 = new Stack(Expression.getCOUNTER_MINUS_1());
		ArithmeticExpression mult = (ArithmeticExpression)ArithmeticExpression.getArithmeticExpression(stackTop, stackTop_minus_1, ExpressionConstants.MULT);
		_normal_Postcondition.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		_normal_Postcondition.substitute(stackTop_minus_1, mult);
		wp = _normal_Postcondition;
		return wp; 
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {

		Stack stackTop = new Stack(Expression.COUNTER);
		Stack stackTop_minus_1 = new Stack(Expression.getCOUNTER_MINUS_1());
		ArithmeticExpression mult = (ArithmeticExpression)ArithmeticExpression.getArithmeticExpression(stackTop, stackTop_minus_1, ExpressionConstants.MULT);
		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		vcs.substitute(stackTop_minus_1, mult);
		
		return vcs; 
	}

}
