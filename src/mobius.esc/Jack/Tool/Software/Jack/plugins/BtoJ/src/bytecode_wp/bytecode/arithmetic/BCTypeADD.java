package bytecode_wp.bytecode.arithmetic;


import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.IADD;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LADD;


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
			
		IJml2bConfiguration config,
		Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		
		Formula wp = null;

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

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		ArithmeticExpression sum =
			(ArithmeticExpression)ArithmeticExpression.getArithmeticExpression(
				new Stack(Expression.COUNTER),
				new Stack(Expression.getCOUNTER_MINUS_1()),
				ExpressionConstants.ADD);
		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		vcs.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), sum);
		
		return vcs;
	}
	

}
