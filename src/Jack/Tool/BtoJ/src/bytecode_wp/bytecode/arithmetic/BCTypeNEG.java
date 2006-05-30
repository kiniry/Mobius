package bytecode_wp.bytecode.arithmetic;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.INEG;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LNEG;


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
	

	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;

		Stack stackTop = new Stack(Expression.COUNTER);
		ArithmeticExpression neg = ArithmeticExpression.getArithmeticExpression(stackTop, ExpressionConstants.NEG);
		_normal_Postcondition.substitute(stackTop, neg);
		wp = _normal_Postcondition;
		return wp; 
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		Stack stackTop = new Stack(Expression.COUNTER);
		ArithmeticExpression neg = ArithmeticExpression.getArithmeticExpression(stackTop, ExpressionConstants.NEG);
		vcs.substitute(stackTop, neg);
		return vcs; 
	}
}
