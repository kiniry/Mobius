/*
 * Created on Apr 16, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.conversioninstruction;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.BitExpression;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.ExpressionConstants;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 *	I2C
 *	convert int to char 
 *    ..., value ==>  ..., result
 *
 *   The value on the top of the operand stack must be of type int. 
 *   It is popped from the operand stack, truncated to char, then zero-extended to an int result. 
 *  That result is pushed onto the operand stack.
 * 
 * psi^n[S(t) <--- S(t) & 0x0000FFFF]
 */
public class BCI2C extends BCConversionInstruction {

	/**
	 * @param _instruction
	 */
	public BCI2C(InstructionHandle _instruction) {
		super(_instruction);		
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return JavaType.JavaCHAR;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	 */
	public void setType(JavaType _type) {
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
//		Stack stackTop = new Stack(Expression.COUNTER );
		// S(t) & 0xFFFF
		BitExpression mask = new BitExpression(new Stack(Expression.COUNTER ), new NumberLiteral(0x0000FFFF), ExpressionConstants.BITWISEAND );
		// psi^n[S(t)<--- S(t) & 0xFFFF]
		wp = (Formula)_normal_Postcondition.substitute(new Stack(Expression.COUNTER ), mask);
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		// S(t) & 0xFFFF
		BitExpression mask = new BitExpression(new Stack(Expression.COUNTER ), new NumberLiteral(0x0000FFFF), ExpressionConstants.BITWISEAND );
		// psi^n[S(t)<--- S(t) & 0xFFFF]
		vcs.substitute(new Stack(Expression.COUNTER ), mask);
		return vcs;
	}

}
