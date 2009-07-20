/*
 * Created on Apr 16, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.conversioninstruction;

import org.apache.bcel.generic.InstructionHandle;

import bcclass.attributes.ExsuresTable;
import bcexpression.BitExpression;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.NumberLiteral;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;
import formula.Formula;

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
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
//		Stack stackTop = new Stack(Expression.COUNTER );
		// S(t) & 0xFFFF
		BitExpression mask = new BitExpression(new Stack(Expression.COUNTER ), new NumberLiteral(0x0000FFFF), ExpressionConstants.BITWISEAND );
		// psi^n[S(t)<--- S(t) & 0xFFFF]
		wp = (Formula)_normal_Postcondition.substitute(new Stack(Expression.COUNTER ), mask);
		return wp;
	}

}
