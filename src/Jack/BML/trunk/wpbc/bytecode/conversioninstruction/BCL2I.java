/*
 * Created on Apr 16, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.conversioninstruction;

import org.apache.bcel.generic.InstructionHandle;

import specification.ExceptionalPostcondition;
import bcexpression.BitExpression;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.NumberLiteral;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;
import formula.Formula;

/**
 * @author mpavlova
 *  
 *  L2I
 *     ..., value  ==> ..., result
 *
 *  The value on the top of the operand stack must be of type long. 
 *   It is popped from the operand stack and converted to an int result by taking the low-order 32 bits of the long value and discarding the high-order 32 bits. 
 *   The result is pushed onto the operand stack.
 *   
 *    wp =psi^n[S(t) <--- S(t) & 0x00000000FFFFFFFF]
 */

public class BCL2I extends BCConversionInstruction {


	/**
	 * @param _instruction
	 */
	public BCL2I(InstructionHandle _instruction) {
		super(_instruction);
		
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return JavaType.JavaINT;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	 */
	public void setType(JavaType _type) {
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition)  {
		Formula wp;
		
		Stack stackTop = new Stack(Expression.getCounter());

		BitExpression mask = new BitExpression(stackTop, new NumberLiteral("FFFFFFFF", 16, JavaType.JavaLONG), ExpressionConstants.BITWISEAND); 
		wp = _normal_Postcondition.substitute(stackTop, mask);
		return wp;
	}
	

}
