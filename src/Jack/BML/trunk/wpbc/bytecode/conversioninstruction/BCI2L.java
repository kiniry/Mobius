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
import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

/**
 * @author mpavlova
 * 	I2L 
 * 	..., value  ==> ..., result
 * 	The value on the top of the operand stack must be of type int.
 *     It is popped from the operand stack and sign-extended to a long result. That result is pushed onto the operand stack.
 * 	wp = s(t) >= 0 ==> psi^n[S(t) <-- S(t) & 0xFFFFFFFFF] &&
 * 			s(t) < 0 ==> psi^n[S(t) <-- (S(t) & 0xFFFFFFFFF) | (0x1111111100000000)] &&
 */
public class BCI2L extends BCConversionInstruction {
	

	/**
	 * @param _instruction
	 */
	public BCI2L(InstructionHandle _instruction) {
		super(_instruction);
		// TODO Auto-generated constructor stub
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return JavaType.JavaLONG;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	 */
	public void setType(JavaType _type) {
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition) {
		Formula  wp;
		Stack stackTop = new Stack(Expression.getCounter());
		
		Formula positive =  new Predicate2Ar(stackTop, new NumberLiteral("0",10, JavaType.JavaINT), PredicateSymbol.GRTEQ);
		Formula pCopy = _normal_Postcondition.copy();
		BitExpression pextend = new BitExpression(stackTop, new NumberLiteral("FFFFFFFF",16, JavaType.JavaINT), ExpressionConstants.BITWISEAND);
		pCopy.substitute(stackTop,  pextend); 
		Formula wpPositive = new Formula(positive, pCopy, Connector.IMPLIES);
		
		Formula negative =  new Predicate2Ar(stackTop, new NumberLiteral("0",10, JavaType.JavaINT), PredicateSymbol.LESS);
		Formula nCopy = _normal_Postcondition.copy();
		BitExpression nmask = new BitExpression(stackTop, new NumberLiteral("00000000FFFFFFFF",16, JavaType.JavaLONG), ExpressionConstants.BITWISEAND);
		BitExpression nextend = new BitExpression(nmask, new NumberLiteral( "FFFFFFFF0000000",16, JavaType.JavaLONG), ExpressionConstants.BITWISEOR);
		nCopy.substitute(stackTop,  nextend); 
		Formula wpNeg = new Formula(negative, nCopy, Connector.IMPLIES);
		
		wp = new Formula(wpPositive, wpNeg, Connector.AND);
		return wp;
	}

}
