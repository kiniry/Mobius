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
import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

/**
 * @author mpavlova
 *
 * I2B
 * Convert int to byte
 * 
 *  ..., value === >..., result
 * 
 * The value on the top of the operand stack must be of type int. 
 * It is popped from the operand stack, truncated to a byte, then sign-extended to an int result. 
 * That result is pushed onto the operand stack.
 * 
 * S(t) >= 0 => psi^n[S(t) <-- (S(t) &0xFF) | 0x00000000] 
 * &&
 * S(t) >= 0 => psi^n[S(t) <-- (S(t) &0xFF) | 0x11111100] 
 * 
 */
public class BCI2B extends BCConversionInstruction  {


	/**
	 * @param _instruction
	 */
	public BCI2B(InstructionHandle _instruction) {
		super(_instruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return JavaType.JavaBYTE;
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
//		Stack stackTop = new Stack(Expression.COUNTER);
		
		Formula  positive = new Predicate2Ar(new Stack(Expression.COUNTER), new NumberLiteral(0), PredicateSymbol.GRTEQ);
		BitExpression pMask = new BitExpression(new Stack(Expression.COUNTER), new NumberLiteral(0xFF), ExpressionConstants.BITWISEAND);
		Formula pCopy = (Formula)_normal_Postcondition.copy();
		pCopy.substitute(new Stack(Expression.COUNTER), pMask);
		Formula wpPositive = Formula.getFormula(positive, pCopy, Connector.IMPLIES);
		
		Formula  neg = new Predicate2Ar(new Stack(Expression.COUNTER), new NumberLiteral(0), PredicateSymbol.LESS);
		BitExpression nMask = new BitExpression(new Stack(Expression.COUNTER), new NumberLiteral(0xFF), ExpressionConstants.BITWISEAND);
		BitExpression nExtend = new BitExpression(nMask, new NumberLiteral(0xFFFFFF00), ExpressionConstants.BITWISEOR);
		Formula nCopy = (Formula)_normal_Postcondition.copy();
		pCopy.substitute(new Stack(Expression.COUNTER), nExtend);
		Formula wpNeg = Formula.getFormula(neg, pCopy, Connector.IMPLIES);
		
		wp = Formula.getFormula(wpPositive, wpNeg, Connector.AND);
		return wp;
	}

}
