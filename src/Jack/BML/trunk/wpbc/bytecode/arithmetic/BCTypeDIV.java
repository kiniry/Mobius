/*
 * Created on Apr 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.arithmetic;

import org.apache.bcel.generic.IDIV;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LDIV;

import specification.ExceptionalPostcondition;
import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

import bcexpression.ArithmeticExpression;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.NumberLiteral;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;
import bytecode.BCConstants;
import bytecode.BCInstructionCodes;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCTypeDIV extends BCArithmeticInstructionWithException {

	/**
	 * @param _instruction
	 * @param _type
	 */
	public BCTypeDIV(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		if (_instruction.getInstruction() instanceof IDIV ) {
			setArithmeticOperation(BCConstants.DIV_INT);
			setInstructionCode(BCInstructionCodes.IDIV);
		} else if (_instruction.getInstruction() instanceof LDIV ) {
			setArithmeticOperation(BCConstants.DIV_LONG);
			setInstructionCode(BCInstructionCodes.LDIV);
		} 
		
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExceptionalPostcondition _exc_Postcondition) {
			
		Formula wp = null;
		Stack stackTop = new Stack(Expression.getCounter());
		Stack stackTop_minus_1 = new Stack(Expression.getCounter_minus_1());
		// stack(top ) != null 
		Formula divisorNonZero =
			new Predicate2Ar(stackTop, new NumberLiteral(new Integer(0)), PredicateSymbol.NOTEQ);
		ArithmeticExpression divResult =
			new ArithmeticExpression(
				stackTop,
				stackTop_minus_1,
				ExpressionConstants.DIV);
		_normal_Postcondition.substitute(
			Expression.getCounter(),
			Expression.getCounter_minus_1());
		_normal_Postcondition.substitute(stackTop_minus_1, divResult);

		Formula wpNormalExecution =
			new Formula(
				divisorNonZero,
				_normal_Postcondition,
				Connector.IMPLIES);
		//stack(top ) == null 
		Formula divisorIsZero =
			new Predicate2Ar(stackTop, new NumberLiteral(new Integer(0)), PredicateSymbol.EQ);

		//_excPost = if exists exceptionHandler for NullPointerException then  wp(exceptionHandler,  normalPost) else 
		//                  else ExcPostcondition 
		Formula _excPost =
			getWpForException(
				JavaType.getJavaClass("java.lang.ArithmeticException"),
				_exc_Postcondition);
		Formula wpExceptionExecution =
			new Formula(divisorIsZero, _excPost, Connector.IMPLIES);
		// stack(top)  != null ==> _normal_Postcondition[t <-- t-1][S(t-1) <-- S(t-1) / S(t)] 
		// &&
		// stack(top)  == null ==> excPost
		wp = new Formula(wpNormalExecution, wpExceptionExecution, Connector.AND);
		return wp;
	}

}
