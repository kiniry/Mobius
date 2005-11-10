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

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

import bcclass.attributes.ExsuresTable;
import bcexpression.ArithmeticExpression;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.NumberLiteral;
import bcexpression.javatype.JavaObjectType;
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
		if (_instruction.getInstruction() instanceof IDIV) {
			setArithmeticOperation(BCConstants.DIV_INT);
			setInstructionCode(BCInstructionCodes.IDIV);
		} else if (_instruction.getInstruction() instanceof LDIV) {
			setArithmeticOperation(BCConstants.DIV_LONG);
			setInstructionCode(BCInstructionCodes.LDIV);
		}

	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {

		Formula wp = null;
//		Stack stackTop = new Stack(Expression.COUNTER);
//		Stack stackTop_minus_1 = new Stack(Expression.COUNTER_MINUS_1);
		// ! (stack(top ) == 0) 
		Formula divisorNonZero =
			Formula.getFormula(new Predicate2Ar(
				new Stack(Expression.COUNTER),
				new NumberLiteral(0),
				PredicateSymbol.EQ) , Connector.NOT );
		ArithmeticExpression divResult =
			(ArithmeticExpression)ArithmeticExpression.getArithmeticExpression(
				new Stack(Expression.COUNTER),
				new Stack(Expression.getCOUNTER_MINUS_1()),
				ExpressionConstants.DIV);
		_normal_Postcondition.substitute(
			Expression.COUNTER,
			Expression.getCOUNTER_MINUS_1());
		_normal_Postcondition.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), divResult);

		Formula wpNormalExecution =
		Formula.getFormula(
				divisorNonZero,
				_normal_Postcondition,
				Connector.IMPLIES);
		//stack(top ) == null 
		Formula divisorIsZero =
			new Predicate2Ar(
				new Stack(Expression.COUNTER),
				new NumberLiteral(0),
				PredicateSymbol.EQ);

		//_excPost = if exists exceptionHandler for NullPointerException then  wp(exceptionHandler,  normalPost) else 
		//                  else ExcPostcondition 
		Formula _excPost =
			getWpForException(
				(JavaObjectType) JavaType.getJavaRefType(
					"Ljava/lang/ArithmeticException;"));
		Formula wpExceptionExecution =
		Formula.getFormula(divisorIsZero, _excPost, Connector.IMPLIES);
		// stack(top)  != null ==>�_normal_Postcondition[t <-- t-1][S(t-1) <-- S(t-1) / S(t)] 
		// &&
		// stack(top)  == null ==> excPost
		wp =
		Formula.getFormula(wpNormalExecution, wpExceptionExecution, Connector.AND);
		return wp;
	}


}
