package bytecode.arithmetic;

import org.apache.bcel.generic.DREM;
import org.apache.bcel.generic.FREM;
import org.apache.bcel.generic.IREM;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LREM;
import specification.ExceptionalPostcondition;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

import bcexpression.ArithmeticExpression;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.NumberLiteral;
import bcexpression.javatype.JavaReferenceType;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Counter;
import bcexpression.vm.Stack;
import bytecode.BCConstants;
import bytecode.BCInstructionCodes;

/**
 * @author Mariela
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class BCTypeREM extends BCArithmeticInstructionWithException {
	/**
	 * @param _instruction
	 */
	public BCTypeREM(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		if (_instruction.getInstruction() instanceof IREM) {
			setArithmeticOperation(BCConstants.REM_INT);
			setInstructionCode(BCInstructionCodes.IREM);
		} else if (_instruction.getInstruction() instanceof LREM) {
			setArithmeticOperation(BCConstants.REM_LONG);
			setInstructionCode(BCInstructionCodes.LREM);
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
				new Predicate2Ar(
					stackTop,
					new NumberLiteral("0",10, JavaType.JavaINT),
					PredicateSymbol.NOTEQ);
			ArithmeticExpression remResult =
				new ArithmeticExpression(
					stackTop,
					stackTop_minus_1,
					ExpressionConstants.REM);
			_normal_Postcondition.substitute(
				Expression.getCounter(),
				Expression.getCounter_minus_1());
			_normal_Postcondition.substitute(stackTop_minus_1, remResult);

			Formula wpNormalExecution =
				new Formula(
					divisorNonZero,
					_normal_Postcondition,
					Connector.IMPLIES);
			//stack(top ) == null 
			Formula divisorIsZero =
				new Predicate2Ar(
					stackTop,
					new NumberLiteral("0",10, JavaType.JavaINT),
					PredicateSymbol.EQ);

			//_excPost = if exists exceptionHandler for NullPointerException then  wp(exceptionHandler,  normalPost) else 
			//                  else ExcPostcondition 
			Formula _excPost =
				getWpForException(
					JavaType.getJavaRefType("java.lang.ArithmeticException"),
					_exc_Postcondition);
			Formula wpExceptionExecution =
				new Formula(divisorIsZero, _excPost, Connector.IMPLIES);
			// stack(top)  != null ==>_normal_Postcondition[t <-- t-1][S(t-1) <-- S(t-1) rem S(t)] 
			// &&
			// stack(top)  == null ==> excPost
			wp =
				new Formula(
					wpNormalExecution,
					wpExceptionExecution,
					Connector.AND);
			return wp;
		}

	}
