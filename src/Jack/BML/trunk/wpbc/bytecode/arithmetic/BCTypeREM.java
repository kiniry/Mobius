package bytecode.arithmetic;

import java.util.Hashtable;

import org.apache.bcel.generic.IREM;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LREM;

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
 * @author Mariela
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class BCTypeREM extends BCArithmeticInstructionWithException {
	
	
	private JavaObjectType[] exceptionsThrown ;
	private Hashtable excHandleBlocks;
	
	
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
		ExsuresTable _exc_Postcondition) {

		Formula wp = null;
//		Stack stackTop = new Stack(Expression.COUNTER);
//		Stack stackTop_minus_1 = new Stack(Expression.COUNTER_MINUS_1);
		// stack(top ) != 0
		
		Formula divisorNonZero =
			Formula.getFormula( new Predicate2Ar(
				new Stack(Expression.COUNTER),
				new NumberLiteral(0),
				PredicateSymbol.EQ) , Connector.NOT) ;
		ArithmeticExpression remResult =
			(ArithmeticExpression)ArithmeticExpression.getArithmeticExpression(
				new Stack(Expression.COUNTER),
				new Stack(Expression.getCOUNTER_MINUS_1()),
				ExpressionConstants.REM);
		_normal_Postcondition.substitute(
			Expression.COUNTER,
			Expression.getCOUNTER_MINUS_1());
		_normal_Postcondition.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), remResult);

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
		// stack(top)  != null ==>_normal_Postcondition[t <-- t-1][S(t-1) <-- S(t-1) rem S(t)] 
		// &&
		// stack(top)  == null ==> excPost
		wp =
		Formula.getFormula(wpNormalExecution, wpExceptionExecution, Connector.AND);
		return wp;
	}

}
