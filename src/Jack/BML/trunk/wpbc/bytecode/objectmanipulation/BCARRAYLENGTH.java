/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.objectmanipulation;

import org.apache.bcel.generic.InstructionHandle;

import constants.ArrayLengthConstant;

import bcexpression.Expression;
import bcexpression.FieldAccessExpression;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;
import bytecode.BCExceptionThrower;

import specification.ExceptionalPostcondition;
import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

/**
 * @author mpavlova
 *
 * Operation Get length of array
 */
public class BCARRAYLENGTH  extends BCExceptionThrower {

	/**
	 * @param _instruction
	 */
	public BCARRAYLENGTH(InstructionHandle _instruction) {
		super(_instruction);
		// TODO Auto-generated constructor stub
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition) {
		Formula wp;
		Stack topStack = new Stack(Expression.getCounter());
		
		//wp in case of normal termination
		Formula objNotNull = new Predicate2Ar(topStack, Expression.NULL, PredicateSymbol.NOTEQ);
		//S(t).length
		FieldAccessExpression arrLength =  new FieldAccessExpression( new ArrayLengthConstant(), topStack) ;
		Formula _nps = _normal_Postcondition.substitute(topStack, arrLength);
		Formula wpNormalTermination = new Formula(objNotNull, _nps , Connector.IMPLIES);
		
		//wp in case of throwing exception
		Formula objNull = new Predicate2Ar(topStack, Expression.NULL, PredicateSymbol.EQ);
		Formula excPrecondition = getWpForException(JavaType.getJavaRefType("java.lang.NullPointerException"),_exc_Postcondition);
		Formula wpExceptionalTermination = new Formula(objNull, excPrecondition, Connector.IMPLIES);
		wp = new Formula(wpNormalTermination, wpExceptionalTermination, Connector.AND );
		
		return wp;
	}

}
