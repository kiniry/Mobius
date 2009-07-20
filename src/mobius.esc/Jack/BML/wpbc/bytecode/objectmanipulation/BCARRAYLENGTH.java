/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.objectmanipulation;

import org.apache.bcel.generic.InstructionHandle;

import constants.ArrayLengthConstant;

import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.FieldAccess;
import bcexpression.javatype.ClassNames;
import bcexpression.javatype.JavaObjectType;

import bcexpression.vm.Stack;
import bytecode.BCExceptionThrower;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

/**
 * @author mpavlova
 *
 * Operation Get length of array
 */
public class BCARRAYLENGTH extends BCExceptionThrower {

	/**
	 * @param _instruction
	 */
	public BCARRAYLENGTH(InstructionHandle _instruction) {
		super(_instruction);
		setExceptionsThrown( new JavaObjectType[]{ (JavaObjectType)JavaObjectType.getJavaRefType( ClassNames.NULLPOINTERException) });

	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;
//		Stack topStack = new Stack(Expression.COUNTER);

		//wp in case of normal termination
		Formula objNotNull =
			Formula.getFormula(
					new Predicate2Ar( new Stack(Expression.COUNTER), Expression._NULL, PredicateSymbol.EQ), Connector.NOT);
		//S(t).length
		FieldAccess arrLength =
			new FieldAccess(ArrayLengthConstant.ARRAYLENGTHCONSTANT,  new Stack(Expression.COUNTER));
		Formula _nps = (Formula)_normal_Postcondition.substitute( new Stack(Expression.COUNTER), arrLength);
		Formula wpNormalTermination =
		Formula.getFormula(objNotNull, _nps, Connector.IMPLIES);

		//wp in case of throwing exception
		Formula objNull =
			new Predicate2Ar( new Stack(Expression.COUNTER), Expression._NULL, PredicateSymbol.EQ);
			
			// in case the array object is null - Ljava/lang/NullPointerException; is thrown 
		Formula excPrecondition =
			getWpForException(
				getExceptionsThrown()[0]);
		Formula wpExceptionalTermination =
		Formula.getFormula(objNull, excPrecondition, Connector.IMPLIES);
		wp =
		Formula.getFormula(
				wpNormalTermination,
				wpExceptionalTermination,
				Connector.AND);

		return wp;
	}

}
