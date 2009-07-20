package bytecode;

import org.apache.bcel.generic.InstructionHandle;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.NumberLiteral;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;

/**
 * @author mpavlova
 * 
 *	Operand Stack
 * ..., value1, value2 ==> ..., result
 * 
 * 
 * Description
 *
 *	Both value1 and value2 must be of type long. They are both popped from 
 *	the operand stack, and a signed integer comparison is performed. 
 * If value1 is greater than value2, the int value 1 is
 *	pushed onto the operand stack. If value1 is equal to value2, the int value 0 is pushed onto the operand stack. 
 * If value1 is less than value2, the int value -1 is pushed onto the operand stack.
 *
 *  
 */
public class BCLCMP extends BCInstruction implements BCTypedInstruction{
	//LCMP 

	/**
	 * @param _instruction
	 */
	public BCLCMP(InstructionHandle _instruction) {
		super(_instruction);

	}

	/* 
	 * returns the type  result of this instruction
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return JavaType.JavaLONG;
	}

	/* (non-Javadoc)
	 * does nothing as the type of this instruction is by default long
	 * @see bytecode.BCTypedInstruction#setType(org.apache.bcel.generic.TypedInstruction, org.apache.bcel.generic.ConstantPoolGen)
	 */
	public void setType(JavaType _type) {
		
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		Formula[] wps = new Formula[3];
				
		//Stack topStack = new Stack(Expression.COUNTER);
//		Stack topStack_minus_1 = new Stack(Expression.COUNTER_MINUS_1);
		
		// v1 == v2 => S(t)[t<--- t-1][S(t-1) <-- 0]
		Formula v1Equalsv2 = new Predicate2Ar(new Stack(Expression.COUNTER), new Stack(Expression.getCOUNTER_MINUS_1()), PredicateSymbol.EQ );
		Formula resultZero = (Formula)_normal_Postcondition.copy();
		resultZero.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		resultZero.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), new NumberLiteral(0));
		wps[0] = Formula.getFormula(v1Equalsv2, resultZero, Connector.IMPLIES);
		
		 //	v1 >  v2 => S(t)[t<--- t-1][S(t-1) <-- 1]
		 Formula v1Grt2 = new Predicate2Ar( new Stack(Expression.getCOUNTER_MINUS_1()), new Stack(Expression.COUNTER), PredicateSymbol.GRT);
		 Formula resultOne = (Formula)_normal_Postcondition.copy();
		 resultOne.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		 resultZero.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), new NumberLiteral(1));
		 wps[1] = Formula.getFormula(v1Grt2 , resultOne, Connector.IMPLIES);
		 
		 
		//	v1 < v2 => S(t)[t<--- t-1][S(t-1) <-- 0]
		Formula v1Less2 = new Predicate2Ar( new Stack(Expression.getCOUNTER_MINUS_1()), new Stack(Expression.COUNTER), PredicateSymbol.LESS);
		Formula resultMinusOne = (Formula)_normal_Postcondition.copy();
		resultOne.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		resultZero.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), new NumberLiteral(-1));
		wps[2] = Formula.getFormula(v1Less2 , resultMinusOne, Connector.IMPLIES);
	 
	 	wp = Formula.getFormula(wps, Connector.AND);
		return wp;
	}

}


