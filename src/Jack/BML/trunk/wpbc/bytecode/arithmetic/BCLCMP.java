package bytecode.arithmetic;

import java.net.ConnectException;

import org.apache.bcel.generic.InstructionHandle;
import specification.ExceptionalPostcondition;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

import bcexpression.Expression;
import bcexpression.NumberLiteral;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;
import bytecode.BCInstruction;
import bytecode.BCTypedInstruction;

/**
 * @author mpavlova
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
 * Note: this class doesnot extend the Arithmetic Instruction. Anyway  in order to comply with the VM specification the class is put in this package 
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
	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition) {
		Formula wp;
		Formula[] wps = new Formula[3];
				
		Stack topStack = new Stack(Expression.getCounter());
		Stack topStack_minus_1 = new Stack(Expression.getCounter_minus_1());
		
		// v1 == v2 => S(t)[t<--- t-1][S(t-1) <-- 0]
		Formula v1Equalsv2 = new Predicate2Ar(topStack, topStack_minus_1, PredicateSymbol.EQ );
		Formula resultZero = _normal_Postcondition.copy();
		resultZero.substitute(Expression.getCounter(), Expression.getCounter_minus_1());
		resultZero.substitute(topStack_minus_1, new NumberLiteral("0", 10, JavaType.JavaINT));
		wps[0] = new Formula(v1Equalsv2, resultZero, Connector.IMPLIES);
		
		 //	v1 >  v2 => S(t)[t<--- t-1][S(t-1) <-- 1]
		 Formula v1Grt2 = new Predicate2Ar( topStack_minus_1, topStack, PredicateSymbol.GRT);
		 Formula resultOne = _normal_Postcondition.copy();
		 resultOne.substitute(Expression.getCounter(), Expression.getCounter_minus_1());
		 resultZero.substitute(topStack_minus_1, new NumberLiteral("1",10, JavaType.JavaINT));
		 wps[1] = new Formula(v1Grt2 , resultOne, Connector.IMPLIES);
		 
		 
		//	v1 < v2 => S(t)[t<--- t-1][S(t-1) <-- 0]
		Formula v1Less2 = new Predicate2Ar( topStack_minus_1, topStack, PredicateSymbol.LESS);
		Formula resultMinusOne = _normal_Postcondition.copy();
		resultOne.substitute(Expression.getCounter(), Expression.getCounter_minus_1());
		resultZero.substitute(topStack_minus_1, new NumberLiteral("-1", 10, JavaType.JavaINT));
		wps[2] = new Formula(v1Less2 , resultMinusOne, Connector.IMPLIES);
	 
	 	wp = new Formula(wps, Connector.AND);
		return wp;
	}

}


