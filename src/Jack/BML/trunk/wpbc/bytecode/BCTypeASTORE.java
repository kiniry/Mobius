/*
 * Created on Mar 31, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import org.apache.bcel.generic.InstructionHandle;

import constants.ArrayLengthConstant;
import specification.ExceptionalPostcondition;
import bcexpression.ArithmeticExpression;
import bcexpression.ArrayAccessExpression;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.FieldAccessExpression;
import bcexpression.NumberLiteral;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Counter;
import bcexpression.vm.Stack;
import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCTypeASTORE
	extends BCExceptionThrower
	implements BCTypedInstruction {
	private JavaType type;
	//    .., arrayref, index, value  ==> ...  
	//assigns to arrayref[index] value

	/**
	 * @param _instruction
	 */
	public BCTypeASTORE(InstructionHandle _instruction, JavaType _type) {
		super(_instruction);
		setType(_type);
	}
	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return type;
	}
	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType(org.apache.bcel.generic.TypedInstruction, org.apache.bcel.generic.ConstantPoolGen)
	 */
	public void setType(JavaType _type) {
		type = _type;
	}
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, java.util.HashMap)
	 */
	public Formula wp(
		Formula _n_Postcondition,
		ExceptionalPostcondition _exc_Postcondition) {
		
		Formula wp;
		Formula[] wps = new Formula[3];
		//		normal execution 
		Stack stackTop = new Stack(Expression.getCounter());
		Stack stackTop_minus_1 = new Stack(Expression.getCounter_minus_1());
		Stack stackTop_minus_2 = new Stack(Expression.getCounter_minus_2());

		//t <------ t -1
		_n_Postcondition.substitute(Expression.getCounter(), Expression.getCounter_minus_3());

		//S(t-2 ) != null
		Formula array_not_null =
			new Predicate2Ar(
				stackTop_minus_2,
				Expression.NULL,
				PredicateSymbol.NOTEQ);
		//S(t-1) < S(t-2).length
		Formula arr_index_correct =
			new Predicate2Ar(
				stackTop_minus_1,
				new FieldAccessExpression(
					new ArrayLengthConstant(),
					stackTop_minus_2),
				PredicateSymbol.LESS);
				
		Formula condition = new Formula(array_not_null, arr_index_correct, Connector.AND);
		Expression arrElementAtIndex = new ArrayAccessExpression(stackTop_minus_2, stackTop_minus_1 );
		//S(t-2)[S(t-1)] <--- S(t)
		_n_Postcondition.substitute( arrElementAtIndex, stackTop);
		
		wps[0] = new Formula(condition, _n_Postcondition, Connector.IMPLIES);
		
		//exceptional termination
		//S(t-2 ) == null ==> _exc_Postcondition(java.lang.NullPointerException)
		Formula array_null =
			new Predicate2Ar(
				stackTop_minus_2,
				Expression.NULL,
				PredicateSymbol.EQ);
		Formula nullPointer = getWpForException(JavaType.getJavaClass("java.lang.NullPointerException"), _exc_Postcondition);
		wps[1] = new Formula(array_null, nullPointer, Connector.IMPLIES );	
		
		  //S(t-1) > S(t-2).length ==> _exc_Postcondition(java.lang. ArrayIndexOutOfBoundsException)
		  Formula arr_index_not_correct =
			  new Predicate2Ar(
				  stackTop_minus_1,
				  new FieldAccessExpression(
					  new ArrayLengthConstant(),
					  stackTop_minus_2),
				  PredicateSymbol.GRTEQ);
		Formula outOfBounds = getWpForException(JavaType.getJavaClass("java.lang. ArrayIndexOutOfBoundsException"), _exc_Postcondition);
		wps[2] = new Formula(arr_index_not_correct, outOfBounds, Connector.IMPLIES);
	 	wp = new Formula(wps, Connector.AND);
		return wp;		
	}
}
