/*
 * Created on Mar 31, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.objectmanipulation;

import org.apache.bcel.generic.InstructionHandle;

import utils.Util;

import constants.ArrayLengthConstant;

import bcclass.attributes.ExsuresTable;
import bcexpression.ArrayAccessExpression;
import bcexpression.Expression;
import bcexpression.NumberLiteral;

import bcexpression.FieldAccess;
import bcexpression.javatype.ClassNames;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;

import bcexpression.vm.Stack;
import bytecode.BCExceptionThrower;
import bytecode.BCTypedInstruction;
import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

/**
 * @author mpavlova
 *
 * iastore
 *
 * Operation : Store into int array
 *
 * Format :  iastore 	
 * 
 * Operand Stack : ..., arrayref, index, value  ==> ...
 *
 * Description : The arrayref must be of type reference and must refer to an array whose 
 * components are of type int. Both index and value must be of type int. The arrayref, index, and 
 * value are popped from the operand stack. The int value is stored as the component of the array indexed by index. 
 *
 * Runtime Exceptions :
 * If arrayref is null, iastore throws a NullPointerException. 
 * Otherwise, if index is not within the bounds of the array referenced by arrayref, 
 * the iastore instruction throws an ArrayIndexOutOfBoundsException
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
		setExceptionsThrown(
			new JavaObjectType[] {
				(JavaObjectType) JavaObjectType.getJavaRefType(
					ClassNames.NULLPOINTERException),
				(JavaObjectType) JavaObjectType.getJavaRefType(
					ClassNames.ARRAYINDEXOUTOFBOUNDException)});
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
		ExsuresTable _exc_Postcondition) {

		Formula wp;
		Formula[] wps = new Formula[3];
		//	normal execution 
		Stack stackTop = new Stack(Expression.COUNTER);

		//t <------ t - 3
		_n_Postcondition.substitute(
			Expression.COUNTER,
			Expression.getCOUNTER_MINUS_3());

		//S(t-2 ) != null
		Formula array_not_null =
			Formula.getFormula( 
			new Predicate2Ar(
			new Stack(Expression.getCOUNTER_MINUS_2()),
				Expression._NULL,
				PredicateSymbol.EQ), Connector.NOT );
		//S(t-1) < S(t-2).length
		Formula arr_index_correct =
			new Predicate2Ar(
			new Stack(Expression.getCOUNTER_MINUS_1()),
				new FieldAccess(
						ArrayLengthConstant.ARRAYLENGTHCONSTANT,
			new Stack(Expression.getCOUNTER_MINUS_2())),
				PredicateSymbol.LESS);

		Formula condition =
		Formula.getFormula(array_not_null, arr_index_correct, Connector.AND);
		Expression arrElementAtIndex =
			new ArrayAccessExpression(new Stack(Expression.getCOUNTER_MINUS_2()), new Stack(Expression.getCOUNTER_MINUS_1()));
		//S(t-2)[S(t-1)] <--- S(t)
		_n_Postcondition = (Formula)_n_Postcondition.substitute(arrElementAtIndex, stackTop);
		
		wps[0] = Formula.getFormula(condition, _n_Postcondition, Connector.IMPLIES);
	
		
		//exceptional termination
		//S(t-2 ) == null ==> _exc_Postcondition(java.lang.NullPointerException)
		Formula array_null =
			new Predicate2Ar(
			new Stack(Expression.getCOUNTER_MINUS_2()),
				Expression._NULL,
				PredicateSymbol.EQ);
		Formula nullPointer =
			getWpForException(
				(JavaObjectType) JavaType.getJavaRefType(
					ClassNames.NULLPOINTERException));
		wps[1] = Formula.getFormula(array_null, nullPointer, Connector.IMPLIES);
		/*Util.dump(" wps[1] " + wps[1]);*/
		
		//S(t-1) > S(t-2).length ==> _exc_Postcondition(java.lang. ArrayIndexOutOfBoundsException)
		
		Formula indGrtLen = new Predicate2Ar(
				new Stack(Expression.getCOUNTER_MINUS_1()),
				new FieldAccess(
						ArrayLengthConstant.ARRAYLENGTHCONSTANT,
			new Stack(Expression.getCOUNTER_MINUS_2())),
				PredicateSymbol.GRTEQ);
		Formula indLe0 = new Predicate2Ar(
				new Stack(Expression.getCOUNTER_MINUS_1()),
				new NumberLiteral(0 ),
				PredicateSymbol.LESS);
		
		Formula arr_index_not_correct = Formula.getFormula( indGrtLen, indLe0, Connector.OR);
			
		/*Util.dump(" arr_index_not_correct " + arr_index_not_correct);*/
		
		Formula outOfBounds =
			getWpForException(
				(JavaObjectType) JavaType.getJavaRefType(
					ClassNames.ARRAYINDEXOUTOFBOUNDException));
		/*Util.dump(" excPost" + outOfBounds);*/
		
		wps[2] =
		Formula.getFormula(arr_index_not_correct, outOfBounds, Connector.IMPLIES);
		/*Util.dump("wps[2] " + wps[2]);*/
		wp = Formula.getFormula(wps, Connector.AND);
		/*Util.dump("the typeASTORE instruction " + wp);*/
		return wp;
	}
}
