package bytecode.objectmanipulation;

import org.apache.bcel.generic.InstructionHandle;

import constants.ArrayLengthConstant;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

import utils.FreshIntGenerator;

import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.FieldAccessExpression;
import bcexpression.NumberLiteral;

import bcexpression.javatype.ClassNames;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;
import bcexpression.ref.ArrayReference;
import bcexpression.vm.Stack;
import bytecode.BCAllocationInstruction;

/**
 * @author mpavlova
 *
 * newarray
 * 
 * Operation:  Create new array
 *  
 * Operand Stack:  ..., count ==> ..., arrayref
 * 
 * Format: newarray atype
 * 
 * Description:   The count must be of type int. It is popped off the operand stack. 
 * The count represents the number of elements in the array to be created.  	atype is a type among : 
 *  byte, long, int, short, float, double, boolean (NB: in this application long type is discarded) 
 * 
 * A new array whose components are of type atype and of length count is allocated from the garbage-collected heap. 
 * A reference arrayref to this new array object is pushed into the operand stack. 
 * Each of the elements of the new array is initialized to the default initial value for the type of the array
 * 
 * Runtime Exception: If count is less than zero, newarray throws a NegativeArraySizeException. 
 * 
 * wp = S(t) >= 0 ==> psi^n_psi^n[length( with o == new ArrayObject(type, S(t)) <-- S(t)][S(t) <-- new ArrayObject(type, S(t))]
 * 		&&
 * 		S(t) < 0 ==> psi^e
 */
public class BCNEWARRAY extends BCAllocationInstruction {

	private JavaType type;

	public BCNEWARRAY(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		setType(_type);
		setExceptionsThrown(
			new JavaObjectType[] {
				(JavaObjectType) JavaObjectType.getJavaRefType(
					ClassNames.NEGATIVEARRAYSIZEException)});
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return type;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	 */
	public void setType(JavaType _type) {
		type = _type;
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;

		//in case of normal termination
		//Stack stackTop = new Stack(Expression.COUNTER);
		Formula topStack_grt_0 =
			new Predicate2Ar(
			new Stack(Expression.COUNTER),
				new NumberLiteral(0),
				PredicateSymbol.GRTEQ);
		ArrayReference new_arr_ref =
			new ArrayReference(FreshIntGenerator.getInt(), getType(), new Stack(Expression.COUNTER));

		//length( new ArrayObject(type, S(t) ) ) 
		//WITH length_with_new_arr_ref = new WITH(new_arr_ref);
		FieldAccessExpression arr_length_access =
			new FieldAccessExpression(new ArrayLengthConstant(), new_arr_ref);

		//_psi^n[length( with o == new ArrayObject(type, S(t)) <-- S(t)]
		Formula topStack_grt_0_implies =
			_normal_Postcondition.substitute(arr_length_access, new Stack(Expression.COUNTER));

		//_psi^n[S(t) <-- new Ref[index] (S(t) )]
		topStack_grt_0_implies =
			topStack_grt_0_implies.substitute(new Stack(Expression.COUNTER), new_arr_ref);

		Formula nWpTermination =
		Formula.getFormula(
				topStack_grt_0,
				topStack_grt_0_implies,
				Connector.IMPLIES);

		//in case of exc termination
		Formula topStack_lesseq_0 =
			new Predicate2Ar(
			new Stack(Expression.COUNTER),
				new NumberLiteral(0),
				PredicateSymbol.LESS);
		Formula topStack_lesseq_0_implies =
			getWpForException(
				(JavaObjectType) JavaType.getJavaRefType(
					"Ljava/lang/NegativeArraySizeException;"),
				_exc_Postcondition);
		Formula excWpTermination =
		Formula.getFormula(
				topStack_grt_0,
				topStack_grt_0_implies,
				Connector.IMPLIES);
		wp = Formula.getFormula(nWpTermination, excWpTermination, Connector.AND);
		return wp;
	}
}
