package bytecode.objectmanipulation;

import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.InstructionHandle;

import constants.ArrayLengthConstant;
import utils.FreshIntGenerator;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.FieldAccessExpression;
import bcexpression.NumberLiteral;
import bcexpression.WITH;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;
import bcexpression.ref.ArrayReference;
import bcexpression.vm.Stack;
import bytecode.BCAllocationInstruction;

/**
 * @author mpavlova
 *
 * anewarray

   Operation: Create new array of reference

    Format  anewarray  indexbyte1 indexbyte2 	

	Operand Stack:    ..., count ==>  ..., arrayref

	Description : The count must be of type int. It is popped off the operand stack. 
	The count represents the number of components of the array to be created.
	The unsigned indexbyte1 and indexbyte2 are used to construct an index into the
	runtime constant pool of the current class, where the value of the index is (indexbyte1 << 8) | indexbyte2. 
	The runtime constant pool item at that index must be a symbolic reference to a class, array, or interface type. 
	The named class, array, or interface type is resolved . A new array with components of that type,
	 of length count, is allocated from the garbage-collected heap, and a reference arrayref to this new array object is
	  pushed onto the operand stack. All components of the new array are initialized to null, the default value for reference types .

Linking Exceptions

    During resolution of the symbolic reference to the class, array, or interface type, any of the exceptions documented in can be thrown.

Runtime Exception

    Otherwise, if count is less than zero, the anewarray instruction throws a NegativeArraySizeException. 
 *
 *  NB: the same as newarray. Should be added the wp for linking exception
 */
public class BCANEWARRAY
	extends BCAllocationInstruction
	implements BCCPInstruction {
		
	private int index;
	private JavaType type;
	
	public BCANEWARRAY(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		setIndex(((CPInstruction) _instruction.getInstruction()).getIndex());
		setType(_type);
	}

	/* (non-Javadoc)
	* @see bytecode.BCIndexedInstruction#setIndex(int)
	*/
	public void setIndex(int _index) {
		index = _index;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCIndexedInstruction#getIndex()
	 */
	public int getIndex() {
		return index;
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
		Stack stackTop = new Stack(Expression.COUNTER);
		Formula topStack_grt_0 =
			new Predicate2Ar(
				stackTop,
				new NumberLiteral(0),
				PredicateSymbol.GRTEQ);
		ArrayReference new_arr_ref =
			new ArrayReference(FreshIntGenerator.getInt(), getType(), stackTop);

		//			length( new ArrayObject(type, S(t) ) ) 
		//WITH length_with_new_arr_ref = new WITH(new_arr_ref);

		FieldAccessExpression arr_length_access =
			new FieldAccessExpression(
				new ArrayLengthConstant(),
				new_arr_ref);
		//_psi^n[length( with o == new ArrayObject(type, S(t)) <-- S(t)]
		Formula topStack_grt_0_implies =
			_normal_Postcondition.substitute(arr_length_access, stackTop);
		topStack_grt_0_implies =
			topStack_grt_0_implies.substitute(stackTop, new_arr_ref);

		Formula nWpTermination =
			new Formula(
				topStack_grt_0,
				topStack_grt_0_implies,
				Connector.IMPLIES);

		//in case of exc termination
		Formula topStack_lesseq_0 =
			new Predicate2Ar(
				stackTop,
				new NumberLiteral(0),
				PredicateSymbol.LESS);
		Formula topStack_lesseq_0_implies =
			getWpForException(
				(JavaObjectType) JavaType.getJavaRefType(
					"Ljava/lang/NegativeArraySizeException;"),
				_exc_Postcondition);
		Formula excWpTermination =
			new Formula(
				topStack_grt_0,
				topStack_grt_0_implies,
				Connector.IMPLIES);
		wp = new Formula(nWpTermination, excWpTermination, Connector.AND);
		return wp;
	}
}
