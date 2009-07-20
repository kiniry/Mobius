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
import bcexpression.FieldAccess;
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

 *   During resolution of the symbolic reference to the class, array, or interface type, any of the exceptions documented in can be thrown.
 *
 *   Runtime Exception : Otherwise, if count is less than zero, the anewarray instruction throws a NegativeArraySizeException. 
 *
 *  NB: the same as newarray. Should be added the wp for linking exception
 */
public class BCANEWARRAY
	extends BCAllocationInstruction
	implements BCCPInstruction {
		
	private int cpIndex;
	private JavaType type;
	
	public BCANEWARRAY(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		setIndex(((CPInstruction) _instruction.getInstruction()).getIndex());
		setType(_type);
		setExceptionsThrown( new JavaObjectType[]{ (JavaObjectType)JavaObjectType.getJavaRefType( ClassNames.NEGATIVEARRAYSIZEException) });
	}

	/* (non-Javadoc)
	* @see bytecode.BCIndexedInstruction#setIndex(int)
	*/
	public void setIndex(int _index) {
		cpIndex = _index;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCIndexedInstruction#getIndex()
	 */
	public int getIndex() {
		return cpIndex;
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
//		Stack stackTop = new Stack(Expression.COUNTER);
		Formula topStack_grt_0 =
			new Predicate2Ar(
			new Stack(Expression.COUNTER),
				new NumberLiteral(0),
				PredicateSymbol.GRTEQ);
		ArrayReference new_arr_ref =
			new ArrayReference(FreshIntGenerator.getInt(), getType(), new Stack(Expression.COUNTER));

		//			length( new ArrayObject(type, S(t) ) ) 
		//WITH length_with_new_arr_ref = new WITH(new_arr_ref);

		FieldAccess arr_length_access =
			new FieldAccess(
				ArrayLengthConstant.ARRAYLENGTHCONSTANT,
				new_arr_ref);
		//_psi^n[length( with o == new ArrayObject(type, S(t)) <-- S(t)]
		
		Formula topStack_grt_0_implies =
		(Formula)_normal_Postcondition.substitute(new Stack(Expression.COUNTER), new_arr_ref);
		topStack_grt_0_implies =
			(Formula)topStack_grt_0_implies.substitute(arr_length_access, new Stack(Expression.COUNTER));
		Formula nWpTermination =
		Formula.getFormula(
				topStack_grt_0,
				topStack_grt_0_implies,
				Connector.IMPLIES);

		//in case of exc termination//////////////////////////////////////////////////////
		Formula topStack_lesseq_0 =
			new Predicate2Ar(
			new Stack(Expression.COUNTER),
				new NumberLiteral(0),
				PredicateSymbol.LESS);
				
				
		//in the  case where the specified size is negative -  "Ljava/lang/NegativeArraySizeException;" is thrown
		Formula topStack_lesseq_0_implies =
			getWpForException(
				getExceptionsThrown()[0]);
		Formula excWpTermination =
		Formula.getFormula(
				(Formula)topStack_grt_0.copy(),
				topStack_grt_0_implies,
				Connector.IMPLIES);
		wp = Formula.getFormula(nWpTermination, excWpTermination, Connector.AND);
		return wp;
	}

	
	
}
