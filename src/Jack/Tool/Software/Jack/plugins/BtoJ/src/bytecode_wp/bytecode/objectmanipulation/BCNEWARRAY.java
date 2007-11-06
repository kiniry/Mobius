package bytecode_wp.bytecode.objectmanipulation;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;

import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.FieldAccess;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.javatype.ClassNames;
import bytecode_wp.bcexpression.javatype.JavaObjectType;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.ref.ArrayReference;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCAllocationInstruction;
import bytecode_wp.constants.ArrayLengthConstant;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.utils.FreshIntGenerator;
import bytecode_wp.utils.Util;
import bytecode_wp.vcg.VCGPath;

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
 * wp = S(t) >= 0 ==> psi^n[S(t) <-- new ArrayRef(type, S(t))]
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
		IJml2bConfiguration config,
		Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		return null;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		//in case of normal termination
		//Stack stackTop = new Stack(Expression.COUNTER);
	
		Formula topStack_grt_0 =
			new Predicate2Ar(
				new Stack(Expression.COUNTER),
				new NumberLiteral(0),
				PredicateSymbol.GRTEQ);
		
		ArrayReference new_arr_ref =
			new ArrayReference(
				FreshIntGenerator.getInt(),
				getType()
				);
	
		//_psi^n[S(t) <-- new ArrayRef[index] (S(t) )]
		vcs.substitute(
				new Stack(Expression.COUNTER),
				new_arr_ref);

		//			length( new ArrayRef(type, S(t) ) ) 
		FieldAccess arr_length_access =
			new FieldAccess(ArrayLengthConstant.ARRAYLENGTHCONSTANT, new_arr_ref);
		
		// substitute the access to the length field of the created array by stack top
		//_psi^n[length( new ArrayRef(type) <-- S(t)]
		vcs.substitute(
				arr_length_access,
				new Stack(Expression.COUNTER));

		Integer key1 = vcs.addHyp(getPosition(), topStack_grt_0);
		vcs.addHypsToVCs(key1 );
		
		// the length of the created array is the element store on the stack top
		Integer keyLen_eq_stack_top = vcs.addHyp(getPosition(), new Predicate2Ar( arr_length_access.copy(), new Stack( Expression.COUNTER), PredicateSymbol.EQ));
		vcs.addHypsToVCs(keyLen_eq_stack_top);
		
		//reference is different from null 
		Formula refNeqNull = new Predicate2Ar( Expression._NULL, new_arr_ref , PredicateSymbol.NOTEQ);
		Integer  keyRefDiffNull = vcs.addHyp(getPosition(), refNeqNull);
		vcs.addHypsToVCs( keyRefDiffNull);
		
		//in case of exc termination
		Formula topStack_lesseq_0 =
			new Predicate2Ar(
				new Stack(Expression.COUNTER),
				new NumberLiteral(0),
				PredicateSymbol.LESS);
				
		// condition for exceptional termination - the length is negative 		
		VCGPath excPre =
			getWpForException(config,
				(JavaObjectType) JavaType.getJavaRefType(
					ClassNames.NEGATIVEARRAYSIZEException));
		
		Integer key2 = excPre.addHyp(getPosition(), topStack_lesseq_0);
		excPre.addHypsToVCs( key2);
		vcs.merge(excPre);
		return vcs;
	}
}
