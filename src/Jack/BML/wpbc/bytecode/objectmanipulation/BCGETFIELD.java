package bytecode.objectmanipulation;

import org.apache.bcel.generic.InstructionHandle;


import constants.BCConstantFieldRef;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

import bcclass.BCConstantPool;
import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.FieldAccess;
import bcexpression.javatype.ClassNames;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;

/**
 * @author mpavlova
 *
 *	 Operation
 *
 *   Fetch field from object
 *
 *   Format : getfield 	indexbyte1 	indexbyte2 	
 *
 *   Operand Stack : ..., objectref == > ..., value 
 * 
 *  Description: The objectref, which must be of type reference, is popped from the operand stack. The unsigned indexbyte1 and 
 *  indexbyte2 are used to construct an index into the runtime constant pool of the current class, where the value of the index is 
 *  (indexbyte1 << 8) | indexbyte2. The runtime constant pool item at that index must be a symbolic reference to a field , 
 *  which gives the name and descriptor of the field as well as a symbolic reference to the class in which the field is to be found. 
 *  The referenced field is resolved . The value of the referenced field in objectref is fetched and pushed onto the operand stack.
 *  The class of objectref must not be an array. If the field is protected, and it is either a member of the current class or a member
 *  of a superclass of the current class, then the class of objectref must be either the current class or a subclass of the current class.
 *
 * Linking Exceptions: During resolution of the symbolic reference to the field, any of the errors pertaining to field resolution 
 * documented in JVM (Section 5.4.3.2) can be thrown.
 * Otherwise, if the resolved field is a static field, getfield throws an IncompatibleClassChangeError.
 * 
 * Runtime Exception:  Otherwise, if objectref is null, the getfield instruction throws a NullPointerException.
 * 
 * 
 * NB: linking exceptions not considered for the moment
 */
public class BCGETFIELD extends BCFieldOrMethodInstruction {

	/**
	 * @see bytecode.BCFIELDInstruction#BCFIELDInstruction(InstructionHandle, JavaType)
	 */
	public BCGETFIELD(
		InstructionHandle _instruction,
		JavaType _type,
		JavaType _classType,
		BCConstantPool _cp) {
		super(_instruction, _type, _classType, _cp);
		setExceptionsThrown( new JavaObjectType[]{ (JavaObjectType)JavaObjectType.getJavaRefType( ClassNames.NULLPOINTERException) });
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;
		//normal termination
		//S(t) != null
		Formula stackTopNotNull =
			Formula.getFormula(
					new Predicate2Ar(new Stack(Expression.COUNTER), Expression._NULL, PredicateSymbol.EQ),
					Connector.NOT);
	

		FieldAccess fieldAccess =
			new FieldAccess(
				(BCConstantFieldRef) getConstantPool().getConstant(getIndex()),
				new Stack(Expression.COUNTER));

//		Util.dump("getField  _normal_Postcondition " + getInstructionHandle().getInstruction() +  "  " +_normal_Postcondition);
		//substitute the top stack by the field access object
		//psi^n[S(t) <-- index( S(t)) ]
		
		
			
		Stack stackTop  = new Stack(Expression.COUNTER);
		Formula stackTopNotNullImplies =
		(Formula)_normal_Postcondition.substitute(stackTop , fieldAccess);

//		Util.dump("getField   stackTopNotNullImplies " + getInstructionHandle().getInstruction() +  "  " +stackTopNotNullImplies);

		//S(t) != null ==> psi^n[S(t) <-- field(index)( S(t)) ]
		Formula wpStackTopNotNull =
		Formula.getFormula(
				stackTopNotNull,
				stackTopNotNullImplies,
				Connector.IMPLIES);
				
		

		//exceptional termination - null object access
		//S(t) == null
		Formula stackTopNull =
			new Predicate2Ar(new Stack(Expression.COUNTER), Expression._NULL, PredicateSymbol.EQ);

		//psi^e ("Ljava/lang/NullPointerException;")
		// if there if the object is null throw a "Ljava/lang/NullPointerException;"
		Formula stackTopNullImplies =
			getWpForException(
				getExceptionsThrown()[0]);

		//S(t) == null ==> psi^e("Ljava/lang/NullPointerException;")
		Formula wpStackTopNull =
		Formula.getFormula(stackTopNull, stackTopNullImplies, Connector.IMPLIES);

		wp = Formula.getFormula(wpStackTopNull, wpStackTopNotNull, Connector.AND);
//		Util.dump("wp getfield " + wp);
		return wp;
	}
}
