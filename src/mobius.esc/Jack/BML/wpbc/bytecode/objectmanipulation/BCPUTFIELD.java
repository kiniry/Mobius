package bytecode.objectmanipulation;

import org.apache.bcel.generic.InstructionHandle;
import utils.Util;

import constants.BCConstantFieldRef;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

import bcclass.BCConstantPool;
import bcclass.attributes.ExsuresTable;
import bcexpression.ArithmeticExpression;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.FieldAccess;
import bcexpression.NumberLiteral;

import bcexpression.javatype.ClassNames;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;

/**
 * @author mpavlova
 *  
 *  putfield
 * 
 *  Operation: Set field in object
 *
 *  Format : putfield 	indexbyte1 	indexbyte2 	
 * 
 * Operand Stack:   ..., objectref, value ==>  ...
 *
 * Description : The unsigned indexbyte1 and indexbyte2 are used to construct an index into the runtime constant pool of the 
 * current class, where the value of the index is (indexbyte1 << 8) | indexbyte2. The runtime constant pool item at that index must 
 * be a symbolic reference to a field, which gives the name and descriptor of the field as well as a symbolic reference to the 
 * class in which the field is to be found. The class of objectref must not be an array. If the field is protected, and it is either a member 
 * of the current class or a member of a superclass of the current class, then the class of objectref must be either the current class 
 * or a subclass of the current class.
 *
 * The referenced field is resolved. The type of a value stored by a putfield instruction must be compatible with the descriptor of the 
 * referenced field . If the field descriptor type is boolean, byte, char, short, or int, then the value must be an int. If the field descriptor type 
 * is float, long, or double, then the value must be a float, long, or double, respectively. If the field descriptor type is a reference type, then 
 * the value must be of a type that is assignment compatible with the field descriptor type. If the field is final, it should be declared in the 
 * current class. Otherwise, an IllegalAccessError is thrown.
 *
 *  The value and objectref are popped from the operand stack. The objectref must be of type reference. 
 * The value undergoes value set conversion (?3.8.3), resulting in value', and the referenced field in objectref is set to value'.
 * 
 * 
 * Linking Exceptions : During resolution of the symbolic reference to the field, any of the exceptions pertaining to field resolution documented in Section 5.4.3.2 can be thrown.
 * Otherwise, if the resolved field is a static field, putfield throws an IncompatibleClassChangeError.
 * Otherwise, if the field is final, it must be declared in the current class. Otherwise, an IllegalAccessError is thrown.
 *
 * Runtime Exception :  Otherwise, if objectref is null, the putfield instruction throws a NullPointerException.
 * 
 * 
 *  wp = S(t-1) != null ==> psi^n[t <-- t -2 ] [index with ( S(t-1)) <-- S(t)] &&
 *           S(t-1) == null ==> psi^e(NullPointerException)   
 */
public class BCPUTFIELD extends BCFieldOrMethodInstruction {

	/**
	 * @param _instruction
	 * @param _type
	 * @param _classType
	 *  @param _cp
	 */
	public BCPUTFIELD(
		InstructionHandle _instruction,
		JavaType _type,
		JavaType _classType,
		BCConstantPool _cp) {
		super(_instruction, _type, _classType, _cp);
		setExceptionsThrown(
			new JavaObjectType[] {
				(JavaObjectType) JavaObjectType.getJavaRefType(
					ClassNames.NULLPOINTERException)});
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;

		// the object whose field is assigned - S(t-1)
		Stack obj =
			new Stack(
				ArithmeticExpression.getArithmeticExpression(
					Expression.COUNTER,
					new NumberLiteral(1),
					ExpressionConstants.SUB));

		// S(t-1 ) != null
		Formula objNotNull =
			Formula.getFormula ( new Predicate2Ar(obj, Expression._NULL, PredicateSymbol.EQ), 
					Connector.NOT);

		//psi^n[t <-- t-2 ]
		Formula wpObjNotNullImpl =
		(Formula)_normal_Postcondition.substitute(
				Expression.COUNTER,
				ArithmeticExpression.getArithmeticExpression(
					Expression.COUNTER,
					new NumberLiteral(2),
					ExpressionConstants.SUB));
		// field access in this form :
		// index -the index of the field in the cp for the field that is accessed; 
		// S(t-1) - the object whose field is dereferenced):   
		// This results in :  index(  S(t-1)  )
		FieldAccess fieldAccess =
			new FieldAccess(
				(BCConstantFieldRef) (getConstantPool()
					.getConstant(getIndex())),
				new Stack(
					(
						ArithmeticExpression) ArithmeticExpression
							.getArithmeticExpression(
						Expression.COUNTER,
						new NumberLiteral(1),
						ExpressionConstants.SUB)));

		//			psi^n[t <-- t-2 ][ index(  S(t-1)  ) <-- S(t)]
		wpObjNotNullImpl =
		(Formula)wpObjNotNullImpl.substitute(
				fieldAccess,
				new Stack(Expression.COUNTER));

		Formula wpObjNotNull =
			Formula.getFormula(objNotNull, wpObjNotNullImpl, Connector.IMPLIES);
		//		///////////////////////////////////////////////////////////////////////////
		//		///////////////////////////////////////////////////////////////////////////
		/////////////////////////////////////////////////////////////////////////////
		//exceptional termination - null object access
		//S(t - 1) == null
		Formula objNull =
			new Predicate2Ar(
				new Stack(
					ArithmeticExpression.getArithmeticExpression(
						Expression.COUNTER,
						new NumberLiteral(1),
						ExpressionConstants.SUB)),
				Expression._NULL,
				PredicateSymbol.EQ);

		//psi^e ("Ljava/lang/NullPointerException;")
		// if there if the object is null throw a "Ljava/lang/NullPointerException;"
		Formula objNullImplies =
			getWpForException(getExceptionsThrown()[0]);

		//S(t -1) == null ==> psi^e("Ljava/lang/NullPointerException;")
		Formula wpObjNull =
			Formula.getFormula(objNull, objNullImplies, Connector.IMPLIES);

		wp = Formula.getFormula(wpObjNotNull, wpObjNull, Connector.AND);
		return wp;
	}

}
