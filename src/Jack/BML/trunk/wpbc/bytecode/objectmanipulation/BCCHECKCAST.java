/*
 * Created on Apr 6, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.objectmanipulation;

import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.InstructionHandle;

import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.javatype.ClassNames;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;
import bcexpression.jml.TYPEOF;
import bcexpression.vm.Stack;
import bytecode.BCExceptionThrower;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

/**
 * @author mpavlova
 *
 * checkcast
 *
 *  Operation:   Check whether object is of given type
 *  
 *  Format: checkcast 	indexbyte1 	 indexbyte2 	
 * 
 *  Operand Stack:  ..., objectref  ==> ..., objectref
 * 
 * 
 * Description
 *
 *   The objectref must be of type reference. The unsigned indexbyte1 and indexbyte2 are used to construct an index into the runtime constant pool of the current class (?3.6), where the value of the index is (indexbyte1 << 8) | indexbyte2. The runtime constant pool item at the index must be a symbolic reference to a class, array, or interface type. The named class, array, or interface type is resolved (?5.4.3.1).
 *
 *   If objectref is null or can be cast to the resolved class, array, or interface type, the operand stack is unchanged; otherwise, the checkcast instruction throws a ClassCastException.
 *
 *   The following rules are used to determine whether an objectref that is not null can be cast to the resolved type: if S is the class of the object referred to by objectref and T is the resolved class, array, or interface type, checkcast determines whether objectref can be cast to type T as follows:
 *
 *   * If S is an ordinary (nonarray) class, then:

          o If T is a class type, then S must be the same class  as T, or a subclass of T.

          o If T is an interface type, then S must implement  interface T. 

    * If S is an interface type, then:

          o If T is a class type, then T must be Object .

          o If T is an interface type, then T must be the same interface as S or a superinterface of S .

    * If S is a class representing the array type SC[], that is, an array of components of type SC, then:

          o If T is a class type, then T must be Object .

          o If T is an array type TC[], that is, an array of components of type TC, then one of the following must be true:

                + TC and SC are the same primitive type .

                + TC and SC are reference types , and type SC can be cast to TC by recursive application of these rules.

          o If T is an interface type, T must be one of the interfaces implemented by arrays . 
 *
 * wp = S(t) <: ClassAtIndex(index) ==> psi^n 
 * 		&& 
 * 	   !(	S(t) <: 	 ClassAtIndex(index) ) ==> excPost(java.lang.ClassCastException)
 */
public class BCCHECKCAST
	extends BCExceptionThrower
	implements BCCPInstruction {

	/**
	 * the index into the constant pool that contains the  CONSTANT_Class_info
	 * structure that describes the class which will must be super type of the type of the object pointed by the reference on the top of stack 
	 * */
	private int cpIndex;
	private JavaType type;
	/**
	 * @param _instruction
	 */
	public BCCHECKCAST(
		InstructionHandle _instruction,
		JavaType _type) {
		super(_instruction);
		setIndex(((CPInstruction) _instruction.getInstruction()).getIndex());
		setType(_type);
		setExceptionsThrown( new JavaObjectType[]{ (JavaObjectType)JavaObjectType.getJavaRefType( ClassNames.CLASSCASTException) });
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
		Formula wp = null;
//		Stack topStack = new Stack(Expression.COUNTER);
		Formula objectCastableToType =
			new Predicate2Ar(
				new TYPEOF(new Stack(Expression.COUNTER)) ,
				getType(),
				PredicateSymbol.SUBTYPE);
		Formula nTermination =
		Formula.getFormula(
				objectCastableToType,
				_normal_Postcondition,
				Connector.IMPLIES);

		Formula objectNotCastableToType =
		Formula.getFormula ( new Predicate2Ar(
			new TYPEOF(new Stack(Expression.COUNTER)) ,
			getType(),
			PredicateSymbol.SUBTYPE) , Connector.NOT );
			// in case the object cannot be cast - Ljava/lang/ClassCastException; is thrown
		Formula excWp =
			getWpForException(
				getExceptionsThrown()[0]);
		Formula excTermination =
		Formula.getFormula(objectNotCastableToType, excWp, Connector.IMPLIES);
		wp = Formula.getFormula(nTermination, excTermination, Connector.AND);
		return wp;
	}

}
