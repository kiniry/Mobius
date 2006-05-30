/*
 * Created on Apr 6, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.objectmanipulation;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.javatype.ClassNames;
import bytecode_wp.bcexpression.javatype.JavaObjectType;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.jml.TYPEOF;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCExceptionThrower;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.vcg.Hypothesis;
import bytecode_wp.vcg.VCGPath;

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
 * wp =( S(t) <: ClassAtIndex(index)  || S(t) == null) ==> psi^n 
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
		IJml2bConfiguration config,
		Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		return null;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		Formula objectCastableToType =
			new Predicate2Ar(
				new TYPEOF(new Stack(Expression.COUNTER)) ,
				getType(),
				PredicateSymbol.SUBTYPE);
		// add the hypothesis in the pool of hypothesis	
		Integer hCastable = vcs.addHyp( getPosition(), objectCastableToType);
		
		//add the hypothesis to all vc-s
		vcs.addHypsToVCs(hCastable);
		
		Formula objectNotCastableToType =
		Formula.getFormula ( new Predicate2Ar(
			new TYPEOF(new Stack(Expression.COUNTER)) ,
			getType(),
			PredicateSymbol.SUBTYPE) , Connector.NOT );
			// in case the object cannot be cast - Ljava/lang/ClassCastException; is thrown
		VCGPath excWp =
			getWpForException(config,
				getExceptionsThrown()[0]);
		
		Integer hNotCastable = excWp.addHyp(getPosition(), objectNotCastableToType);
		excWp.addHypsToVCs( hNotCastable);
		vcs.merge(excWp );
		
		return vcs;
	}

}
