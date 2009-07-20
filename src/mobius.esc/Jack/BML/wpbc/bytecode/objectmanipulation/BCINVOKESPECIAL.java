/*
 * Created on 7 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode.objectmanipulation;


import org.apache.bcel.generic.InstructionHandle;

import formula.Connector;
import formula.Formula;

import bcclass.BCConstantPool;

import bcclass.attributes.ExsuresTable;
import bcexpression.javatype.ClassNames;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;



/**
 * Operation : Invoke instance method; special handling for superclass, private, and instance initialization method invocations
 */
public class BCINVOKESPECIAL extends BCInvoke {

	private Formula classInvariant;

	/**
	 * @param _instruction
	 * @param _type
	 * @param _argTypes - types of arguments for the method
	 * @param _classType
	 */
	public BCINVOKESPECIAL(
		InstructionHandle _instruction,
		JavaType _type,
		//JavaType[] _argTypes,
		JavaType _classType,
		BCConstantPool _cp) {
		super(_instruction, _type, _classType, _cp);
		setExceptionsThrown( new JavaObjectType[]{ (JavaObjectType)JavaObjectType.getJavaRefType( ClassNames.NULLPOINTERException) });
	//	argTypes = _argTypes;
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
//			if (classInvariant == null) {
//						return wp;
//					}
//		Formula normalPost =  Formula.getFormula( _normal_Postcondition, classInvariant, Connector.AND);
		// the class invariant must hold in the state after the exec of a constructor
//		Formula wp = super.wp(normalPost, _exc_Postcondition);
		Formula wp = super.wp(_normal_Postcondition, _exc_Postcondition);
		return wp;
	}


}
