/*
 * Created on 7 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.bytecode.objectmanipulation;


import org.apache.bcel.generic.InstructionHandle;

import bytecode_wp.bcclass.BCConstantPool;
import bytecode_wp.bcexpression.javatype.ClassNames;
import bytecode_wp.bcexpression.javatype.JavaObjectType;
import bytecode_wp.bcexpression.javatype.JavaType;


/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class BCINVOKEINTERFACE extends BCInvoke {

//	/private JavaType[] argTypes;

	/**
	 * @param _instruction
	 * @param _type
	 * @param _argTypes - types of arguments for the method
	 * @param _classType
	 */
	public BCINVOKEINTERFACE(
		InstructionHandle _instruction,
		JavaType _type,
		//JavaType[] _argTypes,
		JavaType _classType,
		BCConstantPool _cp) {
		super(_instruction, _type, _classType, _cp);
		setExceptionsThrown( new JavaObjectType[]{ (JavaObjectType)JavaObjectType.getJavaRefType( ClassNames.NULLPOINTERException) });
	//	argTypes = _argTypes;
	}


}
