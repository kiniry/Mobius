/*
 * Created on Apr 6, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.objectmanipulation;

import org.apache.bcel.generic.InstructionHandle;



import bcclass.BCConstantPool;
import bcexpression.javatype.ClassNames;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;


/**
 * @author mpavlova
 *
 * Operation : Invoke instance method; dispatch based on class
 *
 * Format :  invokevirtual 	indexbyte1 	indexbyte2 	
 * 
 * invokevirtual = 182 (0xb6)
 *
 * Operand Stack :  ..., objectref, [arg1, [arg2 ...]]  == >...
 *
 * 
 */
public class BCINVOKEVIRTUAL extends BCInvoke {

	//	/private JavaType[] argTypes;

	/**
	 * @param _instruction - the corresponding bcel data structure
	 * @param _type
	 * @param _classType
	 * @param _cp constant
	 * pool of the class where this executuion is declared
	 */
	public BCINVOKEVIRTUAL(
		InstructionHandle _instruction,
		JavaType _type,
		JavaType _classType,
		BCConstantPool _cp) {
		super(_instruction, _type, _classType, _cp);
		setExceptionsThrown( new JavaObjectType[]{ (JavaObjectType)JavaObjectType.getJavaRefType( ClassNames.NULLPOINTERException) });		
	}


}
