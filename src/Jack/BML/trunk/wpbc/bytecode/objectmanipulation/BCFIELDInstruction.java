/*
 * Created on Apr 6, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.objectmanipulation;

import org.apache.bcel.generic.InstructionHandle;
import bcclass.BCConstantPool;
import bcexpression.javatype.JavaType;



/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract class BCFIELDInstruction extends BCFieldOrMethod {
		/**
	 * @param _instruction - the object form the bcel library representing the instruction 
	 * @param _type - the type of the instruction (of the object that is treated by the instruction)
	 * @param _classType - the class where the field is declared
	 */
	public BCFIELDInstruction(InstructionHandle _instruction, JavaType _type, JavaType _classType, BCConstantPool _cp) {
		super(_instruction , _type, _classType, _cp);
		
		
	}
}
