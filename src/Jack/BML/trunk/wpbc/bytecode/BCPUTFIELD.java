package bytecode;

import org.apache.bcel.generic.InstructionHandle;

import bcexpression.javatype.JavaType;

/**
 * @author Mariela
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class BCPUTFIELD extends BCFIELDInstruction {
	/**
	 * 
	 * @see bytecode.BCFIELDInstruction#BCFIELDInstruction(InstructionHandle, JavaType)
	 */
	public BCPUTFIELD(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
	}

}
