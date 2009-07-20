/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.conversioninstruction;

import org.apache.bcel.generic.InstructionHandle;

import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.bytecode.BCTypedInstruction;

/**
 * @author mpavlova
 * Super class for the x2y family of instructions
 */
public abstract class BCConversionInstruction  extends BCInstruction implements  BCTypedInstruction {

	private JavaType  type;
	/**
	 * @param _instruction
	 */
	public BCConversionInstruction(InstructionHandle _instruction) {
		super(_instruction);
	}

	
	
}
