/*
 * Created on Apr 6, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode;

import org.apache.bcel.generic.InstructionHandle;

import bytecode_wp.bcexpression.javatype.JavaType;

/**
 * @author mpavlova
 *
 *  Denote family of instructions that allocates space in the heap.
 *  ANEWARRAY, MULTIANEWARRAY, NEW, NEWARRAY
 */
public abstract class BCAllocationInstruction extends BCExceptionThrower {
	//    ANEWARRAY, MULTIANEWARRAY, NEW, NEWARRAY
	
	/**
	 * @param _instruction
	 */
	public BCAllocationInstruction(InstructionHandle _instruction, JavaType _type) {
		super(_instruction);
	}
}
