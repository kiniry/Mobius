/*
 * Created on Apr 6, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.InstructionHandle;

import specification.ExceptionalPostcondition;
import bcexpression.javatype.JavaType;
import formula.Formula;

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

	

//	/* (non-Javadoc)
//	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
//	 */
//	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition) {
//		// TODO Auto-generated method stub
//		return null;
//	}
	

}
