/*
 * Created on Mar 1, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.Type;

import java.lang.Class;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCAthrowInstruction extends BCUnconditionalBranch implements EndBlock{
	
	

	/**
	 * @param _branchInstruction
	 */
	public BCAthrowInstruction(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
		//dump(_branchInstruction.toString() + " throws "  + getExceptions().length);
	
	}
	
	
	
	/**
	 * 
	 * @return the block that  handles
	 * that handles this exception; returns null if there is not any
	 */
	public ExceptionHandleBlock getHandler() {
		return (ExceptionHandleBlock)getTargetBlocks().elementAt(0);
	}
	
	public void setHandler(ExceptionHandleBlock _excHandler) {
		addTargetBlock(_excHandler);
	}
}
