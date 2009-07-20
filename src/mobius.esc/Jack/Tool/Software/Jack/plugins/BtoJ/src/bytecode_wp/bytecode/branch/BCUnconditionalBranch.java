/*
 * Created on Feb 27, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.branch;

import org.apache.bcel.generic.InstructionHandle;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract class BCUnconditionalBranch extends BCJumpInstruction {

	/**
	 * @param _branchInstruction
	 */
	public BCUnconditionalBranch(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
	}
	

}
