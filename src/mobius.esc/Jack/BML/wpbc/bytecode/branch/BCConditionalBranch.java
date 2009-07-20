/*
 * Created on Mar 2, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.branch;

import org.apache.bcel.generic.InstructionHandle;

import bcclass.attributes.ExsuresTable;

import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract  class BCConditionalBranch extends BCJumpInstruction {
	
	
	/**
	 * @param _branchInstruction
	 */
	public BCConditionalBranch(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
	}
		
	/**
	 * this method is called by  objects that represent instructions that are exectuted after this one
	 * in case the condition is true and 
	 * the jump is done
	 */
	public abstract Formula wpBranch(
	Formula _normal_Postcondition,
	ExsuresTable _exc_Postcondition);


}
