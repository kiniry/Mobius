/*
 * Created on Mar 2, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.branch;

import org.apache.bcel.generic.InstructionHandle;

import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract  class BCConditionalBranch extends BCJumpInstruction {
	
	private Formula branchWP;
	
	/**
	 * @param _branchInstruction
	 */
	public BCConditionalBranch(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
		
	}
	
	/**
	 * @return Returns the branchPostconditionCondition.
	 */
	public Formula getBranchWP() {
		return branchWP;
	}

	/**
	 * sets the posctcondition for the branch byte code 
	 * @param branchPostconditionCondition The branchPostconditionCondition to set.
	 */
	public void setBranchWP( Formula _branchWP) {
		branchWP = _branchWP;
	}
}
