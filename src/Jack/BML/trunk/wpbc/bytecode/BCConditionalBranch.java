/*
 * Created on Mar 2, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import org.apache.bcel.generic.InstructionHandle;

import specification.ExceptionalPostcondition;
import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCConditionalBranch extends BCJumpInstruction {
	
	private Formula branchPostconditionCondition;
	
	/**
	 * @param _branchInstruction
	 */
	public BCConditionalBranch(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
		
	}
	/**
	 * @return Returns the branchPostconditionCondition.
	 */
	public Formula getBranchPostconditionCondition() {
		return branchPostconditionCondition;
	}

	/**
	 * sets the posctcondition for the branch byte code 
	 * @param branchPostconditionCondition The branchPostconditionCondition to set.
	 */
	public void setBranchPostconditionCondition( Formula _branchPostconditionCondition) {
		branchPostconditionCondition = _branchPostconditionCondition;
	}
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition) {
		// TODO Auto-generated method stub
		return null;
	}

}
