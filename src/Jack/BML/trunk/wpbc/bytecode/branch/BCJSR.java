/*
 * Created on Mar 1, 2004
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
 *  jump to subroutione
 * 
 *wp (psi^n, psi^e) = psi^n
 */
public class BCJSR extends  BCUnconditionalBranch {

	/**
	 * @param _branchInstruction
	 */
	public BCJSR(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
	}
	
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
//		Block subroutine = getTargetBlock();
//		
//		// the wp for the jsr instruction is the wp of the block that represents the subroutine
//		wp = subroutine.wp( _normal_Postcondition, _exc_Postcondition);
		wp = _normal_Postcondition;
		return wp;
	}

}
