/*
 * Created on Mar 2, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.branch;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract class BCConditionalBranch extends BCJumpInstruction {

	/**
	 * @param _branchInstruction
	 */
	public BCConditionalBranch(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
	}

	/**
	 * this method is called by objects that represent instructions that are
	 * exectuted after this one in case the condition is true and the jump is
	 * done
	 * @param config TODO
	 */
	public abstract Formula wpBranch(IJml2bConfiguration config,
			Formula _normal_Postcondition, ExsuresTable _exc_Postcondition);

	public abstract VCGPath wpBranch(IJml2bConfiguration config, VCGPath vcs,
			ExsuresTable _exc);

}
