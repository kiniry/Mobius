/*
 * Created on Feb 27, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.branch;

import java.util.Enumeration;


import org.apache.bcel.generic.InstructionHandle;

import bcclass.attributes.ExsuresTable;
import bytecode.EndBlockInstruction;
import bytecode.block.*;
import bytecode.branch.*;


import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCGOTO extends BCUnconditionalBranch implements EndBlockInstruction{
	
	
	/**
	 * @param _branchInstruction
	 */
	public BCGOTO(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
	}
	

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		return _normal_Postcondition;
	}

}
