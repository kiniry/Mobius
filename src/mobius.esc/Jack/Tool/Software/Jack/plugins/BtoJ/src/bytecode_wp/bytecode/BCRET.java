/*
 * Created on Feb 26, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode;

import java.util.Vector;

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
public class BCRET extends BCInstruction {
	private BCInstruction retToInstruction;

	private Vector retToBlocks;

//	Block blockEndingWithThis;
	/**
	 * @param _instruction
	 */
	public BCRET(InstructionHandle _instruction) {
		super(_instruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		IJml2bConfiguration config,
		Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		return _normal_Postcondition;
	}


	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		// TODO Auto-generated method stub
		return vcs;
	}



}
