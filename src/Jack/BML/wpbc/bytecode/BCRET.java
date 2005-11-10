/*
 * Created on Feb 26, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import java.util.Vector;

import org.apache.bcel.generic.InstructionHandle;

import bcclass.attributes.ExsuresTable;

import formula.Formula;

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
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		return _normal_Postcondition;
	}
//	/**
//	 * sets the block that ends with this instruction
//	 */
//	public void setBlock(Block block) {
//		blockEndingWithThis = block;
//	}

//	/* (non-Javadoc)
//	 * @see bytecode.EndBlockInstruction#calculateRecursively(formula.Formula, bcclass.attributes.ExsuresTable)
//	 */
//	public Formula calculateRecursively(
//		Formula _normal_postcondition,
//		ExsuresTable _exs_postcondition) {
//		Formula wp = blockEndingWithThis.calculateRecursively(_normal_postcondition, _exs_postcondition);
//		return wp;
//	}

}
