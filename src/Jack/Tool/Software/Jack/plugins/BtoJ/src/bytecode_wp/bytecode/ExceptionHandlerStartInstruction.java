/*
 * Created on Jul 29, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode;

import jml2b.IJml2bConfiguration;
import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 *
 * Instructions that are starting points for instruction handles 
 * are wrapped in objects of this class. As the wp for this instructions may be calculated more than one time for the same path and the same postcondition the wp for this instruction
 * is saved in the object
 */

// deprecated
public class ExceptionHandlerStartInstruction extends BCInstruction {
	private BCInstruction instruction;
	private VCGPath wp;
	
	public ExceptionHandlerStartInstruction(BCInstruction _instruction) {
		instruction = _instruction;
		instructionHandle = _instruction.getInstructionHandle();
		setNext(_instruction.getNext());
		setPrev(_instruction.getPrev());
		setBCIndex(_instruction.getBCIndex());
		setTargeters(_instruction.getTargeters());
		
		setPosition(_instruction.getPosition());

		//actualise the values in the previous and the next instruction
		BCInstruction prev = _instruction.getPrev();
		prev.setNext(this);
		BCInstruction next = _instruction.getNext();
		next.setPrev(this);
	}
	
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		return null;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		if (wp != null) {
			return wp;
		}
		return instruction.wp(config, vcs, _exc);
		
	}
	


}
