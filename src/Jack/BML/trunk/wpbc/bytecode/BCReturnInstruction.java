package bytecode;

import java.util.Vector;

import org.apache.bcel.generic.InstructionHandle;

import vm.Stack;

import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCReturnInstruction  extends BCInstruction implements EndBlock {
	
	/**
	 * @param _instruction
	 */
	public BCReturnInstruction(InstructionHandle _instruction) {
		super(_instruction);
	}
	public Vector wp(Vector postcondition, Stack stack) {
		return null;
	}
}
