/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.branch;
import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.InstructionHandle;

import bytecode.BCInstruction;

//import bytecode.block.*;
//import utils.Util;
/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract class BCJumpInstruction extends BCInstruction {
	
	private int targetPosition;
	
//	protected Block targetBlock;
	
	public BCJumpInstruction(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
		targetPosition = ((BranchInstruction) _branchInstruction
				.getInstruction()).getTarget().getPosition();
	}
	
	/**
	 * @param _t -
	 *            the instruction to which this jump instruction targets to
	 */
	public void setTarget(BCInstruction _t) {
		if (_t == null) {
			targetPosition = -1;
			return;
		}
		targetPosition = _t.getPosition();
	}
	/**
	 * return BCInstruction -- the instruction to which this jump instruction
	 * targets to
	 */
	public BCInstruction getTarget() {
		if (targetPosition == -1) {
			return null;
		}
		BCInstruction target = utils.Util.getBCInstructionAtPosition( getBytecode(), targetPosition);
		return target;
		
	}

	
	 
//	/**
//	 * this method is called by exterior once the target instruction is set It
//	 * sets the target blocks for this jump instruction
//	 *  
//	 */
//	public void setTargetBlock(Block b) {
//		 targetBlock = b;
//	}
//	
//	
//	/*
//	 * public void setTargetBlocks(Vector v) { targetBlocks = v;
//	 */
//	/* public Vector getTargetBlocks() { */
//	public Block getTargetBlock() {
//		return targetBlock;
//	}
//	public void dump() {
//		/*
//		 * Enumeration en = targetBlocks.elements();
//		 */
//		Util.dump("target blocks for " + getInstructionHandle().toString());
//		targetBlock.dump("");
//		/*
//		 * while (en.hasMoreElements()) { _b = (Block) en.nextElement();
//		 * _b.dump("");
//		 */
//	}
	/**
	 * @return
	 */
	public int getTargetPosition() {
		return targetPosition;
	}
}
