/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.branch;
import java.util.Enumeration;
import java.util.Vector;
import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.InstructionHandle;
import bytecode.BCInstruction;
import bytecode.EndBlockInstruction;
import bytecode.block.*;
import utils.Util;
/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract class BCJumpInstruction extends BCInstruction {
	private BCInstruction target;
	private int targetPosition;
	/* private Vector targetBlocks; */
	protected Block targetBlock;
	
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
		target = _t;
	}
	/**
	 * return BCInstruction -- the instruction to which this jump instruction
	 * targets to
	 */
	public BCInstruction getTarget() {
		return target;
	}
	/*	*//**
			 * @param _block -
			 *            adds _block to the vector of blocks to which targets
			 *            this instruction
			 */
	/*
	 * protected void addTargetBlock(Block _block) { if (targetBlocks == null) {
	 * targetBlocks = new Vector(); } targetBlocks.add(_block);
	 */
	/**
	 * this method is called by exterior once the target instruction is set It
	 * sets the target blocks for this jump instruction
	 *  
	 */
	public void setTargetBlock(Trace _trace) {
		Block _b = null;
		if (getTargetPosition() <= getPosition()) {
			if ((_b = _trace.getBlockStartingAtEndingAt(target, this)) == null) {
				_b = new LoopBlock(target, this);
				_trace.addBlock(_b);
			}
			if (_b != null) {
				targetBlock = _b;
				return;
			}
		}
		BCInstruction _last = target;
		while (_last != null) {
			if (_last instanceof EndBlockInstruction) {
				if ((_b = _trace.getBlockStartingAtEndingAt(target, _last)) == null) {
					_b = new Block(target, _last);
					_trace.addBlock(_b);
				}
				targetBlock = _b;
				break;
			}
			_last = _last.getNext();
		}
	}
	
	
	/*
	 * public void setTargetBlocks(Vector v) { targetBlocks = v;
	 */
	/* public Vector getTargetBlocks() { */
	public Block getTargetBlock() {
		return targetBlock;
	}
	public void dump() {
		/*
		 * Enumeration en = targetBlocks.elements();
		 */
		Util.dump("target blocks for " + getInstructionHandle().toString());
		targetBlock.dump("");
		/*
		 * while (en.hasMoreElements()) { _b = (Block) en.nextElement();
		 * _b.dump("");
		 */
	}
	/**
	 * @return
	 */
	public int getTargetPosition() {
		return targetPosition;
	}
}
