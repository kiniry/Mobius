/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import java.util.Enumeration;
import bcexpression.vm.Stack;
import java.util.Vector;

import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.InstructionHandle;

import specification.ExceptionalPostcondition;
import utils.Util;
import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract  class BCJumpInstruction extends BCInstruction   {

	
	private BCInstruction target;
	private int targetPosition;
	
	private Vector targetBlocks;

	
	public BCJumpInstruction(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
		targetPosition = ( (BranchInstruction)_branchInstruction.getInstruction()).getTarget().getPosition();
	}
	

	/**
	 * @param _t - the instruction to which this jump instruction targets to
	 */
	public void setTarget(BCInstruction _t) {
		target = _t;
	}
	
	/**
	 * return BCInstruction -- the instruction to which this jump instruction targets to
	 */
	public BCInstruction getTarget() {
		return target;
	}
	/**
	 * 
	 * @param _block - adds _block to the vector of blocks to which
	 *  targets this instruction 
	 */
	protected void addTargetBlock(Block _block) {
		if (targetBlocks == null) {
			targetBlocks = new Vector();
		}
		targetBlocks.add(_block);
	}
	
	/**
	 * this method is called by exterior once the target instruction is set
	 * It sets the target blocks for this jump instruction
	 * 
	 */
	public void setTargetBlocks(Trace _trace) {
		BCInstruction _last = target;
		Block _b = null;
		
		while (_last != null)  {
			if ((_last instanceof BCConditionalBranch) || (_last instanceof EndBlock ) ) {
				if ((_b = _trace.getBlockStartingAtEndingAt(target, _last)) == null ){
					_b = Util.getBlock(target,  _last);
					_trace.addBlock(_b);
				} 
				if (_b != null) {
					_b.dump(""); 
					addTargetBlock(_b) ;
					break;
				}
			}
			_last = _last.getNext();		
		}
		if ((_b != null ) && (_b instanceof LoopBlock ) ) {
			return;
		}
		while (_last != null)  {
			if ( (_last instanceof BCJumpInstruction) && (target.equals(((BCJumpInstruction)_last).getTarget())) ){
				if ((_b = _trace.getBlockStartingAtEndingAt(target, _last)) == null ){
					_b = Util.getBlock(target,  (BCJumpInstruction)_last);
					_trace.addBlock(_b);
				} 
				_b.dump("");
				addTargetBlock(_b) ;
				return;	
			}
			_last = _last.getNext();
		}
	}
	
	public void setTargetBlocks(Vector v) {
		targetBlocks = v;	
	}
	
	public Vector getTargetBlocks() {
		return targetBlocks;
	}
	
	public void dump() {
		Enumeration en = targetBlocks.elements();
		Block _b = null;
		Util.dump("target blocks for "  +getInstructionHandle().toString());
		while (en.hasMoreElements()) {
			_b = (Block)en.nextElement();
			_b.dump("");
		}
	}

	
	/**
	 * @return
	 */
	public int getTargetPosition() {
		return targetPosition;
	}

}
