/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import java.util.Enumeration;
import vm.Stack;
import java.util.Vector;

import org.apache.bcel.generic.InstructionHandle;

import utils.Util;
import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public   class BCJumpInstruction extends BCInstruction   {

	
	private BCInstruction target;
	
	private Vector targetBlocks;
	private Formula branchPostconditionCondition;
	
	public BCJumpInstruction(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
	}
	
	/**
	 * 
	 * @param _wp -  formula object. 
	 * _wp  must be provable before  this instruiction
	 */
	public  void setWP(Formula  _wp) {
		branchPostconditionCondition = _wp;
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
	public void setTargetBlocks() {
		BCInstruction _i = target;
		Block _b = null;
		while (_i != null)  {
			if ((_i instanceof BCConditionalBranch) || (_i instanceof EndBlock ) ) {
				_b = Util.getBlock(target,  _i);
				if (_b != null) {
					_b.dump(""); 
					addTargetBlock(_b) ;
					break;
				}
			}
			_i = _i.getNext();		
		}
		if ((_b != null ) && (_b instanceof LoopBlock ) ) {
			return;
		}
		while (_i != null)  {
			if ( (_i instanceof BCJumpInstruction) && (target.equals(((BCJumpInstruction)_i).getTarget())) ){
					_b = Util.getBlock(target,  (BCJumpInstruction)_i); 
					_b.dump("");
					addTargetBlock(_b) ;
					return;	
			}
			_i = _i.getNext();
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

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula)
	 */
	public Formula wp(Formula postcondition, Stack stack ) {
		return null;
	}
	/**
	 * @return Returns the branchPostconditionCondition.
	 */
	public Formula getBranchPostconditionCondition() {
		return branchPostconditionCondition;
	}
	/**
	 * @param branchPostconditionCondition The branchPostconditionCondition to set.
	 */
	public void setBranchPostconditionCondition( Formula _branchPostconditionCondition) {
		branchPostconditionCondition = _branchPostconditionCondition;
	}
}
