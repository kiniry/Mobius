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
import bytecode.block.*;

import formula.Formula;

import utils.Util;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCRET extends BCInstruction implements EndBlockInstruction {
	private BCInstruction retToInstruction;
	
	private Vector retToBlocks;
	/**
	 * @param _instruction
	 */
	public BCRET(InstructionHandle _instruction) {
		super(_instruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		return _normal_Postcondition;
	}
	
	/**
	 * @param _t - the instruction to which this jump instruction targets to
	 *//*
	public void setRetToInstrcution(BCInstruction _t) {
		retToInstruction = _t;
	}
	
	*//**
	 * return BCInstruction -- the instruction to which this jump instruction targets to
	 *//*
	public BCInstruction getRetToInstruction() {
		return retToInstruction;
	}
	*//**
	 * 
	 * @param _block - adds _block to the vector of blocks to which
	 *  targets this instruction 
	 *//*
	protected void addRetBlock(Block _block) {
		if (retToBlocks == null) {
			retToBlocks = new Vector();
		}
		retToBlocks.add(_block);
	}
	
	*//**
	 * this method is called by exterior once the target instruction is set
	 * It sets the target blocks for this jump instruction
	 * 
	 *//*
	public void setRetToBlocks() {
		BCInstruction _i = retToInstruction;
		Block _b = null;
		while (_i != null)  {
			if ( (_i instanceof  BCJumpInstruction)|| (_i instanceof BCReturnInstruction)) {
				_b = Util.getBlock(retToInstruction,  _i);
				if (_b != null) {
					_b.dump(""); 
					addRetBlock(_b) ;
				}
			}
			if (_b instanceof LoopBlock) {
				return;
			}
			if ( (_i instanceof BCUnconditionalBranch) || (_i instanceof BCReturnInstruction)) {
				break;
			}	
			_i = _i.getNext();
		}
		
		while (_i != null)  {
			if ( (_i instanceof BCJumpInstruction) && (retToInstruction.equals(((BCJumpInstruction)_i).getTarget())) ){
					_b = Util.getBlock(retToInstruction,  (BCJumpInstruction)_i); 
					_b.dump("");
					addRetBlock(_b) ;
					return;	
			}
			_i = _i.getNext();
		}
	}
	
	public void setRetToBlocks(Vector v) {
		retToBlocks = v;	
	}
	
	public Vector getRetToBlocks() {
		return retToBlocks;
	}
	
*/
}
