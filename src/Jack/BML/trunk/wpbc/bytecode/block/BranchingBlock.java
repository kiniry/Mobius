package bytecode.block;

import java.util.HashMap;

import utils.Util;

import formula.Connector;
import formula.Formula;

import bcclass.attributes.ExsuresTable;
import bytecode.BCInstruction;
import bytecode.BCLoopEnd;
import bytecode.branch.BCConditionalBranch;

/**
 * @author mpavlova
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class BranchingBlock extends Block {

	private Block branchTargetBlock;

	public BranchingBlock(int _first, int _last, BCInstruction[] _bytecode) {
		super(_first, _last, _bytecode);
	}

	/**
	 * Returns the branchTargetBlock.
	 * @return Block
	 */
	public Block getBranchTargetBlock() {
		return branchTargetBlock;
	}

	public void setTargetBlocks(HashMap blocks) {
		if ( getLast() instanceof BCLoopEnd) {
			BCConditionalBranch last  =  (BCConditionalBranch)((BCLoopEnd)  getLast()).getWrappedInstruction();
					
			BCInstruction targetInstr = last.getTarget();
			if (targetInstr != null) {
				Integer posTargetInstr = new Integer(targetInstr.getPosition());
				Block targetBlock = (Block) blocks.get(posTargetInstr);
				setBranchTargetBlock(targetBlock);
			}
			BCInstruction nextInstr = last.getNext();
			if (nextInstr != null) {
				Integer posNextInstr = new Integer(nextInstr.getPosition());
				Block nextBlock = (Block) blocks.get(posNextInstr);
				setTargetSeqBlock(nextBlock);
			}
			return;	
		}
		BCConditionalBranch last = (BCConditionalBranch) getLast();

		BCInstruction targetInstr = last.getTarget();
		BCInstruction nextInstr = last.getNext();

		Integer posTargetInstr = new Integer(targetInstr.getPosition());
		Block targetBlock = (Block) blocks.get(posTargetInstr);

		Integer posNextInstr = new Integer(nextInstr.getPosition());
		Block nextBlock = (Block) blocks.get(posNextInstr);

		setBranchTargetBlock(targetBlock);
		setTargetSeqBlock(nextBlock);
	}

	/**
	 * Sets the branchTargetBlock.
	 * @param branchTargetBlock The branchTargetBlock to set
	 */
	public void setBranchTargetBlock(Block branchTargetBlock) {
		this.branchTargetBlock = branchTargetBlock;
	}

	/**
	 * 
	 * @param _normal_Postcondition
	 * @param _exc_postcondition
	 * @return
	 * this method serves to call wpBranch in branching instructions.
	 * When the branching instruction is a loop end instruction then we require that the invariant establishes the 
	 * normal_Postcondition
	 */
	public Formula calculateBranchRecursively(
		Formula _normal_Postcondition,
		ExsuresTable _exc_postcondition) {
		Formula wp = (Formula)_normal_Postcondition.copy();
		if (getLast() instanceof BCLoopEnd) {
			BCLoopEnd loopEnd = (BCLoopEnd ) getLast();
//			Formula invariant = (Formula)loopEnd.getInvariant().copy();
//			Formula invImpliesWp = Formula.getFormula( invariant, wp, Connector.IMPLIES); 
			wp = loopEnd.wpBranch(_normal_Postcondition, _exc_postcondition);	
		}
		BCConditionalBranch last = (BCConditionalBranch) getLast();
		
		wp = last.wpBranch(wp, _exc_postcondition);
		if (last.getBCIndex() == 2494) {
			Util.dump("this is the ILL INSTRUCTION ");
		}
		Util.dump(
			" wp instr : "
				+ last
				+ "  = "
				+ wp);
		Formula wpBlock = wp(wp, _exc_postcondition);
//		Util.dump("***********************************************************");
		_calculateRecursively(wpBlock,_exc_postcondition); 
	
		
		return wp;
	}

	public String toString(String _offset) {
		return "BRANCH  " + super.toString();
	

	}
}
