package bytecode_wp.bytecode.block;

import java.util.HashMap;

import jml2b.IJml2bConfiguration;
import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.bytecode.BCLoopEnd;
import bytecode_wp.bytecode.branch.BCConditionalBranch;
import bytecode_wp.formula.Formula;
import bytecode_wp.utils.Util;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 * 
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates. To enable and disable the creation of type
 * comments go to Window>Preferences>Java>Code Generation.
 */
public class BranchingBlock extends Block {

	private Block branchTargetBlock;

	public BranchingBlock(int _first, int _last, BCInstruction[] _bytecode) {
		super(_first, _last, _bytecode);
	}

	/**
	 * Returns the branchTargetBlock.
	 * 
	 * @return Block
	 */
	public Block getBranchTargetBlock() {
		return branchTargetBlock;
	}

	public void setTargetBlocks(HashMap blocks) {
		if (getLast() instanceof BCLoopEnd) {
			BCConditionalBranch last = (BCConditionalBranch) ((BCLoopEnd) getLast())
					.getWrappedInstruction();

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
	 * 
	 * @param branchTargetBlock
	 *            The branchTargetBlock to set
	 */
	public void setBranchTargetBlock(Block branchTargetBlock) {
		this.branchTargetBlock = branchTargetBlock;
	}

	/**
	 * 
	 * @param _normal_Postcondition
	 * @param _exc_postcondition
	 * @return this method serves to call wpBranch in branching instructions.
	 *         When the branching instruction is a loop end instruction then we
	 *         require that the invariant establishes the normal_Postcondition
	 */
	public Formula calculateBranchRecursively(IJml2bConfiguration config,
			VCGPath _normal_Postcondition, ExsuresTable _exc_postcondition) {
		VCGPath wp = (VCGPath) _normal_Postcondition.copy();
		BCInstruction last = getLast();
		if (last instanceof BCLoopEnd) {

			last = ((BCLoopEnd) last).getWrappedInstruction();

		}
		wp = ((BCConditionalBranch) last).wpBranch(config, wp,
				_exc_postcondition);
		Util.dump(" wp instr : " + last + "  = " + wp);
		VCGPath wpBlock = wp(config, wp, _exc_postcondition);
		_calculateRecursively(config, wpBlock, _exc_postcondition);
		return null;

	}

	public String toString(String _offset) {
		return "BRANCH  " + super.toString();

	}
}
