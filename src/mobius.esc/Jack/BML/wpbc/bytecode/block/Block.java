/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.block;

import java.util.Enumeration;
import java.util.HashMap;
import java.util.Vector;

import utils.Util;
import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.jml.SET;
import bytecode.BCATHROW;
import bytecode.BCInstruction;
import bytecode.BCLoopEnd;
import bytecode.BCRET;
import bytecode.BCTypeRETURN;
import bytecode.ByteCode;
import bytecode.branch.BCGOTO;
import bytecode.branch.BCJSR;
import formula.Connector;
import formula.Formula;

/**
 * @author mpavlova
 *
 * a block is defined by the  rules:
 * 1. if it ends with a jump that jumps beckwards.
 * 
 * 2.1. it starts either with the first instruction of a bytecode
 * either of an instruction that is a target of a jump instruction.
 * 
 * 2.2. it ends with an instruction that is either a goto, athrow, ret or return instruction
 */
public class Block implements ByteCode {

	private BCInstruction[] bytecode;

	/**
	 * position in the bytecode at which is the first instruction of the block
	 */
	private int first;

	/**
	 * position in the bytecode at which is the last instruction of the block
	 */
	private int last;

	private Block targetSeqBlock;
	private Vector targeterBlocks;

	//not good
	Vector wps;
	public Block() {
	}

	public Block(int _first, int _last, BCInstruction[] _bytecode) {
		setFirst(_first);
		setLast(_last);
		bytecode = _bytecode;
	}

	protected void setLast(int _last) {
		last = _last;
	}

	protected void setFirst(int _first) {
		first = _first;
	}

	public BCInstruction getFirst() {
		BCInstruction firstInstr =
			Util.getBCInstructionAtPosition(bytecode, first);
		return firstInstr;
	}

	public BCInstruction getLast() {
		BCInstruction lastInstr =
			Util.getBCInstructionAtPosition(bytecode, last);
		return lastInstr;
	}

	/* calculates the wp of the block starting at the penultimate instruction 
	 * @see bytecode.ByteCode#wp(formula.Formula)
	 */
	public Formula wp(Formula _np, ExsuresTable _exc_Postcondition) {
		if (getLast() == getFirst()) {
			return _np;
		}
		BCInstruction _instr = getLast().getPrev();

		while (true) {
			if (_instr == null) {
				return _np;
			}
			
			_np = _instr.wp(_np, _exc_Postcondition);
			SET[] assignModelVars = _instr.getAssignToModel();
			
			// making the necessary substitutions for any assignments that appear in the "set" of this instruction 
			if (assignModelVars != null) {
				for (int i = 0; i < assignModelVars.length ; i++ ) {
					Expression model = assignModelVars[i].getSubExpressions()[0];
					Expression assignToModel = assignModelVars[i].getSubExpressions()[1];
					_np.substitute(model, assignToModel.copy());
				}
			}
			
			Formula assertion = _instr.getAssert();
			if (assertion != null) {
				_np = Formula.getFormula(_np, assertion, Connector.AND);
			}
			Util.dump(" wp instr :  " + _instr + "  = " + _np);
			BCInstruction first = getFirst();
			if (_instr.equals(first)) {
				break;
			}
			_instr = _instr.getPrev();
		}
		if (getTargeterBlocks() == null ) {
			if (wps == null) {
				wps = new Vector( );
			}
			wps.add(_np);
		}
		return _np;
	}

	/* (non-Javadoc)
	 * @see bytecode.EndBlockInstruction#calculateRecursively(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public void calculateRecursively(
		Formula _normalPostcondition,
		ExsuresTable _exc_postcondition) {
		BCInstruction last = getLast();
		/*Formula _np = (Formula)_normalPostcondition.copy();*/
		Formula wp = last.wp(_normalPostcondition, _exc_postcondition);
		
		Util.dump(
			" wp instr : "
				+ last
				+ "  = "
				+ wp);
		Formula wpBlock = wp(wp, _exc_postcondition);
//		Util.dump("***********************************************************");
		_calculateRecursively(wpBlock, _exc_postcondition);
	}

	/**
	 * invokes  calculateRecursively method of every block that is targeting to this block
	 * @param _normal_postcondition
	 * @param _exc_postcondition
	 */
	protected void _calculateRecursively(
		Formula _normal_postcondition,
		ExsuresTable _exc_postcondition) {
		if (targeterBlocks == null) {
			/*Util.dump("------------- This path ended -------------------");*/
			return;
		}
		for (int k = 0; k < targeterBlocks.size(); k++) {
			Formula wpCopy = (Formula)_normal_postcondition.copy();
			if (targeterBlocks.elementAt(k) instanceof BranchingBlock) {
				BranchingBlock branchingBlock =
					(BranchingBlock) targeterBlocks.elementAt(k);
				Block targetBlock = branchingBlock.getBranchTargetBlock();
				if (this == targetBlock) {
					//						Util.dump("************ wp for branch case");
					branchingBlock.calculateBranchRecursively(
						wpCopy,
						_exc_postcondition);
				} else {
					//						Util.dump("************ wp for straight case");
					branchingBlock.calculateRecursively(
						wpCopy,
						_exc_postcondition);
				}
				continue;
			}
			Block block = ((Block) targeterBlocks.elementAt(k));
			block.calculateRecursively(wpCopy, _exc_postcondition);
		}
	}

	public String toString() {
		return " Block( fst: " + " " + getFirst().toString() + "\\ end:  " + getLast().toString()+ " )" ;		
	}

	public boolean equals(Block _block) {
		if ((getFirst().equals(_block.getFirst()))
			&& (getLast().equals(_block.getLast()))) {
			return true;
		}
		return false;
	}
	/**
	 * @return
	 */
	public Vector getTargeterBlocks() {
		return targeterBlocks;
	}

	/**
		 * called by Trace to set the blocks that are may be executed after this one
		 * @param blocks
		 */
	public void setTargetBlocks(HashMap blocks) {
		BCInstruction last = getLast();
		if (last instanceof BCJSR) {
			BCInstruction targetInstr = ((BCJSR) last).getNext();
			Block b =
				(Block) blocks.get(new Integer(targetInstr.getPosition()));
			setTargetSeqBlock(b);
		} else if (last instanceof BCGOTO) {
			BCInstruction targetInstr = ((BCGOTO) last).getTarget();
			Block b =
				(Block) blocks.get(new Integer(targetInstr.getPosition()));
			setTargetSeqBlock(b);

		} else if (last instanceof BCRET) {
			return;
		} else if (last instanceof BCTypeRETURN) {
			return;
		} else if (last instanceof BCATHROW) {
			return;
		} else if (last instanceof BCLoopEnd) {
			return;
		} // in case that last is not a jump, ret, return then the block ending with last will
		 // be 
		else if ((last.getNext() != null ) && ( last.getNext().getTargeters() != null)) {
			Block b =
				(Block) blocks.get(new Integer(last.getNext().getPosition()));
			setTargetSeqBlock(b);
		}
	}

	/**
	 * called by Trace to set the blocks that may be executed before this one
	 * @param blocks
	 */
	public void setTargeterBlocks(HashMap blocks, Trace trace) {
		Block targeterBlock = null;
		BCInstruction first = getFirst();
		BCInstruction prev = first.getPrev();
		// if there starts a block where the instruction before is not a jump, return , ret , jsr
		if ((prev != null)
			&& !(prev instanceof BCRET)
			&& !(prev instanceof BCTypeRETURN)
			/*&& !(prev instanceof BCJSR)*/
			&& !(prev instanceof BCGOTO)
			&& !(prev instanceof BCATHROW) 
			&& !(prev instanceof BCLoopEnd)) {
			//not good
			if ((targeterBlock = trace.getBlockEndAt(prev, blocks)) != null) {
				if (targeterBlocks == null) {
					targeterBlocks = new Vector();
				}
				targeterBlocks.add(targeterBlock);
			}
		}

		if (first.getTargeters() == null) {
			return;
		}
		Enumeration targeters = first.getTargeters().elements();
		BCInstruction targeter = null;

		while (targeters.hasMoreElements()) {
			targeter = (BCInstruction) targeters.nextElement();

			if ((targeterBlock = trace.getBlockEndAt(targeter, blocks)) != null) {
				if (targeterBlocks == null) {
					targeterBlocks = new Vector();
				}
				targeterBlocks.add(targeterBlock);
			}
		}

	}

	/**
	 * Returns the targetBlocks.
	 * @return Vector
	 */
	public Block getTargetSeqBlock() {
		return targetSeqBlock;
	}

	/**
	 * Sets the targetBlock.
	 * @param targetBlock The targetBlock to set
	 */
	public void setTargetSeqBlock(Block targetBlock) {
		this.targetSeqBlock = targetBlock;
	}

//	/**
//	 * @param block
//	 * used only when if this is a loop end block
//	 */
//	public void removeTargeterBlock(Block block) {
//		if (targeterBlocks == null) {
//			return;
//		}
//		targeterBlocks.remove(block);
//	}

}
