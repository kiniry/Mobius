/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.block;

import java.util.Vector;

import bcclass.attributes.ExsuresTable;
import bytecode.BCInstruction;
import bytecode.ByteCode;
import bytecode.EndBlockInstruction;
import bytecode.branch.BCConditionalBranch;

import utils.Util;

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
	private BCInstruction first;
	private BCInstruction last;

	//protected Vector next;
	protected Vector entryBlocks;

	private Formula postcondition;

	public Block() {
	}

	public Block(BCInstruction _first, BCInstruction _last) {
		first = _first;
		last = _last;
		if (last instanceof EndBlockInstruction) {
			((EndBlockInstruction) last).setBlock(this);
		}
	}

	public BCInstruction getFirst() {
		return first;
	}

	public BCInstruction getLast() {
		return last;
	}

	public void setPostcondition(Formula _postcondition) {
		postcondition = _postcondition;
	}

	public Formula getPostcondition() {
		return postcondition;
	}

	//	/**
	//	 * 
	//	 * @author mpavlova
	//	 * deprecated
	//	 * To change the template for this generated type comment go to
	//	 * Window>Preferences>Java>Code Generation>Code and Comments
	//	 */
	//	public void setNext(Vector _next ) {
	//		next = _next;
	//	} 

	/**
	 * 
	 * @author mpavlova
	 * deprecated
	 * To change the template for this generated type comment go to
	 * Window>Preferences>Java>Code Generation>Code and Comments
	 */
	public void addEntryBlocks(Block _prev) {
		if (entryBlocks == null) {
			entryBlocks = new Vector();
		}
		entryBlocks.add(_prev);
	}

	/**
	 * 
	 * @author mpavlova
	 * deprecated
	 * To change the template for this generated type comment go to
	 * Window>Preferences>Java>Code Generation>Code and Comments
	 */
	public Vector getEntryBlocks() {
		return entryBlocks;
	}

	//	/**
	//	 * returns the calculated wp for the block
	//	 * @return <code>wp </code>
	//	 */
	//	public Formula getWp() {
	//		return wp;
	//	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {

		Util.dump(
			"***********************************************************");
		Util.dump("wp for ");
		dump("");
		//wps = new Vector();
		BCInstruction _instr = last;
		Formula _np = _normal_Postcondition;

		while (true) {
			
			_np = _instr.wp(_np, _exc_Postcondition);
			Util.dump( " wp for instr " + _instr.getInstructionHandle().getInstruction() + "  = "  + _np) ;
			if (_instr.equals(first)) {
				break;
			}
			_instr = _instr.getPrev();
		}

		Util.dump(_np.toString());
		Util.dump(
			"***********************************************************");
		return _np;
	}

	/* (non-Javadoc)
	 * @see bytecode.EndBlockInstruction#calculateRecursively(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public Formula calculateRecursively(
		Formula _normal_postcondition,
		ExsuresTable _exs_postcondition) {
		Formula wp = wp(_normal_postcondition, _exs_postcondition);
		Vector targeters = first.getTargeters();
		if (targeters == null) {

			return wp;
		}
		for (int k = 0; k < targeters.size(); k++) {

			// in case there is a previous block then calculate the wp upon the wp of this block
			if (targeters.elementAt(k) instanceof EndBlockInstruction) {
				(
					(EndBlockInstruction) targeters.elementAt(
						k)).calculateRecursively(
					wp,
					_exs_postcondition);
			} else if (targeters.elementAt(k) instanceof BCConditionalBranch) {
				// else if it is a block branch then give it to  the instruction that is branching on this block
				//				( (BCConditionalBranch) targeters.elementAt(k) ).setBranchWP( wp);
				((BCConditionalBranch) targeters.elementAt(k)).wpBranch(
					wp,
					_exs_postcondition);
			}
		}
		return wp;
	}

	public void dump(String _offset) {
		if (Util.DUMP) {

			String offset = "     ";
			System.out.println(_offset + "Block( ");
			System.out.println(
				_offset
					+ offset
					+ "fst: "
					+ " "
					+ first.getPosition()
					+ " "
					+ first.getInstructionHandle().getInstruction().toString());

			System.out.println(
				_offset
					+ offset
					+ "end: "
					+ last.getPosition()
					+ " "
					+ last.getInstructionHandle().getInstruction().toString());
			System.out.println(_offset + ")");

			BCInstruction _i = first;
		}
	}

	public boolean equals(Block _block) {
		if ((first.equals(_block.getFirst()))
			&& (last.equals(_block.getLast()))) {
			return true;
		}
		return false;
	}
}
