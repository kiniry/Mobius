/*
 * Created on Mar 2, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.block;

import java.util.Enumeration;
import java.util.Vector;

import formula.Formula;
import formula.atomic.Predicate;

import bcclass.attributes.ExceptionHandler;
import bcclass.attributes.ExsuresTable;

import bytecode.*;

import bytecode.BCInstruction;
import bytecode.branch.*;
import utils.Util;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Trace {
	//private BCInstruction[] bytecode;

	private Vector blocks;

	private Block entryBlock;

	public Trace(BCInstruction[] _bytecode, ExceptionHandler[] _excHandlers) {
		//bytecode = _bytecode;
		initGraph(_bytecode);

		//sets the blocks that are targets 
		setTargetBlocks(_bytecode);

		//sets the exception handlers for instructions that may throw exceptions
		setExceptionHandleBlocks(_bytecode, _excHandlers);

		dumpBlocks();
	}

	/**
	 * @param bytecode
	 * @param _excHandlers
	 */
	private void setExceptionHandleBlocks(
		BCInstruction[] bytecode,
		ExceptionHandler[] _excHandlers) {
		for (int i = 0; i < bytecode.length; i++) {
			BCInstruction instruction = bytecode[i];
			if (instruction instanceof BCExceptionThrower) {
				BCExceptionThrower excThro = (BCExceptionThrower) bytecode[i];
				excThro.setExceptionTargetBlocks(bytecode, _excHandlers, this);
			}
		}
	}

	/**
	 * 
	 */
	void dumpBlocks() {
		if (blocks == null) {
			Util.dump("not implemented");
			return;
		}
		Util.dump(" **************** in dumpBlocks ************");
		for (int i = 0; i < blocks.size(); i++) {
			Block b = (Block) blocks.elementAt(i);
			b.dump("");
		}
	}

	/**
	 * set the entry blocks for this method 
	 * (they may be several , for example  there may be 
	 * a loop in the beginning of the method - (2 entry blocks - the loop one and the straight one )) 
	 *
	 */
	public void initGraph(BCInstruction[] bytecode) {
		BCInstruction _i = bytecode[0];
		while (_i != null) {
			if ((_i instanceof BCConditionalBranch)
				|| (_i instanceof BCGOTO)) {
				int targetPosition =
					((BCJumpInstruction) _i).getTargetPosition();
				if (targetPosition == bytecode[0].getPosition()) {
					entryBlock =
						new LoopBlock(bytecode[0], (BCJumpInstruction) _i);
					addBlock(entryBlock);
					return;
				}
			}

			if (_i instanceof EndBlockInstruction) {
				entryBlock = new Block(bytecode[0], _i);
				addBlock(entryBlock);
				/*Util.dump("entry block");
				_b.dump("");*/
				return;
			}
			_i = _i.getNext();
		}
	}

	public void setTargetBlocks(BCInstruction[] code) {
		for (int i = 0; i < code.length; i++) {
			if (code[i] instanceof BCJumpInstruction) {
				/*Util.dump( " targets for " +  code[i].getInstructionHandle().toString() );*/
				setTargetBlock((BCJumpInstruction) code[i]);

				//((BCJumpInstruction)code[i]).getTargetBlock().dump("");
				/*Util.dump("===============================");*/
			}
		}
	}

	/**
	 * gets the block starting at _first and ending at _last from the blocks that are already created
	 * @param _first 
	 * @param _last
	 * @return
	 */
	public Block getBlockStartingAtEndingAt(
		BCInstruction _first,
		BCInstruction _last) {
		if (blocks == null) {
			return null;
		}
		if (blocks.size() == 0) {
			return null;
		}
		Block _b = null;
		for (int i = 0; i < blocks.size(); i++) {
			_b = (Block) (blocks.elementAt(i));

			BCInstruction first = _b.getFirst();
			BCInstruction last = _b.getLast();
			if ((first.equals(_first)) && (last.equals(_last))) {
				return _b;
			}
		}
		return null;
	}

	public void addBlock(Block _b) {
		if (blocks == null) {
			blocks = new Vector();
		}
		blocks.add(_b);
	}

	public void dump() {
		Enumeration en = blocks.elements();
		Block b = null;
		while (en.hasMoreElements()) {
			b = (Block) (en.nextElement());
			b.dump("");
		}
	}

	public Vector getEntryBlocks() {
		return blocks;
	}

	/**
	 * this method is called by setTargetBlocks once the target instruction is set It
	 * sets the target blocks for this jump instruction
	 *  
	 */
	public void setTargetBlock(BCJumpInstruction bcjumpInstruction) {
		Block _b = null;
		if (bcjumpInstruction.getTargetPosition()
			<= bcjumpInstruction.getPosition()) {
			if ((_b =
				getBlockStartingAtEndingAt(
					bcjumpInstruction.getTarget(),
					bcjumpInstruction))
				== null) {
				_b =
					new LoopBlock(
						bcjumpInstruction.getTarget(),
						bcjumpInstruction);
				addBlock(_b);
			}
			if (_b != null) {
				bcjumpInstruction.setTargetBlock(_b);
				return;
			}
		}
		BCInstruction _last = bcjumpInstruction.getTarget();
		while (_last != null) {
			if (_last instanceof EndBlockInstruction) {
				if ((_b =
					getBlockStartingAtEndingAt(
						bcjumpInstruction.getTarget(),
						_last))
					== null) {
					_b = new Block(bcjumpInstruction.getTarget(), _last);
					addBlock(_b);
				}
				bcjumpInstruction.setTargetBlock(_b);
//				((EndBlockInstruction) _last).setBlock(_b);
				break;
			}
			_last = _last.getNext();
		}
	}

	public Formula wp(Formula postcondition, ExsuresTable exsures) {
		if ((blocks == null) || (blocks.size() == 0)) {
			return Predicate._TRUE;
		}
		Formula wp;
		for (int i = 0; i < blocks.size(); i++) {
			Block b = (Block) (blocks.elementAt(i));
			if (b.getLast() instanceof BCTypeRETURN) {
				EndBlockInstruction endBlock = (BCTypeRETURN) b.getLast();
				endBlock.calculateRecursively(postcondition, exsures);
			}
		}
		return entryBlock.getWp();
	}

}
