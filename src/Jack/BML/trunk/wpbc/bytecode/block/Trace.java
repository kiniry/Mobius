/*
 * Created on Mar 2, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.block;

import java.util.HashMap;
import java.util.Iterator;

import formula.Formula;
import formula.atomic.Predicate;

import bcclass.BCMethod;
import bcclass.attributes.ExceptionHandler;
import bcclass.attributes.ExsuresTable;
import bcexpression.javatype.JavaObjectType;

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

	private HashMap blocks;

	private HashMap normalComponent;
	private HashMap excHandlerComponents;

	private BCMethod method;
	private Block entryBlock;

	public Trace(BCMethod _method) {
		method = _method;
		TraceUtils.initLoopInstructions(method.getBytecode()[0], method.getBytecode());
		Util.dump("after LOOPS");
		TraceUtils.initEntryPoints(method);
		Util.dump("after ENTRYPOINTS");
		initNormalComponent();
		Util.dump("after INITNORMALCOMPONENT");
		
		initExceptionHandlerComponents();
		setBlockRelation();
	
		dumpBlocks();
		//		TraceUtils.initExceptionandlerStartInstructions(method);
		initTraceForExcThrower();
	}

	private void setBlockRelation() {
		// in case this is an interface method
		if (blocks == null) {
			return;
		}
		Iterator iter = blocks.values().iterator();
		Block b = null;
		while (iter.hasNext()) {
			b = (Block) iter.next();
			b.setTargetBlocks(blocks);
			b.setTargeterBlocks(blocks, this);
		}
	}

	private void initEntryBlock(Block b) {
		entryBlock = b;
	}

	/**
	 * initialises every strongly connected part of the 
	 * exec graph that represents an exception handler.
	 */
	private void initExceptionHandlerComponents() {
		ExceptionHandler[] excHandlers = method.getExceptionHandlers();
		if (excHandlers == null) {
			return;
		}
		excHandlerComponents = new HashMap();
		for (int i = 0; i < excHandlers.length;i++) {
			int excHandlerStart = excHandlers[i].getHandlerPC();
			BCInstruction excHandlerStartInstr = Util.getBCInstructionAtPosition(method.getBytecode(), excHandlerStart);
			Block b = addBlock(excHandlerStartInstr);
			HashMap excHandlerComp = new HashMap();
			addToComponent(b, excHandlerComp);
			excHandlerComponents.put(new Integer( excHandlerStart), excHandlerComp);
		}
	}
	
	/**
	 * initialises the strongly connected part of the 
	 * exec graph that represents the normal execution of the program starting from the entry point
	 */
	private void initNormalComponent() {
		BCInstruction entryPoint = method.getBytecode()[0];
		Block b = addBlock(entryPoint);
		initEntryBlock(b);
		normalComponent = new HashMap();
		addToComponent(b, normalComponent);
	}

	private void addToComponent(Block b, HashMap normalComponent) {
		
		normalComponent.put(new Integer(b.getFirst().getPosition()), b);
		BCInstruction last = b.getLast();
		Util.dump("ADD ToComponent : " +  last.toString());
		if (last instanceof BCTypeRETURN) {
			return;
		}
		if (last instanceof BCRET) {
			return;
		}
		if (last instanceof BCATHROW) {
			return;
		}
		if (last instanceof BCLoopEnd) {
			BCInstruction next = last.getNext();
			if (next == null) {
				BCInstruction wrappedInstr =
					((BCLoopEnd) last).getWrappedInstruction();
				if (!(wrappedInstr instanceof BCJumpInstruction)) {
					return;
				}
				BCJumpInstruction jumpInstr = (BCJumpInstruction) wrappedInstr;
				if (jumpInstr.getTarget() == null) {
					return;
				}
				Block _b = addBlock(jumpInstr.getTarget());
				addToComponent(_b, normalComponent);
				return;
			}
			Block _b = addBlock(next);
			addToComponent(_b, normalComponent);
			return;
		}
		if (last instanceof BCConditionalBranch) {
			BCConditionalBranch cBranch = (BCConditionalBranch) last;
			Block _b0 = addBlock(cBranch.getNext());
			addToComponent(_b0, normalComponent);
			Block _b1 = addBlock(cBranch.getTarget());
			addToComponent(_b1, normalComponent);
			return;
		}
		if (last instanceof BCUnconditionalBranch) {
			BCUnconditionalBranch cBranch = (BCUnconditionalBranch) last;
			Block _b = addBlock(cBranch.getTarget());
			addToComponent(_b, normalComponent);
			return;
		}
		BCInstruction next = last.getNext();
		Block _b = addBlock(next);
		addToComponent(_b, normalComponent);
	}
	
	public ExceptionHandler getExceptionHandlerForExceptionThrownAt(
		JavaObjectType excThrownType,
		int excThrownAtPos) {
		ExceptionHandler excH = null;

		ExceptionHandler[] excHandlers = method.getExceptionHandlers();
		// find a handler for the exception excThrownType
		for (int i = 0; i < excHandlers.length; i++) {
			//if the handle i doesnot handle the exception k
			if (!JavaObjectType
				.subType(excThrownType, excHandlers[i].getCatchType())) {
				continue;
			}
			if ((excHandlers[i].getStartPC() > excThrownAtPos)
				|| (excThrownAtPos > excHandlers[i].getEndPC())) {
				continue;
			}
			excH = excHandlers[i];
			break;
		}
		return excH;
	}

	/**
	 * gets for the exception type excThrownType an exception handle
	 * 
	 * and finds the wp for
	 * @param excThrownType
	 * @param excThrownAtPos
	 * @return Formula
	 */
	public Formula getWpForExcThrownAt(
		JavaObjectType excThrownType,
		int excThrownAtPos) {
		Formula wp = null;
		ExceptionHandler excH =
			getExceptionHandlerForExceptionThrownAt(
				excThrownType,
				excThrownAtPos);

		// if there is no then
		// take the exceptional postcondition from the exsures table
		if (excH == null) {
			ExsuresTable exsuresTable = method.getExsures();
			if (exsuresTable == null) {
				return Predicate.TRUE;
			}
			wp =
				exsuresTable.getExcPostconditionFor(
					excThrownType.getSignature());
			return wp;
		}
		int handlerStart = excH.getHandlerPC();
		HashMap excHandlerBlocks = (HashMap)excHandlerComponents.get( new Integer(handlerStart));
		//this implementation is very bad , must be  a class which wraps the entry points and access the wp for an exception handler like this
		wp(method.getPostcondition().copy(),method.getExsures(), excHandlerBlocks );
		EntryPoint excHandlerEntryPoint = (EntryPoint)Util.getBCInstructionAtPosition(method.getBytecode(), handlerStart); 
		wp = excHandlerEntryPoint.getWp();
		return wp;
	}

//	/**
//	 * looks if at position i in the bytecode starts an exception handler 
//	 * Method isStartOfExcHandlerBlock.
//	 * @param i
//	 * @return boolean
//	 */
//	private boolean isStartOfExcHandlerBlock(int pos) {
//		ExceptionHandler[] excHandlers = method.getExceptionHandlers();
//		if (excHandlers == null) {
//			return false;
//		}
//		if (excHandlers.length == 0) {
//			return false;
//		}
//		int startExcHandlerPos;
//		for (int i = 0; i < excHandlers.length; i++) {
//			startExcHandlerPos = excHandlers[i].getHandlerPC();
//
//			if (startExcHandlerPos == pos) {
//				Util.dump("exc Handler START " + pos);
//				return true;
//			}
//		}
//		return false;
//	}

	/**
	 * @param bytecode
	 * @param _excHandlers
	 */
	private void initTraceForExcThrower() {
		BCInstruction[] bytecode = method.getBytecode();
		if (bytecode == null) {
			return;
		}
		for (int i = 0; i < bytecode.length; i++) {
			BCInstruction instruction = bytecode[i];
			if (instruction instanceof BCExceptionThrower) {
				BCExceptionThrower excThro = (BCExceptionThrower) bytecode[i];
				excThro.setTrace(this);
			}
		}
	}

	/**
	 * 
	 */
	void dumpBlocks() {
		if (blocks == null) {
			Util.dump("abstract method");
			return;
		}
		Util.dump(" **************** in dumpBlocks ************");
		Iterator iter = blocks.values().iterator();

		while (iter.hasNext()) {
			Block b = (Block) iter.next();

			b.dump("");
		}
	}

	/**
	 * searches in the map of basic blocks if there is a block ending with 
	 * the _first instruction
	 * @param _first
	 * @return
	 */
	public Block getBlockAt(int _firstPos) {
		if (blocks == null) {
			return null;
		}
		if (blocks.size() == 0) {
			return null;
		}
		Block b = (Block) blocks.get(new Integer(_firstPos));
		return b;
	}

	/**
	 * searches in the map of basic blocks if there is a block ending with 
	 * the _last instruction
	 * @param _last
	 * @return null if there is no such a block
	 */
	public Block getBlockEndAt(BCInstruction _last) {
		if (blocks == null) {
			return null;
		}
		if (blocks.size() == 0) {
			return null;
		}
		Iterator iter = blocks.values().iterator();
		Block b = null;
		while (iter.hasNext()) {
			b = (Block) iter.next();
			if (b.getLast() == _last) {
				return b;
			}
		}
		return null;
	}

	public Block addBlock(BCInstruction start) {
		if (blocks == null) {
			blocks = new HashMap();
		}
		Block block = null;
		if ((block = getBlockAt(start.getPosition())) != null) {
			return block;
		}
		block = initBlock(start, method.getBytecode());
		blocks.put(new Integer(start.getPosition()), block);
		return block;
	}

	private Block initBlock(BCInstruction first, BCInstruction[] instrs) {
		BCInstruction next = first;
		while (true) {
			BCInstruction nextOfNext = next.getNext();
			if ((nextOfNext != null) && (nextOfNext.getTargeters() != null)) {
				break;
			}
			if (next instanceof BCJSR) {
				break;
			}
			if (next instanceof BCConditionalBranch) {
				break;
			}
			if (next instanceof BCGOTO) {
				break;
			}
			if (next instanceof BCTypeRETURN) {
				break;
			}
			if (next instanceof BCRET) {
				break;
			}
			if (next instanceof BCATHROW) {
				break;
			}
			// inderted on 30/07
			if (next instanceof BCLoopEnd) {
				break;
			}
			next = next.getNext();
		}
		if ( (next instanceof BCLoopEnd)  && ( ((BCLoopEnd)next) ).getWrappedInstruction() instanceof BCConditionalBranch ) {
			Block block =
							new BranchingBlock(
								first.getPosition(),
								next.getPosition(),
								instrs);
						return block;
		}
		if (next instanceof BCConditionalBranch) {
			Block block =
				new BranchingBlock(
					first.getPosition(),
					((BCConditionalBranch) next).getPosition(),
					instrs);
			return block;
		}
		Block block =
			new Block(first.getPosition(), next.getPosition(), instrs);
		return block;
	}

	public void dump() {
		Iterator en = blocks.values().iterator();
		Block b = null;
		while (en.hasNext()) {
			b = (Block) (en.next());
			b.dump("");
		}
	}

	/**
	 * initialises wp for the sub tree of every exception handler  
	 * @param postcondition
	 * @param exsures
	 */
	private void initWpExcHandlers(
		Formula postcondition,
		ExsuresTable exsures) {
		BCInstruction[] instrs = method.getBytecode();
		for (int i = 0; i < instrs.length; i++) {
			//			if (instrs[i] instanceof ExceptionHandlerStartInstruction) {
			//				((ExceptionHandlerStartInstruction) instrs[i]).initExcWP(
			//					this,
			//					postcondition,
			//					exsures);
			//			}
		}
	}
	
	public void wp(Formula postcondition, ExsuresTable exsures) {
		wp(postcondition, exsures, normalComponent);
	}
	
	private void wp(Formula postcondition, ExsuresTable exsures, HashMap component) {
		if ((blocks == null) || (blocks.size() == 0)) {
			return;
		}
		// initialises the wp for the instructions that are in the 
		//commented 30-07
		//		initWpExcHandlers(postcondition, exsures);
		Formula wp;
		Iterator iter = component.values().iterator();
		while (iter.hasNext()) {
			Block b = (Block) (iter.next());
			if (b.getLast() instanceof BCTypeRETURN) {
				//				EndBlockInstruction endBlock = (BCTypeRETURN) b.getLast();
				b.calculateRecursively(postcondition.copy(), exsures);
			} else if (b.getLast() instanceof BCLoopEnd) {
				BCLoopEnd loopEnd = (BCLoopEnd) b.getLast();
				Formula loopInvariant = loopEnd.getInvariant().copy();
				b.calculateRecursively(loopInvariant, exsures);
			}
		}
	}
}
