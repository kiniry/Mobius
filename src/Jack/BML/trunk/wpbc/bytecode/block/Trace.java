/*
 * Created on Mar 2, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.block;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Vector;
import formula.Formula;
import bcclass.BCMethod;
import bcclass.attributes.ExceptionHandler;
import bcclass.attributes.ExsuresTable;
import bcclass.attributes.SpecificationCase;
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
	/* private HashMap blocks; */
	private HashMap normalComponent;
	private HashMap excHandlerComponents;
	private BCMethod method;
	private Block entryBlock;
	private Formula postcondition;
	private ExsuresTable exsTable;
	// contains the following instructions :
	// the entry point, the start point for every exception handle
	private Vector entryPoints;
	public Trace(BCMethod _method) {
		method = _method;
		TraceUtils.initLoopInstructions(method.getBytecode()[0], method
				.getBytecode());
		/* Util.dump("after LOOPS"); */
		TraceUtils.initEntryPoints(method);
		/* Util.dump("after ENTRYPOINTS"); */
		initNormalComponent();
		Util
				.dump(" ============INITNORMALCOMPONENT=============================");
		dumpNormalComponentBlocks();
		Util
				.dump(" ============INITNORMALCOMPONENT=============================");
		initExceptionHandlerComponents();
		Util
				.dump(" ============INITEXCEPTIONALCOMPONENT=============================");
		dumpExcComponentBlocks();
		Util
				.dump(" ============INITEXCEPTIONALCOMPONENT=============================");
		setBlockRelation();
		test();
		//		TraceUtils.initExceptionandlerStartInstructions(method);
		initTraceForExcThrower();
	}
	void test() {
		Block b = getBlockAt(32, normalComponent);
	}
	private void setBlockRelation() {
		// in case this is an interface method
		/*
		 * if (blocks == null) { return;
		 */
		if (normalComponent != null) {
			Iterator iter = normalComponent.values().iterator();
			Block b = null;
			while (iter.hasNext()) {
				b = (Block) iter.next();
				b.setTargetBlocks(normalComponent);
				b.setTargeterBlocks(normalComponent, this);
			}
		}
		if (excHandlerComponents != null) {
			Iterator iterExc = excHandlerComponents.values().iterator();
			Iterator excHandCompIt = null;
			HashMap excHandComp = null;
			Block b = null;
			while (iterExc.hasNext()) {
				excHandComp = (HashMap) iterExc.next();
				excHandCompIt = excHandComp.values().iterator();
				while (excHandCompIt.hasNext()) {
					b = (Block) excHandCompIt.next();
					b.setTargetBlocks(excHandComp);
					b.setTargeterBlocks(excHandComp, this);
				}
			}
		}
	}
	private void initEntryBlock(Block b) {
		entryBlock = b;
	}
	/**
	 * initialises every strongly connected part of the exec graph that
	 * represents an exception handler.
	 */
	private void initExceptionHandlerComponents() {
		ExceptionHandler[] excHandlers = method.getExceptionHandlers();
		if (excHandlers == null) {
			return;
		}
		excHandlerComponents = new HashMap();
		for (int i = 0; i < excHandlers.length; i++) {
			int excHandlerStart = excHandlers[i].getHandlerPC();
			BCInstruction excHandlerStartInstr = Util
					.getBCInstructionAtPosition(method.getBytecode(),
							excHandlerStart);
			Block b = initBlock(excHandlerStartInstr);
			HashMap excHandlerComp = new HashMap();
			addToComponent(b, excHandlerComp);
			excHandlerComponents.put(new Integer(excHandlerStart),
					excHandlerComp);
		}
	}
	/**
	 * initialises the strongly connected part of the exec graph that
	 * represents the normal execution of the program starting from the entry
	 * point
	 */
	private void initNormalComponent() {
		BCInstruction entryPoint = method.getBytecode()[0];
		Block b = initBlock(entryPoint);;
		initEntryBlock(b);
		normalComponent = new HashMap();
		addToComponent(b, normalComponent);
	}
	
	private void addToComponent(Block b, HashMap component) {
		Block _bIsIn = getBlockAt(b.getFirst().getPosition() , component);
		if ( _bIsIn == null) {
			component.put(new Integer(b.getFirst().getPosition()), b);
		}
		BCInstruction last = b.getLast();
		/* Util.dump("ADD ToComponent : " + last.toString()); */
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
				BCInstruction wrappedInstr = ((BCLoopEnd) last)
						.getWrappedInstruction();
				if (!(wrappedInstr instanceof BCJumpInstruction)) {
					return;
				}
				BCJumpInstruction jumpInstr = (BCJumpInstruction) wrappedInstr;
				if (jumpInstr.getTarget() == null) {
					return;
				}
				Block _b = initBlock(jumpInstr.getTarget());
				addToComponent(_b, component);
				return;
			}
			Block _b = initBlock(next);
			addToComponent(_b, component);
			return;
		}
		if (last instanceof BCConditionalBranch) {
			BCConditionalBranch cBranch = (BCConditionalBranch) last;
			Block _b0 = initBlock(cBranch.getNext());
			addToComponent(_b0, component);
			Block _b1 = initBlock(cBranch.getTarget());
			addToComponent(_b1, component);
			return;
		}
		if (last instanceof BCUnconditionalBranch) {
			BCUnconditionalBranch cBranch = (BCUnconditionalBranch) last;
			Block _b = initBlock(cBranch.getTarget());
			addToComponent(_b, component);
			return;
		}
		BCInstruction next = last.getNext();
		Block _b = initBlock(next);
		addToComponent(_b, component);
	}
	public ExceptionHandler getExceptionHandlerForExceptionThrownAt(
			JavaObjectType excThrownType, int excThrownAtPos) {
		ExceptionHandler excH = null;
		ExceptionHandler[] excHandlers = method.getExceptionHandlers();
		// find the first top -bottom handler for the exception excThrownType
		for (int i = 0; i < excHandlers.length; i++) {
			//if the handle i doesnot handle the exception k
			if (!JavaObjectType.subType(excThrownType, excHandlers[i]
					.getCatchType())) {
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
	 * 
	 * @param excThrownType
	 * @param excThrownAtPos
	 * @return Formula
	 */
	public Formula getWpForExcThrownAt(JavaObjectType excThrownType,
			int excThrownAtPos) {
		Formula wp = null;
		ExceptionHandler excH = getExceptionHandlerForExceptionThrownAt(
				excThrownType, excThrownAtPos);
		// if there is no then
		// take the exceptional postcondition from the exsures table
		if (excH == null) {
			wp = method.getExsuresForException(excThrownType);
			return wp;
		}
		int handlerStart = excH.getHandlerPC();
		// get the component that represents the exception handle
		HashMap excHandlerBlocks = (HashMap) excHandlerComponents
				.get(new Integer(handlerStart));
		//this implementation is very bad , must be a class which wraps
		//the entry points and access the wp for an exception handler like
		// this
		wp((Formula) postcondition.copy(), exsTable, excHandlerBlocks);
		EntryPoint excHandlerEntryPoint = (EntryPoint) Util
				.getBCInstructionAtPosition(method.getBytecode(), handlerStart);
		wp = excHandlerEntryPoint.getWp();
		return wp;
	}
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
/*		if (blocks == null) {
			Util.dump("abstract method");
			return;
		}
		Util.dump(" **************** in dumpBlocks ************");
		Iterator iter = blocks.values().iterator();
		while (iter.hasNext()) {
			Block b = (Block) iter.next();
			Util.dump(b.toString());
		}*/
	}
	/**
	 *  
	 */
	void dumpNormalComponentBlocks() {
		if (normalComponent == null) {
			Util.dump("abstract method");
			return;
		}
		Iterator iter = normalComponent.values().iterator();
		while (iter.hasNext()) {
			Block b = (Block) iter.next();
			Util.dump(b.toString());
		}
	}
	/**
	 *  
	 */
	void dumpExcComponentBlocks() {
		if (excHandlerComponents == null) {
			Util.dump("no exception handlers");
			return;
		}
		Iterator iter = excHandlerComponents.values().iterator();
		while (iter.hasNext()) {
			HashMap map = (HashMap) iter.next();
			Iterator excComp = map.values().iterator();
			Util.dump("excComp ");
			while (excComp.hasNext()) {
				Block b = (Block) excComp.next();
				Util.dump(b.toString());
			}
		}
	}
	/**
	 * searches in the map of basic blocks if there is a block ending with the
	 * _first instruction
	 * 
	 * @param _first
	 * @param _blocks - a hashmap in which a block starting at position first is looked for
	 * @return
	 */
	public Block getBlockAt(int _firstPos, HashMap blocks) {
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
	 * searches in the map of basic blocks if there is a block ending with the
	 * _last instruction
	 * 
	 * @param _last
	 * @return null if there is no such a block
	 */
	public Block getBlockEndAt(BCInstruction _last, HashMap blocks) {
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
	/**
	 * 
	 * @param start
	 * @param blocks - a component where a block starting at start position will be added
	 * @return
	 *//*
	public Block addBlock(BCInstruction start, HashMap blocks) {
		if (blocks == null) {
			blocks = new HashMap();
		}
		Block block = null;
		if ((block = getBlockAt(start.getPosition(), blocks)) != null) {
			return block;
		}
		block = initBlock(start, method.getBytecode());
		blocks.put(new Integer(start.getPosition()), block);
		return block;
	}*/
	private Block initBlock(BCInstruction first) {
		BCInstruction[] instrs = method.getBytecode();
		BCInstruction next = first;
		/*
		 * if (first instanceof BCLoopEnd) { Util.dump("loopEnd : beginning " );
		 * Util.dump(first);
		 */
		while (true) {
			/* Util.dump("next " + next.toString()); */
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
		if ((next instanceof BCLoopEnd)
				&& (((BCLoopEnd) next)).getWrappedInstruction() instanceof BCConditionalBranch) {
			Block block = new BranchingBlock(first.getPosition(), next
					.getPosition(), instrs);
			return block;
		}
		if (next instanceof BCConditionalBranch) {
			Block block = new BranchingBlock(first.getPosition(),
					((BCConditionalBranch) next).getPosition(), instrs);
			return block;
		}
		Block block = new Block(first.getPosition(), next.getPosition(), instrs);
		return block;
	}
	public void dump() {
		Iterator en = normalComponent.values().iterator();
		Block b = null;
		while (en.hasNext()) {
			b = (Block) (en.next());
			Util.dump(b.toString());
		}
	}
	/**
	 * initialises wp for the sub tree of every exception handler
	 * 
	 * @param postcondition
	 * @param exsures
	 */
	private void initWpExcHandlers(Formula postcondition, ExsuresTable exsures) {
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
	public void wp(Formula _n_post, ExsuresTable _exsTable) {
		postcondition = _n_post;
		exsTable = _exsTable;
		wp(postcondition, exsTable, normalComponent);
	}
	private void wp(Formula postcondition, ExsuresTable exsures,
			HashMap component) {
		if ((component == null) || (component.size() == 0)) {
			return;
		}
		// initialises the wp for the instructions that are in the
		// commented 30-07
		// initWpExcHandlers(postcondition, exsures);
		Formula wp;
		Iterator iter = component.values().iterator();
		while (iter.hasNext()) {
			Block b = (Block) (iter.next());
			if (b.getLast() instanceof BCTypeRETURN) {
				//				EndBlockInstruction endBlock = (BCTypeRETURN) b.getLast();
				b.calculateRecursively((Formula) postcondition.copy(), exsures);
				
			} else if (b.getLast() instanceof BCLoopEnd) {
				BCLoopEnd loopEnd = (BCLoopEnd) b.getLast();
				Formula loopInvariant = (Formula) loopEnd.getInvariant().copy();
				b.calculateRecursively(loopInvariant, exsures);
			} else if (b.getLast() instanceof BCATHROW) {
				b.calculateRecursively((Formula) postcondition.copy(), exsures);
			}
		}
	}
	/**
	 * @return
	 */
	public BCMethod getMethod() {
		return method;
	}
	/**
	 * @return Returns the exsTable.
	 */
	public ExsuresTable getExsTable() {
		return exsTable;
	}
	/**
	 * @return
	 */
	public Vector getWP() {
		Vector f = ((EntryPoint) entryBlock.getFirst()).getWps();
		return f;
	}
	public void initWp() {
		BCInstruction[] instrs = getMethod().getBytecode();
		for (int i = 0; i < instrs.length; i++) {
			if (instrs[i] instanceof EntryPoint) {
				((EntryPoint) instrs[i]).initWP();
			}
		}
	}
}
