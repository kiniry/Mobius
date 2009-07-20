/*
 * Created on Mar 2, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.block;

import java.util.Enumeration;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import bytecode_wp.bcclass.BCMethod;
import bytecode_wp.bcclass.attributes.ExceptionHandler;
import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.javatype.JavaObjectType;
import bytecode_wp.bytecode.BCATHROW;
import bytecode_wp.bytecode.BCExceptionThrower;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.bytecode.BCLoopEnd;
import bytecode_wp.bytecode.BCLoopStart;
import bytecode_wp.bytecode.BCRET;
import bytecode_wp.bytecode.BCTypeRETURN;
import bytecode_wp.bytecode.EntryPoint;
import bytecode_wp.bytecode.branch.BCConditionalBranch;
import bytecode_wp.bytecode.branch.BCGOTO;
import bytecode_wp.bytecode.branch.BCJSR;
import bytecode_wp.bytecode.branch.BCJumpInstruction;
import bytecode_wp.bytecode.branch.BCUnconditionalBranch;
import bytecode_wp.formula.Formula;
import bytecode_wp.utils.Util;
import bytecode_wp.vcg.VCGPath;
import bytecode_wp.vcg.VcType;

/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ControlFlowGraph {

	/*
	 * // this field stores all the created blocks // thus if in difefrent
	 * components - for example an exception handler and a // the normal
	 * execution trace have common blocks there will be only one object it
	 * private HashMap blocks;
	 */
	private HashMap normalComponent;

	private HashMap excHandlerComponents;

	private HashMap subroutines;

	private BCMethod method;

	private Block entryBlock;

/*	private VCGPath postcondition;*/

	private ExsuresTable exsTable;

	private Vector loopStarts;

	/*
	 * // contains the following instructions : // the entry point, the start
	 * point for every exception handle private Vector entryPoints;
	 */

	public ControlFlowGraph(BCMethod _method) throws IllegalLoopException {
		method = _method;
		BCInstruction[] bytecode = method.getBytecode();
		if (bytecode == null) {
			return;
		}
		loopStarts = new Vector();
		TraceUtils.initLoopInstructions(bytecode[0], method.getBytecode(),
				loopStarts);
		/* Util.dump("after LOOPS"); */
		TraceUtils.initEntryPoints(method);

		initNormalComponent();

		/*
		 * Util.dump("
		 * ============INITEXCEPTIONALCOMPONENT=============================");
		 */

		initExceptionHandlerComponents();
		/*
		 * dumpExcComponentBlocks(); Util.dump("
		 * ============END_INITEXCEPTIONALCOMPONENT=============================");
		 */

		/*
		 * Util.dump("
		 * ============INITSUBROUTINES=============================");
		 */

		dumpSubRoutineComponentBlocks();

		/*
		 * Util.dump("
		 * ============END_INITSUBROUTINES=============================");
		 */

		setBlockRelation();

		// TraceUtils.initExceptionandlerStartInstructions(method);
		initTraceForExcThrower();
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

		if (subroutines != null) {
			Iterator subRoutIter = subroutines.values().iterator();
			Iterator subRoutineIter = null;
			HashMap subRoutineComponent = null;
			Block b = null;
			while (subRoutIter.hasNext()) {
				subRoutineComponent = (HashMap) subRoutIter.next();
				subRoutineIter = subRoutineComponent.values().iterator();
				while (subRoutineIter.hasNext()) {
					b = (Block) subRoutineIter.next();
					b.setTargetBlocks(subRoutineComponent);
					b.setTargeterBlocks(subRoutineComponent, this);
				}
			}
		}

	}

	/**
	 * set as entry block the block that starts at the first instruction
	 * 
	 * @param b
	 */
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
			/* Block b = initBlock(excHandlerStartInstr); */
			HashMap excHandlerComp = new HashMap();
			addToComponent(excHandlerStartInstr, excHandlerComp);
			excHandlerComponents.put(new Integer(excHandlerStart),
					excHandlerComp);
		}
	}

	/**
	 * initialises the strongly connected part of the exec graph that models the
	 * normal execution of the program starting from the entry point
	 */
	private void initNormalComponent() {
		BCInstruction entryPoint = method.getBytecode()[0];
		normalComponent = new HashMap();
	
		addToComponent(entryPoint, normalComponent);
		Block entryBlock = (Block) normalComponent.get(new Integer(entryPoint
				.getPosition()));
		// initialise the entry block field
		initEntryBlock(entryBlock);
		dumpNormalComponentBlocks();

	}

	/**
	 * Well formed subroutines are those that if we have i: jsr k then the
	 * subroutine starting at position k either must return to next(i) by a ret
	 * instruction or it returns from the method Sun java compiler generates a
	 * code where the subrotine may return by a goto instruction. This may cause
	 * a recursive subroutine call, which breaks the constraints that teh JVM
	 * specification imposes over the bytecode.
	 * 
	 * Thus consider that the bytecode verifier guarantees that the subroutine
	 * may be exitted only by a ret.
	 * 
	 * @param startBlockInstrInSubrt
	 * @param component
	 * @param nextJsrInstr
	 */
	/*
	 * private void addComponentSubroutine(BCInstruction startBlockInstrInSubrt,
	 * HashMap component, BCInstruction nextJsrInstr) {
	 * 
	 * Block b = getBlockAt(startBlockInstrInSubrt.getPosition(), component); //
	 * if the block is not added already then add it if (b == null) { b =
	 * initBlock(startBlockInstrInSubrt); component.put(new
	 * Integer(b.getFirst().getPosition()), b); }
	 *  }
	 */

	/**
	 * Well formed subroutines are those that that satisfies the following
	 * conditions : jsr k then the subroutine starting at position k either must
	 * return to next(i) by a ret instruction or it returns from the method Sun
	 * java compiler generates a code where the subrotine may return by a goto
	 * instruction. This may cause a recursive subroutine call, which breaks the
	 * constraints that teh JVM specification imposes over the bytecode.
	 * 
	 * Thus we assume that the bytecode verifier guarantees that the subroutine
	 * may be exitted only by a ret.
	 */
	private void addToComponent(BCInstruction startBlockInstr, HashMap component) {
		if (startBlockInstr == null) {
			return;
		}
		Block b = getBlockAt(startBlockInstr.getPosition(), component);
		// if the block is not added already then add it
		if (b == null) {
			b = initBlock(startBlockInstr);
			component.put(new Integer(b.getFirst().getPosition()), b);
			/*Util.dump("ADD New block : " + b.toString());*/
		}
		BCInstruction last = b.getLast();

		if (last instanceof BCTypeRETURN) {
			return;
		}
		if (last instanceof BCRET) {
			return;
		}
		if (last instanceof BCATHROW) {
			return;
		}
		if (last instanceof BCJSR) {
			BCJSR jsr = (BCJSR) last;
			jsr.setTrace(this);
			BCInstruction startSubroutine = jsr.getTarget();
			if (subroutines == null) {
				subroutines = new HashMap();
			}
			BCInstruction jsrNext = jsr.getNext();
			HashMap subroutine = (HashMap) subroutines.get(new Integer(
					startSubroutine.getPosition()));

			if (subroutine == null) {
				subroutine = new HashMap();
				addToComponent(startSubroutine, subroutine);
				subroutines.put(new Integer(startSubroutine.getPosition()),
						subroutine);
			}
			addToComponent(jsrNext, component);

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
				addToComponent(jumpInstr.getTarget(), component);
				return;
			}
			addToComponent(next, component);
			return;
		}
		if (last instanceof BCConditionalBranch) {
			BCConditionalBranch cBranch = (BCConditionalBranch) last;
			/* Block _b0 = initBlock(cBranch.getNext()); */
			addToComponent(cBranch.getNext(), component);
			/* Block _b1 = initBlock(cBranch.getTarget()); */
			addToComponent(cBranch.getTarget(), component);
			return;
		}
		if (last instanceof BCGOTO) {
			BCUnconditionalBranch cBranch = (BCUnconditionalBranch) last;
			/* Block _b = initBlock(cBranch.getTarget()); */
			addToComponent(cBranch.getTarget(), component);
			return;
		}
		BCInstruction next = last.getNext();
		/* Block _b = initBlock(next); */
		addToComponent(next, component);
	}

	public ExceptionHandler getExceptionHandlerForExceptionThrownAt(
			JavaObjectType excThrownType, int excThrownAtPos) {
		ExceptionHandler excH = null;
		ExceptionHandler[] excHandlers = method.getExceptionHandlers();
		// find the first top -bottom handler for the exception excThrownType
		for (int i = 0; i < excHandlers.length; i++) {
			// if the handle i doesnot handle the exception k
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
	 * 
	 * @param subRotinePos -
	 *            the instruction index at which this subroutine starts at
	 * @return
	 */
	public VCGPath getWpForSubrotineAt(IJml2bConfiguration config,
			int subRoutinePos, VCGPath postcondition) {
		if (subroutines == null) {
			return null;
		}

		HashMap subroutine = (HashMap) subroutines.get(new Integer(
				subRoutinePos));

		wp(config, (VCGPath) postcondition.copy(), exsTable, subroutine);

		EntryPoint subRtEntryPoint = (EntryPoint) Util
				.getBCInstructionAtPosition(method.getBytecode(), subRoutinePos);
		Vector wp = subRtEntryPoint.getWp();
		VCGPath merge = VCGPath.mergeAll(wp);
		subRtEntryPoint.initWP();
		return merge;

	}

	/**
	 * gets for the exception type excThrownType an exception handle
	 * and calculates the wp for it
	 * 
	 * @param excThrownType
	 * @param excThrownAtPos
	 * @return Formula
	 */
	public VCGPath getWpForExcThrownAt(IJml2bConfiguration config,
			JavaObjectType excThrownType, int excThrownAtPos) {
		Vector wp = null;
		ExceptionHandler excH = getExceptionHandlerForExceptionThrownAt(
				excThrownType, excThrownAtPos);
		// if there is no exception handler then 
		// take the exceptional postcondition from 
		// the exsures table of the current specification case
		if (excH == null) {
			VCGPath vcg = new VCGPath();
			if (exsTable == null) {
				return null;
			}
			exsTable.getExsPostconditionThrow(excThrownType.getSignature(), vcg);
			return vcg;
			///method.getExsuresForException(excThrownType);
		}
		// in case there is an exception handler then calculate over the code of
		// the
		// exception handler the wp
		int handlerStart = excH.getHandlerPC();
		// get the component that represents the exception handle
		HashMap excHandlerBlocks = (HashMap) excHandlerComponents
				.get(new Integer(handlerStart));
		// this implementation is very bad , must be a class which wraps
		// the entry points and access the wp for an exception handler like
		// this
		
		VCGPath vcgExcHandler = new VCGPath();
		method.getMethodSpecification().getSpecificationCases()[0].getPostconditionToProve(vcgExcHandler);		
		wp(config,  vcgExcHandler, exsTable, excHandlerBlocks);
		
		EntryPoint excHandlerEntryPoint = (EntryPoint) Util
				.getBCInstructionAtPosition(method.getBytecode(), handlerStart);
		wp = excHandlerEntryPoint.getWp();
		if (wp == null) {
			return null;
		}
		VCGPath wps = VCGPath.mergeAll(wp);
		return wps;
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
		/*
		 * if (blocks == null) { Util.dump("abstract method"); return; }
		 * Util.dump(" **************** in dumpBlocks ************"); Iterator
		 * iter = blocks.values().iterator(); while (iter.hasNext()) { Block b =
		 * (Block) iter.next(); Util.dump(b.toString()); }
		 */
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
	 * 
	 */
	void dumpSubRoutineComponentBlocks() {
		if (subroutines == null) {
			Util.dump("no subroutines");
			return;
		}
		Iterator iter = subroutines.values().iterator();
		while (iter.hasNext()) {
			HashMap map = (HashMap) iter.next();
			Iterator excComp = map.values().iterator();
			Util.dump("subroutine ");
			while (excComp.hasNext()) {
				Block b = (Block) excComp.next();
				Util.dump(b.toString());
			}
		}
	}

	/**
	 * searches in the map of basic blocks if there is a block that starts with
	 * the _first instruction
	 * 
	 * @param _first
	 * @param _blocks -
	 *            a hashmap in which a block starting at position first is
	 *            looked for
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
	 * @param blocks -
	 *            a component where a block starting at start position will be
	 *            added
	 * @return
	 */
	/*
	 * public Block addBlock(BCInstruction start, HashMap blocks) { if (blocks ==
	 * null) { blocks = new HashMap(); } Block block = null; if ((block =
	 * getBlockAt(start.getPosition(), blocks)) != null) { return block; } block =
	 * initBlock(start, method.getBytecode()); blocks.put(new
	 * Integer(start.getPosition()), block); return block; }
	 */
	private Block initBlock(BCInstruction first) {
		BCInstruction[] instrs = method.getBytecode();
		BCInstruction next = first;
		if (next == null) {
			return null;
		}
		while (next.getNext() != null) {
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

	public void wp(IJml2bConfiguration config, VCGPath vcgPath,
			ExsuresTable _exsTable) {
		exsTable = _exsTable;
		wp(config, vcgPath, exsTable, normalComponent);
	}

	/**
	 * calculate the wp for the component given as fourth parameter for the
	 * postcondition given as second argument
	 * 
	 * @param config
	 * @param postcondition -
	 *            the predicate that ust hold in the poststate of the component
	 * @param exsures -
	 *            a structure that describes for every unhandled exception
	 *            thrown what is the postcondition that must hold
	 * @param component
	 */
	private void wp(IJml2bConfiguration config, VCGPath vcgPath,
			ExsuresTable exsures, HashMap component) {
		if ((component == null) || (component.size() == 0)) {
			return;
		}

		Iterator iter = component.values().iterator();
		while (iter.hasNext()) {
			Block b = (Block) (iter.next());
			if (b.getLast() instanceof BCTypeRETURN) {
				b.calculateRecursively(config, (VCGPath) vcgPath.copy(),
						exsures);
			} else if (b.getLast() instanceof BCRET) {
				b.calculateRecursively(config, (VCGPath) vcgPath.copy(),
						exsures);
			} else if (b.getLast() instanceof BCLoopEnd) {
				BCLoopEnd loopEnd = (BCLoopEnd) b.getLast();

				Formula invariant = (Formula) loopEnd.getInvariant().copy();

				Vector subGoals = invariant.elimConj();
				Enumeration en = subGoals.elements();
				VCGPath vcgPathLoop = new VCGPath();
				while (en.hasMoreElements()) {
					Formula f = (Formula) en.nextElement();
					vcgPathLoop.addGoal(VcType.LOOPPRESERV, f, b.getLast().getPosition());
					
				}
				b.calculateRecursively(config, vcgPathLoop, exsures);
			} else if (b.getLast() instanceof BCATHROW) {
				b.calculateRecursively(config, (VCGPath) vcgPath.copy(),
						exsures);
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
	 * @return list of formulas which represents the wp for a particular
	 *         specification case
	 */
	public Vector getWP() {
		if (entryBlock != null) {
			EntryPoint ep = ((EntryPoint) entryBlock.getFirst());
			Vector f = ep.getWps();
			return f;
		}
		return null;
	}

	// the method sets to null the formulas contained in Entry Point objects
	public void initWp() {
		BCInstruction[] instrs = getMethod().getBytecode();
		if ( instrs == null) {
			return;
		}
		for (int i = 0; i < instrs.length; i++) {
			if (instrs[i] instanceof EntryPoint) {
				((EntryPoint) instrs[i]).initWP();
			}
		}
	}

	/**
	 * returns the loopstart instruction for the loop that has the index given
	 * as parameter
	 * 
	 * @param loopIndex -
	 *            must be >= 0 if <code>loopIndex</code> < 0
	 * @return null if there are no loops in the controlflow graph
	 * @return null if there is no loop with this number
	 * @return null else
	 * @return the loop with the index
	 */
	public BCLoopStart getLoopWithIndex(int loopIndex) {

		if (loopIndex < 0) {
			return null;
		}
		if (loopStarts == null) {
			return null;
		}
		Enumeration loopEn = loopStarts.elements();
		while (loopEn.hasMoreElements()) {
			BCLoopStart start = (BCLoopStart) loopEn.nextElement();
			if (start.getLoopIndex() == loopIndex) {
				return start;
			}
		}
		return null;
	}
}