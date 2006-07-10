/*
 * Created on Feb 21, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package bytecode_wp.memory.allocation;

import jack.util.Logger;

import java.util.Vector;

import bytecode_wp.bc.io.ReadAttributeException;
import bytecode_wp.bcclass.BCMethod;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.bytecode.BCLoopEnd;
import bytecode_wp.bytecode.BCLoopStart;
import bytecode_wp.bytecode.BCTypeRETURN;
import bytecode_wp.bytecode.block.Backedge;
import bytecode_wp.bytecode.block.IllegalLoopException;
import bytecode_wp.bytecode.branch.BCConditionalBranch;
import bytecode_wp.bytecode.branch.BCUnconditionalBranch;
import bytecode_wp.bytecode.objectmanipulation.BCInvoke;
import bytecode_wp.bytecode.objectmanipulation.BCNEW;
import bytecode_wp.utils.Util;

/**
 * @author mpavlova
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
public class MethodAllocation {
	
	// the maximum memory used
	public static NumberLiteral MAX = new NumberLiteral(100); 
	
	
	public static int getMethodAllocates(BCMethod method)
			throws ReadAttributeException, IllegalLoopException, MalformedException {

		method.setChecked(true);

		BCInstruction[] instrs = method.getBytecode();
		if (instrs == null) {
			return 0;
		}
		BCInstructionAlloc[] bcodeAlloc = new BCInstructionAlloc[instrs.length];
		int iters = 1;
		for (int i = 0; i < instrs.length; i++) {
			if (instrs[i] instanceof BCLoopStart) {
				bcodeAlloc[i] = new BCInstructionAlloc(instrs[i], iters);
				continue;
			}
			bcodeAlloc[i] = new BCInstructionAlloc(instrs[i]);
		}
		int numberLoops = getNumberLoops(bcodeAlloc);
		calculateinOrderLoops(numberLoops, bcodeAlloc, instrs, method);
		int alloc = getMethodAllocated(bcodeAlloc[0], bcodeAlloc, instrs,
				method);
		method.setAllocations(alloc);
		Logger.get().println("*************** method " + method.toString()
				+ " allocated " + method.getAllocations() + " units");

		return method.getAllocations();
	}

	/**
	 * 
	 * @param bcalloc -
	 *            the entry poiny oinstruction
	 * @param method
	 * @return
	 * @throws MalformedException
	 * @throws ReadAttributeException
	 * @throws IllegalLoopException
	 */
	private static int getMethodAllocated(BCInstructionAlloc bcalloc,
			BCInstructionAlloc[] bc, BCInstruction[] instrs, BCMethod method)
			throws MalformedException, ReadAttributeException, IllegalLoopException {

		if (bcalloc.isChecked()) {
			return 0;
		}
		BCInstruction instr = bcalloc.getInstruction();
		int allocatedFromNowOn = 0;

		if (instr instanceof BCNEW) {
			bcalloc.setChecked();
			BCInstruction next = instr.getNext();
			int nextPos = next.getBCIndex();
			allocatedFromNowOn = bcalloc.getAllocated()
					+ getMethodAllocated(bc[nextPos], bc, instrs, method);
			return allocatedFromNowOn;
		}
		if (instr instanceof BCConditionalBranch) {
			bcalloc.setChecked();
			BCInstruction next = instr.getNext();
			BCInstruction target = ((BCConditionalBranch) instr).getTarget();
			int posNext = next.getBCIndex();
			int posTarget = target.getBCIndex();
			allocatedFromNowOn = getMethodAllocated(bc[posNext], bc, instrs,
					method)
					+ getMethodAllocated(bc[posTarget], bc, instrs, method);
			return allocatedFromNowOn;
		}
		if (instr instanceof BCUnconditionalBranch) {
			bcalloc.setChecked();
			//BCInstruction next = instr.getNext();
			BCInstruction target = ((BCUnconditionalBranch) instr).getTarget();
			int posTarget = target.getBCIndex();
			allocatedFromNowOn = getMethodAllocated(bc[posTarget], bc, instrs,
					method);
			return allocatedFromNowOn;
		}
		if (instr instanceof BCTypeRETURN) {
			bcalloc.setChecked();
			return 0;
		}
		if (instr instanceof BCLoopStart) {
			allocatedFromNowOn = bcalloc.getLoopConsumption();
			Backedge backedge = (Backedge) ((BCLoopStart) instr).getBackedges()
					.elementAt(0);
			instr = Util.getBCInstructionAtPosition(instrs, backedge
					.getStartBackEdge());
			/* return allocatedFromNowOn; */
		}
		if (instr instanceof BCInvoke) {
			bcalloc.setChecked();
			BCMethod m = null;//((BCInvoke) instr).getInvokedMethod();
			Util.dump(method + " invokes " + m.toString() + " that allocates ");
			m.initMethod();
			
			allocatedFromNowOn = getMethodAllocates(m);
			Util.dump(""+ m.getAllocations());
			//BCInstruction next = instr.getNext();
			//int nextPos = next.getBCIndex();
		}
		bcalloc.setChecked();
		BCInstruction next = instr.getNext();
		if (next == null) {
			return 0;
		}
		//skip the insrtuctions alreasdy passed through
		while ((next != null) && (bc[next.getBCIndex()].isChecked())) {
			next = next.getNext();
		}
		if (next != null) {
			int nextPos = next.getBCIndex();
			allocatedFromNowOn = allocatedFromNowOn
					+ getMethodAllocated(bc[nextPos], bc, instrs, method);
		}
		return allocatedFromNowOn;
	}

	public static int getLoopAllocatedInPath(BCInstructionAlloc bcalloc,
			BCInstructionAlloc[] bc, BCLoopStart start, BCInstruction[] instrs,
			Backedge backEdge) throws MalformedException,
			ReadAttributeException, IllegalLoopException {
		BCInstruction instr = bcalloc.getInstruction();
		// commented recently : may be not needed 
/*		if (instr.getPosition() < backEdge.getEndBackEdge()) {
			return 0;
		}*/
		int allocated = 0;

		if (bcalloc.isChecked()) {
			instr = instr.getPrev();
			while ((instr != null) && (bc[instr.getBCIndex()].isChecked())) {
				if (instr instanceof BCLoopStart) {
					break;
				}
				instr = instr.getPrev();
			}
			if (instr == null) {
				return allocated;
			}
			if (instr instanceof BCLoopStart) {
				BCInstructionAlloc allocatedLoop = bc[instr.getBCIndex()];
				allocated = allocatedLoop.getLoopConsumption();
				Backedge backedge = (Backedge) ((BCLoopStart) instr)
						.getBackedges().elementAt(0);
				instr = Util.getBCInstructionAtPosition(instrs, backedge
						.getEndBackEdge());
				instr = instr.getPrev();
			}
		}

		// if the start loop has been reached stop the procedure
		if (instr == start) {
			allocated = bcalloc.getAllocated();
			return allocated;
		}
		if (instr instanceof BCTypeRETURN) {
			bcalloc.setChecked();
			return 0;
		}
		int invokedMethAlloc = 0;
		if (instr instanceof BCInvoke) {
			//			bcalloc.setChecked();
			BCMethod m = null;//((BCInvoke) instr).getInvokedMethod();
			m.initMethod();
			invokedMethAlloc = getMethodAllocates(m);
		}
		BCInstruction prev = instr.getPrev();
		if (prev == null) {
			return allocated;
		}
		int prevPos = prev.getBCIndex();
		allocated = allocated
				+ getLoopAllocatedInPath(bc[prevPos], bc, start, instrs, backEdge);
		Vector targeters = instr.getTargeters();
		if (targeters != null) {
			for (int i = 0; i < targeters.size(); i++) {
				BCInstruction instTargeter = (BCInstruction) targeters
						.elementAt(i);
				allocated = allocated
						+ getLoopAllocatedInPath(bc[instTargeter.getBCIndex()], bc,
								start, instrs, backEdge);
			}
		}
		allocated = allocated + bcalloc.getAllocated() + invokedMethAlloc;
		bcalloc.setChecked();
		return allocated;
	}

	public static int getNumberLoops(BCInstructionAlloc[] bc) {
		int numberLoops = 0;
		for (int i = 0; i < bc.length; i++) {

			BCInstruction instr = bc[i].getInstruction();
			if (instr instanceof BCLoopStart) {
				numberLoops++;
			}
		}
		return numberLoops;
	}

	public static void calculateinOrderLoops(int numberLoops,
			BCInstructionAlloc[] bc, BCInstruction[] instrs, BCMethod m)
			throws ReadAttributeException, IllegalLoopException, MalformedException {

		for (int j = numberLoops; j >= 0; j--) {
			// run over the loops in down up direction - fist the last and in the end the first loop
			for (int i = 0; i < bc.length; i++) {
				BCInstruction instr = bc[i].getInstruction();
				if ((instr instanceof BCLoopStart)) {
					BCLoopStart ls = (BCLoopStart) instr;
					if (ls.getLoopIndex() == j) {
						calculateForLoop(bc[i], bc, instrs, m);
					}
				}
			}
		}
	}

	
	/**
	 * Calculate the loop consumption per iteration.
	 * Modifies the value stored in bcalloc by calling 
	 * {@link BCInstructionAlloc#setLoopConsumptionPerIteration(int)}.
	 * Also write the result in the command line.
	 * @param bcalloc 
	 * @param bc
	 * @param instrs
	 * @param method
	 * @throws ReadAttributeException
	 * @throws IllegalLoopException
	 * @throws MalformedException
	 */
	//@ modifies bcalloc.loopConsumption;
	private static void calculateForLoop(BCInstructionAlloc bcalloc,
			BCInstructionAlloc[] bc, BCInstruction[] instrs, BCMethod method)
			throws ReadAttributeException, IllegalLoopException, MalformedException {
		BCLoopStart loopEntry = (BCLoopStart) bcalloc.getInstruction();
		Vector loopEnds = loopEntry.getLoopEndPositions();
//		int iters = bcalloc.getMaxIterations();
		int allocatedInLoop = 0;

		for (int i = 0; i < loopEnds.size(); i++) {
			int offset = ((Integer) loopEnds.elementAt(i)).intValue();
			BCInstruction loopEnd = (BCLoopEnd) Util
					.getBCInstructionAtPosition(instrs, offset);
			Backedge backEdge = (Backedge) (loopEntry.getBackedges()
					.elementAt(0)); //NB/ to be revised
			allocatedInLoop = allocatedInLoop
					+ getLoopAllocatedInPath(bc[loopEnd.getBCIndex()], bc, loopEntry,
							instrs, backEdge);
		}
		bcalloc.setLoopConsumptionPerIteration(allocatedInLoop);
		Logger.get().println("in method " + method + " loop starting at "
				+ loopEntry + " allocates " + allocatedInLoop);
	}

}