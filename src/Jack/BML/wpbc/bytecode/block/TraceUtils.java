package bytecode.block;

import java.util.Vector;

import utils.Util;

import bcclass.BCMethod;
import bcclass.attributes.ExceptionHandler;
import bytecode.BCInstruction;

import bytecode.BCATHROW;
import bytecode.BCLoopEnd;
import bytecode.BCLoopStart;
import bytecode.BCRET;
import bytecode.BCTypeRETURN;
import bytecode.EntryPoint;

import bytecode.branch.BCConditionalBranch;
import bytecode.branch.BCGOTO;
import bytecode.branch.BCJSR;
import bytecode.branch.BCUnconditionalBranch;
import bytecode.stackinstruction.BCStackInstruction;

/**
 * @author mpavlova
 * 
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates. To enable and disable the creation of type
 * comments go to Window>Preferences>Java>Code Generation.
 */
public class TraceUtils {
	private static int loopNumber = 0;

	/**
	 * 
	 * 
	 * looks for backedges - blocks that are making a loop in the path
	 * gives an order  also for  loops / this means that 
	 * @param path -
	 *            a list of instructions starting with the entry instruction
	 *            executed before the instructions in the block. It must not be
	 *            null
	 * @param block -
	 *            the current block that is verified if it is a backedge
	 * @param backEdges -
	 *            the list of backedges found up to now
	 * @return
	 * @throws IllegalLoopException
	 */
	public static Vector initLoopInstructions(Path path, BCInstruction instr,
			Vector backEdges, BCInstruction[] instrs)
			throws IllegalLoopException {

		if (instr == null) {
			return backEdges;
		}
		if (instr instanceof BCTypeRETURN) {
			return backEdges;
		}
		if (instr instanceof BCRET) {
			return backEdges;
		}
		if (instr instanceof BCATHROW) {
			return backEdges;
		}

		path.addInstrToPath(new Integer(instr.getPosition()));
		/*Util.dump(path.toString());*/
		if (instr instanceof BCJSR) {
			BCInstruction srt = ((BCJSR) instr).getTarget();
			BCInstruction seqInstr = instr.getNext();
			// the subroutine is an end of a loop
			if ((seqInstr != null) && (path.contains(seqInstr))) {
				if (seqInstr instanceof BCJSR) {
					throw new IllegalLoopException("loop starting at jsr "
							+ instr.getPosition() + "| path : " + path);
				}

//				BCInstruction prevStart = seqInstr.getPrev();
				BCInstruction nextStart = seqInstr.getNext();
				BCInstruction prevLast = instr.getPrev();
				seqInstr.setPrev(null);
				instr.setNext(null);
				BCLoopStart loopStart = wrapLoopStart(seqInstr, instr
						.getPosition(), backEdges);

				if (nextStart != null) {
					nextStart.setPrev(loopStart);
				}
				Util.update(instrs, loopStart);
				BCLoopEnd loopEnd = wrapLoopEnd(instr, seqInstr.getPosition());
				
				if (prevLast != null) {
					prevLast.setNext(loopEnd);
				}
				Util.update(instrs, loopEnd);
				initLoopInstructions(path, srt, backEdges, instrs);
				return backEdges;
			}
			initLoopInstructions(path, seqInstr, backEdges, instrs);
			initLoopInstructions(path, srt, backEdges, instrs);
			return backEdges;
		} else if (instr instanceof BCConditionalBranch) {
			BCConditionalBranch branchInstr = (BCConditionalBranch) instr;
			BCInstruction branchTargetInstr = branchInstr.getTarget();
			BCInstruction seqInstr = branchInstr.getNext();

			// add the backedge
			if (branchTargetInstr.getPosition() < instr.getPosition()) {
				addBackEdge(backEdges, instr, branchTargetInstr);
			}
			if ((branchTargetInstr != null)
					&& (path.contains(branchTargetInstr))) {
				BCInstruction prevStart = branchTargetInstr.getPrev();
				BCInstruction nextStart = branchTargetInstr.getNext();
				BCInstruction prevLast = branchInstr.getPrev();
				BCInstruction nextLast = branchInstr.getNext();
				branchInstr.setTarget(null);
				branchTargetInstr.removeTargeter(branchInstr);
				// get previous instructions and udate them

				BCLoopStart loopStart = wrapLoopStart(branchTargetInstr, instr
						.getPosition(), backEdges);
				//actualise the values in the previous and the next instruction
				if (prevStart != null) {
					prevStart.setNext(loopStart);
				}
				if (nextStart != null) {
					nextStart.setPrev(loopStart);
				}
				Util.update(instrs, loopStart);
				//				commented because the data structure changed
				//				branchTarget.setFirst(loopStart );
				BCLoopEnd loopEnd = wrapLoopEnd(branchInstr, branchTargetInstr
						.getPosition());
				if (prevLast != null) {
					prevLast.setNext(loopEnd);
				}
				if (nextLast != null) {
					nextLast.setPrev(loopEnd);
				}
				Util.update(instrs, loopEnd);
				initLoopInstructions(path, seqInstr, backEdges, instrs);
				return backEdges;
			} else if ((seqInstr != null) && (path.contains(seqInstr))) {			
				BCInstruction nextStart = seqInstr.getNext();
				BCInstruction prevLast = branchInstr.getPrev();
//				BCInstruction nextLast = branchInstr.getNext();

				branchInstr.setNext(null);
				// the conditional instruction is the prev instruction of the
				// seq branch
				seqInstr.setPrev(null);
				initLoopInstructions(path, branchTargetInstr, backEdges, instrs);
				BCLoopStart loopStart = wrapLoopStart(seqInstr, instr
						.getPosition(), backEdges);
				if (nextStart != null) {
					nextStart.setPrev(loopStart);
				}
				Util.update(instrs, loopStart);
				BCLoopEnd loopEnd = wrapLoopEnd(branchInstr, seqInstr.getPosition());
				if (prevLast != null) {
					prevLast.setNext(loopEnd);
				}
				Util.update(instrs, loopEnd);
				return backEdges;
			} else {

				//continue recursively
				Path copyPath = path.copy();
				initLoopInstructions(copyPath, branchTargetInstr, backEdges,
						instrs);
				initLoopInstructions(path, seqInstr, backEdges, instrs);
				return backEdges;
			}
		} else if (instr instanceof BCGOTO) {
			BCUnconditionalBranch uncondBranchInstr = (BCUnconditionalBranch) instr;
			BCInstruction target = uncondBranchInstr.getTarget();
			if (target.getPosition() < instr.getPosition()) {
				addBackEdge(backEdges, instr, target);
			}
			if ((target != null) && (path.contains(target))) {
				if (target instanceof BCJSR) {
					throw new IllegalLoopException("loop starting at jsr "
							+ instr.getPosition() + "| path : " + path);
				}
				BCInstruction prevStart = target.getPrev();
				BCInstruction nextStart = target.getNext();
				BCInstruction prevLast = uncondBranchInstr.getPrev();
				BCInstruction nextLast = uncondBranchInstr.getNext();

				uncondBranchInstr.setTarget(null);
				target.removeTargeter(uncondBranchInstr);

				BCLoopStart loopStart = wrapLoopStart(target, uncondBranchInstr
						.getPosition(), backEdges);
				if (prevStart != null) {
					prevStart.setNext(loopStart);
				}
				if (nextStart != null) {
					nextStart.setPrev(loopStart);
				}
				Util.update(instrs, loopStart);
				BCLoopEnd loopEnd = wrapLoopEnd(uncondBranchInstr, target
						.getPosition());
				if (prevLast != null) {
					prevLast.setNext(loopEnd);
				}
				if (nextLast != null) {
					nextLast.setPrev(loopEnd);
				}
				Util.update(instrs, loopEnd);
				/* addBackEdge(backEdges, loopEnd, loopStart); */
				return backEdges;
			}
			initLoopInstructions(path, target, backEdges, instrs);
			return backEdges;

		} else {
			BCInstruction next = instr.getNext();

			//in case there isa loop do the needed mofifiations = may be even
			// more change
			//the references of targets and targeters to the looppend and
			// loopstart objects respectively
			if ((next != null) && (path.contains(next))) {
				if (next instanceof BCJSR) {
					throw new IllegalLoopException("loop starting at jsr "
							+ instr.getPosition() + "| path : " + path);
				}
				BCInstruction nextStart = next.getNext();
				BCInstruction prevLast = instr.getPrev();

				instr.setNext(null);
				next.setPrev(null);
				BCLoopStart loopStart = wrapLoopStart(next,
						instr.getPosition(), backEdges);
				if (nextStart != null) {
					nextStart.setPrev(loopStart);
				}
				Util.update(instrs, loopStart);
				BCLoopEnd loopEnd = wrapLoopEnd(instr, next.getPosition());

				if (prevLast != null) {
					prevLast.setNext(loopEnd);
				}
				Util.update(instrs, loopEnd);
				return backEdges;
			}
			initLoopInstructions(path, next, backEdges, instrs);
			return backEdges;
		}
		//continue recursively
	}

	private static void addBackEdge(Vector backEdges,
			BCInstruction startBackEdge, BCInstruction endBackEdge) {
		if (backEdges == null) {
			backEdges = new Vector();
		}
		Backedge backEdge = new Backedge(startBackEdge.getPosition(),
				endBackEdge.getPosition());
		//		backEdge.setNumber(backEdges.size());
		backEdge.setNumber(loopNumber);
		loopNumber++;
		backEdges.add(backEdge);
	}

	/**
	 * this method wraps the corresponding instruction into a loopstart class
	 * and adds the last backedge into it
	 * 
	 * @param startLoop
	 * @param loopEndPosition
	 * @param backedges
	 * @return
	 */
	private static BCLoopStart wrapLoopStart(BCInstruction startLoop,
			int loopEndPosition, Vector backedges) {
		//		Backedge back = (Backedge) backedges.remove(backedges.size() - 1);
		BCLoopStart loopStart = null;
		if (startLoop instanceof BCLoopStart) {
			loopStart = (BCLoopStart) startLoop;
			loopStart.addLoopEndPosition(loopEndPosition);
		} else {
			loopStart = new BCLoopStart(startLoop, loopEndPosition);
			//		Util.dump("loopstart found : ");
			//		Util.dump(loopStart.toString());
		}
		if (backedges.size() >= 1) {
			Backedge back = (Backedge) backedges.remove(backedges.size() - 1);
			loopStart.setLoopIndex(back.getNumber());
			loopStart.addBackedges(back);
		}
		Util.dump(loopStart.toString());
		return loopStart;
	}

	private static BCLoopEnd wrapLoopEnd(BCInstruction endLoop,
			int loopStartPosition) {

		if (endLoop instanceof BCLoopEnd) {
			return (BCLoopEnd) endLoop;
		}

		BCLoopEnd loopEnd = new BCLoopEnd(endLoop, loopStartPosition);
		//		Util.dump("loopend found : ");
		Util.dump(loopEnd.toString());
		return loopEnd;
	}

	/**
	 * @param entryBlock
	 * @param instructions
	 * @throws IllegalLoopException
	 */
	public static void initLoopInstructions(BCInstruction entryPoint,
			BCInstruction[] instructions) throws IllegalLoopException {
		loopNumber = 0;
		initLoopInstructions(new Path(), entryPoint, new Vector(), instructions);
	}

	/**
	 * 
	 * An entry point instuction is an instruction that doesnot have any
	 * targeter. initialises the entry points. There is only one entry point for
	 * the graph representing the normal execution of the program. Anyways the
	 * points where the exc handlers code start are considered to be also entry
	 * points for the connex subgraphs that represent an exception handler
	 * 
	 * @param method -
	 *            the method whose bytecode entrypoints are set
	 */
	public static void initEntryPoints(BCMethod method) {
		BCInstruction[] bytecode = method.getBytecode();
		if (bytecode == null) {
			return;
		}
		if (!(bytecode[0] instanceof EntryPoint)) {
			BCInstruction instruction = Util.getBCInstructionAtPosition(
					bytecode, 0);
			instruction = new EntryPoint(instruction);
			Util.update(method.getBytecode(), instruction);
		}
		ExceptionHandler[] excHs = method.getExceptionHandlers();
		if (excHs == null) {
			return;
		}
		for (int i = 0; i < excHs.length; i++) {
			int pos = excHs[i].getHandlerPC();
			BCInstruction instr = Util
					.getBCInstructionAtPosition(bytecode, pos);
			if (!(instr instanceof EntryPoint)) {
				BCInstruction excHandlerEntryPoint = new EntryPoint(instr);
				Util.update(method.getBytecode(), excHandlerEntryPoint);
			}
		}

		for (int i = 0; i < bytecode.length; i++) {
			if (bytecode[i] instanceof BCJSR) {
				int subroutinestart = ((BCJSR) bytecode[i]).getTargetPosition();
				BCInstruction subRtStartInstr = Util
						.getBCInstructionAtPosition(bytecode, subroutinestart);
				// if it is not already wrapped
				if (!(subRtStartInstr instanceof EntryPoint)) {
					BCInstruction excHandlerEntryPoint = new EntryPoint(
							subRtStartInstr);
					Util.update(method.getBytecode(), excHandlerEntryPoint);
				}
			}
		}
	}

}