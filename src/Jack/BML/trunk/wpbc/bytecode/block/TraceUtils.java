package bytecode.block;

import java.util.Vector;

import utils.Util;

import bcclass.BCMethod;
import bcclass.attributes.ExceptionHandler;
import bytecode.BCInstruction;

import bytecode.BCLoopEnd;
import bytecode.BCLoopStart;
import bytecode.EntryPoint;

import bytecode.branch.BCConditionalBranch;
import bytecode.branch.BCUnconditionalBranch;
import bytecode.stackinstruction.BCStackInstruction;

/**
 * @author mpavlova
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class TraceUtils {

	//	/**
	//	 * wraps all instructions that are the start of an exception handler 
	//	 * @param method
	//	 */
	//	public static void  initExceptionandlerStartInstructions( BCMethod method ) {
	//		ExceptionHandler[] excHandlers = method.getExceptionHandlers();
	//		if (excHandlers == null){
	//			return;
	//		}
	//		BCInstruction[] instrs = method.getBytecode();
	//		for (int i = 0; i  < excHandlers.length; i++) {
	//			int pos = excHandlers[i].getHandlerPC() ;
	//			BCInstruction _excHandlerStart = Util.getBCInstructionAtPosition(instrs, pos);
	//			ExceptionHandlerStartInstruction excHandlerStart = new ExceptionHandlerStartInstruction(_excHandlerStart);
	//			Util.update(instrs, excHandlerStart); 
	//		}
	//	}
	//	
	/**
	 * looks for backedges - blocks that are making a loop in the  
	 * path 
	 * @param path - a list of instructions starting  with the entry instruction executed before the instructions in the block 
	 * @param block - the current block that is verified if it is a backedge 
	 * @param backEdges - the list of backedges found up to now
	 * @return
	 */
	public static Vector initLoopInstructions(
		Path path,
		BCInstruction instr,
		Vector backEdges,
		BCInstruction[] instrs) {

		if (instr == null) {
			return backEdges;
		}
		if (path == null) {
			path = new Path();
			path.addBlockToPath(instr);
			if (instr instanceof BCConditionalBranch) {
				BCConditionalBranch branchInstr = (BCConditionalBranch) instr;
				Path copyPath = path.copy();
				initLoopInstructions(
					path,
					branchInstr.getNext(),
					backEdges,
					instrs);
				initLoopInstructions(
					copyPath,
					branchInstr.getTarget(),
					backEdges,
					instrs);
				return backEdges;
			} else if (instr instanceof BCUnconditionalBranch) {
				BCUnconditionalBranch uncondBranchInstr =
					(BCUnconditionalBranch) instr;
				initLoopInstructions(
					path,
					uncondBranchInstr.getTarget(),
					backEdges,
					instrs);
				return backEdges;
			} else {
				initLoopInstructions(path, instr, backEdges, instrs);
				return backEdges;
			}
		}
		path.addBlockToPath(instr);
		if (instr instanceof BCConditionalBranch) {
			BCConditionalBranch branchInstr = (BCConditionalBranch) instr;
			BCInstruction branchTargetInstr = branchInstr.getTarget();
			BCInstruction seqInstr = branchInstr.getNext();

			if ((branchTargetInstr != null)
				&& (path.contains(branchTargetInstr))) {
				BCInstruction prevStart = branchTargetInstr.getPrev();
				BCInstruction nextStart = branchTargetInstr.getNext();
				BCInstruction prevLast = branchInstr.getPrev();
				BCInstruction nextLast = branchInstr.getNext();
				branchInstr.setTarget(null);
				branchTargetInstr.removeTargeter(branchInstr);
				// get previous instructions and udate them

				BCLoopStart loopStart =
					wrapLoopStart(branchTargetInstr, instr.getPosition());
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
				BCLoopEnd loopEnd =
					wrapLoopEnd(branchInstr, branchTargetInstr.getPosition());
				if (prevLast != null) {
					prevLast.setNext(loopEnd);
				}
				if (nextLast != null) {
					nextLast.setPrev(loopEnd);
				}
				Util.update(instrs, loopEnd);
				//				commented because the data structure changed
				//				block.setLast(loopEnd);
				//				Util.dump("=========== backedge in branch =========== ");
				//				path.dump( );
				addBackEdge(backEdges, loopEnd, loopStart);
				initLoopInstructions(path, seqInstr, backEdges, instrs);
				return backEdges;
			} else if ((seqInstr != null) && (path.contains(seqInstr))) {
				BCInstruction prevStart = seqInstr.getPrev();
				BCInstruction nextStart = seqInstr.getNext();
				BCInstruction prevLast = instr.getPrev();
				BCInstruction nextLast = instr.getNext();

				branchInstr.setNext(null);
				// the conditional instruction is the prev instruction of the seq branch 
				seqInstr.setPrev(null);

				BCLoopStart loopStart =
					wrapLoopStart(seqInstr, instr.getPosition());
				if (prevStart != null) {
					prevStart.setNext(loopStart);
				}
				if (nextStart != null) {
					nextStart.setPrev(loopStart);
				}
				Util.update(instrs, loopStart);
				//				commented because the data structure changed
				//				seqTarget.setFirst( loopStart);
				BCLoopEnd loopEnd = wrapLoopEnd(instr, seqInstr.getPosition());
				if (nextLast != null) {
					nextLast.setPrev(loopEnd);
				}
				if (prevLast != null) {
					prevLast.setNext(loopEnd);
				}
				Util.update(instrs, loopEnd);
				// commented because the data structure changed
				//				block.setLast(loopEnd );
				//				Util.dump("=========== backedge in seq target =========== ");
				//				path.dump( );
				addBackEdge(backEdges, loopEnd, loopStart);
				initLoopInstructions(
					path,
					branchTargetInstr,
					backEdges,
					instrs);
				return backEdges;
			} else {
				//continue recursively
				Path copyPath = path.copy();
				initLoopInstructions(path, seqInstr, backEdges, instrs);
				initLoopInstructions(
					copyPath,
					branchTargetInstr,
					backEdges,
					instrs);
				return backEdges;
			}
		} else if (instr instanceof BCUnconditionalBranch) {
			BCUnconditionalBranch uncondBranchInstr =
				(BCUnconditionalBranch) instr;
			BCInstruction target = uncondBranchInstr.getTarget();
			if ((target != null) && (path.contains(target))) {
				BCInstruction prevStart = target.getPrev();
				BCInstruction nextStart = target.getNext();
				BCInstruction prevLast = uncondBranchInstr.getPrev();
				BCInstruction nextLast = uncondBranchInstr.getNext();

				uncondBranchInstr.setTarget(null);
				target.removeTargeter(uncondBranchInstr);

				BCLoopStart loopStart =
					wrapLoopStart(target, uncondBranchInstr.getPosition());
				if (prevStart != null) {
					prevStart.setNext(loopStart);
				}
				if (nextStart != null) {
					nextStart.setPrev(loopStart);
				}
				Util.update(instrs, loopStart);
				BCLoopEnd loopEnd =
					wrapLoopEnd(uncondBranchInstr, target.getPosition());
				if (prevLast != null) {
					prevLast.setNext(loopEnd);
				}
				if (nextLast != null) {
					nextLast.setPrev(loopEnd);
				}
				Util.update(instrs, loopEnd);
				addBackEdge(backEdges, loopEnd, loopStart);
				return backEdges;
			}
			initLoopInstructions(path, target, backEdges, instrs);
			return backEdges;
		} else {
			BCInstruction next = instr.getNext();

			//in case there isa  loop do the  needed mofifiations = may be even more change 
			//the references of targets and targeters to the looppend and loopstart objects respectively
			if ((next != null) && (path.contains(next))) {
//				BCInstruction prevStart = next.getPrev();
				BCInstruction nextStart = next.getNext();
				BCInstruction prevLast = instr.getPrev();
//				BCInstruction nextLast = instr.getNext();
				instr.setNext(null);
				next.setPrev(null);
				BCLoopStart loopStart =
					wrapLoopStart(next, instr.getPosition());
//				if (prevStart != null) {
//					prevStart.setNext(loopStart);
//				}
				if (nextStart != null) {
					nextStart.setPrev(loopStart);
				}

				Util.update(instrs, loopStart);
				//				actualise the first instruction of target  block
				//				commented because the data structure changed
				//				target.setFirst( loopStart);
				BCLoopEnd loopEnd = wrapLoopEnd(instr, next.getPosition());

				if (prevLast != null) {
					prevLast.setNext(loopEnd);
				}
//				if (nextLast != null) {
//					nextLast.setPrev(loopEnd);
//				}
				Util.update(instrs, loopEnd);
				//actualise the last instruction of block 
				//				block.setLast( loopEnd);
				//				Util.dump(" =========== backedge after seq instruction =========== ");
				//				path.dump( );
				addBackEdge(backEdges, loopEnd, loopStart);
				return backEdges;
			}
			initLoopInstructions(path, next, backEdges, instrs);
			return backEdges;
		}
		//continue recursively
	}

	private static void addBackEdge(
		Vector backEdges,
		BCLoopEnd loopEnd,
		BCLoopStart loopStart) {
		if (backEdges == null) {
			backEdges = new Vector();
		}
		Vector backEdge = new Vector();
		backEdge.add(loopEnd);
		backEdge.add(loopStart);
		backEdges.add(backEdge);
		//		backEdge.dump("");
	}

	private static BCLoopStart wrapLoopStart(
		BCInstruction startLoop,
		int loopEndPosition) {
		if (startLoop instanceof BCLoopStart) {
			BCLoopStart loopS = (BCLoopStart) startLoop;
			loopS.addLoopEndPosition(loopEndPosition);
			return loopS;
		}
		BCLoopStart loopStart = new BCLoopStart(startLoop, loopEndPosition);
		//		Util.dump("loopstart found : ");
		//		Util.dump(loopStart.toString());
		loopStart.dump("");
		return loopStart;
	}

	private static BCLoopEnd wrapLoopEnd(
		BCInstruction endLoop,
		int loopStartPosition) {
		BCLoopEnd loopEnd = new BCLoopEnd(endLoop, loopStartPosition);
		//		Util.dump("loopend found : ");
		//		Util.dump( loopEnd.toString());
		return loopEnd;
	}

	/**
	 * @param entryBlock
	 * @param instructions
	 */
	public static void initLoopInstructions(
		BCInstruction entryPoint,
		BCInstruction[] instructions) {
		initLoopInstructions(null, entryPoint, null, instructions);
	}

	/**
	 * 
	 * An entry pint instuction is an instruction that doesnot have any targeter. 
	 * initialises the entry points. There is only one entry point for the graph representing the normal execution of the program. ANyways the points where the exc handlers
	 * are considered to be also entry points for the graphs that represnt an exception handler
	 * 
	 * @param method - the method whose bytecode entrypoints are  set
	 */
	public static void initEntryPoints(BCMethod method) {

		if (method.getBytecode() == null) {
			return;
		}
		BCInstruction instruction = new EntryPoint(method.getBytecode()[0]);
		Util.update(method.getBytecode(), instruction);
		ExceptionHandler[] excHs = method.getExceptionHandlers();
		if (excHs == null) {
			return;
		}
		for (int i = 0; i < excHs.length; i++) {
			int pos = excHs[i].getHandlerPC();
			BCInstruction instr =
				Util.getBCInstructionAtPosition(method.getBytecode(), pos);
			BCInstruction excHandlerEntryPoint = new EntryPoint(instr);
			Util.update(method.getBytecode(), instruction);
		}
	}

}
