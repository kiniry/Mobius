package bytecode_wp.memory.allocation1;

import java.util.Vector;

import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.bytecode.BCLoopEnd;
import bytecode_wp.bytecode.BCLoopStart;
import bytecode_wp.bytecode.branch.BCConditionalBranch;
import bytecode_wp.utils.Util;

public class CalculateLoop {

	public static int allocInIter(BCInstruction[] body, BCLoopStart loopEntry) {
		// if already calculated return it
		if (loopEntry.getIterationAllocation() != -1) {
			return loopEntry.getIterationAllocation();
		}
		loopEntry.setStartToCalculate(true);
		int UPPERBNDITER = 0;
		Vector loopEndIndex = loopEntry.getLoopEndPositions();
		Vector loopEnds = fromIndToIns(body, loopEndIndex);
		if (loopEnds == null) {
			System.out.println("loop entry without loop ends");
		}

		for (int j = 0; j < loopEnds.size(); j++) {
			Vector targeters = ((BCInstruction) loopEnds.elementAt(j))
					.getTargeters();

			for (int k = 0; k < targeters.size(); k++) {
				int upBndNext = __allocInIter(body, loopEntry,
						(BCInstruction) targeters.elementAt(k));
				if (upBndNext > UPPERBNDITER) {
					UPPERBNDITER = upBndNext;
				}
				UPPERBNDITER = ((BCInstruction) loopEnds.elementAt(j)).alloc()
						+ UPPERBNDITER;
			}
		}
		// UPPERBNDITER = loopEntry.alloc() + UPPERBNDITER;
		loopEntry.setIterationAllocation(UPPERBNDITER);
		return UPPERBNDITER;

	}

	private static int __allocInIter(BCInstruction[] body,
			BCLoopStart loopEntry, BCInstruction ins) {
		int UPPERBOUND = 0;
		if (ins == loopEntry) {
			return loopEntry.alloc();
		}
		if (ins == null) {
			return 0;
		}
		if (ins instanceof BCLoopEnd) {
			// get the loop entry
			BCLoopEnd wr = ((BCLoopEnd) ins);
			int loopEntryInd = wr.getLoopEntry();
			BCLoopStart lStart = (BCLoopStart) Util.getBCInstructionAtPosition(
					body, loopEntryInd);

			/*
			 * // get the targeters of the loop entry and continue from them
			 * Vector loopEnds = lStart.getLoopEndPositions() ;
			 */
			// get the loop iteration
			int loopIter = CalculateLoop.allocInIter(body, lStart);

			int UPBNDAFTERLOOP = 0;

			Vector loopStTargets = lStart.getTargeters();
			for (int j = 0; j < loopStTargets.size(); j++) {
				int upBndNext =__allocInIter(body, lStart,
								(BCInstruction) loopStTargets.elementAt(j));
				if (upBndNext > UPBNDAFTERLOOP) {
					UPBNDAFTERLOOP = upBndNext;
				}
			}

			UPPERBOUND = loopIter + UPBNDAFTERLOOP;
		} else if (ins instanceof BCLoopStart) {
			// get the loop entry
			BCLoopStart lStart = ((BCLoopStart) ins);
	
			// if the loop is an englobing loop which has already been started to calculate
			if (lStart.isStartToCalculate() ) {
				return lStart.alloc();
			}
			//get the loop iteration
			int loopIter = CalculateLoop.allocInIter(body, lStart);

			int UPBNDAFTERLOOP = 0;

			Vector loopStTargets = ins.getTargeters();
			for (int j = 0; j < loopStTargets.size(); j++) {
				int upBndNext =__allocInIter(body, lStart,
								(BCInstruction) loopStTargets.elementAt(j));

				if (upBndNext > UPBNDAFTERLOOP) {
					UPBNDAFTERLOOP = upBndNext;
				}

			}
			UPPERBOUND = loopIter + UPBNDAFTERLOOP;
		} else {

			Vector targets = ins.getTargeters();
			int currUpBnd = 0;
			if (targets == null) {
				UPPERBOUND = ins.alloc();
			}
			for (int j = 0; j < targets.size(); j++) {
				currUpBnd = __allocInIter(body, loopEntry,
						(BCInstruction) targets.elementAt(j));
				if (currUpBnd > UPPERBOUND) {
					UPPERBOUND = currUpBnd;
				}
				UPPERBOUND = ins.alloc() + UPPERBOUND;
			}

		}
		return UPPERBOUND;
	}

	/*
	 * private static int _allocInIter(BCInstruction[] body, BCInstruction ins,
	 * Vector LOOPENDS) { int UPPERBOUND =0; if ( isIn(LOOPENDS, ins)) { return
	 * 0; }
	 * 
	 * 
	 * if (ins instanceof BCLoopEnd ) { // get the loop entry BCLoopEnd wr =
	 * ((BCLoopEnd) ins); int loopEntryInd = wr.getLoopEntry(); BCLoopStart
	 * lStart = (BCLoopStart)Util.getBCInstructionAtPosition(body,
	 * loopEntryInd);
	 *  // get the targeters of the loop entry and continue from them Vector
	 * loopEnds = lStart.getLoopEndPositions() ; // get the loop iteration int
	 * loopIter = CalculateLoop.allocInIter(body, lStart); if (loopEnds == null ) {
	 * System.out.println( "loop entry without loop ends"); } int upBndAfterLoop =
	 * 0; for (int i = 0; i < loopEnds.size(); i++ ) { BCInstruction loopEnd =
	 * Util.getBCInstructionAtPosition(body, ((Integer)loopEnds.elementAt(i)
	 * ).intValue()); Vector loopEndTargets = loopEnd.getTargets(); for (int j =
	 * 0; j < loopEndTargets.size(); j++) { int upBndNext = _allocInIter(body,
	 * (BCInstruction)loopEndTargets.elementAt(j), LOOPENDS); if (upBndNext >
	 * upBndAfterLoop) { upBndAfterLoop = upBndNext; } } } UPPERBOUND = loopIter +
	 * upBndAfterLoop ; } else if (ins instanceof BCLoopStart ) { // get the
	 * loop entry BCLoopStart lStart = ((BCLoopStart) ins);
	 *  // get the targeters of the loop entry and continue from them Vector
	 * loopEnds = lStart.getLoopEndPositions() ; // get the loop iteration
	 * 
	 * int loopIter = CalculateLoop.allocInIter(body, lStart); if (loopEnds ==
	 * null ) { System.out.println( "loop entry without loop ends"); } int
	 * upBndAfterLoop = 0; for (int i = 0; i < loopEnds.size(); i++ ) {
	 * BCInstruction loopEnd = Util.getBCInstructionAtPosition(body,
	 * ((Integer)loopEnds.elementAt(i) ).intValue()); Vector loopEndTargets =
	 * loopEnd.getTargets(); for (int j = 0; j < loopEndTargets.size(); j++) {
	 * int upBndNext = _allocInIter(body,
	 * (BCInstruction)loopEndTargets.elementAt(j), LOOPENDS); if (upBndNext >
	 * upBndAfterLoop) { upBndAfterLoop = upBndNext; } } } UPPERBOUND = loopIter +
	 * upBndAfterLoop ; } else { Vector targets = ins.getTargets(); int
	 * currUpBnd = 0; if (targets == null ) { UPPERBOUND = ins.alloc(); } for (
	 * int j = 0; j < targets.size(); j++) { currUpBnd = _allocInIter(body,
	 * (BCInstruction)targets.elementAt(j), LOOPENDS); if (currUpBnd >
	 * UPPERBOUND) { UPPERBOUND = currUpBnd; } UPPERBOUND =ins.alloc()+
	 * UPPERBOUND; } } return UPPERBOUND; }
	 */

	public static Vector fromIndToIns(BCInstruction[] body, Vector loopEnds) {
		if (loopEnds == null) {
			return null;
		}
		Vector instrs = new Vector();
		for (int k = 0; k < loopEnds.size(); k++) {
			BCInstruction ins = Util.getBCInstructionAtPosition(body,
					((Integer) loopEnds.elementAt(k)).intValue());
			instrs.add(ins);
		}
		return instrs;
	}

	/**
	 * checks if ins is in the list of instructions loopEnds
	 * 
	 * @param loopEnds
	 * @param ins
	 * @return
	 */
	public static boolean isIn(Vector loopEnds, BCInstruction ins) {
		if (loopEnds == null) {
			return false;
		}
		if (ins == null) {
			return false;
		}
		for (int k = 0; k < loopEnds.size(); k++) {
			BCInstruction le = (BCInstruction) loopEnds.elementAt(k);
			if (le == ins) {
				return true;
			}
		}
		return false;
	}

}
