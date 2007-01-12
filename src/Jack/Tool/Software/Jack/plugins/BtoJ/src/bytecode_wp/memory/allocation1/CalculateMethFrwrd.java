package bytecode_wp.memory.allocation1;

import java.util.Vector;

import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.bytecode.BCLoopEnd;
import bytecode_wp.bytecode.BCLoopStart;
import bytecode_wp.bytecode.BCTypeRETURN;
import bytecode_wp.bytecode.EntryPoint;
import bytecode_wp.utils.Util;

public class CalculateMethFrwrd {

	public static int memConsMeth(BCInstruction[] body) {
		int UPPERBOUND = 0;
		for (int k = 0; k < body.length; k++) {
			if (body[k] instanceof BCTypeRETURN) {
				int upperBndPath = memConsMeth(body, body[k]);
				if (upperBndPath > UPPERBOUND) {
					UPPERBOUND = upperBndPath;
				}
			}
		}
		return UPPERBOUND;
	}

	public static int memConsMeth(BCInstruction[] body, BCInstruction ins) {

		int UPPERBOUND = 0;
		if (ins == null) {
			UPPERBOUND = 0;
		} else if (ins instanceof EntryPoint) {
			UPPERBOUND = ins.alloc();
		} else if (ins instanceof BCLoopEnd) {
			// get the loop entry
			BCLoopEnd wr = ((BCLoopEnd) ins);
			int loopEntryInd = wr.getLoopEntry();
			BCLoopStart lStart = (BCLoopStart) Util.getBCInstructionAtPosition(
					body, loopEntryInd);

			// get the loop iteration
			int loopIter = CalculateLoop.allocInIter(body, lStart);
			int upBndAfterLoop = 0;

			Vector loopStartTargeters = lStart.getTargeters();
			for (int j = 0; j < loopStartTargeters.size(); j++) {
				int upBndNext = memConsMeth(body,
						(BCInstruction) loopStartTargeters.elementAt(j));
				if (upBndNext > upBndAfterLoop) {
					upBndAfterLoop = upBndNext;
				}
			}

			UPPERBOUND = loopIter + upBndAfterLoop;
		} else if (ins instanceof BCLoopStart) {
			// get the loop entry
			BCLoopStart lStart = ((BCLoopStart) ins);

			// get the loop iteration

			int loopIter = CalculateLoop.allocInIter(body, lStart);
			int upBndAfterLoop = 0;

			Vector loopStartTargeters = lStart.getTargeters();
			for (int j = 0; j < loopStartTargeters.size(); j++) {
				int upBndNext = memConsMeth(body,
						(BCInstruction) loopStartTargeters.elementAt(j));
				if (upBndNext > upBndAfterLoop) {
					upBndAfterLoop = upBndNext;
				}

			}
			UPPERBOUND = loopIter + upBndAfterLoop;
		} else {
			int currUpBnd = 0;
			/*
			 * if (ins.getPosition() == 30 ) { System.out.println("instruction
			 * with two targets"); }
			 */
			Vector targeters = ins.getTargeters();
			if (targeters == null) {
				UPPERBOUND = ins.alloc();
			}
			for (int j = 0; j < targeters.size(); j++) {
				currUpBnd = ins.alloc()
						+ memConsMeth(body, (BCInstruction) targeters
								.elementAt(j));
				if (currUpBnd > UPPERBOUND) {
					UPPERBOUND = currUpBnd;
				}
			}
		}
		return UPPERBOUND;
	}
}
