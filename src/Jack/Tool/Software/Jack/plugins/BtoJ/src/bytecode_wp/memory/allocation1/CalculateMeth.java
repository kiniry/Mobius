package bytecode_wp.memory.allocation1;



import java.util.Vector;

import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.bytecode.BCLoopEnd;
import bytecode_wp.bytecode.BCLoopStart;
import bytecode_wp.bytecode.BCTypeRETURN;
import bytecode_wp.bytecode.EntryPoint;
import bytecode_wp.utils.Util;


public class CalculateMeth {
	public static int memConsMeth( BCInstruction[] body, EntryPoint ep) {

		int upBnd = 0;
		
		for (int i = 0; i <  body.length; i++ ) {
			BCInstruction instr = (BCInstruction )body[i];
			int consum = 0;
			if (instr instanceof BCTypeRETURN) {
				consum = allocPathEndReturn(body, instr, ep );
			}
			if (consum > upBnd) {
				upBnd= consum;
			}
		}
		return upBnd;
		
	}

	private static int allocPathEndReturn(BCInstruction[] body,BCInstruction current, EntryPoint ep) {
		if ( current == ep ) {
			   return 0;
		   }
		   Vector targeters = null;
		   int max = 0;
		   
		   
		   // the amount that the current instruction allocates
		   int currentAlloc = 0;
		   if ( current instanceof BCLoopEnd) {
			   // get the loop entry
			   BCLoopEnd wr = ((BCLoopEnd) current);
			   int loopEntryInd = wr.getLoopEntry();
			   BCLoopStart lStart = (BCLoopStart)Util.getBCInstructionAtPosition( body, loopEntryInd);
			   
			   // get the targeters of the loop entry and continue from them
			   targeters = lStart.getTargeters();
			   // get the loop iteration
			   currentAlloc = CalculateLoop.allocInIter(body, lStart);
			   
		   } else if ( current instanceof BCLoopStart) {
			   		// in case the current insrtuction is a loop start
				   targeters = current.getTargeters();
				   currentAlloc = CalculateLoop.allocInIter(body, (BCLoopStart)current);
			   
		   } else {
			   targeters = current.getTargeters();
			   currentAlloc = current.alloc();
		   } 
		   if (targeters == null) {
			   return max;
		   }
		   for (int i = 0; i < targeters.size(); i++ ) {
			   BCInstruction prev = (BCInstruction ) targeters.elementAt(i);
			   int consum = current.alloc() +  allocPathEndReturn(body, prev, ep );
			   if (consum > max) {
					max = consum;
			   }
		   }
			return max;
		   
	}
}
	
	
	
	

	
	
	
	
	
