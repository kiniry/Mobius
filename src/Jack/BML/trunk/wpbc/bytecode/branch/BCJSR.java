/*
 * Created on Mar 1, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.branch;

import org.apache.bcel.generic.InstructionHandle;

import bcclass.attributes.ExsuresTable;
import bytecode.BCInstruction;
import bytecode.BCRET;
import bytecode.block.Block;
import bytecode.block.Trace;
import bytecode.exception.IllBlockException;

import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCJSR extends  BCUnconditionalBranch {

	/**
	 * @param _branchInstruction
	 */
	public BCJSR(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
	}
	
//	public void setTargetBlock(Trace _trace)  {
//		Block _b = null;
//		BCInstruction last = getTarget();
//		while (last != null ) {
//			if (last instanceof  BCRET) {
//				break;
//			}
//			last = last.getNext();
//		}
//		
///*		if ( last == null) {
//			throw new  IllBlockException("jsr " + getPosition() + "jumps to subroutine without ret in the end ");
//		}*/
//		_b = _trace.getBlockStartingAtEndingAt(getTarget(), last );
//		if ( _b == null) {
//			_b = new Block( getTarget(), last);
//			_trace.addBlock(_b);
//		}
//		targetBlock = _b;
//		
//	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		Block subroutine = getTargetBlock();
		
		// the wp for the jsr instruction is the wp of the block that represents the subroutine
		wp = subroutine.wp( _normal_Postcondition, _exc_Postcondition);
		return wp;
	}

}
