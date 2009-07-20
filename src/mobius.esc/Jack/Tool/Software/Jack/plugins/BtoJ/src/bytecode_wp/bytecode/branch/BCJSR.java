/*
 * Created on Mar 1, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.branch;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bytecode.block.ControlFlowGraph;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 *
 *  jump to subroutione
 * 
 *wp (psi^n, psi^e) = psi^n
 */
public class BCJSR extends  BCJumpInstruction {

	 private ControlFlowGraph trace;
	
	/**
	 * @param _branchInstruction
	 */
	public BCJSR(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
	}
	
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		return null;
/*		int subRtPos = getTargetPosition();
		
		Formula wp = trace.getWpForSubrotineAt(config, subRtPos , _normal_Postcondition );
		return wp;*/
	}

	public void setTrace(ControlFlowGraph _trace) {
		trace = _trace;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		int subRtPos = getTargetPosition();
		
		VCGPath wp = trace.getWpForSubrotineAt(config, subRtPos , vcs );
		return wp;
	}
}
