package bytecode_wp.bytecode;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;

import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;



/**
 * @author Mariela
 *	nop
 *
 * do nothing
 */
public class BCNOP extends BCInstruction {
	
	public BCNOP(InstructionHandle  _instruction) {
		super(_instruction);
	}

	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		return  _normal_Postcondition ;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		
		return vcs;
	}

	

}
