/*
 * Created on Apr 21, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.stackinstruction;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;

import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 *
 * pop
 * 
 * Operation:  Pop the top operand stack value
 *
 *  Format :  pop 	
 *
 *  Operand Stack : ..., value ==> ...
 *
 *  Description: Pop the top value from the operand stack. 
 *   The pop instruction must not be used unless value is a value of a category 1 computational type 
 *    (we consider only types of  computational type 1)
 * 
 *   wp = psi^n[t <-- t-1]
 */

public class BCPOP  extends BCInstruction implements BCStackInstruction{

	/**
	 * @param _instruction
	 */
	public BCPOP(InstructionHandle _instruction) {
		super(_instruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		wp = (Formula)_normal_Postcondition.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		
		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		
		return vcs;
	}

}
