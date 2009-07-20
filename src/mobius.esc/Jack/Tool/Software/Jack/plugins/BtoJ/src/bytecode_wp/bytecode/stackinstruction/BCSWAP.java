/*
 * Created on Apr 21, 2004
 *
 * 
 */
package bytecode_wp.bytecode.stackinstruction;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;

import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.DummyVariable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.Variable;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 *
 * swap
 *
 * Operation :    Swap the top two operand stack values
 *
 * Operand Stack
 *
 *  ..., value2, value1 ==> ..., value1, value2
 *
 * Description:  Swap the top two values on the operand stack. The swap instruction must not be used unless value1 and value2 are both values of a category 1 computational type (?3.11.1).
 *
 * wp = psi^n[ s(t) <-- x][ s(t -1) <-- s(t) ][ x <-- S(t-1)  ]
 * */ 
public class BCSWAP  extends BCInstruction implements BCStackInstruction {

	/**
	 * @param _instruction
	 */
	public BCSWAP(InstructionHandle _instruction) {
		super(_instruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp = null;
		
		Expression v = new DummyVariable();
		
		wp = (Formula)_normal_Postcondition.substitute(new Stack(Expression.COUNTER ) , v);
		wp = (Formula)wp.substitute(new Stack(Expression.getCOUNTER_MINUS_1() ), new Stack( Expression.COUNTER));
		wp = (Formula)wp.substitute( v, new Stack( Expression.getCOUNTER_MINUS_1()));
		return wp; 
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		Expression v = new DummyVariable();
		vcs.substitute(new Stack(Expression.COUNTER ) , v );
		vcs.substitute(new Stack(Expression.getCOUNTER_MINUS_1() ), new Stack( Expression.COUNTER));
		vcs.substitute( v, new Stack( Expression.getCOUNTER_MINUS_1()));
		return vcs; 
	} 

}
