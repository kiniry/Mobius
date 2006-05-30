package bytecode_wp.bytecode;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;

import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;



/**
 * instruction return
 */
public class BCTypeRETURN
	extends BCInstruction {
//	private Block blockEndingWithThis;

	/**
	 * @param _instruction
	 */
	public BCTypeRETURN(InstructionHandle _instruction) {
		super(_instruction);
	}



	public Formula wp(
		IJml2bConfiguration config,
		Formula _normal_postcondition, ExsuresTable _exs_postcondition) {
		Formula wp;
		Stack stackTop = new Stack(Expression.COUNTER);
		wp = (Formula)_normal_postcondition.substitute(Expression._RESULT, stackTop);
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		Stack stackTop = new Stack(Expression.COUNTER);
		vcs.substitute(Expression._RESULT, stackTop);
		return vcs;
	}


}
