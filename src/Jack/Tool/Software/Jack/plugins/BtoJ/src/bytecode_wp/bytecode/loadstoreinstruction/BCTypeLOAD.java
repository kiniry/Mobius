/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.loadstoreinstruction;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.BCLocalVariable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.formula.Formula;
import bytecode_wp.utils.Util;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 * 
 * Operation: Load value of the corresponding type from local variable
 * 
 * Operand Stack : ... ==> ..., objectref
 * 
 * Description: The index is an unsigned byte that must be an index into the
 * local variable array of the current frame. The local variable at index must
 * contain a reference. The objectref in the local variable at index is pushed
 * onto the operand stack.
 * 
 * wp = psi^n[t <-- t +1][S(t+1) <-- local(i)]
 */
public class BCTypeLOAD extends BCLocalVariableInstruction {
	// ALOAD, ILOAD, LLOAD

	/**
	 * @param _instruction
	 */
	public BCTypeLOAD(InstructionHandle _instruction, BCLocalVariable _lv) {
		super(_instruction, _lv);
		setType((JavaType) _lv.getType());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.ByteCode#wp(formula.Formula,
	 *      specification.ExceptionalPostcondition)
	 */
	public Formula wp(IJml2bConfiguration config,
			Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		wp = (Formula) _normal_Postcondition.substitute(Expression.COUNTER,
				Expression.getCOUNTER_PLUS_1());
		wp = (Formula) wp.substitute(new Stack(Expression.getCOUNTER_PLUS_1()),
				getLocalVariable());
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {

/*		if (getPosition() == 63) {
			Logger.get().println("coucou");
			vcs.toStringHyps(); 
			vcs.toStringGoals();
		}*/
		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_PLUS_1());
		vcs.substitute(new Stack(Expression.getCOUNTER_PLUS_1()),
				getLocalVariable());
		return vcs;
	}

}
