/*
 * Created on Apr 20, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.loadstoreinstruction;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.bytecode.BCTypedInstruction;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCACONST_NULL extends BCInstruction implements BCTypedInstruction {

	/**
	 * @param _instruction
	 */
	public BCACONST_NULL(InstructionHandle _instruction) {
		super(_instruction);
		setType(JavaType.JavaNULL);
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
		// Stack topStack_plus_1 = new Stack(Expression.COUNTER_PLUS_1);
		wp = (Formula) wp.substitute(new Stack(Expression.getCOUNTER_PLUS_1()),
				Expression._NULL);
		return wp;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return JavaType.JavaNULL;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	 */
	public void setType(JavaType _type) {
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		Formula wp;

		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_PLUS_1());
		// Stack topStack_plus_1 = new Stack(Expression.COUNTER_PLUS_1);
		vcs.substitute(new Stack(Expression.getCOUNTER_PLUS_1()),
				Expression._NULL);
		return vcs;
	}
}
