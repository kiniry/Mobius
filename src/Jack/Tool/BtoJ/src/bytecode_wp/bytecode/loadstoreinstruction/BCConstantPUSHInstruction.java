/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.loadstoreinstruction;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.ConstantPushInstruction;
import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.bytecode.BCTypedInstruction;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 * 
 * Denotes a push instruction that produces a literal on the stack : BIPUSH,
 * DCONST, FCONST, ICONST, LCONST, SIPUSH
 */
public class BCConstantPUSHInstruction extends BCInstruction implements
		BCTypedInstruction {
	// BIPUSH, DCONST, FCONST, ICONST, LCONST, SIPUSH
	private NumberLiteral value;

	private JavaType type;

	/**
	 * @param _instruction
	 */
	public BCConstantPUSHInstruction(InstructionHandle _instruction) {
		super(_instruction);
		ConstantPushInstruction cp = (ConstantPushInstruction) _instruction
				.getInstruction();
		value = new NumberLiteral(cp.getValue().intValue());
		return;
	}

	public NumberLiteral getValue() {
		return value;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return type;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	 */
	public void setType(JavaType _type) {
		type = _type;
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
		/* Util.dump("in wp i_constant " + _normal_Postcondition ); */
		wp = (Formula) _normal_Postcondition.substitute(Expression.COUNTER,
				Expression.getCOUNTER_PLUS_1());
		/* Util.dump("iconst wp[counter <-- counter +1] " + wp); */

		wp = (Formula) wp.substitute(new Stack(Expression.getCOUNTER_PLUS_1()),
				getValue());
		// Util.dump("iconst " + wp);
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_PLUS_1());
		vcs.substitute(new Stack(Expression.getCOUNTER_PLUS_1()), getValue());
		// Util.dump("iconst " + wp);
		return vcs;
	}
}
