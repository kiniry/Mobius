/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.loadstoreinstruction;

import org.apache.bcel.generic.ConstantPushInstruction;
import org.apache.bcel.generic.InstructionHandle;

import bcexpression.NumberLiteral;
import bcexpression.javatype.JavaType;
import bytecode.BCInstruction;
import bytecode.BCTypedInstruction;

/**
 * @author mpavlova
 *
 * Denotes a push instruction that produces a literal on the stack : BIPUSH, DCONST, FCONST, ICONST, LCONST, SIPUSH
 */
public abstract class BCConstantPUSHInstruction
	extends BCInstruction
	implements BCTypedInstruction {
	//    BIPUSH, DCONST, FCONST, ICONST, LCONST, SIPUSH

	private NumberLiteral value;
	
	private JavaType type;
	/**
	 * @param _instruction
	 */
	public BCConstantPUSHInstruction(InstructionHandle _instruction) {
		super(_instruction);
		ConstantPushInstruction cp =
			(ConstantPushInstruction) _instruction.getInstruction();
		value = new NumberLiteral(cp.getValue().intValue());
	}

	public NumberLiteral getValue() {
		return value;
	}

	/* (non-Javadoc)
		 * @see bytecode.BCTypedInstruction#getType()
		 */
	public JavaType getType() {
		return type;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	 */
	public void setType(JavaType _type) {
		type = _type;
	}

}
