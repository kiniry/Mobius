/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import org.apache.bcel.generic.InstructionHandle;
import specification.ExceptionalPostcondition;
import bcexpression.javatype.JavaType;
import formula.Formula;

/**
 * @author mpavlova
 *
 * comparison of values of the same basic type
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCTypeCMPPredicate extends BCInstruction implements BCTypedInstruction {
	private JavaType type;
	/**
	 * @param _instruction
	 */
	public BCTypeCMPPredicate(InstructionHandle _instruction, JavaType _type) {
		super(_instruction);
		setType(_type);
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return type;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType(org.apache.bcel.generic.TypedInstruction, org.apache.bcel.generic.ConstantPoolGen)
	 */
	public void setType(JavaType _type) {
		type = _type;
		
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition) {
		// TODO Auto-generated method stub
		return null;
	}

}
