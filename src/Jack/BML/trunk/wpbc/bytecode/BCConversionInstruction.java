/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import org.apache.bcel.generic.InstructionHandle;
import bcexpression.javatype.JavaType;
import specification.ExceptionalPostcondition;
import formula.Formula;

/**
 * @author mpavlova
 * Super class for the x2y family of instructions
 */
public class BCConversionInstruction  extends BCInstruction implements  BCTypedInstruction {

	private JavaType  type;
	/**
	 * @param _instruction
	 */
	public BCConversionInstruction(InstructionHandle _instruction) {
		super(_instruction);
		// TODO Auto-generated constructor stub
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
