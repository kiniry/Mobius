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
 *this class represents arithmetic instructions that throw exceptions ,i.e. IDIV, IREM, LDIV and LREM
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCArithmeticInstructionWithException extends BCExceptionThrower implements BCTypedInstruction {
	//IDIV, IREM, LDIV,LREM
	
	private JavaType type;
	/**
	 * @param _instruction
	 * @param _type
	 */
	public BCArithmeticInstructionWithException(InstructionHandle _instruction, JavaType _type) {
		super(_instruction);
		setType(_type);
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType( ) {
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
		
		return null;
	}

}
