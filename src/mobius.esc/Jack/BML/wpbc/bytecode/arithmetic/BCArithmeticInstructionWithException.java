/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.arithmetic;

import org.apache.bcel.generic.InstructionHandle;

import bcexpression.javatype.ClassNames;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;
import bytecode.BCExceptionThrower;
import bytecode.BCTypedInstruction;




/**
 * @author mpavlova
 *this class represents arithmetic instructions that throw exceptions ,i.e. IDIV, IREM, LDIV and LREM
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract class BCArithmeticInstructionWithException extends BCExceptionThrower implements BCTypedInstruction {
	//IDIV, IREM, LDIV,LREM
	
	private JavaType type;
	
	private byte arithmOperation;
	

	
	/**
	 * @param _instruction
	 * @param _type
	 */
	public BCArithmeticInstructionWithException(InstructionHandle _instruction, JavaType _type) {
		super(_instruction);
		setType(_type);
		setExceptionsThrown( new JavaObjectType[]{ (JavaObjectType)JavaObjectType.getJavaRefType( ClassNames.ARITHMETICException) });
	}

	public  void setArithmeticOperation(byte _op) {
		arithmOperation = _op;
	}

	public int getArithmeticOperation() {
		return arithmOperation;
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




	
	

}
