/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.arithmetic;

import org.apache.bcel.generic.InstructionHandle;

import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.bytecode.BCTypedInstruction;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract   class BCArithmeticInstruction extends BCInstruction implements BCTypedInstruction  {
	//DADD, DDIV, DMUL, DNEG, DREM, DSUB, FADD, FDIV, FMUL, FNEG, FREM, FSUB, IADD, IAND, IMUL, INEG, 
	//IOR, ISHL, ISHR, ISUB, IUSHR, IXOR, LADD, LAND, LMUL, LNEG, LOR,  LSHL, LSHR, LSUB, LUSHR, LXOR
	
	private JavaType type;
	private int arithmOperation; 
	
	/**
	 * @param _instruction
	 */
	public BCArithmeticInstruction(InstructionHandle _instruction, JavaType _type) {
		super(_instruction);
		setType(_type);
		
	}
	
	public  void setArithmeticOperation(int _op) {
		arithmOperation = _op;
	}
	
	public int getArithmeticOperation() {
		return arithmOperation;
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
	
	
}
