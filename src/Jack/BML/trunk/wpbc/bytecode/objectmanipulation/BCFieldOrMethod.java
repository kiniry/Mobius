/*
 * Created on Apr 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.objectmanipulation;

import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.InstructionHandle;

import bcclass.BCConstantPool;
import bcexpression.javatype.JavaType;
import bytecode.BCExceptionThrower;
import bytecode.BCTypedInstruction;

/**
 * @author mpavlova
 */
public  abstract class BCFieldOrMethod
	extends BCExceptionThrower
	implements BCCPInstruction, BCTypedInstruction {
		
	private BCConstantPool cp;
	/**
	 * index into the constant pool that represents a CONSTANT_fieldref_info  or CONSTANT_methodref_info  structure
	 */	
	private int index;
	
	/**
	 * index 	 into the constant pool that represents a  CONSTANT_class_info structure
	 */
	private int classIndex;
	
	private JavaType type;

	/** the class where the field or method is declared */
	private JavaType classType;

	/**
	 * @param _instruction
	 */
	public BCFieldOrMethod(
		InstructionHandle _instruction,
		JavaType _type,
		JavaType _classType,
		BCConstantPool _cp) {
			
		super(_instruction);
		setIndex(((CPInstruction) _instruction.getInstruction()).getIndex());
		setType(_type);
		classType = _classType;
		cp  = _cp;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCIndexedInstruction#getIndex()
	 */
	public int getIndex() {
		return index;
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

	/**
	 * @return the class where the field is declared
	 */
	public JavaType getClassType() {
		return classType;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCIndexedInstruction#setIndex(int)
	 */
	public void setIndex(int index) {
		// TODO Auto-generated method stub
		
	}
	
	public BCConstantPool getConstantPool() {
		return cp;
	}


}
