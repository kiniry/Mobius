/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.localvarinstruction;

import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LocalVariableInstruction;

import bcexpression.javatype.JavaType;
import bytecode.BCInstruction;

import specification.ExceptionalPostcondition;
import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public  class BCTypeLOAD  extends BCInstruction implements BCLocalVariableInstruction{
	//ALOAD, DLOAD, FLOAD, ILOAD, LLOAD 
	/**
	 * index of local variable 
	 */
	private int index ;
	/**
	 * @param _instruction
	 */
	public BCTypeLOAD(InstructionHandle _instruction) {
		super(_instruction);
		setIndex(((LocalVariableInstruction)(_instruction.getInstruction())).getIndex());
		// TODO Auto-generated constructor stub
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition) {
		// TODO Auto-generated method stub
		return null;
	}
	/**
	 * @see bytecode.BCLocalVariableInstruction#BCLocalVariableInstruction()
	 */
	public void BCLocalVariableInstruction() {
	}
	/**
	 * @see bytecode.BCLocalVariableInstruction#setIndex(int)
	 */
	public void setIndex(int _index) {
		index = _index;
	}
	/**
	 * @see bytecode.BCLocalVariableInstruction#getIndex()
	 */
	public int getIndex() {
		return index;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	 */
	public void setType(JavaType _type) {
		// TODO Auto-generated method stub
		
	}

}
