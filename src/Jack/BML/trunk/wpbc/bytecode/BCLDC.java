/*
 * Created on Apr 6, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.InstructionHandle;

import specification.ExceptionalPostcondition;
import bcexpression.javatype.JavaType;
import formula.Formula;

/**
 * @author mpavlova
 *
 *  Push item from constant pool - LDC , LDC_W
 */
public class BCLDC extends BCExceptionThrower implements BCCPInstruction {
	private int index;
	private JavaType type;
	/**
	 * @param _instruction
	 */
	public BCLDC(InstructionHandle _instruction, JavaType _type ) {
		super(_instruction);
		setIndex( ( (CPInstruction)_instruction.getInstruction()).getIndex());
	    setType(_type);
	}

	/* (non-Javadoc)
	 * @see bytecode.BCIndexedInstruction#setIndex(int)
	 */
	public void setIndex(int _index) {
		index = _index;
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
		type =_type;
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition) {
		// TODO Auto-generated method stub
		return null;
	}

}
