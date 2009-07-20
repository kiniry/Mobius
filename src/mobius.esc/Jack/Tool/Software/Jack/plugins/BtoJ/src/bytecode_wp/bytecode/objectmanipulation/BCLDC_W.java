/*
 * Created on Apr 6, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.objectmanipulation;

import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.InstructionHandle;

import bytecode_wp.bcclass.BCConstantPool;
import bytecode_wp.bcexpression.javatype.JavaType;


public class BCLDC_W extends BCLDC {
	private int index;
	private JavaType type;

	/**
	 * @param _instruction
	 */
	public BCLDC_W(
		InstructionHandle _instruction,
		JavaType _type,
		BCConstantPool _cp) {
		super(_instruction, _type, _cp);
		setIndex(((CPInstruction) _instruction.getInstruction()).getIndex());
		setType(_type);
	}

	//	/* (non-Javadoc)
	//	 * @see bytecode.BCIndexedInstruction#setIndex(int)
	//	 */
	//	public void setIndex(int _index) {
	//		index = _index;
	//	}
	//
	//	/* (non-Javadoc)
	//	 * @see bytecode.BCIndexedInstruction#getIndex()
	//	 */
	//	public int getIndex() {
	//		return index;
	//	}
	//
	//	/* (non-Javadoc)
	//	 * @see bytecode.BCTypedInstruction#getType()
	//	 */
	//	public JavaType getType() {
	//		return type;
	//	}
	//
	//	/* (non-Javadoc)
	//	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	//	 */
	//	public void setType(JavaType _type) {
	//		type =_type;
	//	}
	//
	//
	//	public Formula wp(Formula _normal_Postcondition, Exsures _exc_Postcondition) {
	//
	//		return null;
	//	}

}
