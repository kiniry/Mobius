package bytecode.loadstoreinstruction;

import org.apache.bcel.generic.InstructionHandle;

import bcclass.BCLocalVariable;
import bcexpression.javatype.JavaType;
import bytecode.BCIndexedInstruction;
import bytecode.BCInstruction;

/**
 * @author Mariela
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public abstract class  BCLocalVariableInstruction extends BCInstruction implements  BCIndexedInstruction {
	/**
	 * index in the local variable table that contains the local variable incremented by this instruction 
	 */
	private int index;
	
	/**
	 * the type of  the local variable is returned
	 */
	private JavaType type;
	
	public BCLocalVariableInstruction(InstructionHandle _instruction, BCLocalVariable _lv) {
		 super(_instruction);
		 setIndex(_lv.getIndex());
		
	}
	
	/**
	 * @see bytecode.BCLocalVariableInstruction#setIndex(int)
	 */
	public void setIndex(int _index) {
		index = _index;
	}
	
	/**
	 * returns the index of the local variable that this instructiction treats
	 * @return int
	 */
	public int getIndex()  {
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
		type = _type;
	}
	
	

}
