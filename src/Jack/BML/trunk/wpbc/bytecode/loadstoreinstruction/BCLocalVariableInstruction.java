package bytecode.loadstoreinstruction;

import org.apache.bcel.generic.InstructionHandle;

import bcexpression.BCLocalVariable;
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
	
	private BCLocalVariable localVariable;
	/**
	 * the type of  the local variable is returned
	 */
	private JavaType type;
	
	public BCLocalVariableInstruction(InstructionHandle _instruction, BCLocalVariable _lv) {
		 super(_instruction);
		 localVariable = _lv;
	}
	
	/**
	 * @see bytecode.BCLocalVariableInstruction#setIndex(int)
	 */
	public void setIndex(int _index) {
		
	}
	
	/**
	 * returns the index of the local variable that this instructiction treats
	 * @return int
	 */
	public int getIndex()  {
		return localVariable.getIndex();
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
	 * @return Returns the localVariable.
	 */
	public BCLocalVariable getLocalVariable() {
		return localVariable;
	}
}
