package bytecode.localvarinstruction;

import bytecode.BCIndexedInstruction;

/**
 * @author Mariela
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public interface BCLocalVariableInstruction extends BCIndexedInstruction {
	/**
	 * sets the index of the local variable that this instructions deals with
	 * @param index
	 */
	public void setIndex(int index);
	
	/**
	 * returns the index of the local variable that this instructiction treats
	 * @return int
	 */
	public int getIndex();
}
