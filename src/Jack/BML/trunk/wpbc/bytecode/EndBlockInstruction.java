/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode;

import formula.Formula;
import bcclass.attributes.ExsuresTable;
import bytecode.block.Block;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public interface EndBlockInstruction {
	
	
	
	/**
	 * sets the block where the end is this instruction
	 */
	public void setBlock(Block block);
	
	public Formula calculateRecursively(Formula  _normal_postcondition, ExsuresTable _exs_postcondition);
}
