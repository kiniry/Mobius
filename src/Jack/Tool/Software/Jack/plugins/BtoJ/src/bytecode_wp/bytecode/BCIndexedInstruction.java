/*
 * Created on Apr 6, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode;


/**
 * @author mpavlova
 *
 * Denote entity that refers to an index intyot the consstantpool CPInstruction, etc.
 */
public interface BCIndexedInstruction  extends BCTypedInstruction {

	public void setIndex(int index ) ;
	
	/**
	 * @return the index in the constant pool
	 */
	public int getIndex() ;
	
}
