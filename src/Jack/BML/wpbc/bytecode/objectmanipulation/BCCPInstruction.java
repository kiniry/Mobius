/*
 * Created on Mar 31, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.objectmanipulation;


import bytecode.BCIndexedInstruction;

/**
 * @author mpavlova
 *
 * Abstract super class for instructions that use an index into the constant pool such as LDC, INVOKEVIRTUAL, etc.
 * the same as CPInstruction  in the bcel library
 */
public  interface BCCPInstruction  extends BCIndexedInstruction {
//	public BCConstantPool getConstantPool() ;
}
