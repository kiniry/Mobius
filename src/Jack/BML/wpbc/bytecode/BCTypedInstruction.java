package bytecode;


import bcexpression.javatype.JavaType;

/*
 * Created on Mar 31, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */

/**
 * @author mpavlova
 *
 *Get the type associated with an instruction, int for ILOAD, or the type of the field of a PUTFIELD instruction, e.g..
 *
 **/
public interface BCTypedInstruction {
	
	public JavaType getType();
	public void setType(JavaType _type );
}
