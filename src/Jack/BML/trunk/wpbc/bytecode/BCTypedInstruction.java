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
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public interface BCTypedInstruction {

	public JavaType getType();
	public void setType(JavaType _type );
}
