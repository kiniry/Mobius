/*
 * Created on Mar 25, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression.javatype;

import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.Type;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class JavaBasicType extends JavaType  {
	private int virtualCPindex ; 
	/**
	 * @param _type
	 */
	public JavaBasicType(BasicType _type ) {
		super(_type);
	}
	
	/**
	 * @param _type
	 */
	public JavaBasicType(Class _class) {
		this((BasicType)Type.getType(_class));
	}

}
