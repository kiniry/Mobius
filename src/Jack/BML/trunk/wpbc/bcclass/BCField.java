/*
 * Created on Mar 4, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass;

import org.apache.bcel.classfile.Field;

import bcexpression.javatype.JavaType;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCField extends AccessFlags {
	private String name;
	private JavaType type;
	
	public BCField(Field f) {
		super(f.getAccessFlags() );
		name = f.getName();
		type = JavaType.getJavaType(f.getType());	 
	}
		
	public String getName( ) {
		return name;
	}
	
	public JavaType getType() {
		return type;
	}

	/**
	 * @return
	 */
	public boolean isVisible() {
		
		return isPublic() || isProtected();
	}
}
