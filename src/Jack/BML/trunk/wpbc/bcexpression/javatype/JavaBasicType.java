/*
 * Created on Mar 25, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression.javatype;

import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.Type;

import bcexpression.NumberLiteral;

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
	protected JavaBasicType(BasicType _type, NumberLiteral _compType ) {
		super(_type, _compType);
	}
	
	/**
	 * @param _type
	 */
	protected JavaBasicType(Class _class, NumberLiteral _compType) {
		this((BasicType)Type.getType(_class), _compType);
	}

	public static boolean subType(JavaBasicType _type1 , JavaBasicType _type2 ) {
		if ((_type2 == JavaType.JavaSHORT )&&( _type1 == JavaType.JavaBYTE)) {
			return true;
		}
		if ((_type2 == JavaType.JavaINT )&&( _type1 == JavaType.JavaBYTE)) {
			return true;
		}
		if ((_type2 == JavaType.JavaINT )&&( _type1 == JavaType.JavaSHORT)) {
			return true;
		}
		
		return false;
	}
	
		
}
