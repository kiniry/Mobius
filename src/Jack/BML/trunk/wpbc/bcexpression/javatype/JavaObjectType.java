/*
 * Created on Mar 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression.javatype;

import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.Type;

import constants.BCConstantClass;


/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class JavaObjectType extends JavaReferenceType {

	
	/**
	 * @param _type
	 * this constructor is for default reference types as the String class 
	 * */
	protected JavaObjectType(ObjectType _type) {
		super(_type);
	}
	
	/**
	 * @param _type
	 */
	protected JavaObjectType(ObjectType _type, BCConstantClass _cc) {
		super(_type, _cc);
	}
	
	/**
	 * @param _type
	 */
	protected JavaObjectType(Class _class, BCConstantClass _cc) {
		this((ObjectType)Type.getType(_class), _cc);
	}
	
	public static boolean subType(JavaObjectType  _type1, JavaObjectType  _type2) {
	   return ((ObjectType)_type1.bcelType).subclassOf((ObjectType)_type2.bcelType);
   }

}
