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
	public JavaObjectType(ObjectType _type) {
		super(_type);
	}
	
	/**
	 * @param _type
	 */
	public JavaObjectType(ObjectType _type, BCConstantClass _cc) {
		super(_type, _cc);
	}
	
	/**
	 * @param _type
	 */
	public JavaObjectType(Class _class, BCConstantClass _cc) {
		this((ObjectType)Type.getType(_class), _cc);
	}
	
	public boolean subclassOf(JavaObjectType  _ot) {
	   return ((ObjectType)bcelType).subclassOf((ObjectType)_ot.bcelType);
   }

}
