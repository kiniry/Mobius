package annot.bcexpression.javatype;

import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.Type;

public class JavaObjectType extends JavaReferenceType {
	
	/**
	 * @param _type
	 * this constructor is for default reference types as the String class 
	 * */
	protected JavaObjectType(ObjectType _type) {
		super(_type);
	}
	
//	
//	
//	/**
//	 * @param _type
//	 */
//	protected JavaObjectType(Class _class) {
//		this((ObjectType)Type.getType(_class));
//	}
//	
//	
//	/**
//	 * _type1 <: _type2 ==> return  true else return false
//	 *  else return false
//	 * @param _type1
//	 * @param _type2
//	 * @return
//	 */
//	public static boolean subType(JavaObjectType  _type1, JavaObjectType  _type2) {
//		if ( _type1 == _type2) {
//			return true;
//		}
//		return ((ObjectType)_type1.getBcelType()).subclassOf((ObjectType)_type2.getBcelType());
//   }
}
