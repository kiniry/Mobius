/*
 * Created on 19 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.type;

import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.Type;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class JavaTypeFactory {
	
	private static JavaTypeFactory typeFactory = null;
	
	private JavaTypeFactory() {
		
	}
	
	public static JavaTypeFactory getJavaTypeFactory() {
		if (typeFactory != null) {
			return typeFactory;			
		}
		typeFactory = new JavaTypeFactory();
		return typeFactory;
	}

	public JavaType getJavaType(Class type) {
			JavaType _t = null;
			Type _type = Type.getType(type);
			 if (_type instanceof ArrayType) {
				_t = getJavaArrType((ArrayType)_type);
			} else if (_type instanceof  ObjectType) {
				_t = getObjectType((ObjectType)_type);
			} else if (_type instanceof Type) {
				_t = getType(_type);
			} 
			return _t;	
		
		}

	/**
	 * @param type
	 * @return
	 */
	private JavaObjectType getObjectType(ObjectType _type) {
		JavaObjectType _t = new JavaObjectType(_type);
		return _t;
	}

	public JavaType getJavaType(Type _type) {
		JavaType _t = null;
		if (_type instanceof Type) {
			_t = getType(_type);
		} else if (_type instanceof ArrayType) {
			_t = getJavaArrType((ArrayType)_type);
		}
		return _t;	
		
	}
	
	private JavaType getType(Type _type ) {
		JavaType _jt = new JavaType(_type);
		return _jt;
	}
	
	private JavaArrType getJavaArrType(ArrayType _type ) {
		JavaArrType _jt = new JavaArrType(_type);
		return _jt;
	}
	
}
