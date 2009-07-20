/*
 * Created on 17 mars 2004
 *
 */
package bcexpression.javatype;

import java.util.HashMap;

import org.apache.bcel.generic.ArrayType;

import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.Type;

import constants.BCConstantClass;

import bcexpression.Expression;
import bcexpression.NumberLiteral;
import bcexpression.jml.JML_CONST_TYPE;


/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class JavaType extends Expression  {
	protected Type bcelType; //still keeping reference to the bcel type object

	public JavaType() {
	}
	
	/**
	 * this is a static variable that representing the type of all types 
	 */
//	private static final JML_CONST_TYPE  JML_CONST_TYPE = new JML_CONST_TYPE();
	/*private BCConstantClass constantClassCp;*/
	private NumberLiteral computationalType;

	//	(computational type1 : boolean, byte, char, short, int, float(not considered in this application) , reference, returnAddress)
	public static final NumberLiteral COMPUTATIONAL_TYPE_1 = new NumberLiteral(0);

	//	(computational type2: long, double (not considered in this application) )
	public static final NumberLiteral COMPUTATIONAL_TYPE_2 = new NumberLiteral(1);

	public static final JavaBasicType JavaBYTE =
		new JavaBasicType(Type.BYTE, COMPUTATIONAL_TYPE_1);
	public static final JavaBasicType JavaSHORT =
		new JavaBasicType(Type.SHORT, COMPUTATIONAL_TYPE_1);
	public static final JavaBasicType JavaINT =
		new JavaBasicType(Type.INT, COMPUTATIONAL_TYPE_1);
	public static final JavaBasicType JavaLONG =
		new JavaBasicType(Type.LONG, COMPUTATIONAL_TYPE_2);
	//	public static final JavaBasicType  JavaFLOAT = new JavaBasicType(Type.FLOAT);
	//	public static final JavaBasicType  JavaDOUBLE = new JavaBasicType(Type.DOUBLE);
	public static final JavaBasicType JavaBOOLEAN =
		new JavaBasicType(Type.BOOLEAN, COMPUTATIONAL_TYPE_1);
	public static final JavaObjectType JavaSTRING =
		new JavaObjectType(Type.STRING);
	public static final JavaBasicType JavaCHAR =
		new JavaBasicType(Type.CHAR, COMPUTATIONAL_TYPE_1);
	public static final JavaBasicType JavaVOID =
		new JavaBasicType(Type.VOID, COMPUTATIONAL_TYPE_1);
	public static final JavaReferenceType JavaNULL =
		new JavaReferenceType(Type.NULL);

	private static HashMap loadedTypes;

	protected JavaType(Type _type, NumberLiteral _compType) {
		bcelType = _type;
		computationalType = _compType;
	}


	public String getSignature() {
		String signature =bcelType.getSignature();
		return signature;
	}

	/**
	 * return  JML_CONST_TYPE;
	 */
	public Expression getType() {
		return JML_CONST_TYPE.JML_CONST_TYPE;
	}

	public static JavaType getJavaType(String typeName) {
		JavaType _jt = getJavaBasicType(typeName);
		if (_jt != null) {
			return _jt;
		}
		return getJavaRefType(typeName);
	}
	
	public static JavaType getJavaType(Type _type) {
		JavaType _jt = getJavaBasicType(_type);
		if (_jt != null) {
			return _jt;
		}
		return getJavaRefType(_type);
	}

	public static JavaType getJavaBasicType(Type _type) {
		if (_type == Type.BOOLEAN) {
			return JavaBOOLEAN;
		} else if (_type == Type.BYTE) {
			return JavaBYTE;
		} else if (_type == Type.CHAR) {
			return JavaCHAR;
		} else
			//		 if (_type == Type.DOUBLE) {
			//			return JavaDOUBLE;
			//		} else
			//		 if (_type == Type.FLOAT) {
			//			return JavaFLOAT;
			//		} else
			if (_type == Type.INT) {
				return JavaINT;
			} else if (_type == Type.LONG) {
				return JavaLONG;
			} else if (_type == Type.SHORT) {
				return JavaSHORT;
			} else if (_type == Type.VOID) {
				return JavaVOID;
			}
		return null;
	}

	public static JavaBasicType getJavaBasicType(String _baseType) {
		if (_baseType.equals("Z")) {
			return JavaBOOLEAN;
		} else if (_baseType.equals("B")) {
			return JavaBYTE;
		} else if (_baseType.equals("C")) {
			return JavaCHAR;
		} else
			//		if (_baseType == BaseTypeCharacters.D) {
			//			return JavaDOUBLE;
			//		} else
			//		if (_baseType == BaseTypeCharacters.F) {
			//			return JavaFLOAT;
			//		} else
			if (_baseType.equals("I")) {
				return JavaINT;
			} else if (_baseType.equals("L")) {
				return JavaLONG;
			} else if (_baseType.equals("S")) {
				return JavaSHORT;
			} else if (_baseType.equals("V")) {
				return JavaVOID;
			}
		return null;
	}

	public static JavaReferenceType getJavaRefType(Type _type) {
		return getJavaRefType(_type.getSignature());
	}
	
	public static JavaArrType getJavaArrTypeWithBasicType(JavaType type ) {
		String sig = type.getSignature();
		String arrSig = "[" +sig;
		JavaArrType arrType = (JavaArrType)getJavaRefType(arrSig);
		if (arrType != null ) {
			return arrType;
		}
		return new JavaArrType(type);
	}

	/**
	 * 
	 * @param _signature - must be of the form for example Ljava/lang/String;
	 * 	or [[[Ljava/lang/String;
	 * @return an object representing this type 
	 */
	public static JavaReferenceType getJavaRefType(String _signature) {
		_signature = _signature.replace('.', '/');
		if ((!_signature.startsWith("L")) &&  (!_signature.startsWith("["))) {
			_signature =  "L".concat(_signature);
		}
		if (!_signature.endsWith(";")) {
			_signature =  _signature.concat(";");
		}
		if (_signature.equals("Ljava/lang/String;")) {
			return JavaSTRING;
		}
		//
		if (loadedTypes == null) {
			loadedTypes = new HashMap();
		}
		JavaReferenceType _jt = null;
		if ((_jt = (JavaReferenceType) loadedTypes.get(_signature)) != null) {
			return _jt;
		}
		Type _t = Type.getType(_signature);
		if (_t instanceof ObjectType) {
			_jt = new JavaObjectType((ObjectType) _t);
		} else if (_t instanceof ArrayType) {
			_jt = new JavaArrType((ArrayType) _t);
		}
		loadedTypes.put(_jt.getSignature(), _jt);
		return _jt;
	}

//	/**
//	 * 
//	 * @param _class_name String that represents a valid java class name , i.e. java.lang.String. Only classes are stored here
//	 * @return
//	 */
//	public static JavaReferenceType getJavaRefType(
//		Integer _cpIndex,
//		ConstantPoolGen _cpg) {
//		JavaReferenceType _jt = null;
//		ConstantClass _cc =
//			(ConstantClass) _cpg.getConstant(_cpIndex.intValue());
//		//		BCConstantClass bcc = new BCConstantClass(_cc , _cpIndex.intValue());
//		//		Type _bcelt = Type.getType(_cc.getBytes(_cpg.getConstantPool()));
//		_jt = getJavaRefType(_cc.getBytes(_cpg.getConstantPool()));
//		//_jt.setBCConstantClass(bcc);
//		return _jt;
//	}

	public NumberLiteral getComputationalType() {
		return computationalType;
	}
	
	/**
	 * checks if _type1 is a subtype of _type2
	 * @param _type1
	 * @param _type2
	 * @return
	 */
	public static boolean subType(JavaType _type1 , JavaType _type2 ) {
		if ((_type1 instanceof JavaBasicType) && (_type2 instanceof JavaBasicType)) {
			return JavaBasicType.subType((JavaBasicType)_type1, (JavaBasicType)_type2);
		}
		if ((_type1 instanceof JavaObjectType) && (_type2 instanceof JavaObjectType)) {
			return JavaArrType.subType((JavaObjectType)_type1, (JavaObjectType)_type2);
		}
		if ((_type1 instanceof JavaArrType) && (_type2 instanceof JavaArrType)) {
			return JavaArrType.subType((JavaArrType)_type1, (JavaArrType)_type2);
		}
		return false;
	}
	
	public Expression substitute(Expression _e1 , Expression _e2) { 
		return this;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		if (this == JavaReferenceType.ReferenceType  ) {
			return "ReferenceType";
		} 
		return getSignature();
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		return this;
	}
	
	
}
