/*
 * Created on 17 mars 2004
 *
 */
package bcexpression.javatype;

import java.util.HashMap;

import org.apache.bcel.classfile.ConstantClass;

import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.Type;

import constants.BCConstantClass;

import bcexpression.Expression;
import bcexpression.jml.JML_CONST_TYPE;
import type.BCType;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class JavaType extends Expression implements BCType {
	protected Type bcelType; //stil reference to the bcel type object

	/**
	 * this is a static variable that representing the type of all types 
	 */
	private static final JML_CONST_TYPE type = new JML_CONST_TYPE();
	private BCConstantClass constantClassCp;
	private byte computationalType;

	//	(computational type1 : boolean, byte, char, short, int, float(not considered in this application) , reference, returnAddress)
	public static final byte COMPUTATIONAL_TYPE_1 = 0;

	//	(computational type2: long, double (not considered in this application) )
	public static final byte COMPUTATIONAL_TYPE_2 = 1;

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

	public JavaType(Type _type, BCConstantClass _cc, byte _compType) {
		bcelType = _type;
		constantClassCp = _cc;
		computationalType = _compType;
		setType();
	}

	public JavaType(Type _type, byte _compType) {
		bcelType = _type;
		computationalType = _compType;
		setType();
	}

	/** 
	 * method does nothiong as the type is a static final variable
	 */
	public void setType() {
		//		if(type != null){
		//			return;
		//		}
		//		type = new JML_CONST_TYPE();
	}

	public String getSignature() {
		return bcelType.getSignature();
	}

	/**
	 * return  JML_CONST_TYPE;
	 */
	public BCType getType() {
		return type;
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

	public static JavaBasicType getJavaBasicType(int _baseType) {
		if (_baseType == BaseTypeCharacters.Z) {
			return JavaBOOLEAN;
		} else if (_baseType == BaseTypeCharacters.B) {
			return JavaBYTE;
		} else if (_baseType == BaseTypeCharacters.C) {
			return JavaCHAR;
		} else
			//		if (_baseType == BaseTypeCharacters.D) {
			//			return JavaDOUBLE;
			//		} else
			//		if (_baseType == BaseTypeCharacters.F) {
			//			return JavaFLOAT;
			//		} else
			if (_baseType == BaseTypeCharacters.I) {
				return JavaINT;
			} else if (_baseType == BaseTypeCharacters.L) {
				return JavaLONG;
			} else if (_baseType == BaseTypeCharacters.S) {
				return JavaSHORT;
			} else if (_baseType == BaseTypeCharacters.V) {
				return JavaVOID;
			}
		return null;
	}

	public static JavaReferenceType getJavaRefType(Type _type) {
		return getJavaRefType(_type.getSignature());
	}
	public static JavaReferenceType getJavaRefType(String _signature) {
		if (_signature.equals("java.lang.String")) {
			return JavaSTRING;
		}
		String signature = "L" + _signature.replace('.', '/') + ";";
		if (loadedTypes == null) {
			loadedTypes = new HashMap();
		}
		JavaReferenceType _jt = null;
		if ((_jt = (JavaReferenceType) loadedTypes.get(signature)) != null) {
			return _jt;
		}
		Type _t = Type.getType(signature);
		if (_t instanceof ObjectType) {
			_jt = new JavaObjectType((ObjectType) _t);
		} else if (_t instanceof ArrayType) {
			_jt = new JavaArrType((ArrayType) _t);
		}
		loadedTypes.put(_jt.getSignature(), _jt);
		return _jt;
	}

	/**
	 * 
	 * @param _class_name String that represents a valid java class name , i.e. java.lang.String. Only classes are stored here
		 * @return
	 */
	public static JavaReferenceType getJavaRefType(
		Integer _cpIndex,
		ConstantPoolGen _cpg) {
		JavaReferenceType _jt = null;
		ConstantClass _cc =
			(ConstantClass) _cpg.getConstant(_cpIndex.intValue());
		//		BCConstantClass bcc = new BCConstantClass(_cc , _cpIndex.intValue());
		//		Type _bcelt = Type.getType(_cc.getBytes(_cpg.getConstantPool()));
		_jt = getJavaRefType(_cc.getBytes(_cpg.getConstantPool()));
		//_jt.setBCConstantClass(bcc);
		return _jt;
	}

	public byte getComputationalType() {
		return computationalType;
	}

}
