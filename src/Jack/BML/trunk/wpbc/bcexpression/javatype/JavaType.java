/*
 * Created on 17 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.javatype;

import java.util.HashMap;

import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantPool;
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
public class JavaType  extends Expression   implements BCType {
	protected Type  bcelType;
	private JML_CONST_TYPE    oftype;
	private BCConstantClass constantClassCp;
	
	
	public static final JavaBasicType  JavaBYTE  = new JavaBasicType(Type.BYTE);
	public static final JavaBasicType  JavaSHORT  = new JavaBasicType(Type.SHORT);
	public static final JavaBasicType  JavaINT = new JavaBasicType(Type.INT);
	public static final JavaBasicType  JavaLONG = new JavaBasicType(Type.LONG);
	public static final JavaBasicType  JavaFLOAT = new JavaBasicType(Type.FLOAT);
	public static final JavaBasicType  JavaDOUBLE = new JavaBasicType(Type.DOUBLE);
	public static final JavaBasicType  JavaBOOLEAN = new JavaBasicType(Type.BOOLEAN);
	public static final JavaObjectType JavaSTRING = new JavaObjectType(Type.STRING);
	public static final JavaBasicType  JavaCHAR  = new JavaBasicType(Type.CHAR);
	public static final JavaBasicType  JavaVOID  = new JavaBasicType(Type.VOID);
	public static final JavaReferenceType  JavaNULL  = new JavaReferenceType(Type.NULL);

	private static HashMap loadedTypes;
	
	public JavaType(Type _type, BCConstantClass _cc )  {	
		bcelType = _type;
		constantClassCp = _cc;
		setType();
	}
	
	public JavaType(Type _type )  {	
		bcelType = _type;
		setType();
	}
	
	
	
	

	/* (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		if(oftype != null){
			return;
		}
		oftype = new JML_CONST_TYPE();
		
	}


	

	public String getSignature() {
		return bcelType.getSignature();
	}



	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		return oftype;
	}
	
	public static JavaType getJavaBasicType( Type _type) {
		if (_type == Type.BOOLEAN) {
			return JavaBOOLEAN;	
		} else if (_type == Type.BYTE) {
			return JavaBYTE;
		} else if (_type == Type.CHAR) {
			return JavaCHAR;
		} else if (_type == Type.DOUBLE) {
			return JavaDOUBLE;
		} else if (_type == Type.FLOAT) {
			return JavaFLOAT;
		} else if (_type == Type.INT) {
			return JavaINT;
		} else if (_type == Type.LONG) {
			return JavaLONG;
		} else if (_type == Type.SHORT) {
			return JavaSHORT;
		}  else if (_type ==  Type.VOID) {
			return JavaVOID;
		} 
		return null;
	}
	
	public static JavaBasicType getJavaBasicType( int _baseType) {
		if (_baseType == BaseTypeCharacters.Z ) {
			return JavaBOOLEAN;	
		} else if (_baseType == BaseTypeCharacters.B) {
			return JavaBYTE;
		} else if (_baseType == BaseTypeCharacters.C) {
			return JavaCHAR;
		} else if (_baseType == BaseTypeCharacters.D) {
			return JavaDOUBLE;
		} else if (_baseType == BaseTypeCharacters.F) {
			return JavaFLOAT;
		} else if (_baseType == BaseTypeCharacters.I) {
			return JavaINT;
		} else if (_baseType == BaseTypeCharacters.L) {
			return JavaLONG;
		} else if (_baseType == BaseTypeCharacters.S) {
			return JavaSHORT;
		}  else if (_baseType == BaseTypeCharacters.V) {
			return JavaVOID;
		}
		return null;
	}
	
	public static JavaReferenceType getJavaClass( String _signature)  {
		if (_signature.equals("java.lang.String")) {
			return JavaSTRING;
		}
		String signature =  "L" + _signature.replace('.', '/') + ";";
	   if (loadedTypes == null ) {
		   loadedTypes = new HashMap();	
	   }
	   JavaReferenceType _jt = null;
	   if ((_jt =(JavaReferenceType) loadedTypes.get(signature) )!= null )  {
		   return  _jt;
	   }
	   Type _t = Type.getType(signature);
	   if (_t instanceof ObjectType) {
		  _jt =  new JavaObjectType((ObjectType)_t);
	  } else if ( _t instanceof ArrayType) {
		  _jt = new JavaArrType((ArrayType)_t);
	  }
	  loadedTypes.put(_jt.getSignature(), _jt );	
	   return _jt;
	} 
	
	/**
	 * 
	 * @param _class_name String that represents a valid java class name , i.e. java.lang.String. Only classes are stored here
 	 * @return
	 */
	public static JavaReferenceType getJavaClass(Integer _cpIndex, ConstantPoolGen _cpg)  {
		JavaReferenceType _jt = null;
		ConstantClass _cc = (ConstantClass)_cpg.getConstant(_cpIndex.intValue() );
//		BCConstantClass bcc = new BCConstantClass(_cc , _cpIndex.intValue());
//		Type _bcelt = Type.getType(_cc.getBytes(_cpg.getConstantPool()));
		_jt = getJavaClass(_cc.getBytes(_cpg.getConstantPool()));
	   //_jt.setBCConstantClass(bcc);
		return _jt;
	}

	
	
	

}
