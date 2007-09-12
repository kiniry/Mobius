package annot.bcexpression.javatype;

import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.Type;

import annot.bcexpression.NumberLiteral;

public class JavaBasicType extends JavaType  {
//	private int virtualCPindex ; 
	
	protected JavaBasicType(BasicType _type, NumberLiteral _compType ) {
		super(_type, _compType);
	}
	
//	/**
//	 * @param _type
//	 */
//	protected JavaBasicType(Class _class, NumberLiteral _compType) {
//		this((BasicType)Type.getType(_class), _compType);
//	}
//
///*	*//**
//	 * this relation between basic types on bytecode level is used 
//	 * only in case of subtype comparison(instanceof and cast instructions)
//	 * between array reference type. Even then, only the first three casts are valid 
//	 * (@see  JavaType.subtype specification)
//	 * @param _type1
//	 * @param _type2
//	 * @return
//	 *//*
//	public static boolean subType(JavaBasicType _type1 , JavaBasicType _type2 ) {
//		if ( (_type2 == JavaType.JavaSHORT )&& (_type1 == JavaType.JavaSHORT )) {
//			return true;
//		}
//		if ( (_type2 == JavaType.JavaINT )&& (_type1 == JavaType.JavaINT )) {
//			return true;
//		}
//		if ( (_type2 == JavaType.JavaBYTE )&& (_type1 == JavaType.JavaBYTE )) {
//			return true;
//		}
//		if ((_type2 == JavaType.JavaSHORT )&&( _type1 == JavaType.JavaBYTE)) {
//			return true;
//		}
//		if ((_type2 == JavaType.JavaINT )&&( _type1 == JavaType.JavaBYTE)) {
//			return true;
//		}
//		if ((_type2 == JavaType.JavaINT )&&( _type1 == JavaType.JavaSHORT)) {
//			return true;
//		}
//		
//		return false;
//	}*/
}
