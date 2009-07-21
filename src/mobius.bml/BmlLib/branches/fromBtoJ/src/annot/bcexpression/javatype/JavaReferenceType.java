package annot.bcexpression.javatype;

import org.apache.bcel.generic.ReferenceType;
import org.apache.bcel.generic.Type;

public class JavaReferenceType extends JavaType {
//	/*private BCConstantClass bcc;*/
//	
	public static final JavaReferenceType ReferenceType = new JavaReferenceType();
	
	public JavaReferenceType() {
	}
	protected JavaReferenceType(ReferenceType _type) {
		super(_type,  JavaType.COMPUTATIONAL_TYPE_1);
	}
	
//	/**
//	 * @param _type
//	 */
//	protected JavaReferenceType(Class _class) {
//		this((ReferenceType)Type.getType(_class));
//	}
//	
//	
//	
//
//
//
//	/*
//	 * 
//	 *     The following rules are used to determine if a reference type is
//	 *     a subtype of another reference type
//     * If S is an ordinary (nonarray) class, then:
//     *
//     *     o If T is a class type, then S must be the same class  as T or 
//     *     a subclass of T.
//     *
//     *     o If T is an interface type, then S must implement  interface T. 
//     * 
//     * If S is an interface type, then:
//     *
//     *     o If T is a class type, then T must be Object 
//     *
//     *     o If T is an interface type, then T must be the same interface as S, 
//     *     or a superinterface of S (§2.13.2).
//     *
//     * If S is a class representing the array type SC[], that is, an array of
//     *  components of type SC, then:
//     *
//     *     o If T is a class type, then T must be Object.
//     *
//     *     o If T is an array type TC[], that is, an array of components of type TC, 
//     *     then one of the following must be true:
//     *
//     *       TC and SC are the same primitive type .
//     *
//     *            TC and SC are reference types (§2.4.6), and type SC can be cast 
//     *           to TC by these runtime rules.
//     *
//     *     o If T is an interface type, T must be one of the interfaces implemented by arrays (§2.15). 
//     *
//	 */
//	/**
//	 * @param _type1
//	 * @param _type2
//	 * @return
//	 */
//	public static boolean subType(JavaType _type1 , JavaType _type2 ) {
//	/*	if ((_type1 instanceof JavaBasicType) && (_type2 instanceof JavaBasicType)) {
//			return JavaBasicType.subType((JavaBasicType)_type1, (JavaBasicType)_type2);
//		}*/
//		if ((_type1 instanceof JavaObjectType) && (_type2 instanceof JavaObjectType)) {
//			return JavaObjectType.subType((JavaObjectType)_type1, (JavaObjectType)_type2);
//		}
//		
//		if ((_type1 instanceof JavaArrType) && (_type2 instanceof JavaArrType)) {
//			return JavaArrType.subType((JavaArrType)_type1, (JavaArrType)_type2);
//		}
//		return false;
//	}
}
