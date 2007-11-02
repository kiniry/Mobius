package annot.bcexpression;

import org.apache.bcel.generic.Type;

import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.IDisplayStyle;
import annot.textio.Priorities;

/**
 * This class represents return type of an expression.
 * The constructor is protected, so use
 * {@link #getJavaType(String)}
 * or {@link #getJavaBasicType(String)} instead.
 * 
 * @author tomekb
 */
public abstract class JavaType1 extends BCExpression {

	// type comparation results:
	
	/**
	 * Type are totally diffrent (no type is a subtype
	 * of the other).
	 */
	public static final int TYPES_UNRELATED = 0;
	
	/**
	 * Given type is a subtype of this type.
	 */
	public static final int IS_SUBTYPE = 1;
	
	/**
	 * This type is a subtype of given type.
	 */
	public static final int IS_SUPERTYPE = 2;
	
	/**
	 * types are equal.
	 */
	public static final int TYPES_EQUAL = 3;

	/**
	 * A standard constructor for subclasses.
	 */
	protected JavaType1() {
		super(Code.JAVA_TYPE);
	}

	/**
	 * Gives proper instance of JavaType.
	 * 
	 * @param name - type name.
	 * @return - instance of JavaType representing type
	 * 		of given <code>name</code>.
	 */
	public static JavaType1 getJavaType(String name) {
		if (IDisplayStyle.jt_int.equals(name)
			|| ("I".equals(name)))
				return JavaBasicType.JavaInt;
		if (IDisplayStyle.jt_boolean.equals(name)
			|| ("B".equals(name)))
				return JavaBasicType.JavaBool;
		return new JavaReferenceType(name);
	}

	/**
	 * Gives proper instance of JavaBasicType.
	 * 
	 * @param name - type name, as in variable declaration.
	 * @return - instance of JavaType representing type
	 * 		of given <code>name</code>.
	 * @throws ReadAttributeException - if <code>name</code>
	 * 		parameter is invalid.
	 */
	public static JavaBasicType getJavaBasicType(String name)
		throws ReadAttributeException {
		if (IDisplayStyle.jt_int.equals(name))
			return JavaBasicType.JavaInt;
		if (IDisplayStyle.jt_boolean.equals(name))
			return JavaBasicType.JavaBool;
		throw new ReadAttributeException("Unknown java type");
	}

	public static JavaType1 convert(Type t) {
		if (t == Type.BOOLEAN)
			return JavaBasicType.JavaBool;
		if ((t == Type.BYTE) || (t == Type.SHORT)
			|| (t == Type.INT) || (t == Type.LONG))
				return JavaBasicType.JavaInt;
		return JavaReferenceType.ANY; //XXX
	}

	@Override
	public int getPriority() {
		return Priorities.LEAF;
	}

	/**
	 * @return type of JavaType, that is,
	 * 		{@link JavaBasicType#JavaType}.
	 */
	@Override
	protected JavaType1 checkType1() {
		return JavaBasicType.JavaType;
	}

	/**
	 * @return type of JavaType, that is,
	 * 		{@link JavaBasicType#JavaType}.
	 */
	@Override
	public JavaType1 getType1() {
		return JavaBasicType.JavaType;
	}

	/**
	 * Compares this type with given type.<br>
	 * //TODO checking for subtypes currently unsupported!
	 * 
	 * @param type - type to compare to.
	 * @return <b>{@link #TYPES_UNRELATED}</b> - if neither
	 * 		this type is a subtype of given one, nor given
	 * 		type is a subtype of this type,<br>
	 * 		<b>{@link #IS_SUBTYPE}</b> - if given type
	 * 		is a subtype of this type,<br>
	 * 		<b>{@link #IS_SUPERTYPE}</b> - if this type
	 * 		is a subtype of given type,<br>
	 * 		<b>{@link #TYPES_EQUAL}</b> - if this type
	 * 		is equal to given type.
	 */
	public abstract int compareTypes(JavaType1 type);

}
