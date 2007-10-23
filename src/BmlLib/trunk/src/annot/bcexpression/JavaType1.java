package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
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
		if (IDisplayStyle.jt_int.equals(name))
			return JavaBasicType.JavaInt;
		if (IDisplayStyle.jt_boolean.equals(name))
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
	public JavaType1 getType() {
		return JavaBasicType.JavaType;
	}

	/**
	 * JavaType has no constructor from AttributeReader,
	 * so it doesn't need pre-superconstructor initializetion.
	 */
	@Override
	protected void init() {};

	@Override
	protected abstract String printCode1(BMLConfig conf);

	/**
	 * This method should not be called.
	 * 
	 * @throws RuntimeException - always.
	 */
	@Override
	protected void read(AttributeReader ar, int root) {
		throw new RuntimeException(
				"read() method unavaliable, use getJavaType() instead.");
	}

	@Override
	public abstract String toString();

	@Override
	public abstract void write(AttributeWriter aw);

}
