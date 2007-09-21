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
 * The constructor is private, so use
 * {@link #getJavaType(String)} instead.
 * 
 * @author tomekb
 */
public class JavaType extends BCExpression {

	/**
	 * String representation of JavaType.
	 */
	private String name;

	/**
	 * A private constructor.
	 * 
	 * @param name - string representation of JavaType.
	 */
	private JavaType(String name) {
		super(Code.JAVA_TYPE);
		this.name = name;
	};

	/**
	 * Type of this class only.
	 */
	public static final JavaType JavaType = new JavaType(null);

	/**
	 * int type.
	 */
	public static final JavaType JavaInt = new JavaType(IDisplayStyle.jt_int);

	/**
	 * boolean type.
	 */
	public static final JavaType JavaBool = new JavaType(
			IDisplayStyle.jt_boolean);

	/**
	 * Gives proper instance of JavaType.
	 * 
	 * @param name - type name, as in variable declaration.
	 * @return - instance of JavaType representing type
	 * 		of given <code>name</code>.
	 * @throws ReadAttributeException - if <code>name</code>
	 * 		parameter is invalid.
	 */
	public static JavaType getJavaType(String name)
			throws ReadAttributeException {
		if (IDisplayStyle.jt_int.equals(name))
			return JavaInt;
		if (IDisplayStyle.jt_boolean.equals(name))
			return JavaBool;
		throw new ReadAttributeException("Unknown java type");
	}

	/**
	 * Displays JavaType to a String.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return String representation of JavaType.
	 * @see BCExpression#printCode1(BMLConfig)
	 */
	@Override
	public String printCode1(BMLConfig conf) {
		return name;
	}

	/**
	 * @return Simple String representation of this
	 * 		JavaType, for debugging only.
	 */
	@Override
	public String toString() {
		return name;
	}

	/**
	 * This method should not be called.
	 * 
	 * @throws RuntimeException - always.
	 */
	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		throw new RuntimeException(
				"read() emthod unavaliable, use getJavaType() instead.");
	}

	/**
	 * Writes this expression to AttributeWirter.
	 * 
	 * @param aw - stream to save to.
	 */
	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.JAVA_TYPE);
		int cpIndex = aw.findConstant(name);
		aw.writeShort(cpIndex);
	}

	/**
	 * Does nothing.
	 */
	@Override
	protected void init() {
	}

	/**
	 * JavaType has no subexpressions, so it has
	 * the highest priority.
	 * 
	 * @return priority of this expression
	 * 		(from annot.textio.Priorities).
	 */
	@Override
	protected int getPriority() {
		return Priorities.LEAF;
	}

	/**
	 * @return type of JavaType, that is,
	 * 		{@link JavaType#JavaType}.
	 */
	@Override
	protected JavaType getType1() {
		return JavaType;
	}

}
