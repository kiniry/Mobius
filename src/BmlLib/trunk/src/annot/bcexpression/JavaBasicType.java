package annot.bcexpression;

import annot.io.AttributeWriter;
import annot.io.Code;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;

/**
 * This class represents basic return type of an expression. The constructor is
 * private, so use {@link JavaType1#getJavaType(String)} instead.
 * 
 * @author tomekb
 */
public class JavaBasicType extends JavaType1 {

	/**
	 * String representation of JavaType.
	 */
	private String name;

	/**
	 * A private constructor.
	 * 
	 * @param name -
	 *            string representation of JavaType.
	 */
	private JavaBasicType(String name) {
		this.name = name;
	};

	/**
	 * Type of JavaClass subclasses only.
	 */
	public static final JavaBasicType JavaType = new JavaBasicType(null);

	/**
	 * int type.
	 */
	public static final JavaBasicType JavaInt = new JavaBasicType(
			IDisplayStyle.jt_int);

	/**
	 * boolean type.
	 */
	public static final JavaBasicType JavaBool = new JavaBasicType(
			IDisplayStyle.jt_boolean);

	/**
	 * Displays JavaType to a String.
	 * 
	 * @param conf -
	 *            see {@link BMLConfig}.
	 * @return String representation of JavaType.
	 * @see BCExpression#printCode1(BMLConfig)
	 */
	@Override
	public String printCode1(BMLConfig conf) {
		return name;
	}

	/**
	 * @return Simple String representation of this JavaType, for debugging
	 *         only.
	 */
	@Override
	public String toString() {
		return name;
	}

	/**
	 * Writes this expression to AttributeWirter.
	 * 
	 * @param aw -
	 *            stream to save to.
	 */
	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.JAVA_TYPE);
		int cpIndex = aw.findConstant(name);
		aw.writeShort(cpIndex);
	}

	@Override
	public int compareTypes(JavaType1 type) {
		if (type == this)
			return TYPES_EQUAL;
		return TYPES_UNRELATED;
	}

}
