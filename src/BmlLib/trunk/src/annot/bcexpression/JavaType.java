package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;
import annot.textio.Priorities;

public class JavaType extends BCExpression {

	private String name;

	private JavaType(String name) {
		super(Code.JAVA_TYPE);
		this.name = name;
	};

	public static final JavaType JavaType = new JavaType(null);
	public static final JavaType JavaInt = new JavaType(IDisplayStyle.jt_int);
	public static final JavaType JavaBool = new JavaType(IDisplayStyle.jt_boolean);

	public static JavaType getJavaType(String name)
			throws ReadAttributeException {
		if (IDisplayStyle.jt_int.equals(name))
			return JavaInt;
		if (IDisplayStyle.jt_boolean.equals(name))
			return JavaBool;
		throw new ReadAttributeException("Unknown java type");
	}

	@Override
	public int getPriority() {
		return Priorities.LEAF;
	}

	@Override
	public String printCode1(BMLConfig conf) {
		return name;
	}

	@Override
	public void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		throw new RuntimeException(
				"read() emthod unavaliable, use getJavaType() instead.");
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.JAVA_TYPE);
		int cpIndex = aw.findConstant(name);
		aw.writeShort(cpIndex);
	}

	@Override
	public void init() {
		name = "??";
	}

	@Override
	public String toString() {
		return name;
	}

	@Override
	public JavaType getType1() {
		return JavaType;
	}

}
