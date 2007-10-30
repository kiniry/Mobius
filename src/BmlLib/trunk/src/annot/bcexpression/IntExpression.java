package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

public class IntExpression extends AbstractIntExpression {

	public IntExpression(BCExpression subExpr) {
		super(-1, subExpr);
	}

	@Override
	protected JavaType1 checkType1() {
		JavaType1 type = getSubExpr(0).checkType();
		if (type != JavaBasicType.JavaInt)
			return null;
		return JavaBasicType.JavaInt;
	}

	@Override
	protected int getPriority() {
		if (getAllSubExpr() == null)
			return -1;
		if (getSubExpr(0) == null)
			return -1;
		return getSubExpr(0).getPriority();
	}

	@Override
	protected void init() {
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return getSubExpr(0).printRawCode(conf);
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		throw new RuntimeException("'read' method unavaliable.");
	}

	@Override
	public String toString() {
		return getSubExpr(0).toString();
	}

	@Override
	public void write(AttributeWriter aw) {
		getSubExpr(0).write(aw);
	}

}
