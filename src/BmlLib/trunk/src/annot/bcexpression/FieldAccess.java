package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents dot expression (obj.field).
 * 
 * @author tomekb
 */
public class FieldAccess extends BCExpression {

	/**
	 * A standard constructor.
	 * 
	 * @param connector - type of expression, should be
	 * 		{@link Code#FIELD_ACCESS},
	 * @param left - left subexpression (an object),
	 * @param right - right subexpression (<code>left</code>'s
	 * 		field).
	 */
	public FieldAccess(int connector, BCExpression left, BCExpression right) {
		super(connector, left, right);
	}

	/**
	 * A constructor from AtributeReader.
	 * 
	 * @param ar - input stream to load from,
	 * @param root - connector (last byte read from
	 * 		<code>ar</code>).
	 * @throws ReadAttributeException - if root + remaining
	 * 		stream in <code>ar</code> doesn't represent
	 * 		corrent field access expression.
	 */
	public FieldAccess(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	protected JavaType1 checkType1() {
		if (getSubExpr(0).checkType() == null)
			return null;
		return getSubExpr(1).checkType();
	}

	@Override
	protected int getPriority() {
		return Priorities.getPriority(getConnector());
	}

	@Override
	public JavaType1 getType() {
		return getSubExpr(1).getType();
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return getSubExpr(0).printCode(conf)
			+ "." + getSubExpr(1).printCode(conf);
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		setSubExprCount(2);
		setSubExpr(0, ar.readExpression());
		setSubExpr(1, ar.readExpression());
	}

	@Override
	public String toString() {
		return getSubExpr(0).toString()
			+ "." + getSubExpr(1).toString();
	}

}
