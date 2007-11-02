package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents an <code>OLD</code> expression.
 * 
 * @author tomekb
 */
public class OLD extends OldExpression {

	/**
	 * A standard constructor.
	 * 
	 * @param connector - type of this expression, should
	 * 		be {@link Code#OLD},
	 * @param subExpr - it's subexpression.
	 */
	public OLD(int connector, BCExpression subExpr) {
		super(makeOld(connector), subExpr);
	}

	/**
	 * A constructor from AttributeReader.
	 * 
	 * @param ar - input stream to load from.
	 * @param root - type of expression (last byte read from
	 * 		<code>ar</code>).
	 * @throws ReadAttributeException - if root + remaining
	 * 		stream in <code>ar</code> doesn't represent
	 * 		correct <code>OLD</code> expression.
	 */
	public OLD(AttributeReader ar, int root) throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	protected JavaType1 checkType2() {
		return getSubExpr(0).checkType();
	}

	@Override
	protected int getPriority() {
		return Priorities.LEAF;
	}

	@Override
	public JavaType1 getType1() {
		return getSubExpr(0).getType();
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return "old(" + getSubExpr(0).printCode(conf) + ")";
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		setSubExprCount(1);
		setSubExpr(0, ar.readExpression());
	}

	@Override
	public String toString() {
		return "old(" + getSubExpr(0).toString() + ")";
	}

}
