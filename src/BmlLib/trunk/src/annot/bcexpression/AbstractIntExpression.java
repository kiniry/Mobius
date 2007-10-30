package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.ReadAttributeException;

/**
 * This class represents expressions that returns an integer
 * value.
 * 
 * @author tomekb
 */
public abstract class AbstractIntExpression extends BCExpression {

	/**
	 * Another constructor for 0Arg expressions.
	 * 
	 * @param connector - type of expression
	 * 		(from annot.io.Code interface).
	 */
	protected AbstractIntExpression(int connector) {
		super(connector);
	}

	/**
	 * A Constructor for unary expressions.
	 * 
	 * @param connector - type of expression
	 * 		(from annot.io.Code interface),
	 * @param subExpr - subexpression.
	 */
	protected AbstractIntExpression(int connector, BCExpression subExpr) {
		super(connector, subExpr);
	}

	/**
	 * A constructor for binary expressions.
	 * 
	 * @param connector - type of expression
	 * 		(from annot.io.Code interface),
	 * @param left - left subexpression,
	 * @param right - right subexrpession.
	 */
	protected AbstractIntExpression(int connector, BCExpression left,
			BCExpression right) {
		super(connector, left, right);
	}

	/**
	 * A constructor from AttributeReader.
	 * 
	 * @param ar - stream to load from,
	 * @param root - expression type (connector).
	 * @throws ReadAttributeException - if connector + stream
	 * 		in <code>ar</code> doesn't represent any
	 * 		expression from constructing subclass.
	 * @see BCExpression#BCExpression(AttributeReader, int)
	 */
	protected AbstractIntExpression(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	public JavaType1 getType() {
		return JavaBasicType.JavaInt;
	}

}
