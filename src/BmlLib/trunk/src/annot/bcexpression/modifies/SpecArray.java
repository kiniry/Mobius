package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.bcexpression.JavaType1;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;
import annot.textio.Priorities;

/**
 * Describes modification of array's elements (which elements
 * can be modified).
 * 
 * @author tomekb
 */
public abstract class SpecArray extends BCExpression {

	/**
	 * A standard constructor for 0-args array specifications.
	 * 
	 * @param connector - type of expression. 
	 */
	public SpecArray(int connector) {
		super(connector);
	}

	/**
	 * A standard constructor for unary array specifications.
	 * 
	 * @param connector - type of expression,
	 * @param expr - it's subexpression.
	 */
	public SpecArray(int connector, BCExpression expr) {
		super(connector, expr);
	}

	/**
	 * A standard constructor for binary array specifications.
	 * 
	 * @param connector - type of expression,
	 * @param left - left subexpression,
	 * @param right - right subexpression.
	 */
	public SpecArray(int connector, BCExpression left, BCExpression right) {
		super(connector, left, right);
	}

	/**
	 * A constructor from AttributeReader.
	 * 
	 * @param ar - input stream to load from,
	 * @param root - type of this expression.
	 * @throws ReadAttributeException - if root + stream
	 * 		in <code>ar</code> doesn't represent correct
	 * 		array modification specification.
	 */
	public SpecArray(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	/**
	 * Noone should need JavaType of SpecArray.
	 * I will return here sth if I will need JavaType
	 * of this expression.
	 * 
	 * @throws RuntimeException - always.
	 */
	@Override
	protected JavaType1 checkType1() {
		throw new RuntimeException("What type should it return?");
	}

	@Override
	protected int getPriority() {
		return Priorities.MAX_PRI;
	}

	/**
	 * Noone should need JavaType of SpecArray.
	 * I will return here sth if I will need JavaType
	 * of this expression.
	 * 
	 * @throws RuntimeException - always.
	 */
	@Override
	public JavaType1 getType1() {
		throw new RuntimeException("What type should it return?");
	}

}
