package annot.bcexpression.formula;

import annot.bcexpression.BCExpression;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;

/**
 * This class represents all expressions that returns boolean
 * value.
 * 
 * @author tomekb
 */
public abstract class AbstractFormula extends BCExpression {

	/**
	 * Another constructor for 0Arg formula.
	 * 
	 * @param connector - type of expression
	 * 		(from annot.io.Code interface).
	 */
	protected AbstractFormula(int connector) {
		super(connector);
	}

	/**
	 * A Constructor for unary formula.
	 * 
	 * @param connector - type of expression
	 * 		(from annot.io.Code interface),
	 * @param subExpr - subexpression.
	 */
	protected AbstractFormula(int connector, BCExpression subExpr) {
		super(connector, subExpr);
	}

	/**
	 * A constructor for binary formula.
	 * 
	 * @param connector - type of expression
	 * 		(from annot.io.Code interface),
	 * @param left - left subexpression,
	 * @param right - right subexrpession.
	 */
	protected AbstractFormula(int connector, BCExpression left, BCExpression right) {
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
	protected AbstractFormula(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	public JavaType getType1() {
		return JavaBasicType.JavaBool;
	}

}
