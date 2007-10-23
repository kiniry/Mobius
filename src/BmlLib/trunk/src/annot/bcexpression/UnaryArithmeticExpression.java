package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents unary minus.
 * 
 * @author tomekb
 */
public class UnaryArithmeticExpression extends ArithmeticExpression {

	/**
	 * A standard constructor.
	 * 
	 * @param connector - type of exrpession, should be
	 * 		{@link Code#NEG},
	 * @param subExpr - subexpression.
	 */
	public UnaryArithmeticExpression(int connector, BCExpression subExpr) {
		super(connector, subExpr);
	}

	/**
	 * A constructor from AttributeReader, used for loading
	 * from file (from BCEL's unknown Attribute).
	 * 
	 * @param ar - input stream to load from,
	 * @param root - type o expression (last read byte from
	 * 		<code>ar</code>.
	 * @throws ReadAttributeException - if stream
	 * 		in <code>ar</code> doesn't represent any correct
	 * 		expression.
	 * @see BCExpression#BCExpression(AttributeReader, int)
	 */
	public UnaryArithmeticExpression(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	protected JavaType1 checkType1() {
		if (getSubExpr(0).checkType() != JavaBasicType.JavaInt)
			return null;
		return JavaBasicType.JavaInt;
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return printRoot() + getSubExpr(0).printCode(conf);
	}

	@Override
	protected void read(AttributeReader ar, int root) throws ReadAttributeException {
		setSubExprCount(1);
		BCExpression sub = ar.readExpression();
		setSubExpr(0, sub);
	}

	@Override
	public String toString() {
		return printRoot() + getSubExpr(0).toString();
	}

}
