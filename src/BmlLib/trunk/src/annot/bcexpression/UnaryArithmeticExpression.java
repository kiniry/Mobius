package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

public class UnaryArithmeticExpression extends ArithmeticExpression {

	public UnaryArithmeticExpression(int connector, BCExpression subExpr) {
		super(connector, subExpr);
	}

	public UnaryArithmeticExpression(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	protected JavaBasicType getType1() {
		if (getSubExpr(0).getType() != JavaBasicType.JavaInt)
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
