package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

public abstract class AbstractIntExpression extends BCExpression {

	public AbstractIntExpression() {
		super();
	}

	public AbstractIntExpression(int connector) {
		super(connector);
	}

	public AbstractIntExpression(int connector, BCExpression subExpr) {
		super(connector, subExpr);
	}

	public AbstractIntExpression(int connector, BCExpression left,
			BCExpression right) {
		super(connector, left, right);
	}

	public AbstractIntExpression(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	public abstract int getPriority();

	@Override
	public abstract String printCode1(BMLConfig conf);

	@Override
	public abstract void read(AttributeReader ar, int root)
			throws ReadAttributeException;

	@Override
	public abstract void write(AttributeWriter aw);

}
