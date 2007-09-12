package annot.formula;

import annot.bcexpression.BCExpression;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;

public abstract class AbstractFormula extends BCExpression {

	public AbstractFormula() {
		super();
	}

	public AbstractFormula(int connector, BCExpression left, BCExpression right) {
		super(connector, left, right);
	}

	public AbstractFormula(int connector, BCExpression subExpr) {
		super(connector, subExpr);
	}

	public AbstractFormula(int connector) {
		super(connector);
	}

	public AbstractFormula(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

}
