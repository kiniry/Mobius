package annot.bcexpression.util;

import annot.bcexpression.BCExpression;

public abstract class ExpressionWalker {
	public abstract void iter(BCExpression parent, BCExpression expr);
}
