package annot.bcexpression.util;

import annot.bcclass.MLog;
import annot.bcexpression.BCExpression;
import annot.io.Code;

public class DesugarWalker extends ExpressionWalker {

	@Override
	public void iter(BCExpression parent, BCExpression expr) {
		if (parent == null)
			return;
		removeDoubleNegation(expr);
	}

	/**
	 * Removes double negation from <code>expr</code>:
	 * ~~expr --> expr
	 */
	private void removeDoubleNegation(BCExpression expr) {
		if (expr.getConnector() == Code.NOT)
			if (expr.getSubExpr(0).getConnector() == Code.NOT) {
				expr.replaceWith(expr.getSubExpr(0).getSubExpr(0));
				MLog.putMsg(MLog.PInfo, expr + " ~~~~~> " + expr.getSubExpr(0).getSubExpr(0));
				incChanges();
			}
	}

}
