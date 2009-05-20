package annot.bcexpression.util;

import annot.bcclass.MLog;
import annot.bcclass.MessageLog;
import annot.bcexpression.BCExpression;
import annot.io.Code;

/**
 * TODO describe
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class DesugarWalker extends ExpressionWalker {

  @Override
  public void iter(final BCExpression parent, final BCExpression expr) {
    if (parent == null) {
      return;
    }
    removeDoubleNegation(expr);
  }

  /**
   * Removes double negation from <code>expr</code>:
   * !!expr -- >  expr
   */
  private void removeDoubleNegation(final BCExpression expr) {
    if (expr.getConnector() == Code.NOT) {
      if (expr.getSubExpr(0).getConnector() == Code.NOT) {
        expr.replaceWith(expr.getSubExpr(0).getSubExpr(0));
        MLog.putMsg(MessageLog.LEVEL_PINFO, expr + " ~~~~~ >  " +
                    expr.getSubExpr(0).getSubExpr(0));
        incChanges();
      }
    }
  }

}
