package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.PreExprVisitor;
import mobius.bmlvcgen.util.Visitable;
import annot.bcexpression.BCExpression;
import annot.bcexpression.LocalVariable;
import annot.io.Code;

/**
 * Wrapper factory for preconditions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class PreExprWrapper 
    extends ExprWrapper<PreExprVisitor> {

  /** {@inheritDoc} */
  @Override
  public Visitable<PreExprVisitor> 
  wrap(final BCExpression expression) {
    final BCExpression expr = unpack(expression);
    if (expr.getConnector() == Code.LOCAL_VARIABLE) {
      final LocalVariable lv = (LocalVariable)expr;
      return new ArgExpr(
                   lv.getIndex(), 
                   lv.getName(), 
                   BmllibType.getInstance(lv.getType()));
    } else {
      return super.wrap(expr);
    }
  }
}
