package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.PostExprVisitor;
import mobius.bmlvcgen.bml.PreExprVisitor;
import mobius.bmlvcgen.util.Visitable;
import annot.bcexpression.BCExpression;
import annot.bcexpression.LocalVariable;
import annot.io.Code;

/**
 * Wrapper for bmllib postconditions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class PostExprWrapper 
    extends ExprWrapper<PostExprVisitor> {
  private final ExprFactory<Visitable<PreExprVisitor>> pre;
  
  /**
   * Constructor.
   * @param pre Object used to wrap old subexpressions.
   */
  public PostExprWrapper(
      final ExprFactory<Visitable<PreExprVisitor>> pre) {
    this.pre = pre;
  }
  
  /** {@inheritDoc} */
  @Override
  public Visitable<PostExprVisitor> 
  wrap(final BCExpression expression) {
    final BCExpression expr = unpack(expression);
    final Visitable<PostExprVisitor> result;
    switch (expr.getConnector()) {
      case Code.LOCAL_VARIABLE:
        final LocalVariable lv = (LocalVariable)expr;
        result = new PostArgExpr(
          lv.getIndex(), 
          lv.getName(), 
          BmllibType.getInstance(lv.getType())                                       
        );
        break;
      case Code.RESULT:
        result = new ResultExpr();
        break;
      case Code.OLD:
        result = new OldExpr(pre.wrap(expr.getSubExpr(0)));
        break;
      default:
        result = super.wrap(expr);
        break;
    }
    return result;
  }
}
