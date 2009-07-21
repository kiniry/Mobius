package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.ExprVisitor;
import mobius.bmlvcgen.bml.types.Type;
import mobius.bmlvcgen.util.Visitable;
import annot.bcexpression.BCExpression;
import annot.bcexpression.FieldAccess;
import annot.bcexpression.FieldRef;

/**
 * Wrapper for bmllib field access expressions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 * @param <V> Type of visitors.
 */
public class FieldAccessExpr<V extends ExprVisitor<V>> 
    implements Visitable<V> {
  final Visitable<V> left;
  final String name;
  final Type type;
  
  /**
   * Constructor.
   * @param expr Expression to be wrapped.
   * @param factory Object used to wrap subexpressions.
   */
  public FieldAccessExpr(final FieldAccess expr,
                      final ExprFactory<Visitable<V>> factory) {
    left = factory.wrap(expr.getSubExpr(0));
    final BCExpression right = expr.getSubExpr(1);
    assert right instanceof FieldRef;
    name = ((FieldRef)right).getName();
    type = BmllibType.getInstance(expr.getType());
  }

  /** {@inheritDoc} */
  public void accept(final V visitor) {
    visitor.getField(left, name, type);
  }
}
