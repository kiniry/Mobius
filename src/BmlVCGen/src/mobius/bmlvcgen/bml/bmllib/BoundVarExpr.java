package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.ExprVisitor;
import mobius.bmlvcgen.util.Visitable;
import annot.bcexpression.BCExpression;
import annot.bcexpression.BoundVar;
import annot.bcexpression.formula.QuantifiedFormula;

/**
 * A wrapper for bmllib bound variables.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 * @param <V> Type of visitors.
 */
public class BoundVarExpr<V extends ExprVisitor<V>> 
    implements Visitable<V> {
  private final int dist;
  
  /**
   * Constructor.
   * @param expr Expression to be wrapped.
   */
  public BoundVarExpr(final BoundVar expr) {
    dist = findQuantifier((BoundVar)expr);
  }
  
  /** {@inheritDoc} */
  public void accept(final V visitor) {
    visitor.boundvar(dist);
  }  
  
  // Return distance from quantifier.
  private static int findQuantifier(final BoundVar var) {
    int dist = 0;
    final int index = getIndex(var);
    BCExpression current = var;
    
  treewalk:
    while (current != null) {
      if (current instanceof QuantifiedFormula) {
        final QuantifiedFormula qf = (QuantifiedFormula)current;
        for (int i = qf.getLength() - 1; i >= 0; i++) {
          if (getIndex((BoundVar)qf.getVar(i)) == index) {
            break treewalk;
          } else {
            dist = dist + 1;
          }
        }
      }
      current = current.getParent();
    }
    if (current == null) {
      throw new IllegalArgumentException("Free variable?");
    }
    return dist;
  }
  
  //TODO: find a better way of getting variable indices.
  private static int getIndex(final BoundVar bv) {
    return bv.hashCode();
  }
  
}
