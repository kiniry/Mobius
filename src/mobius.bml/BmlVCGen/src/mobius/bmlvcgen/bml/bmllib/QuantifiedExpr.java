package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.ExprVisitor;
import mobius.bmlvcgen.util.Visitable;
import annot.bcexpression.BoundVar;
import annot.bcexpression.formula.QuantifiedFormula;
import annot.io.Code;

/**
 * Wrapper for bmllib quantified expressions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 * @param <V> Type of visitors.
 */
public class QuantifiedExpr<V extends ExprVisitor<V>> 
  implements Visitable<V> {
  private final QuantifiedFormula expr;
  private final int var;
  private final ExprFactory<Visitable<V>> factory;
  private final boolean universal;
  
  /**
   * Constructor.
   * @param expr Expression to be wrapped.
   * @param var Variable index.
   * @param factory Object used to wrap quantified expr.
   */
  public QuantifiedExpr(
      final QuantifiedFormula expr, 
      final int var,
      final ExprFactory<Visitable<V>> factory) {
    this.expr = expr;
    this.var = var;
    this.factory = factory;
    universal = expr.getConnector() == Code.FORALL ||
                expr.getConnector() == Code.FORALL_WITH_NAME;
  }

  /** {@inheritDoc} */
  public void accept(final V visitor) {
    final BoundVar bv = expr.getVar(var);
    final Visitable<V> subExpr;
    
    if (expr.getLength() - 1 > var) {
      subExpr = new QuantifiedExpr<V>(expr, var + 1, factory);
    } else {
      subExpr = factory.wrap(expr.getSubExpr(0));
    }
    if (universal) {
      visitor.forall(
        subExpr, 
        bv.getVname(), 
        BmllibType.getInstance(bv.getType()));
    } else {
      visitor.exists(
        subExpr, 
        bv.getVname(), 
        BmllibType.getInstance(bv.getType()));        
    }
  }

}
