package mobius.bmlvcgen.bml.bmllib;

import annot.bcexpression.BCExpression;

/**
 * Objects which can produce wrappers for
 * bmllib expressions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 * @param <Expr> Wrapper type.
 */
public interface ExprFactory<Expr> {
  /**
   * Wrap an expression.
   * @param e Bmllib expression.
   * @return Wrapped expression.
   */
  Expr wrap(BCExpression e);
}
