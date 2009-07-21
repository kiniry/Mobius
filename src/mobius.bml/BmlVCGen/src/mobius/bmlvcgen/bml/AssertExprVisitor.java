package mobius.bmlvcgen.bml;

import mobius.bmlvcgen.bml.types.Type;
import mobius.bmlvcgen.util.Visitable;

/**
 * Visitor for expressions valid in assertions/loop invariants.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface AssertExprVisitor 
  extends ExprVisitor<AssertExprVisitor> {

  /**
   * Reference to local variable or argument.
   * @param i Argument index.
   * @param name Argument name (possibly null).
   * @param type Field type.
   */
  void local(int i, String name, Type type);
  
  // TODO: \old with label
  
  /**
   * Expression evaluated before method call.
   * @param expr Expression.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super PreExprVisitor>>
  void aold(Expr expr);
}
