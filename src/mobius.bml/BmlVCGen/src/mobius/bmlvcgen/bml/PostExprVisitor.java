package mobius.bmlvcgen.bml;

import mobius.bmlvcgen.bml.types.Type;
import mobius.bmlvcgen.util.Visitable;

/**
 * Builder for expressions valid in method postcondition.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface PostExprVisitor 
  extends ExprVisitor<PostExprVisitor> {
  /**
   * Expression evaluated before method call.
   * @param expr Expression.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super PreExprVisitor>>
  void old(Expr expr);
  
  /**
   * Reference to local variable (argument).
   * @param i Argument index.
   * @param name Argument name (possibly null).
   * @param type Field type.
   */
  void arg(int i, String name, Type type);
  
  /**
   * Method result.
   */
  void result();
}
