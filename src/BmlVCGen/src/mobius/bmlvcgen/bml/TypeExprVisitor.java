package mobius.bmlvcgen.bml;

import mobius.bmlvcgen.bml.types.Type;
import mobius.bmlvcgen.util.Visitable;

/**
 * Expression visitor for type-related expressions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 * @param <V> Type of visitors.
 */
public interface TypeExprVisitor<V> {
  /**
   * Type constant.
   * @param t Type.
   */
  void typeConst(Type t);
  
  /**
   * Cast.
   * @param t Result type.
   * @param e Operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void cast(Type t, Expr e);
}
