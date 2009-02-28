package mobius.bmlvcgen.bml;

import mobius.bmlvcgen.util.Visitable;

/**
 * Expression visitor which contains comparison
 * operators.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 * @param <V> Type of visitors.
 */
public interface CmpExprVisitor<V> {
  /**
   * Equality operator.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void eq(Expr l, Expr r);
  
  /**
   * Inequality operator.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void neq(Expr l, Expr r);
  
  /**
   * Lesser than.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void lt(Expr l, Expr r);
  
  /**
   * Greater than.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void gt(Expr l, Expr r); 

  /**
   * Lesser than or equal.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void le(Expr l, Expr r);  
  
  /**
   * Greater than or equal.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void ge(Expr l, Expr r);
  
  /**
   * Subtype operator.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void isSubtype(Expr l, Expr r);  
}
