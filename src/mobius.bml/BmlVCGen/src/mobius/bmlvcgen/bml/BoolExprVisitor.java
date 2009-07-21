package mobius.bmlvcgen.bml;

import mobius.bmlvcgen.util.Visitable;

/**
 * Expression visitor with boolean operations.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 * @param <V> Type of visitors.
 */
public interface BoolExprVisitor<V> {
  /**
   * Boolean constant.
   * @param v Constant value.
   */
  void boolConst(boolean v);
  
  /**
   * Boolean negation.
   * @param e Operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void boolNot(Expr e);
  
  /**
   * Boolean 'and'.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void boolAnd(Expr l, Expr r);
  
  /**
   * Boolean 'or'.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void boolOr(Expr l, Expr r);
  
  /**
   * Boolean implication.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void boolImpl(Expr l, Expr r);
  
  /**
   * Boolean reverse implication.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void boolRimpl(Expr l, Expr r);
  
  /**
   * Boolean equivalence.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void boolEquiv(Expr l, Expr r);

  /**
   * Boolean inequivalence.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void boolInequiv(Expr l, Expr r);
}
