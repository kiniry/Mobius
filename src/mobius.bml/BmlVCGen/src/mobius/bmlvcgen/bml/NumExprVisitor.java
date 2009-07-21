package mobius.bmlvcgen.bml;

import mobius.bmlvcgen.util.Visitable;

/**
 * Visitor for arithmetic expressions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 * @param <V> Type of visitors.
 */
public interface NumExprVisitor<V> {
  //
  // Constants
  //
  /**
   * Integer constant.
   * @param v Constant value.
   */
  void intConst(int v);
  
  /**
   * Long integer constant.
   * @param v Constant value.
   */
  void longConst(long v);
  
  /**
   * Short integer constant.
   * @param v Constant value.
   */
  void shortConst(short v);
  
  /**
   * Character constant.
   * @param v Constant value.
   */
  void charConst(char v);
  
  /**
   * Byte constant.
   * @param v Constant value.
   */
  void byteConst(byte v);
  
  //
  // Binary operators.
  //
  /**
   * Addition.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void add(Expr l, Expr r);
  
  /**
   * Subtraction.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void sub(Expr l, Expr r);
  
  /**
   * Multiplication.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void mul(Expr l, Expr r);
  
  /**
   * Integer division.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void intDiv(Expr l, Expr r);
  
  /**
   * Remainder.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void mod(Expr l, Expr r);
  
  //
  // Shifts.
  //
  /**
   * Arithmetic shift right ('>>').
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void sar(Expr l, Expr r);
  
  /**
   * Right shift ('>>>').
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void shr(Expr l, Expr r);
  
  /**
   * Left shift.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void shl(Expr l, Expr r);
  
  //
  // Other bitwise operators.
  // 

  /**
   * Bitwise 'and'.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void bitAnd(Expr l, Expr r);
  
  /**
   * Bitwise 'or'.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void bitOr(Expr l, Expr r);
  
  /**
   * Bitwise 'xor'.
   * @param l Left operand.
   * @param r Right operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void bitXor(Expr l, Expr r);

  //
  // Unary operators.
  //
  /**
   * Bitwise negation.
   * @param e Operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void bitNeg(Expr e);
  
  /**
   * Unary minus operator.
   * @param e Operand.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>>
  void minus(Expr e);
}
