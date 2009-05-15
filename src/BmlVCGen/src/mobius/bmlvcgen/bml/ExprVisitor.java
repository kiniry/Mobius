package mobius.bmlvcgen.bml;

import mobius.bmlvcgen.bml.types.Type;
import mobius.bmlvcgen.util.Visitable;

/**
 * Common interface for all kinds of expression visitors.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 * @param <V> Type of visitors.
 */
public interface ExprVisitor<V> 
  extends 
    BoolExprVisitor<V>,
    CmpExprVisitor<V>, 
    NumExprVisitor<V>, 
    TypeExprVisitor<V> {
  
  /**
   * Array access expression.
   * @param array Array.
   * @param index Index.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>> 
  void arrayAccess(Expr array, Expr index);
  
  /**
   * Array length expression.
   * @param array Array.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>> 
  void arrayLength(Expr array);
  
  /**
   * Null value.
   */
  void constNull();
  
  /**
   * Reference to current object.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>> 
  void self();
  
  /**
   * Field access.
   * @param obj Object.
   * @param field Field name.
   * @param type Field type.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>> 
  void getField(Expr obj, String field, Type type);

  /**
   * Field access (for 'this' object).
   * @param field Field name.
   * @param type Field type.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>> 
  void getField(String field, Type type);
  
  /**
   * Method call.
   * @param obj Object.
   * @param method Method name and type.
   * @param args Arguments.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>> 
  void call(Expr obj, MethodName method, Expr... args);
  
  /**
   * Conditional expression (cond ? if : else).
   * @param cnd Condition.
   * @param ifTrue Result when condition is true.
   * @param ifFalse Result when condition is true.
   * @param <Expr> Type of expressions.
   */
  <Expr extends Visitable<? super V>> 
  void cond(Expr cnd, Expr ifTrue, Expr ifFalse);

   /**
    * Universal quantification.
    * @param pred Quantified expression.
    * @param varName Variable name (can be null).
    * @param type Variable type.
    * @param <Expr> Type of expressions.
    * @see #boundvar()
    */
  <Expr extends Visitable<? super V>> 
  void forall(Expr pred, String varName, Type type);
   
   /**
    * Existential quantification.
    * @param pred Quantified expression.
    * @param varName Variable name (can be null).
    * @param type Variable type.
    * @param <Expr> Type of expressions.
    * @see #boundvar()
    */
  <Expr extends Visitable<? super V>> 
  void exists(Expr pred, String varName, Type type);
   
   /**
    * Bound variable.
    * @param level Index of quantifier which binds
    *              this variable. Zero means nearest
    *              quantifier.
    */
  void boundvar(int level);
}
