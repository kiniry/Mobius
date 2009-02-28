package mobius.bmlvcgen.bml;

import mobius.bmlvcgen.bml.types.Type;

/**
 * Visitor for expressions valid in method precondition.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface PreExprVisitor 
  extends ExprVisitor<PreExprVisitor> {
  
  /**
   * Reference to local variable (argument).
   * @param i Argument index.
   * @param name Argument name (possibly null).
   * @param type Argument type.
   */
  void arg(int i, String name, Type type);
}
