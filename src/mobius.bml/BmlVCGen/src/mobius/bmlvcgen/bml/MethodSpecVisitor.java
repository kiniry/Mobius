package mobius.bmlvcgen.bml;

import mobius.bmlvcgen.util.Visitable;

/**
 * Interface of method specification case visitors.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface MethodSpecVisitor {
  /**
   * Visit precondition.
   * @param pre Precondition.
   */
  void visitPrecondition(
         Visitable<? super PreExprVisitor> pre);
  
  /**
   * Visit postcondition.
   * @param post Postcondition.
   */
  void visitPostcondition(
         Visitable<? super PostExprVisitor> post);
  
  /**
   * Visit signals clause.
   * @param exc Exception class name.
   * @param expr Postcondition.
   */
  void visitSignals(String exc, 
                    Visitable<? super PostExprVisitor> expr);
  
  // TODO: assignable
}
