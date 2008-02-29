package freeboogie.backend;

import freeboogie.ast.Expr;

/**
 * Transforms BPL expressions into prover terms.
 *
 * @author rgrig
 * @author reviewed by TODO
 */
public interface TermOfExpr {
  /**
   * Transforms {@code e} into a term. Implementations
   * should handle all BPL expressions. If that is not possible,
   * then at least fail early if {@code e} is too rich.
   */
  Term get(Expr e);
}
