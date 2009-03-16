package mobius.logic.lang.ast;

/**
 * An associative operator has a neutral element (zero) and
 * a (closed) composition law (plus).
 *
 * TODO: Move this in freeboogie.util?
 */
public interface AssociativeOperator<R> {
  /** Returns the neutral element. */
  R zero();

  /** Combines two elements of {@code R}. */
  R plus(R a, R b);
}
