package genericutils;

/**
 * An associative operator has a neutral element (zero) and
 * a (closed) composition law (plus).
 */
public interface AssociativeOperator<R> {
  /** Returns the neutral element. */
  R zero();

  /** Combines two elements of {@code R}. */
  R plus(R a, R b);
}
