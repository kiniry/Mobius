package freeboogie.backend;

import java.util.Set;

/**
 * A term that knows its sort. In theorem prover jargon,
 * instances of this class represent both terms and formulas.
 *
 * Terms are built under the assumption that the prover will
 * see certain axioms before seeing the term. These axioms are
 * returned by {@code axioms()}.
 *
 * The class {@code Term} is intended to be subclassed (in
 * conjunction with concrete prover classes).
 *
 * @author rgrig 
 */
public abstract class Term<T> {
  private Sort sort;
  
  /**
   * Constructs a term, and remembers its sort.
   * @param sort
   */
  public Term(Sort sort) {
    this.sort = sort;
  }
  
  /**
   * Returns the sort of this term.
   * @return the sort of this term
   */
  public Sort sort() {
    return sort;
  }

  /**
   * Adds axioms needed to read {@code this} to {@code axiomBag}.
   */
  public abstract void collectAxioms(Set<T> axiomBag);
}
