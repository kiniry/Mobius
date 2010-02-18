/**
 * Package for data structures.
 */
package structure;

import java.util.List;
import java.util.Vector;

import logic.BeetlzExpression;

/**
 * Container for class invariant.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class Invariant {
  /**
   * Predictates of this invariant.
   */
  private final List < BeetlzExpression > my_predicates;
  /**
   * Predicates of the history constraint.
   */
  private final List < BeetlzExpression > my_historyConstraints;

  /**
   * Creae a new invariant with given predicates.
   * @param some_predicates invariant clauses
   * @param some_history_constraints constraint clauses
   */
  public Invariant(final List < BeetlzExpression > some_predicates,
                   final List < BeetlzExpression > some_history_constraints) {
    my_predicates = some_predicates;
    my_historyConstraints = some_history_constraints;
  }

  /**
   * Get all invariant clauses.
   * @return predicates of invariant
   */
  public final List < BeetlzExpression > getPredicates() {
    return my_predicates;
  }

  /**
   * Invariant clauses that are not informal.
   * @return all not-informal clauses
   */
  public final List < BeetlzExpression > getNonTrivialPredicates() {
    final List < BeetlzExpression > list = new Vector < BeetlzExpression > ();
    for (final BeetlzExpression e : my_predicates) {
      if (!e.skip()) {
        list.add(e);
      }
    }
    return list;
  }

  /**
   * Get all informal invariant clauses.
   * @return informal clauses
   */
  public final List < BeetlzExpression > getInformalPredicates() {
    final List < BeetlzExpression > list = new Vector < BeetlzExpression > ();
    for (final BeetlzExpression e : my_predicates) {
      if (e.skip()) {
        list.add(e);
      }
    }
    return list;
  }

  /**
   * Get all history constraint.
   * @return  history constraint clauses
   */
  public final List < BeetlzExpression > getHistoryConstraints() {
    return my_historyConstraints;
  }

  /**
   * Get all constraints that are not informal.
   * @return all not-informal history constraints
   */
  public final List < BeetlzExpression > getNonTrivialHistoryConstraints() {
    final List < BeetlzExpression > list = new Vector < BeetlzExpression > ();
    for (final BeetlzExpression e : my_historyConstraints) {
      if (!e.skip()) {
        list.add(e);
      }
    }
    return list;
  }

  /**
   * Get all informal history constraints.
   * @return informal constraint clauses
   */
  public final List < BeetlzExpression > getInformalHistoryConstraints() {
    final List < BeetlzExpression > list = new Vector < BeetlzExpression > ();
    for (final BeetlzExpression e : my_historyConstraints) {
      if (e.skip()) {
        list.add(e);
      }
    }
    return list;
  }

  /**
   * Is invariant empty.
   * @return true if no invariant and no history constraint clauses
   */
  public final boolean isEmpty() {
    return my_predicates.isEmpty() && my_historyConstraints.isEmpty();
  }

  /**
   * String representation.
   * @see java.lang.Object#toString()
   * @return string representation
   */
  @Override
  public final String toString() {
    String string = ""; //$NON-NLS-1$
    
    if (my_predicates.size() > 0) {
      string += "invariants \n"; //$NON-NLS-1$
      for (final BeetlzExpression s : my_predicates) {
        if (s.skip()) {
          string += "\t (* " + s + " *)\n"; //$NON-NLS-1$ //$NON-NLS-2$
        } else {
          string += "\t" + s + "\n"; //$NON-NLS-1$ //$NON-NLS-2$
        }
      }
    }
    if (my_historyConstraints.size() > 0) {
      string += "history constraint \n\t"; //$NON-NLS-1$
      for (final BeetlzExpression s : my_historyConstraints) {
        if (s.skip()) {
          string += "\t (* " + s + " *)\n"; //$NON-NLS-1$ //$NON-NLS-2$
        } else {
          string += "\t" + s + "\n"; //$NON-NLS-1$ //$NON-NLS-2$
        }
      }
    }
    return string;
  }


}
