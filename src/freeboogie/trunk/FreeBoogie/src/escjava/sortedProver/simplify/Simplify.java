/** Public domain. */

package escjava.sortedProver.simplify;

import java.util.Properties;

import escjava.sortedProver.NodeBuilder;
import escjava.sortedProver.SortedProver;
import escjava.sortedProver.SortedProverCallback;
import escjava.sortedProver.SortedProverResponse;
import escjava.sortedProver.NodeBuilder.SPred;

/**
 * Responsible for the interaction with provers that support the
 * Simplify format.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class Simplify extends SortedProver {

  /* @see escjava.sortedProver.SortedProver#declareAxiom(escjava.sortedProver.NodeBuilder.SPred) */
  @Override
  public SortedProverResponse declareAxiom(SPred formula) {
    // TODO: Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.SortedProver#getNodeBuilder() */
  @Override
  public NodeBuilder getNodeBuilder() {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.SortedProver#isValid(escjava.sortedProver.NodeBuilder.SPred, escjava.sortedProver.SortedProverCallback, java.util.Properties) */
  @Override
  public SortedProverResponse isValid(SPred formula,
    SortedProverCallback callback, Properties properties) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.SortedProver#makeAssumption(escjava.sortedProver.NodeBuilder.SPred) */
  @Override
  public SortedProverResponse makeAssumption(SPred formula) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.SortedProver#retractAssumption(int) */
  @Override
  public SortedProverResponse retractAssumption(int count) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.SortedProver#sendBackgroundPredicate() */
  @Override
  public SortedProverResponse sendBackgroundPredicate() {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.SortedProver#setProverResourceFlags(java.util.Properties) */
  @Override
  public SortedProverResponse setProverResourceFlags(Properties properties) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.SortedProver#startProver() */
  @Override
  public SortedProverResponse startProver() {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.SortedProver#stopProver() */
  @Override
  public SortedProverResponse stopProver() {
    // TODO Implement
    assert false;
    return null;
  }
}
