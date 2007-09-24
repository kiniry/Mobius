package escjava.sortedProver;

import escjava.sortedProver.NodeBuilder.SPred;

/**
 * This response is returned when the prover finds a counter example.
 */
public class CounterExampleResponse extends SortedProverResponse {
  private final String[] labels;

  /**
   * Construct new instance.
   * 
   * @param labels the current set of labels describing the counter example
   */
  public CounterExampleResponse(String[] labels) {
    super(COUNTER_EXAMPLE);
    this.labels = labels;
  }

  /**
   * @return a list of labels contained in the counterexample found by the
   *         prover
   */
  public String[] getLabels() {
    return labels;
  }

  /**
   * Can be called by the reciver of the response to discharge it.
   * 
   * @param pred The reciver can pass here a formula that would be conjoined to
   *          the original query to hint the direction in which prover should
   *          look for further counter examples. The prover can treat the
   *          formula returned as a theory tautology (in which case it can say
   *          the formula is valid). It is however free to ignore that.
   */
  public void discharge(@SuppressWarnings("unused") SPred pred) {
    // do nothing
  }
}
