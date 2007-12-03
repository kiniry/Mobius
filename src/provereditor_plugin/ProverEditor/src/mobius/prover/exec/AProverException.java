package mobius.prover.exec;

/**
 * A generic exception containing a description.
 * Used to have a single way to catch all the exceptions thrown by
 * the ProverEditor.
 */
public abstract class AProverException extends Exception {
  /**
   * Create a new prover exception.
   * @param description A description of the error.
   */
  public AProverException(String description) {
    super(description);
  }

}
