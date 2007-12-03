package mobius.prover.exec;

/**
 * A generic exception containing a description.
 * Used to have a single way to catch all the exceptions thrown by
 * the ProverEditor.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public abstract class AProverException extends Exception {
  /**
   * Create a new prover exception.
   * @param description A description of the error.
   */
  public AProverException(final String description) {
    super(description);
  }

}
