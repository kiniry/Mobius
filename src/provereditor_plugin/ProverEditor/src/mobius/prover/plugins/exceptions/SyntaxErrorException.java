/*
 * Created on Mar 7, 2005
 *
 */
package mobius.prover.plugins.exceptions;


/**
 * Exception to be thrown in case of a syntax error
 * detected by the prover.
 */
public class SyntaxErrorException extends ProverException {
  /** Serial UID to have much more fun... */
  private static final long serialVersionUID = 1L;

  /**
   * The constructor. Takes a description of the error as parameter.
   * @param description The source of the error.
   */
  public SyntaxErrorException(final String description) {
    super(description);
  }

}
