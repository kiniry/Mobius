package mobius.bmlvcgen.args.exceptions;

/**
 * Base class of exceptions thrown during command-line parsing.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class ArgException extends Exception {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;

  /**
   * Constructor.
   */
  public ArgException() {
    super();
  }

  /**
   * Constructor.
   * @param msg Message.
   */
  public ArgException(final String msg) {
    super(msg);
  }

  /**
   * Constructor.
   * @param cause Cause (inner exception).
   */
  public ArgException(final Throwable cause) {
    super(cause);
  }

  /**
   * Constructor.
   * @param msg Message.
   * @param cause Cause (inner exception).
   */
  public ArgException(final String msg, final Throwable cause) {
    super(msg, cause);
  }
}
