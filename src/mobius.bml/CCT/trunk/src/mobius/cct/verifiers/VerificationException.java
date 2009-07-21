package mobius.cct.verifiers;

/**
 * Superclass of exceptions thrown during the verification
 * process.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class VerificationException extends Exception {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;

  /**
   * Constructor.
   */
  public VerificationException() {
  }

  /**
   * Constructor.
   * @param msg Message.
   */
  public VerificationException(final String msg) {
    super(msg);
  }

  /**
   * Constructor.
   * @param cause Cause.
   */
  public VerificationException(final Throwable cause) {
    super(cause);
  }

  /**
   * Constructor.
   * @param msg Message.
   * @param cause Cause.
   */
  public VerificationException(final String msg, 
                               final Throwable cause) {
    super(msg, cause);
  }

}
