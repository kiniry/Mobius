package mobius.cct.util;

/**
 * Superclass of exceptions thrown by various visitors.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class VisitorException extends Exception {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;

  /**
   * Constructor.
   */
  public VisitorException() {
  }

  /**
   * Constructor.
   * @param msg Message.
   */
  public VisitorException(final String msg) {
    super(msg);
  }

  /**
   * Constructor.
   * @param cause Cause.
   */
  public VisitorException(final Throwable cause) {
    super(cause);
  }

  /**
   * Constructor.
   * @param msg Message.
   * @param cause Cause.
   */
  public VisitorException(final String msg, 
                          final Throwable cause) {
    super(msg, cause);
  }

}
