package mobius.bmlvcgen.finder.exceptions;

/**
 * Exception thrown by class finders.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class FinderException extends Exception {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;

  /**
   * Constructor.
   */
  public FinderException() {
  }
  
  /**
   * Constructor.
   * @param msg Message.
   */
  public FinderException(final String msg) {
    super(msg);
  }
  
  /**
   * Constructor.
   * @param cause Cause (inner exception).
   */
  public FinderException(final Throwable cause) {
    super(cause);
  }
  
  /**
   * Constructor.
   * @param msg Message.
   * @param cause Cause (inner exception).
   */
  public FinderException(final String msg, final Throwable cause) {
    super(msg, cause);
  }
  
}
