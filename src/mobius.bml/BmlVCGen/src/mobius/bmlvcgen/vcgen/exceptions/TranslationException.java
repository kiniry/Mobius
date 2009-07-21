package mobius.bmlvcgen.vcgen.exceptions;

/**
 * Exception raised by translation procedures.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class TranslationException extends RuntimeException {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;

  /** Constructor. */
  public TranslationException() {
  }
  
  /**
   * Constructor.
   * @param msg Message.
   */
  public TranslationException(final String msg) {
    super(msg);
  }

  /**
   * Constructor.
   * @param cause Cause (inner exception).
   */
  public TranslationException(final Throwable cause) {
    super(cause);
  }
  
  /**
   * Constructor.
   * @param msg Message.
   * @param cause Cause (inner exception).
   */
  public TranslationException(final String msg, 
                              final Throwable cause) {
    super(msg, cause);
  }
  
  
  
}
