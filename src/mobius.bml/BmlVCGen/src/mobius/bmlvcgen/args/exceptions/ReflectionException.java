package mobius.bmlvcgen.args.exceptions;

/**
 * RuntimeException used to wrap exceptions
 * throws by reflection operations.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class ReflectionException extends RuntimeException {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;

  /**
   * Constructor.
   * @param cause Cause (inner exception).
   */
  public ReflectionException(final Throwable cause) {
    super(cause);
  }
  
}
