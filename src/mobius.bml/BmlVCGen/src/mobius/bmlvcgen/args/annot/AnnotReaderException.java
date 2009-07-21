package mobius.bmlvcgen.args.annot;

/**
 * Class of exceptions thrown by AnnotReader.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class AnnotReaderException extends RuntimeException {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;
  
  /**
   * Constructor.
   * @param msg Message.
   */
  public AnnotReaderException(final String msg) {
    super(msg);
  }

  /**
   * Constructor.
   * @param msg Message.
   * @param cause Cause (inner exception).
   */
  public AnnotReaderException(final String msg, 
                              final Throwable cause) {
    super(msg, cause);
  }
  
}
