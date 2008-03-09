package mobius.cct.repositories.classpath;

/**
 * Exception thrown by classpath objects when requested resource
 * is not in the classpath or cannot be read.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class ClassNotFoundException extends Exception {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;

  /**
   * Constructor.
   */
  public ClassNotFoundException() {
  }
  
  /**
   * Constructor.
   * @param msg Message.
   */
  public ClassNotFoundException(final String msg) {
    super(msg);
  }
  
  /**
   * Constructor.
   * @param cause Cause.
   */
  public ClassNotFoundException(final Throwable cause) {
    super(cause);
  }
}
