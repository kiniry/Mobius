package mobius.cct.repositories;

/**
 * Exception thrown if added certificate does not match class signature.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class InvalidCertificateException extends Exception {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;

  /**
   * Constructor.
   */
  public InvalidCertificateException() {
  }
  
  /** 
   * Constructor.
   * @param msg Message.
   */
  public InvalidCertificateException(final String msg) {
    super(msg);
  }
}
