package mobius.cct.repositories;

/**
 * Exception thrown by Repository objects if a class 
 * cannot be located.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class NotFoundException extends Exception {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;

  /**
   * Constructor.
   */
  public NotFoundException() {
  }
  
  /**
   * Constructor.
   * @param msg Message.
   */
  public NotFoundException(final String msg) {
    super(msg);
  }
}
