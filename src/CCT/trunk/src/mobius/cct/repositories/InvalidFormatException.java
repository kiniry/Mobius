package mobius.cct.repositories;

import java.io.IOException;

/**
 * Exception thrown by class readers if the class file is invalid.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class InvalidFormatException extends IOException {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;

  /**
   * Constructor.
   */
  public InvalidFormatException() {
  }
  
  /** 
   * Constructor.
   * @param msg Message.
   */
  public InvalidFormatException(final String msg) {
    super(msg);
  }
}
