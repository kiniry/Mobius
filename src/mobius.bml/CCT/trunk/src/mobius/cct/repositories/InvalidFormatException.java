package mobius.cct.repositories;

import java.io.IOException;

/**
 * Exception thrown if the class file is invalid.
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

  /**
   * Constructor.
   * @param cause Cause.
   */
  public InvalidFormatException(final Throwable cause) {
    super(cause.getLocalizedMessage()); //super(cause); not java1.5 compat.
  }
  
  /**
   * Constructor.
   * @param msg Message.
   * @param cause Cause.
   */
  public InvalidFormatException(final String msg, 
                                final Throwable cause) {
    super(msg); //super(msg, cause); not java1.5 compat.
  }
  
}
