package mobius.cct.repositories;

import mobius.cct.classfile.ClassName;

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
   * Class name.
   */
  private final ClassName fName;
  
  /**
   * Constructor.
   * @param name Class name.
   */
  public NotFoundException(final ClassName name) {
    fName = name;
  }
  
  /**
   * Constructor.
   * @param name Class name.
   * @param msg Message.
   */
  public NotFoundException(final ClassName name,
                           final String msg) {
    super(msg);
    fName = name;
  }
  
  /**
   * Get message.
   * @return Message.
   */
  @Override
  public String getMessage() {
    final String msg = super.getMessage();
    if (msg == null) {
      return "Class not found: " + fName.externalForm();
    } else {
      return msg + "(" + fName.externalForm() + ")";
    }
  }
}
