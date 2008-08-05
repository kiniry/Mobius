package mobius.cct.constantpool;

/**
 * Exception thrown during constant pool parsing if 
 * a constant of unknown/unsupported type is encountered.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class UnknownConstantException extends Exception {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;
  
  /**
   * Constant type.
   */
  private final int fType;
  
  /**
   * Constructor.
   * @param type Constant type.
   */
  public UnknownConstantException(final int type) {
    fType = type;
  }
  
  /**
   * Constructor.
   * @param msg Message.
   * @param type Constant type.
   */
  public UnknownConstantException(final String msg, 
                                  final int type) {
    super(msg);
    fType = type;
  }
  
  /**
   * Get constant type.
   * @return Constant type.
   */
  public int getType() {
    return fType;
  }
  
  /**
   * Get message (not localized).
   * @return Message.
   */
  @Override
  public String getMessage() {
    if (super.getMessage() != null) {
      return super.getMessage();
    } else {
      return "Unknown constant type: " + fType;
    }
  }
  
}
