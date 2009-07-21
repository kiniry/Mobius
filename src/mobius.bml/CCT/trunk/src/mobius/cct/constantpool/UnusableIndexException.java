package mobius.cct.constantpool;

/**
 * Exception thrown if constant pool index is unusable - valid,
 * but lies inside a multi-index constant.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class UnusableIndexException extends IllegalIndexException {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;
  
  /** Constructor. 
   * @param index Illegal index.
   **/
  public UnusableIndexException(final int index) {
    super(index);
  }
  
  /** 
   * Constructor. 
   * @param msg Message.
   * @param index Illegal index.
   **/
  public UnusableIndexException(final String msg, final int index) {
    super(msg, index);
  }
}
