package mobius.cct.constantpool;

/**
 * Exception thrown if constant pool index is invalid - smaller than
 * one or greater than constant pool size.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class InvalidIndexException extends IllegalIndexException {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;
  
  /** Constructor.
   * @param index Illegal index.
   **/
  public InvalidIndexException(final int index) {
    super(index);
  }
  
  /** 
   * Constructor. 
   * @param msg Message.
   * @param index Illegal index. 
   **/
  public InvalidIndexException(final String msg, final int index) {
    super(msg, index);
  }
}
