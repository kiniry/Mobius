package mobius.cct.constantpool;

/**
 * Exception thrown if constant pool index is either invalid
 * or unusable.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class IllegalIndexException extends Exception {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;
  
  /** Illegal index. */
  private final int fIndex;
  
  /** 
   * Constructor. 
   * @param index Illegal index.
   **/
  public IllegalIndexException(final int index) {
    this.fIndex = index;
  }
  
  /** 
   * Constructor. 
   * @param msg Message. 
   * @param index Illegal index.
   **/
  public IllegalIndexException(final String msg, final int index) {
    super(msg);
    this.fIndex = index;
  }
  
  /**
   * Return index which caused the exception.
   * @return Index.
   */
  int getIndex() {
    return fIndex;
  }
}
