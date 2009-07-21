package mobius.cct.classfile.types;

/**
 * Signed byte.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class ByteType extends PrimitiveType {
  /**
   * Instance.
   */
  private static final ByteType INSTANCE = new ByteType();
  
  /**
   * Constructor.
   */
  private ByteType() {
  }
  
  /**
   * Get instance of this class.
   * @return Instance.
   */
  public static ByteType getInstance() {
    return INSTANCE;
  }
  /**
   * See {@link ResultType}.
   * @return 'B'
   */
  @Override
  public String internalForm() {
    return "B";
  }

  /**
   * See {@link ResultType}.
   * @return 'byte'
   */
  @Override
  public String externalForm() {
    return "byte";
  }

}
