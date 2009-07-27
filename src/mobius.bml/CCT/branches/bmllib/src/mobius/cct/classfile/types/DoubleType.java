package mobius.cct.classfile.types;

/**
 * Double precision float.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class DoubleType extends PrimitiveType {
  /**
   * Instance.
   */
  private static final DoubleType INSTANCE = new DoubleType();
  
  /**
   * Constructor.
   */
  private DoubleType() {
  }
  
  /**
   * Get instance of this class.
   * @return Instance.
   */
  public static DoubleType getInstance() {
    return INSTANCE;
  }
  
  /**
   * See {@link ResultType}.
   * @return 'D'
   */
  @Override
  public String internalForm() {
    return "D";
  }

  /**
   * See {@link ResultType}.
   * @return 'double'
   */
  @Override
  public String externalForm() {
    return "double";
  }

}
