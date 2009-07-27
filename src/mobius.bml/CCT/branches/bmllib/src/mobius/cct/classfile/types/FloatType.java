package mobius.cct.classfile.types;

/**
 * Single precision float.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class FloatType extends PrimitiveType {
  /**
   * Instance.
   */
  private static final FloatType INSTANCE = new FloatType();
  
  /**
   * Constructor.
   */
  private FloatType() {
  }
  
  /**
   * Get instance of this class.
   * @return Instance.
   */
  public static FloatType getInstance() {
    return INSTANCE;
  }
  
  /**
   * See {@link ResultType}.
   * @return 'F'
   */
  @Override
  public String internalForm() {
    return "F";
  }

  /**
   * See {@link ResultType}.
   * @return 'float'
   */
  @Override
  public String externalForm() {
    return "float";
  }

}
