package mobius.cct.classfile.types;

/**
 * Boolean.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class BooleanType extends PrimitiveType {
  /**
   * Instance.
   */
  private static final BooleanType INSTANCE = new BooleanType();
  
  /**
   * Constructor.
   */
  private BooleanType() {
  }
  
  /**
   * Get instance of this class.
   * @return Instance.
   */
  public static BooleanType getInstance() {
    return INSTANCE;
  }
  
  /**
   * See {@link ResultType}.
   * @return 'Z'
   */
  @Override
  public String internalForm() {
    return "Z";
  }

  /**
   * See {@link ResultType}.
   * @return 'boolean'
   */
  @Override
  public String externalForm() {
    return "boolean";
  }

}
