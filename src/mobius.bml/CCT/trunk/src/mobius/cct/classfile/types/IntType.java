package mobius.cct.classfile.types;

/**
 * 32-bit signed integer.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class IntType extends PrimitiveType {
  /**
   * Instance.
   */
  private static final IntType INSTANCE = new IntType();
  
  /**
   * Constructor.
   */
  private IntType() {
  }
  
  /**
   * Get instance of this class.
   * @return Instance.
   */
  public static IntType getInstance() {
    return INSTANCE;
  }
  
  /**
   * See {@link ResultType}.
   * @return 'I'
   */
  @Override
  public String internalForm() {
    return "I";
  }

  /**
   * See {@link ResultType}.
   * @return 'int'
   */
  @Override
  public String externalForm() {
    return "int";
  }

}
