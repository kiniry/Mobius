package mobius.cct.classfile.types;

/**
 * 64-bit signed integer.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class LongType extends PrimitiveType {
  /**
   * Instance.
   */
  private static final LongType INSTANCE = new LongType();
  
  /**
   * Constructor.
   */
  private LongType() {
  }
  
  /**
   * Get instance of this class.
   * @return Instance.
   */
  public static LongType getInstance() {
    return INSTANCE;
  }
  
  /**
   * See {@link ResultType}.
   * @return 'J'
   */
  @Override
  public String internalForm() {
    return "J";
  }

  /**
   * See {@link ResultType}.
   * @return 'long'
   */
  @Override
  public String externalForm() {
    return "long";
  }

}
