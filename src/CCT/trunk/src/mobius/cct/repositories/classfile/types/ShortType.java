package mobius.cct.repositories.classfile.types;

/**
 * 16-bit signed integer.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class ShortType extends PrimitiveType {
  /**
   * Instance.
   */
  private static final ShortType INSTANCE = new ShortType();
  
  /**
   * Constructor.
   */
  private ShortType() {
  }
  
  /**
   * Get instance of this class.
   * @return Instance.
   */
  public static ShortType getInstance() {
    return INSTANCE;
  }
  
  /**
   * See {@link FieldType}.
   * @return 'S'
   */
  @Override
  public String internalForm() {
    return "S";
  }

  /**
   * See {@link FieldType}.
   * @return 'short'
   */
  @Override
  public String externalForm() {
    return "short";
  }

}
