package mobius.cct.classfile.types;

/**
 * Unicode character.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class CharType extends PrimitiveType {
  /**
   * Instance.
   */
  private static final CharType INSTANCE = new CharType();
  
  /**
   * Constructor.
   */
  private CharType() {
  }
  
  /**
   * Get instance of this class.
   * @return Instance.
   */
  public static CharType getInstance() {
    return INSTANCE;
  }
  
  /**
   * See {@link ResultType}.
   * @return 'C'
   */
  @Override
  public String internalForm() {
    return "C";
  }

  /**
   * See {@link ResultType}.
   * @return 'char'
   */
  @Override
  public String externalForm() {
    return "char";
  }

}
