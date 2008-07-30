package mobius.cct.classfile.types;

/**
 * Void type.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class VoidType extends ResultType {
  /**
   * Instance.
   */
  private static final VoidType INSTANCE = new VoidType();
  
  /**
   * Constructor.
   */
  private VoidType() {
  }
  
  /**
   * Get instance of this class.
   * @return Instance.
   */
  public static VoidType getInstance() {
    return INSTANCE;
  }
  
  /**
   * See {@link ResultType}.
   * @return 'V'
   */
  @Override
  public String internalForm() {
    return "V";
  }

  /**
   * See {@link ResultType}.
   * @return 'void'
   */
  @Override
  public String externalForm() {
    return "void";
  }

  /**
   * Check if this object represents an array type.
   * @return false.
   */
  @Override
  public boolean isArray() {
    return false;
  }

  /**
   * Check if this object represents an object type.
   * @return false.
   */
  @Override
  public boolean isObject() {
    return false;
  }

  /**
   * Check if this object represents a primitive type.
   * @return false.
   */
  @Override
  public boolean isPrimitive() {
    return false;
  }

  /**
   * Check if this object represents the void type.
   * @return true.
   */
  @Override
  public boolean isVoid() {
    return true;
  }

}
