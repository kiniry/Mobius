package mobius.cct.classfile.types;

/**
 * Array reference.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class ArrayType extends FieldType {
  /**
   * Class name.
   */
  private final FieldType fElementType;
  
  /**
   * Constructor.
   * @param elementType Type of array elements.
   */
  public ArrayType(final FieldType elementType) {
    fElementType = elementType;
  }
  
  /**
   * See {@link ResultType}.
   * @return '[element_type'
   */
  @Override
  public String internalForm() {
    return "[" + fElementType.internalForm();
  }

  /**
   * See {@link ResultType}.
   * @return 'element_type[]'
   */
  @Override
  public String externalForm() {
    return fElementType.externalForm() + "[]";
  }

  /** 
   * Check if this type is an array type.
   * @return true
   */
  @Override
  public boolean isArray() {
    return true;
  }

  /** 
   * Check if this type is an object type.
   * @return false
   */
  @Override
  public boolean isObject() {
    return false;
  }
  
  /** 
   * Check if this type is a primitive type.
   * @return false
   */
  @Override
  public boolean isPrimitive() {
    return false;
  }
  
}
