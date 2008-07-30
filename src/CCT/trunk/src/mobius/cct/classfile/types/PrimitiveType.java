package mobius.cct.classfile.types;

/**
 * Superclass of all primitve types.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public abstract class PrimitiveType extends FieldType {

  /** 
   * Check if this type is an array type.
   * @return false
   */
  @Override
  public boolean isArray() {
    return false;
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
   * @return true
   */
  @Override
  public boolean isPrimitive() {
    return true;
  }

}
