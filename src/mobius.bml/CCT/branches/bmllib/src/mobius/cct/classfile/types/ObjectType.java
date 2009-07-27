package mobius.cct.classfile.types;

import mobius.cct.classfile.ClassName;

/**
 * Object reference.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class ObjectType extends FieldType {
  /**
   * Class name.
   */
  private final ClassName fName;
  
  /**
   * Constructor.
   * @param name Class name.
   */
  public ObjectType(final ClassName name) {
    fName = name;
  }
  
  /**
   * See {@link ResultType}.
   * @return 'Lpackage/Class;'
   */
  @Override
  public String internalForm() {
    return "L" + fName.internalForm() + ";";
  }

  /**
   * See {@link ResultType}.
   * @return 'package.Class'
   */
  @Override
  public String externalForm() {
    return fName.externalForm();
  }

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
   * @return true
   */
  @Override
  public boolean isObject() {
    return true;
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
