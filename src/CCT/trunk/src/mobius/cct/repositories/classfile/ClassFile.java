package mobius.cct.repositories.classfile;

import java.util.Iterator;

/**
 * This interface contains methods common to all
 * implementations of class file.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface ClassFile {
  /**
   * Return all class attributes.
   * @return Iterator.
   */
  Iterator<Attribute> classAttributes();
  
  /**
   * Return all methods of this class.
   * @return Iterator.
   */
  Iterator<MethodName> getMethods();
  
  /**
   * Return all attributes of given method.
   * @param m Method name.
   * @return Iterator.
   */
  Iterator<Attribute> methodAttributes(MethodName m);
}
