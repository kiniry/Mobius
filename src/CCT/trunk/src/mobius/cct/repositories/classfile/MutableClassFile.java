package mobius.cct.repositories.classfile;

import java.io.IOException;
import java.io.OutputStream;

/**
 * Interface of modifiable class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface MutableClassFile extends ClassFile {
  /**
   * Get number of class attributes with given name.
   * @param name Attribute name.
   * @return Number of attributes (possibly 0).
   */
  int getClassAttrCount(String name);
  
  /**
   * Get i-th class attribute with given name.
   * Throws IllegalArgumentException if the index is invalid.
   * @param name Attribute name.
   * @param i Attribute index.
   * @return Attribute. 
   */
  Attribute getClassAttr(String name, int i);
  
  /**
   * Remove class attribute. Does nothing if the index is invalid.
   * @param name Attribute name.
   * @param i Attribute index.
   */
  void removeClassAttr(String name, int i);
  
  /**
   * Add class attribute.
   * @param attr Attribute.
   */
  void addClassAttr(Attribute attr);
  
  /**
   * Get number of method attributes with given name.
   * @param m Method name.
   * @param name Attribute name.
   * @return Number of attributes (possibly 0).
   */
  int getMethodAttrCount(MethodName m, String name);
  
  /**
   * Get i-th method attribute with given name.
   * Throws IllegalArgumentException if the index is invalid.
   * @param m Method name.
   * @param name Attribute name.
   * @param i Attribute index.
   * @return Attribute. 
   */
  Attribute getMethodAttr(MethodName m, String name, int i);
  
  /**
   * Remove method attribute. Does nothing if the index is invalid.
   * @param m Method name.
   * @param name Attribute name.
   * @param i Attribute index.
   */
  void removeMethodAttr(MethodName m, String name, int i);
  
  /**
   * Add method attribute.
   * @param m Method name.
   * @param attr Attribute.
   */
  void addMethodAttr(MethodName m, Attribute attr);
  
  /**
   * Write class to output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  void writeTo(OutputStream os) throws IOException;
  
}
