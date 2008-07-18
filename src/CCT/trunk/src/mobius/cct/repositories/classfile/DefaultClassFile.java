package mobius.cct.repositories.classfile;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.Iterator;

/**
 * Default implementation of class file. No external 
 * libraries (bcel, asm, ...) are used.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultClassFile implements MutableClassFile {
  /**
   * Constructor - read class from input stream.
   * @param is Input stream.
   * @throws IOException if the file cannot be parsed. If its format is invalid,
   *    InvalidFormatException should be thrown.
   */
  public DefaultClassFile(final InputStream is) throws IOException {
  }

  /**
   * Return all methods of this class.
   * @return Iterator.
   */
  @Override
  public Iterator<MethodName> getMethods() {
    //TODO
    return null;
  }
  
  /**
   * Add class attribute.
   * @param attr Attribute.
   */
  @Override
  public void addClassAttr(final Attribute attr) {
    // TODO Auto-generated method stub
    
  }

  /**
   * Add method attribute.
   * @param m Method name.
   * @param attr Attribute.
   */  
  @Override
  public void addMethodAttr(final MethodName m, 
                            final Attribute attr) {
    // TODO Auto-generated method stub
    
  }

  /**
   * Get class attribute.
   * @param name Attribute name.
   * @param i Attribute index.
   * @return Attribute.
   */  
  @Override
  public Attribute getClassAttr(final String name, final int i) {
    // TODO Auto-generated method stub
    return null;
  }

  /**
   * Get number of class attributes.
   * @param name Attribute name.
   * @return Attribute count.
   */  
  @Override
  public int getClassAttrCount(final String name) {
    // TODO Auto-generated method stub
    return 0;
  }
  
  /**
   * Get method attribute.
   * @param m Method name.
   * @param name Attribute name.
   * @param i Attribute index.
   * @return Attribute.
   */  
  @Override
  public Attribute getMethodAttr(final MethodName m, 
                                 final String name, 
                                 final int i) {
    // TODO Auto-generated method stub
    return null;
  }

  /**
   * Get number of method attributes.
   * @param m Method name.
   * @param name Attribute name.
   * @return Attribute count.
   */  
  @Override
  public int getMethodAttrCount(final MethodName m, 
                                final String name) {
    // TODO Auto-generated method stub
    return 0;
  }

  /**
   * Remove class attribute.
   * @param name Attribute name.
   * @param i Attribute index.
   */  
  @Override
  public void removeClassAttr(final String name, final 
                              int i) {
    // TODO Auto-generated method stub
    
  }
  
  /**
   * Remove method attribute.
   * @param m Method name.
   * @param name Attribute name.
   * @param i Attribute index.
   */  
  @Override
  public void removeMethodAttr(final MethodName m, 
                               final String name, 
                               final int i) {
    // TODO Auto-generated method stub
    
  }

  /**
   * Write class to output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  @Override
  public void writeTo(final OutputStream os) throws IOException {
    // TODO Auto-generated method stub
    
  }

  /**
   * Get all class attributes.
   * @return Iterator.
   */
  @Override
  public Iterator<Attribute> classAttributes() {
    // TODO Auto-generated method stub
    return null;
  }

  /**
   * Get all attributes of a method.
   * @param m Method name.
   * @return Iterator.
   */
  @Override
  public Iterator<Attribute> methodAttribute(final MethodName m) {
    // TODO Auto-generated method stub
    return null;
  }

}
