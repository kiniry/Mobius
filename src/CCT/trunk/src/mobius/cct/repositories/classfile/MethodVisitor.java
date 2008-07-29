package mobius.cct.repositories.classfile;

import mobius.cct.util.VisitorException;


/**
 * Interface of objects used to visit classes.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface MethodVisitor {
  /**
   * This method is called once before the method is parsed.
   * @param cls Method name.
   * @throws VisitorException .
   */
  void begin(MethodName m) throws VisitorException;
  
  /**
   * This method is called once for each method attribute.
   * @param attr Attribute.
   * @throws VisitorException .
   */
  void visitAttribute(Attribute attr) throws VisitorException;
  
  /**
   * Last method called.
   * @throws VisitorException .
   */
  void end() throws VisitorException;
}
