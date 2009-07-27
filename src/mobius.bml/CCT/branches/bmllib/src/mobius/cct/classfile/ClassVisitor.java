package mobius.cct.classfile;

import mobius.cct.util.VisitorException;

/**
 * Interface of objects used to visit classes.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface ClassVisitor {
  /**
   * This method is called once before the class is parsed.
   * @param cls Class name.
   * @throws VisitorException .
   */
  void begin(ClassName cls) throws VisitorException;
  
  /**
   * This method is called once for each class attribute.
   * @param attr Attribute.
   * @throws VisitorException .
   */
  void visitAttribute(Attribute attr) throws VisitorException;
  
  /**
   * This method is called once for each method.
   * @param m Method name.
   * @return Visitor which will be used to visit the method.
   * If null is returned, the method is not visited.
   * @throws VisitorException .
   */
  MethodVisitor visitMethod(MethodName m) throws VisitorException;
  
  /**
   * Last method called.
   * @throws VisitorException .
   */
  void end() throws VisitorException;
}
