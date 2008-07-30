package mobius.cct.classfile;

import mobius.cct.util.VisitorException;

/**
 * This interface contains methods common to all
 * implementations of class file.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface ClassFile {
  /**
   * Use visitor to visit the class.
   * @param v Visitor.
   * @throws VisitorException If thrown by the visitor.
   */
  void visit(ClassVisitor v) throws VisitorException;
}
