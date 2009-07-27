package mobius.cct.certificates;

import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.MethodName;
import mobius.cct.util.VisitorException;

/**
 * Interface of objects used to visit class certificates.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface ClassCertificateVisitor {
  /**
   * This method is called once before any 
   * certificates are visited.
   * @param cls Class name.
   * @throws VisitorException .
   */
  void begin(ClassName cls) throws VisitorException;
  
  /**
   * Visit class certificate. 
   * @param cert Class certificate.
   * @throws VisitorException .
   */
  void visitClassCert(ClassCertificate cert) throws VisitorException;
  
  /**
   * Visit method certificates.
   * @param m Method name.
   * @return Visitor used to visit method certificates.
   * Can be null.
   * @throws VisitorException .
   */
  MethodCertificateVisitor visitMethod(MethodName m) throws VisitorException;
  
  /**
   * This method is called after all certificates
   * have been visited.
   * @throws VisitorException .
   */
  void end() throws VisitorException;
}
