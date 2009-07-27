package mobius.cct.certificates;

import mobius.cct.classfile.MethodName;

/**
 * Interface of objects used to visit class certificates.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface MethodCertificateVisitor {
  /**
   * This method is called once before any 
   * certificates are visited.
   * @param m Method name.
   */
  void begin(MethodName m);
  
  /**
   * Visit method certificate.
   * @param cert Method certificate.
   */
  void visitMethodCert(MethodCertificate cert);
  
  /**
   * This method is called after all certificates
   * have been visited.
   */
  void end();
}
