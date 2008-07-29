package mobius.cct.certificates;

import mobius.cct.repositories.classfile.ClassFile;

/**
 * A class file with set of certificates.
 * @param <C> Type of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface CertifiedClass<C extends ClassFile> {
  /**
   * Visit all class certificates.
   * @param v Visitor.
   */
  void visitClassCertificates(ClassCertificateVisitor v);

  /**
   * Get class file.
   * @return Class file.
   */
  C getClassFile();
}
