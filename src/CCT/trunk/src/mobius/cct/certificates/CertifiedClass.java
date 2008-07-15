package mobius.cct.certificates;

import java.util.Iterator;

import mobius.cct.repositories.classfile.ClassFile;

/**
 * A class file with set of certificates.
 * @param <C> Type of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface CertifiedClass<C extends ClassFile> {
  /**
   * Get all certificates of this class.
   * @return Iterator.
   */
  Iterator<Certificate> getCertificates();

  /**
   * Get class file.
   * @return Class file.
   */
  C getClassFile();
}
