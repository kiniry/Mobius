package mobius.cct.certificates;

import mobius.cct.repositories.InvalidFormatException;
import mobius.cct.repositories.classfile.ClassFile;

/**
 * Interface of objects used to extract certificates from
 * class files.
 * @param <C> Type of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface CertificateParser<C extends ClassFile> {
  
  /**
   * Read certificates from a class.
   * @param c Class file.
   * @return Class with parsed certificates.
   * @throws InvalidFormatException If certificate format
   * is invalid
   */
  CertifiedClass<C> parse(C c) throws InvalidFormatException;
}
