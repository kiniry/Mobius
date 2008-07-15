package mobius.cct.certificates;

import mobius.cct.repositories.InvalidFormatException;
import mobius.cct.repositories.classfile.ClassFile;

/**
 * Default implementation of CertificateParser.
 * @param <C> Type of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultCertificateParser<C extends ClassFile>
  implements CertificateParser<C> {

  /**
   * Parse class file and read certificates.
   * @param c Class file.
   * @return Class with certificates.
   * @throws InvalidFormatException If certificate format
   * is invalid
   */
  @Override
  public CertifiedClass<C> parse(final C c) 
    throws InvalidFormatException {
    return new DefaultCertifiedClass<C>(c);
  }

}
