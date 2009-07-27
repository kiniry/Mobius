package mobius.cct.certificates;

import mobius.cct.classfile.ClassFile;
import mobius.cct.repositories.InvalidFormatException;
import mobius.cct.util.VisitorException;

/**
 * Interface of objects used to extract certificates from
 * class files.
 * @param <C> Type of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface CertificateParser<C extends ClassFile> {  
  /**
   * Read class certificates and visit them.
   * @param c Class file.
   * @param v Object used to visit parsed certificates.
   * @throws InvalidFormatException If certificate format
   * is invalid
   * @throws VisitorException .
   */
  void parse(C c, ClassCertificateVisitor v) 
    throws InvalidFormatException, VisitorException;
}
