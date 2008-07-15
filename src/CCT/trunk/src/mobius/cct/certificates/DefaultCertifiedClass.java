package mobius.cct.certificates;

import java.util.Iterator;

import mobius.cct.repositories.InvalidFormatException;
import mobius.cct.repositories.classfile.ClassFile;

/**
 * Default implementation of CertifiedClass.
 * @param <C> Type of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultCertifiedClass<C extends ClassFile> 
  implements CertifiedClass<C> {
  /**
   * Constructor.
   * @param cls Class file.
   * @throws InvalidFormatException if certificates are in invalid format.
   */
  DefaultCertifiedClass(final C cls) 
    throws InvalidFormatException {
    //TODO
  }
  
  /**
   * Get all certificates of this class.
   * @return Iterator.
   */
  public Iterator<Certificate> getCertificates() {
    //TODO
    return null;
  }
  
  /**
   * Get class file.
   * @return Class file.
   */
  public C getClassFile() {
    //TODO
    return null;
  }
}
