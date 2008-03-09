package mobius.cct.repositories;

import java.io.IOException;

/**
 * Repositories are objects used to locate class and certificate files.
 * @param <C> Type of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface Repository<C extends ClassFile> {
  /**
   * Locate and read class file.
   * @param name Fully qualified class name.
   * @return ClassFile object.
   * @throws NotFoundException if the class cannot be found.
   * @throws InvalidCertificateException if file format is invalid.
   * @throws IOException if it is thrown during class reading.
   */
  C getClassFile(String name) 
    throws NotFoundException, 
           IOException, 
           InvalidCertificateException;
  
  /**
   * Locate and read certificate file.
   * @param name Fully qualified class name.
   * @return ClassFile object or null (if certificate cannot be found).
   * @throws InvalidCertificateException if file format is invalid.
   * @throws IOException if it is thrown during class reading.
   */
  C getCertFile(String name) 
    throws IOException, 
           InvalidCertificateException;
}
