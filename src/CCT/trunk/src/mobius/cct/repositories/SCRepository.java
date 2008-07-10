package mobius.cct.repositories;

import java.io.IOException;

/**
 * Repository which uses different locations for class and certificate files.
 * This class uses two repositories
 * - one to load classes (possibly with embedded certficates)
 * - another one to load certificates.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 * @param <C> Class file implementation.
 */
public class SCRepository<C extends ClassFile> 
  implements Repository<C> {
  
  /**
   * Create repository.
   * @param classRepository Repository used to locate classes.
   * @param certRepository Repository used to locate standalone 
   * certificates.
   */
  public SCRepository(final Repository<C> classRepository,
                      final Repository<C> certRepository) {
  }

  /**
   * Locate and read class file.
   * @param name Fully qualified class name.
   * @return ClassFile object.
   * @throws NotFoundException if the class cannot be found.
   * @throws InvalidCertificateException if file format is invalid.
   * @throws IOException if it is thrown during class reading.
   */
  @Override
  public C getClassFile(final String name) 
    throws NotFoundException, IOException, InvalidCertificateException {
    return null;
  }
  
  /**
   * Locate and read certificate file.
   * @param name Fully qualified class name.
   * @return ClassFile object or null (if certificate cannot be found).
   * @throws InvalidCertificateException if file format is invalid.
   * @throws IOException if it is thrown during class reading.
   */
  @Override
  public C getCertFile(final String name) 
    throws IOException, 
           InvalidCertificateException {
    return null; 
  }  
}
