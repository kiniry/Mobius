package mobius.cct.repositories;

import java.io.IOException;

/**
 * Repository capable of using certificates stored in separate files.
 * This class uses two repositories
 * - one to load classes (possibly with embedded certficates)
 * - another one to load certificates.
 * These certificates are stored in class files with structure
 * identical to the certified class, but without any code.
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
   * Read class file and standalone certificate (if present).
   * @param name Fully qualified class name.
   * @return ClassFile object.
   * @throws NotFoundException if the class cannot be found.
   * @throws IOException if it is thrown during class reading.
   * @throws InvalidCertificateException if class or certificate is
   * in invalid format or if it is impossible to merge certificates.
   */
  @Override
  public C getClassFile(final String name) 
    throws NotFoundException, 
    IOException, 
    InvalidCertificateException {
    return null;
  }
  
}
