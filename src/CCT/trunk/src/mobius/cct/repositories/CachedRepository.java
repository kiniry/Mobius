package mobius.cct.repositories;

import java.io.IOException;
import mobius.cct.cache.Cache;

/**
 * Repository with cache. This class can be used to add
 * cache to any repository.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 * @param <C> Class file implementation.
 */
public class CachedRepository<C extends ClassFile>
  implements Repository<C> {

  /**
   * Create repository with unlimited cache size.
   * @param repo Repository from which classes are read if
   * they cannot be found in cache.
   */
  public CachedRepository(final Repository<C> repo) {
  }
  
  /**
   * Create repository with given cache.
   * @param repo Repository from which classes are read if
   * they cannot be found in cache.
   * @param cache Cache object used to store classes.
   */
  public CachedRepository(final Repository<C> repo, 
                          final Cache<C> cache) {
  }
  
  /**
   * Locate and read class file. The returned object is 
   * taken from cache if possible. 
   * @param name Fully qualified class name.
   * @return ClassFile object.
   * @throws NotFoundException if the class cannot be found.
   * @throws InvalidCertificateException if the class or certificate 
   * are in invalid format.
   * @throws IOException if it is thrown during class reading.
   */
  @Override
  public C getClassFile(final String name) 
    throws NotFoundException, IOException, InvalidCertificateException {
    return null;
  }
  
}
