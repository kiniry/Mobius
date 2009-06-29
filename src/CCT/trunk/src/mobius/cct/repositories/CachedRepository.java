package mobius.cct.repositories;

import java.io.IOException;

import mobius.cct.cache.Cache;
import mobius.cct.cache.InfiniteCache;
import mobius.cct.classfile.ClassFile;
import mobius.cct.classfile.ClassName;

/**
 * Repository with cache. This class can be used to add
 * cache to any repository.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 * @param <C> Class file implementation.
 */
public class CachedRepository<C extends ClassFile>
  implements Repository<C> {
  /**
   * Cache used to store classes and certificates.
   */
  private final Cache<C> fCache;
  
  /**
   * Repository from which classes are read.
   */
  private final Repository<? extends C> fRepo;
  
  /**
   * Create repository with unlimited cache size.
   * @param repo Repository from which classes are read if
   * they cannot be found in cache.
   */
  public CachedRepository(final Repository<? extends C> repo) {
    fCache = new InfiniteCache<C>();
    this.fRepo = repo;
  }
  
  /**
   * Create repository with given cache.
   * @param repo Repository from which classes are read if
   * they cannot be found in cache.
   * @param cache Cache object used to store classes.
   */
  public CachedRepository(final Repository<? extends C> repo, 
                          final Cache<C> cache) {
    this.fCache = cache;
    this.fRepo = repo;
  }
  
  /**
   * Locate and read class file. The returned object is 
   * taken from cache if possible. 
   * @param name Fully qualified class name.
   * @return ClassFile object.
   * @throws NotFoundException if the class cannot be found.
   * @throws IOException if it is thrown during class reading.
   */
  public C getClassFile(final ClassName name) 
    throws NotFoundException, IOException {
    final String key = name.externalForm() + ".class";
    if (fCache.hasKey(key)) {
      return fCache.lookup(key);
    } else {
      final C cls = fRepo.getClassFile(name);
      fCache.update(key, cls);
      return cls;
    }
  }
  
  /**
   * Locate and read certificate file.
   * @param name Fully qualified class name.
   * @return ClassFile object or null (if certificate cannot be found).
   * @throws IOException if it is thrown during class reading.
   */
  public C getCertFile(final ClassName name) 
    throws IOException {
    final String key = name.externalForm() + ".cert";
    if (fCache.hasKey(key)) {
      return fCache.lookup(key);
    } else {
      final C cert = fRepo.getCertFile(name);
      if (cert != null) {
        fCache.update(key, cert);
      }
      return cert;
    }
  }
}
