package mobius.cct.repositories;

/**
 * Default implementation of a repository. Loads classes 
 * and certificates from system classpath.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 * @param <C> Type of class files.
 */
public class DefaultRepository<C extends ClassFile> 
  extends CachedRepository<C> {
  /**
   * Constructor.
   * @param reader Object used to read classes from streams.
   */
  public DefaultRepository(final ClassReader<C> reader) {
    super(new ClasspathRepository<C>(reader));
  }
}
