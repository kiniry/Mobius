package mobius.cct.repositories;

import mobius.cct.classfile.ClassFile;
import mobius.cct.classfile.ClassReader;

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
