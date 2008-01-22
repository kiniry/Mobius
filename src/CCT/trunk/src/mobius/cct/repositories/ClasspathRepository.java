package mobius.cct.repositories;

import java.io.IOException;

import mobius.cct.repositories.classpath.ClassPath;

/**
 * This repository uses classpath to locate files on disk.
 * @param <C> Type of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class ClasspathRepository<C extends ClassFile> 
  implements Repository<C> {
  /**
   * Constructor. Creates repository using given classpath.
   * @param reader Object used to read class files.
   * @param path Classpath to use.
   */
  public ClasspathRepository(final ClassReader<C> reader,
                             final ClassPath path) {
  }
  
  /**
   * Constructor. Creates repository using system classpath.
   * @param reader Object used to read class files.
   */
  public ClasspathRepository(final ClassReader<C> reader) {
  }  
  
  /**
   * Locate and read class file. 
   * @param name Fully qualified class name.
   * @return ClassFile object.
   * @throws NotFoundException file not in classpath.
   * @throws IOException if it is thrown during class reading.
   */
  @Override
  public C getClassFile(final String name) 
    throws NotFoundException, IOException {
    return null;
  }
}
