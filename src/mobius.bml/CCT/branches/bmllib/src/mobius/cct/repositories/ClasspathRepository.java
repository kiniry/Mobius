package mobius.cct.repositories;

import java.io.IOException;

import mobius.cct.classfile.ClassFile;
import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.ClassReader;
import mobius.cct.repositories.classpath.ClassPath;

/**
 * This repository uses classpath to locate files on disk.
 * @param <C> Type of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class ClasspathRepository<C extends ClassFile> 
  implements Repository<C> {
  /**
   * Classpath used to locate files.
   */
  private final ClassPath fPath;
  
  /**
   * Reader used to read classes.
   */
  private final ClassReader<C> fReader;
  
  /**
   * Constructor. Creates repository using given classpath.
   * @param reader Object used to read class files.
   * @param path Classpath to use.
   */
  public ClasspathRepository(final ClassReader<C> reader,
                             final ClassPath path) {
    this.fReader = reader;
    this.fPath = path;
  }
  
  /**
   * Constructor. Creates repository using system classpath.
   * @param reader Object used to read class files.
   */
  public ClasspathRepository(final ClassReader<C> reader) {
    this.fReader = reader;
    this.fPath = ClassPath.getSystemClassPath();
  }  
  
  /**
   * Locate and read class file.
   * @param name Fully qualified class name.
   * @return ClassFile object.
   * @throws NotFoundException if the class cannot be found.
   * @throws IOException if it is thrown during class reading.
   */
  public C getClassFile(final ClassName name) 
    throws NotFoundException, IOException {
    return fPath.getClassFile(name, fReader);
  }
  
  /**
   * Locate and read certificate file.
   * @param name Fully qualified class name.
   * @return ClassFile object or null (if certificate cannot be found).
   * @throws IOException if it is thrown during class reading.
   */
  public C getCertFile(final ClassName name) 
    throws IOException { 
    try {
      return fPath.getCertFile(name, fReader);
    } catch (NotFoundException e) {
      return null;
    }
  }
}
