package mobius.cct.repositories.classpath;

import java.util.List;

import mobius.cct.repositories.ClassFile;
import mobius.cct.repositories.ClassReader;

/**
 * Sequence of directories and JAR/ZIP files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class ClassPath {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;


  /**
   * Constructor - create classpath from string.
   * @param path sequence of entries separated by ':'.
   */
  public ClassPath(final String path) {
  }
  
  /**
   * Constructor - creates empty classpath.
   */
  public ClassPath() {
  }
  
  /**
   * Return system classpath.
   * @return Classpath.
   */
  public static ClassPath getSystemClassPath() {
    return null;
  }
  
  /**
   * Read a class.
   * @param <C> Type of class.
   * @param name FQN of a class.
   * @param reader Reader object used to read class.
   * @return Class returned by the reader.
   */
  <C extends ClassFile> C getClassFile(final String name, 
      final ClassReader<C> reader) {
    return null;
  }

  /**
   * Read a certificate file.
   * @param <C> Type of class.
   * @param name FQN of a class.
   * @param reader Reader object used to read class.
   * @return Class returned by the reader.
   */
  <C extends ClassFile> C getCertFile(final String name, 
      final ClassReader<C> reader) {
    return null;
  }
  
  /**
   * Set entries.
   * @param e List of entries.
   */
  public void setEntries(final List<ClassPathEntry> e) {
  }
  
  /**
   * Get entries.
   * @return List of entries.
   */
  public List<ClassPathEntry> getEntries() {
    return null;
  }
}
