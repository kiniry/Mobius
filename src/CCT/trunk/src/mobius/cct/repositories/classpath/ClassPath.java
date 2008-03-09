package mobius.cct.repositories.classpath;

import java.util.Iterator;
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
   * @throws ClassNotFoundException Unable to read class.
   */
  <C extends ClassFile> C getClassFile(final String name, 
      final ClassReader<C> reader) throws ClassNotFoundException {
    return null;
  }

  /**
   * Read a certificate file.
   * @param <C> Type of class.
   * @param name FQN of a class.
   * @param reader Reader object used to read class.
   * @return Class returned by the reader.
   * @throws ClassNotFoundException Unable to read class.
   */
  <C extends ClassFile> C getCertFile(final String name, 
      final ClassReader<C> reader) throws ClassNotFoundException {
    return null;
  }
  
  /**
   * Append entry to the end of classpath.
   * @param entry Entry.
   */
  public void addEntry(final ClassPathEntry entry) {
  }
  
  /**
   * Remove all occurrences of given entry from classpath. 
   * Does nothing if the entry is not in the classpath.
   * @param entry Entry.
   */
  public void removeEntry(final ClassPathEntry entry) {
  }
  
  /**
   * Iterate over entries in this classpath. The iterator
   * does not have to support element removal.
   */
  public Iterator<ClassPathEntry> entries() {
    return null;
  }
}
