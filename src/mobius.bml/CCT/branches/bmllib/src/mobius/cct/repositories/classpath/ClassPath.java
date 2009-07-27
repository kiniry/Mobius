package mobius.cct.repositories.classpath;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import mobius.cct.classfile.ClassFile;
import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.ClassReader;
import mobius.cct.repositories.NotFoundException;
import mobius.cct.repositories.Resource;

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
   * List of entries.
   */
  private final List<ClassPathEntry> fEntries; 
  
  /**
   * Constructor - create classpath from string array.
   * @param path sequence of entries.
   */
  public ClassPath(final String[] path) {
    fEntries = new ArrayList<ClassPathEntry>(path.length);
    appendPath(path);
  }
  
  /**
   * Constructor - create classpath from string.
   * @param path Sequence of entries separated by path.separator .
   */
  public ClassPath(final String path) {
    fEntries = new ArrayList<ClassPathEntry>();
    appendPath(path);
  }
  
  /**
   * Constructor - creates empty classpath.
   */
  public ClassPath() {
    fEntries = new ArrayList<ClassPathEntry>();
  }
  
  /**
   * Return system classpath. Includes all entries from CLASSPATH 
   * and bootstrap classes.
   * @return Classpath.
   */
  public static ClassPath getSystemClassPath() {
    final ClassPath result = new ClassPath();
    result.appendPath(System.getProperty("sun.boot.class.path", ""));
    result.appendPath(System.getProperty("java.class.path", ""));
    result.appendPath(".");
    return result;
  }

  /**
   * Load class file.
   * @param name Class name (FQN).
   * @return Class file.
   * @throws NotFoundException If the class cannot be found.
   */
  private Resource findClass(final ClassName name) 
    throws NotFoundException {
    final Iterator<ClassPathEntry> i = fEntries.iterator();
    // CHECKSTYLE:OFF
    while (i.hasNext()) {
      try {
        return i.next().getClassFile(name);
      } catch (NotFoundException e) { 
        // Ignore
      }
    }
    // CHECKSTYLE:ON
    throw new NotFoundException(name);
  }

  /**
   * Load certificate file.
   * @param name Class name (FQN).
   * @return Class file.
   * @throws NotFoundException If the class cannot be found.
   */
  private Resource findCert(final ClassName name) 
    throws NotFoundException {
    final Iterator<ClassPathEntry> i = fEntries.iterator();
    // CHECKSTYLE:OFF
    while (i.hasNext()) {
      try {
        return i.next().getCertFile(name);
      } catch (NotFoundException e) {
        // Ignore
      }
    }
    // CKECKSTYLE:ON
    throw new NotFoundException(name);
  }
  
  /**
   * Read a class.
   * @param <C> Type of class.
   * @param name FQN of a class.
   * @param reader Reader object used to read class.
   * @return Class returned by the reader.
   * @throws NotFoundException Unable to read class.
   * @throws IOException If thrown by reader.
   */
  public <C extends ClassFile> 
    C getClassFile(final ClassName name, 
                   final ClassReader<C> reader) 
      throws NotFoundException, IOException {
    final InputStream r = findClass(name).open();
    final C result = reader.read(r);
    r.close();
    if (result == null) {
      throw new NotFoundException(name);
    }
    return result;
  }

  /**
   * Read a certificate file.
   * @param <C> Type of class.
   * @param name FQN of a class.
   * @param reader Reader object used to read class.
   * @return Class returned by the reader.
   * @throws NotFoundException Unable to read class.
   * @throws IOException If thrown by reader.
   */
  public <C extends ClassFile> 
    C getCertFile(final ClassName name, 
                  final ClassReader<C> reader) 
      throws NotFoundException, IOException {
    final InputStream r = findCert(name).open();
    final C result = reader.read(r);
    r.close();
    return result;
  }
  
  /**
   * Append entry to the end of classpath.
   * @param entry Entry.
   */
  public void addEntry(final ClassPathEntry entry) {
    fEntries.add(entry);
  }
  
  /**
   * Remove all occurrences of given entry from classpath. 
   * Does nothing if the entry is not in the classpath.
   * @param entry Entry.
   */
  public void removeEntry(final ClassPathEntry entry) {
    while (fEntries.remove(entry));
  }
  
  /**
   * Append all entries from string array.
   * @param path Sequence of entries.
   */
  public void appendPath(String[] path) {
    for (int i = 0; i < path.length; i++) {
      File f = new File(path[i]);
      try {
        if (f.isDirectory()) {
          fEntries.add(new DirEntry(f));
        } else {
          fEntries.add(new ZipEntry(f));
        }
      } catch (Exception e) {
        // Ignore invalid entries.
      }
    }    
  }
  
  /**
   * Append all entries from given string.
   * @param path Sequence of entries separated by path.separator .
   */
  public void appendPath(String path) {
    appendPath(path.split("\\:"));
  }
  
  /**
   * Iterate over entries in this classpath. The iterator
   * does not have to support element removal.
   */
  public Iterator<ClassPathEntry> getEntries() {
    return fEntries.iterator();
  }
}
