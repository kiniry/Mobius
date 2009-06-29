package mobius.cct.repositories.classpath;

import java.io.File;
import java.io.IOException;
import java.util.zip.ZipFile;

import mobius.cct.classfile.ClassName;
import mobius.cct.repositories.NotFoundException;
import mobius.cct.repositories.Resource;
import mobius.cct.repositories.ZipResource;

/**
 * ZIP/JAR file on a classpath. 
 * Class-Path attribute in the JAR file manifest is ignored.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class ZipEntry implements ClassPathEntry {
  /**
   * JAR file.
   */
  private final ZipFile fFile;
  
  /**
   * Constructor.
   * @param path File path. 
   */
  public ZipEntry(final File path) {
    try {
      fFile = new ZipFile(path);
    } catch (IOException e) {
      throw new IllegalArgumentException("path", e);
    }
  }
  
  /**
   * Constructor.
   * @param path Directory path. 
   */
  public ZipEntry(final String path) {
    try {
      fFile = new ZipFile(path);
    } catch (IOException e) {
      throw new IllegalArgumentException("path", e);
    }
  }
  
  /**
   * Read class with given FQN using this archive
   * as a root of package hierarchy.
   * @param name Name of a class.
   * @return Class (as a <code>Resource</code>).
   * @throws NotFoundException Cannot read requested file.
   */
  public Resource getClassFile(final ClassName name)
    throws NotFoundException {
    final char sep = System.getProperty("file.separator", "/").charAt(0);
    final String path = 
      name.internalForm().replace('/', sep) + ".class";
    final java.util.zip.ZipEntry entry = fFile.getEntry(path);
    if (entry == null) {
      throw new NotFoundException(name);
    } else {
      return new ZipResource(fFile, entry);
    }
  }
  
  /**
   * Read a certificate file.
   * @param name FQN of a class.
   * @return Resource which contains the class.
   * @throws NotFoundException Cannot read requested file.
   */
  public Resource getCertFile(final ClassName name)
    throws NotFoundException {
    final char sep = 
      System.getProperty("file.separator", "/").charAt(0);
    final String path = 
      name.internalForm().replace('/', sep) + ".cert";
    final java.util.zip.ZipEntry entry = fFile.getEntry(path);
    if (entry == null) {
      throw new NotFoundException(name);
    } else {
      return new ZipResource(fFile, entry);
    }
  }
}
