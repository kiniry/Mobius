package mobius.cct.repositories.classpath;

import java.io.File;

import mobius.cct.repositories.FileResource;
import mobius.cct.repositories.NotFoundException;
import mobius.cct.repositories.Resource;

/**
 * Directory on a classpath.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class DirEntry implements ClassPathEntry {
  /** 
   * Directory path.
   */
  private final File fPath;
  
  /**
   * Constructor.
   * @param path Directory path. 
   */
  public DirEntry(final File path) {
    if ((path == null) || (!path.isDirectory())) {
      throw new IllegalArgumentException("path");
    }
    this.fPath = path;
  }

  /**
   * Constructor.
   * @param path Directory path. 
   */
  public DirEntry(final String path) {
    if (path == null) {
      throw new IllegalArgumentException("path");
    }
    final File f = new File(path);
    if (!f.isDirectory()) {
      throw new IllegalArgumentException("path");
    }
    this.fPath = new File(path);
  }
  
  /**
   * 
   * Read class with given FQN using this directory
   * as a root of package hierarchy.
   * @param name Name of a class (FQN).
   * @return Class (as a <code>Resource</code>).
   * @throws NotFoundException Cannot read requested file.
   */
  @Override
  public Resource getClassFile(final String name) 
    throws NotFoundException {
    final char sep = System.getProperty("file.separator", "/").charAt(0);
    final File f = new File(fPath, name.replace('.', sep) + ".class");
    if ((!f.exists()) || (!f.isFile())) {
      throw new NotFoundException();
    }
    return new FileResource(f);
  }
  
  /**
   * Read a certificate file.
   * @param name FQN of a class.
   * @return Resource which contains the class.
   * @throws NotFoundException Cannot read requested file.
   */
  @Override
  public Resource getCertFile(final String name) 
    throws NotFoundException {
    final char sep = System.getProperty("file.separator", "/").charAt(0);
    final File f = new File(fPath, name.replace('.', sep) + ".cert");
    if ((!f.exists()) || (!f.isFile())) {
      throw new NotFoundException();
    }
    return new FileResource(f);
  }
}
