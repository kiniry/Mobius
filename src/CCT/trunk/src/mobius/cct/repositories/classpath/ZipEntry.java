package mobius.cct.repositories.classpath;

import java.io.File;

import mobius.cct.repositories.Resource;

/**
 * ZIP/JAR file on a classpath.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class ZipEntry implements ClassPathEntry {
  /**
   * Constructor.
   * @param path File path. 
   */
  public ZipEntry(final File path) {
  }
  
  /**
   * Read class with given FQN using this archive
   * as a root of package hierarchy.
   * @param name Name of a class.
   * @return Class (as a <code>Resource</code>).
   * @throws ClassNotFoundException Cannot read requested file.
   */
  @Override
  public Resource getClassFile(final String name)
      throws ClassNotFoundException {
    return null;
  }
  
  /**
   * Read a certificate file.
   * @param name FQN of a class.
   * @return Resource which contains the class.
   * @throws ClassNotFoundException Cannot read requested file.
   */
  @Override
  public Resource getCertFile(final String name)
      throws ClassNotFoundException {
    return null;
  }
}
