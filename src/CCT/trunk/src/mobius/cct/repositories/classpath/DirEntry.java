package mobius.cct.repositories.classpath;

import java.io.File;

import mobius.cct.repositories.Resource;

/**
 * Directory on a classpath.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DirEntry implements ClassPathEntry {
  /**
   * Constructor.
   * @param path Directory path. 
   */
  public DirEntry(final File path) {
  }
  
  /**
   * 
   * Read class with given FQN using this directory
   * as a root of package hierarchy.
   * @param name Name of a class.
   * @return Class (as a <code>Resource</code>).
   */
  @Override
  public Resource getClassFile(final String name) {
    return null;
  }
  
  /**
   * Read a certificate file.
   * @param name FQN of a class.
   * @return Resource which contains the class.
   */
  @Override
  public Resource getCertFile(final String name) {
    return null;
  }
}
