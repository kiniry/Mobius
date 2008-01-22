package mobius.cct.repositories.classpath;

import mobius.cct.repositories.Resource;

/**
 * Part of a classpath.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface ClassPathEntry {
  /**
   * Read a class.
   * @param name FQN of a class.
   * @return Resource which contains the class.
   */
  Resource getClassFile(final String name);
  
  /**
   * Read a certificate file.
   * @param name FQN of a class.
   * @return Resource which contains the class.
   */
  Resource getCertFile(final String name);
}
