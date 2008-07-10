package mobius.cct.repositories.classpath;

import mobius.cct.repositories.NotFoundException;
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
   * @throws NotFoundException Cannot read requested file.
   */
  Resource getClassFile(final String name) 
    throws NotFoundException;
  
  /**
   * Read a certificate file.
   * @param name FQN of a class.
   * @return Resource which contains the class.
   * @throws NotFoundException Cannot read requested file.
   */
  Resource getCertFile(final String name)
    throws NotFoundException;
}
