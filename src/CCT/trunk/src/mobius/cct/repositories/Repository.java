package mobius.cct.repositories;

import java.io.IOException;

/**
 * Repositories are objects used to locate class files.
 * @param <C> Type of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface Repository<C extends ClassFile> {
  /**
   * Locate and read class file.
   * @param name Fully qualified class name.
   * @return ClassFile object.
   * @throws NotFoundException if the class cannot be found.
   * @throws InvalidCertificateException if the class or certificate 
   * are in invalid format.
   * @throws IOException if it is thrown during class reading.
   */
  C getClassFile(String name) 
    throws NotFoundException, 
           IOException, 
           InvalidCertificateException;
}
