package mobius.cct.repositories;

import java.io.IOException;

import mobius.cct.classfile.ClassFile;
import mobius.cct.classfile.ClassName;

/**
 * Repositories are objects used to locate class and certificate files.
 * @param <C> Type of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface Repository<C extends ClassFile> {
  /**
   * Locate and read class file.
   * @param name Fully qualified class name.
   * @return ClassFile object.
   * @throws NotFoundException if the class cannot be found.
   * @throws IOException if it is thrown during class reading.
   */
  C getClassFile(ClassName name) 
    throws NotFoundException, 
           IOException;
  
  /**
   * Locate and read certificate file.
   * @param name Fully qualified class name.
   * @return ClassFile object or null (if certificate cannot be found).
   * @throws IOException if it is thrown during class reading.
   */
  C getCertFile(ClassName name) 
    throws IOException;
}
