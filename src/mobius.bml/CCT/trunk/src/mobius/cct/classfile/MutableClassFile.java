package mobius.cct.classfile;

import java.io.OutputStream;

/**
 * Interface of modifiable class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface MutableClassFile extends ClassFile {
  /**
   * Get writer. A writer is a class visitor which
   * saves all received class and method attributes
   * in a class file. Other data (methods, fields, ...)
   * is taken from the source class file.
   * @param os Stream to which the classfile will
   * be written by the returned writer.
   * @return Writer.
   */
  ClassVisitor getWriter(OutputStream os);
}
