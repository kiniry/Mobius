package mobius.cct.classfile;

import java.io.IOException;
import java.io.OutputStream;

/**
 * Attribute in Java class file.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface Attribute {
  /**
   * Get attribute name.
   * @return Attribute name.
   */
  String getName();
  
  /**
   * Write attribute data to a stream.
   * @param os Output stream.
   * @throws IOException .
   */
  void writeData(OutputStream os) throws IOException;
}
