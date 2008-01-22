package mobius.cct.repositories;

import java.io.IOException;
import java.io.InputStream;

/**
 * Resource is an object that can be opened, read and closed.
 * Reading from which has not been opened results in an IOException.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface Resource {
  /**
   * Open (prepare for reading).
   * @return InputStream from which the file can be read.
   * @throws IOException if the resource cannot be opened.
   */
  InputStream open() throws IOException;
  
  /**
   * Close resource. The resource may not be reopened.
   * @throws IOException if the resource cannot be closed.
   */
  void close() throws IOException;
}
