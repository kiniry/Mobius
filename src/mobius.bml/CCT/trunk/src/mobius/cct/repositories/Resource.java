package mobius.cct.repositories;

import java.io.IOException;
import java.io.InputStream;

/**
 * Resource is an object that can be opened and read.
 * Reading from a closed resource results in an IOException.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface Resource {
  /**
   * Open (prepare for reading).
   * @return InputStream from which the resource can be read.
   * @throws IOException if the resource cannot be opened.
   */
  InputStream open() throws IOException;
  
}
