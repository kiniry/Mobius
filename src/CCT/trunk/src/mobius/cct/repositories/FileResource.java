package mobius.cct.repositories;

import java.io.IOException;
import java.io.InputStream;

/**
 * File wrapped in a Resource.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class FileResource implements Resource {
  
  /**
   * Close the file.
   * @throws IOException if an error occurs.
   */
  @Override
  public void close() throws IOException {
  }

  /**
   * Close the file. This resource can be reopened.
   * @return FileInputStream from which the file can be read.
   * @throws IOException if an error occurs.
   */
  @Override
  public InputStream open() throws IOException {
    return null;
  }

}
