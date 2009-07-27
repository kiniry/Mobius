package mobius.cct.repositories;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

/**
 * File wrapped in a Resource.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class FileResource implements Resource {
  /**
   * File path.
   */
  private final File fFile;
  
  /**
   * Constructor - create resource.
   * @param file File path.
   */
  public FileResource(final File file) {
    this.fFile = file;
  }

  /**
   * Open the file.
   * @return FileInputStream from which the file can be read.
   * @throws IOException if an error occurs.
   */
  public InputStream open() throws IOException {
    return new FileInputStream(fFile);
  }

}
