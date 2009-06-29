package mobius.cct.repositories;

import java.io.IOException;
import java.io.InputStream;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

/**
 * Entry in a Zip/Jar file.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class ZipResource implements Resource {
  /**
   * Zip file.
   */
  private final ZipFile fFile;
  
  /**
   * Entry path.
   */
  private final ZipEntry fEntry;
  
  /**
   * Constructor.
   * @param file ZIP/JAR file.
   * @param entry File path in the ZIP file.
   */
  public ZipResource(final ZipFile file, final ZipEntry entry) {
    this.fFile = file;
    this.fEntry = entry;
  }
  
  /**
   * Open the resource.
   * @return InputStrem from which file contents can be read.
   * @throws IOException .
   */
  public InputStream open() throws IOException {
    return fFile.getInputStream(fEntry);
  }

}
