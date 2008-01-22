package mobius.cct.repositories;

import java.io.IOException;
import java.io.InputStream;

/**
 * Class reader for default class file implementation.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultClassReader 
  implements ClassReader<DefaultClassFile> {

  /**
   * Read class from byte stream.
   * @param is Input stream.
   * @return ClassFile object.
   * @throws IOException if an error occurs during reading.
   */
  @Override
  public DefaultClassFile read(final InputStream is) 
    throws IOException {
    return null;
  }

}
