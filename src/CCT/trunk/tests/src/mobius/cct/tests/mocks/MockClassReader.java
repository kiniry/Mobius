package mobius.cct.tests.mocks;

import java.io.IOException;
import java.io.InputStream;

import mobius.cct.repositories.classfile.ClassReader;

/**
 * Class reader used for tests.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 *
 */
public class MockClassReader 
  implements ClassReader<MockClassFile> {

  /**
   * Return a mock class file with no certificates.
   * @param is Input stream (ignored).
   */
  @Override
  public MockClassFile read(InputStream is) throws IOException {
    return new MockClassFile(new MockCertificate[]{});
  }

}
