package mobius.cct.tests.mocks;

import java.io.IOException;
import java.io.InputStream;

import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.ClassReader;

/**
 * Class reader used for tests.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 *
 */
public class MockClassReader 
  implements ClassReader<MockClassFile> {
  /**
   * Classfile returned by read.
   */
  private MockClassFile fClassFile;
  
  /**
   * Constructor.
   */
  public MockClassReader() {
    fClassFile = 
      new MockClassFile(ClassName.parseInternal("testpackage/TestClass"));
  }
  
  /**
   * Set classfile returned by read().
   */
  public void setClassFile(final MockClassFile f) {
    fClassFile = f;
  }
  
  /**
   * Return a mock class file.
   * @param is Input stream (ignored).
   */
  @Override
  public MockClassFile read(InputStream is) throws IOException {
    return fClassFile;
  }

}
