package mobius.cct.tests.certificates;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import mobius.cct.certificates.MethodCertificate;
import mobius.cct.classfile.MethodName;
import mobius.cct.util.Version;

import org.junit.Test;

/**
 * Tests for class MethodCertificate.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MethodCertificateTest {
  /**
   * Test constructor.
   */
  @Test
  public void testConstructor() {
    final MethodName m = MethodName.get("<init>", "()V");
    final String type = "mobius.testcert";
    final Version version = new Version(8, 26);
    final byte[] data = new byte[] { 12, 34, 56, 78 };
    final MethodCertificate c = 
      new MethodCertificate(m, type, version, data);
    assertEquals(type, c.getType());
    assertEquals(version, c.getVersion());
    assertArrayEquals(data, c.getData());
  }
  
  /**
   * Test merge.
   */
  @Test
  public void testMerge() {
    final MethodName m = MethodName.get("<init>", "()V");
    final String type = "mobius.testcert";
    final Version version = new Version(8, 26);
    final byte[] data1 = new byte[] { 12, 34, 56 };
    final byte[] data2 = new byte[] { 78 };
    final byte[] data = new byte[] { 12, 34, 56, 78 };
    final MethodCertificate c1 = 
      new MethodCertificate(m, type, version, data1); 
    final MethodCertificate c2 = 
      new MethodCertificate(m, type, version, data2); 
    final MethodCertificate c = c1.merge(c2);
    assertEquals(type, c.getType());
    assertEquals(version, c.getVersion());

    assertArrayEquals(data, c.getData());
  }
  
  /**
   * Test equality of method certificates.
   * @param c1 Class cert 1.
   * @param c2 Class cert 2.
   */
  public static void assertMethodCertsEq(final MethodCertificate c1,
                                   final MethodCertificate c2) {
    assertEquals(c1.getMethod(), c2.getMethod());
    assertEquals(c1.getType(), c2.getType());
    assertEquals(c1.getVersion(), c2.getVersion());
    assertArrayEquals(c1.getData(), c2.getData());
  }
  
}
