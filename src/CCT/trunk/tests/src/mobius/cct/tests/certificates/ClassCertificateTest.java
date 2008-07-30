package mobius.cct.tests.certificates;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;

import java.util.Iterator;

import mobius.cct.certificates.ClassCertificate;
import mobius.cct.util.Version;

import org.junit.Test;

/**
 * Tests for class ClassCertificate.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class ClassCertificateTest {
  /**
   * Test constructor.
   */
  @Test
  public void testConstructor() {
    final String type = "mobius.testcert";
    final Version version = new Version(8, 26);
    final String[] imports = new String[]{
      "IMPORT1",
      "IMPORT2"
    };
    final int test[] = new int[imports.length];
    final byte[] data = new byte[] { 12, 34, 56, 78 };
    final ClassCertificate c = 
      new ClassCertificate(type, version, imports, data);
    assertEquals(type, c.getType());
    assertEquals(version, c.getVersion());
    assertEquals(imports.length, c.getImportCount());
    Iterator<String> i = c.getImports();
    while (i.hasNext()) {
      for (int j = 0; j < imports.length; j++) {
        if (i.next().equals(imports[j])) {
          test[j]++;
        }
      }
    }
    for (int j = 0; j < imports.length; j++) {
      assertEquals(1, test[j]);
    }
    assertArrayEquals(data, c.getData());
  }
  
  /**
   * Test merge.
   */
  @Test
  public void testMerge() {
    final String type = "mobius.testcert";
    final Version version = new Version(8, 26);
    final String[] imports1 = new String[]{
      "IMPORT1",
      "IMPORT2"
    };
    final byte[] data1 = new byte[] { 12, 34, 56 };
    final String[] imports2 = new String[]{
       "IMPORT1",
       "IMPORT3"
     };
     final byte[] data2 = new byte[] { 78 };
     final String[] imports = new String[]{
       "IMPORT1",
       "IMPORT2",
       "IMPORT3"
     };
    final int test[] = new int[imports.length];
    final byte[] data = new byte[] { 12, 34, 56, 78 };
    final ClassCertificate c1 = 
      new ClassCertificate(type, version, imports1, data1); 
    final ClassCertificate c2 = 
      new ClassCertificate(type, version, imports2, data2); 
    final ClassCertificate c = c1.merge(c2);
    assertEquals(type, c.getType());
    assertEquals(version, c.getVersion());
    assertEquals(imports.length, c.getImportCount());
    Iterator<String> i = c.getImports();
    while (i.hasNext()) {
      for (int j = 0; j < imports.length; j++) {
        if (i.next().equals(imports[j])) {
          test[j]++;
        }
      }
    }
    for (int j = 0; j < imports.length; j++) {
      assertEquals(1, test[j]);
    }
    assertArrayEquals(data, c.getData());
  }
}
