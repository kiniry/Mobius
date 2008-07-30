package mobius.cct.tests.certificates;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import mobius.cct.certificates.CertificatePack;
import mobius.cct.certificates.ClassCertificate;
import mobius.cct.certificates.MethodCertificate;
import mobius.cct.repositories.classfile.MethodName;
import mobius.cct.util.Version;

import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Test for class CertificatePack.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class CertificatePackTest {
  /**
   * Test merging.
   */
  @Test
  public void testMerge() {
    final MethodName m = MethodName.get("<init>", "()V");
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
    final byte[] data = new byte[] { 12, 34, 56, 78 };
    final ClassCertificate c1 = 
      new ClassCertificate(type, version, imports1, data1); 
    final ClassCertificate c2 = 
      new ClassCertificate(type, version, imports2, data2); 
    final ClassCertificate c = 
      new ClassCertificate(type, version, imports, data);
    final MethodCertificate mc1 = 
      new MethodCertificate(m, type, version, data1);
    final MethodCertificate mc2 = 
      new MethodCertificate(m, type, version, data2);
    final MethodCertificate mc = 
      new MethodCertificate(m, type, version, data);
    final Collection<MethodCertificate> mcs1 = new
      ArrayList<MethodCertificate>();
    mcs1.add(mc1);
    final Collection<MethodCertificate> mcs2 = new
      ArrayList<MethodCertificate>();
    mcs2.add(mc2);
    final CertificatePack cp1 = new CertificatePack(c1, mcs1);
    final CertificatePack cp2 = new CertificatePack(c2, mcs2);
    final CertificatePack cp = cp1.merge(cp2);
    assertClassCertsEq(c, cp.getClassCertificate());
    Iterator<MethodCertificate> i = cp.getMethodCerts();
    assertTrue(i.hasNext());
    assertMethodCertsEq(mc, i.next());
    assertFalse(i.hasNext());
  }
  
  /**
   * Test equality of class certificates.
   * @param c1 Class cert 1.
   * @param c2 Class cert 2.
   */
  private void assertClassCertsEq(final ClassCertificate c1,
                             final ClassCertificate c2) {
    assertEquals(c1.getType(), c2.getType());
    assertEquals(c1.getVersion(), c2.getVersion());
    Set<String> imports1 = new HashSet<String>();
    Iterator<String> i1 = c1.getImports();
    while (i1.hasNext()) {
      imports1.add(i1.next());
    }
    Set<String> imports2 = new HashSet<String>();
    Iterator<String> i2 = c2.getImports();
    while (i2.hasNext()) {
      imports2.add(i2.next());
    }
    assertEquals(imports1, imports2);
    assertArrayEquals(c1.getData(), c2.getData());
  }
  
  /**
   * Test equality of method certificates.
   * @param c1 Class cert 1.
   * @param c2 Class cert 2.
   */
  private void assertMethodCertsEq(final MethodCertificate c1,
                                   final MethodCertificate c2) {
    assertEquals(c1.getMethod(), c2.getMethod());
    assertEquals(c1.getType(), c2.getType());
    assertEquals(c1.getVersion(), c2.getVersion());
    assertArrayEquals(c1.getData(), c2.getData());
  }
}
