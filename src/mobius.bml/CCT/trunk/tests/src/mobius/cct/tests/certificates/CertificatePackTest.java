package mobius.cct.tests.certificates;

import static mobius.cct.tests.certificates.ClassCertificateTest.assertClassCertsEq;
import static mobius.cct.tests.certificates.MethodCertificateTest.assertMethodCertsEq;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import mobius.cct.certificates.CertificatePack;
import mobius.cct.certificates.ClassCertificate;
import mobius.cct.certificates.MethodCertificate;
import mobius.cct.classfile.MethodName;
import mobius.cct.util.Version;

import org.junit.Test;

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
   * Test equality of CertificatePacks.
   * @param cp1 First certificate pack.
   * @param cp2 Second certificate pack.
   */
  public static void assertCertPacksEq(final CertificatePack cp1,
                                       final CertificatePack cp2) {
    if (cp1 == null) {
      assertNull(cp2);
    }
    if (cp2 == null) {
      fail();
    }
    assertClassCertsEq(cp1.getClassCertificate(), 
                       cp2.getClassCertificate());
    final Set<MethodName> s1 = new HashSet<MethodName>();
    final Iterator<MethodName> i1 = cp1.getCertifiedMethods();
    while (i1.hasNext()) {
      s1.add(i1.next());
    }
    final Set<MethodName> s2 = new HashSet<MethodName>();
    final Iterator<MethodName> i2 = cp2.getCertifiedMethods();
    while (i2.hasNext()) {
      s2.add(i2.next());
    }
    assertEquals(s1, s2);
    Iterator<MethodName> i = s1.iterator();
    while (i.hasNext()) {
      final MethodName m = i.next();
      assertMethodCertsEq(cp1.getMethodCertificate(m),
                          cp2.getMethodCertificate(m));
    }
  }
  
}
