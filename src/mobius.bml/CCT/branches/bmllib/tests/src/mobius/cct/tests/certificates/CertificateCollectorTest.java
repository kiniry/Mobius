package mobius.cct.tests.certificates;

import java.util.LinkedList;
import java.util.List;

import mobius.cct.certificates.CertificateCollector;
import mobius.cct.certificates.CertificatePack;
import mobius.cct.certificates.ClassCertificate;
import mobius.cct.certificates.MethodCertificate;
import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.MethodName;
import mobius.cct.tests.mocks.MockCertificateParser;
import mobius.cct.tests.mocks.MockRepoClass;
import mobius.cct.util.Version;

import org.junit.Test;

/**
 * Tests for class CertificateCollector.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class CertificateCollectorTest {
  /**
   * Test.
   */
  @Test
  public void testCollector() throws Exception {
    final ClassName clsName = 
      ClassName.parseInternal("mobius.cct.Test");
    final String certType = "mobius.testcert";
    final Version version = new Version(0, 5);
    final CertificateCollector<MockRepoClass> c = 
      new CertificateCollector<MockRepoClass>();
    ClassCertificate cert = 
      new ClassCertificate(certType,
                           version,
                           new String[]{},
                           new byte[]{});
    MethodCertificate mc1 = 
      new MethodCertificate(MethodName.get("<init>", "()V"),
                            certType,
                            version,
                            new byte[]{ 0x00, 0x01 }
      );
    MethodCertificate mc2 = 
      new MethodCertificate(MethodName.get("test", "()V"),
                            certType,
                            version,
                            new byte[]{ 0x02, 0x03 }
      );
    final List<MethodCertificate> mcs = 
      new LinkedList<MethodCertificate>();
    mcs.add(mc1);
    mcs.add(mc2);
    final CertificatePack cp1 = new CertificatePack(cert, mcs);
    CertificatePack[] certs = new CertificatePack[] { 
      cp1
    };
    final MockRepoClass cls = new MockRepoClass(clsName, certs);
    c.collect(new MockCertificateParser(), cls);
    final CertificatePack cp2 = c.getCertificatePack(certType, version);
    CertificatePackTest.assertCertPacksEq(cp1, cp2);
  }
}
