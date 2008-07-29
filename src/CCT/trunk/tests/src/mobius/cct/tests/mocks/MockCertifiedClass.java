package mobius.cct.tests.mocks;

import java.util.Iterator;

import mobius.cct.certificates.CertificatePack;
import mobius.cct.certificates.CertifiedClass;
import mobius.cct.certificates.ClassCertificateVisitor;
import mobius.cct.certificates.MethodCertificate;
import mobius.cct.certificates.MethodCertificateVisitor;

/**
 * ClassFile implementation used for tests.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MockCertifiedClass implements 
  CertifiedClass<MockClassFile> {

  /**
   * MockClassFile used by this object.
   */
  private final MockClassFile fClass;
  
  /**
   * Constructor.
   * @param c MockClassFile from which certificates are taken.
   */
  public MockCertifiedClass(final MockClassFile c) {
    fClass = c;
  }

  @Override
  public MockClassFile getClassFile() {
    return fClass;
  }


  @Override
  public void visitClassCertificates(ClassCertificateVisitor v) {
    CertificatePack[] certs = fClass.getCerts();
    for (int i = 0; i < certs.length; i++) {
      v.visitClassCert(certs[i].getClassCertificate());
    }
  }


  @Override
  public void visitMethodCertificates(MethodCertificateVisitor v) {
    CertificatePack[] certs = fClass.getCerts();
    for (int i = 0; i < certs.length; i++) {
      final Iterator<MethodCertificate> it = 
        certs[i].getMethodCerts();
      while (it.hasNext()) {
        v.visitMethodCert(it.next());
      }
    }
  }

}
