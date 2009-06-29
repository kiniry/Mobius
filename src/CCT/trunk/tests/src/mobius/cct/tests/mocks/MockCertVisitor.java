package mobius.cct.tests.mocks;

import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;
import static junit.framework.Assert.fail;

import java.util.List;

import mobius.cct.certificates.Certificate;
import mobius.cct.certificates.ClassCertificate;
import mobius.cct.certificates.ClassCertificateVisitor;
import mobius.cct.certificates.MethodCertificate;
import mobius.cct.certificates.MethodCertificateVisitor;
import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.MethodName;
import mobius.cct.tests.certificates.ClassCertificateTest;
import mobius.cct.tests.certificates.MethodCertificateTest;
import mobius.cct.util.VisitorException;

/**
 * A certificate visitor which checks 
 * if the visited class contains all
 * of the specified certificates.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MockCertVisitor implements ClassCertificateVisitor {
  /**
   * List of method and class certificates.
   */
  private final List<Certificate> fCerts;
  
  /**
   * Flags for certificates.
   */
  private final boolean[] fFound;
  
  /**
   * Was begin called?
   */
  private boolean fBeginCalled;
  
  /**
   * Was end called?
   */
  private boolean fEndCalled;
  
  /**
   * Was unexpected certificate encountered?
   */
  private boolean fUnexpected;
  
  /**
   * Constructor.
   */
  public MockCertVisitor(final List<Certificate> certs) {
    fCerts = certs;
    fFound = new boolean[fCerts.size()];
    fBeginCalled = false;
    fEndCalled = false;
  }
  
  public void assertVisitOK() {
    assertFalse(fUnexpected);
    for (int i = 0; i < fCerts.size(); i++) {
      if (!fFound[i]) {
        fail("Certificate not found");
      }
    }
    assertTrue(fEndCalled);
    assertTrue(fBeginCalled);
  }
  
  public void begin(ClassName cls) throws VisitorException {
    fBeginCalled = true;
    for (int i = 0; i < fCerts.size(); i++) {
      fFound[i] = false;
    }
    fUnexpected = false;
  }

  public void end() throws VisitorException {
    fEndCalled = true;
  }
  
  public void visitClassCert(ClassCertificate cert) throws VisitorException {
    for (int i = 0; i < fCerts.size(); i++) {
      if ((!fFound[i]) &&
          fCerts.get(i) instanceof ClassCertificate) {
        final ClassCertificate c = (ClassCertificate)fCerts.get(i);
        //WARNING: UGLY HACK
        try {
          ClassCertificateTest.assertClassCertsEq(cert, c);
          fFound[i] = true;
          return;
        } catch (Exception e) {
        }
      }
    }
    fUnexpected = true;
  }

  public MethodCertificateVisitor visitMethod(MethodName m)
      throws VisitorException {
    return new MethodVisitor();
  }
  
  private final class MethodVisitor implements MethodCertificateVisitor {    
    public void begin(MethodName m) {
    }

    public void end() {
    }

    public void visitMethodCert(MethodCertificate cert) {
      for (int i = 0; i < fCerts.size(); i++) {
        if ((!fFound[i]) && 
            fCerts.get(i) instanceof MethodCertificate) {
          final MethodCertificate c = (MethodCertificate)fCerts.get(i);
          //WARNING: UGLY HACK
          try {
            MethodCertificateTest.assertMethodCertsEq(cert, c);
            fFound[i] = true;
            return;
          } catch (Exception e) {
          }
        }
      }
      fUnexpected = true;
    }
    
  }
  
}
