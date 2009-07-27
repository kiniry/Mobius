package mobius.cct.tests.mocks;

import mobius.cct.certificates.CertificatePack;
import mobius.cct.classfile.ClassFile;
import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.ClassVisitor;
import mobius.cct.util.VisitorException;

/**
 * Mock class file used for testing.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MockRepoClass implements ClassFile {
  /**
   * Certificates.
   */
  private final CertificatePack[] fCerts;
  
  /**
   * Name.
   */
  private final ClassName fName;
  
  public CertificatePack[] getCerts() {
    return fCerts;
  }

  /**
   * Constructor - create file with no certificates.
   * @param name Class name.
   */
  public MockRepoClass(final ClassName name){
    fName = name;
    fCerts = new CertificatePack[]{};
  }
  
  /**
   * Constructor - create class file with given set of
   * certificates.
   * @param name Class name.
   * @param certs Certificates.
   */
  public MockRepoClass(final ClassName name, 
                       final CertificatePack[] certs) {
    fName = name;
    fCerts = certs;
  }

  /**
   * Get class name.
   * @return Class name.
   */
  public ClassName getName() {
    return fName;
  }
  
  public void visit(ClassVisitor v) throws VisitorException {
    // Not implemented...
  }

  
}
