package mobius.cct.tests.mocks;

import java.util.Iterator;

import mobius.cct.certificates.Certificate;
import mobius.cct.certificates.CertifiedClass;
import mobius.cct.util.ArrayIterator;

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
  public Iterator<Certificate> getCertificates() {
    return new ArrayIterator<Certificate>(fClass.getCerts());
  }


  @Override
  public MockClassFile getClassFile() {
    return fClass;
  }

}
