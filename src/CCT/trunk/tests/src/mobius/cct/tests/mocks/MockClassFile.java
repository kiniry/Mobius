package mobius.cct.tests.mocks;

import java.io.IOException;
import java.io.OutputStream;
import java.util.Iterator;

import mobius.cct.certificates.Certificate;
import mobius.cct.repositories.InvalidCertificateException;
import mobius.cct.repositories.classfile.ClassFile;
import mobius.cct.util.ArrayIterator;

/**
 * ClassFile implementation used for tests.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MockClassFile implements ClassFile {
  /**
   * Collection of certificates associated with this
   * class file. 
   */
  private Certificate[] fCerts;
  
  /**
   * Constructor.
   * @param certs Array of certificates to be associated with
   * this class file.
   */
  public MockClassFile(final Certificate[] certs) {
    fCerts = certs;
  }
  
  @Override
  public Iterator<Certificate> getCertificates() {
    return new ArrayIterator<Certificate>(fCerts);
  }

  @Override
  public void setCertificates(final Certificate[] certs) {
    fCerts = certs;
  }

  @Override
  public void write(final OutputStream os) throws IOException,
      InvalidCertificateException {
    // Empty
  }
}
