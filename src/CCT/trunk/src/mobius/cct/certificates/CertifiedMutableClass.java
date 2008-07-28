package mobius.cct.certificates;

import java.io.IOException;
import java.io.OutputStream;
import java.util.Iterator;

import mobius.cct.repositories.InvalidCertificateException;
import mobius.cct.repositories.InvalidFormatException;
import mobius.cct.repositories.classfile.MutableClassFile;
import mobius.cct.util.Version;

/**
 * A mutable class with set of certificates.
 * @param <C> Type of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class CertifiedMutableClass<C extends MutableClassFile> 
  implements CertifiedClass<C> {
  /**
   * Constructor.
   * @param cls Class file.
   * @throws InvalidFormatException if certificates are in invalid format.
   */
  public CertifiedMutableClass(final CertifiedClass<C> cls)
    throws InvalidFormatException {
    //TODO
  }
  
  /**
   * Remove certificate. If there is no certificate with requested
   * name and version, nothing is modified.
   * @param name Certificate name.
   * @param v Certificate version.
   */
  public void removeCert(final String name, final Version v) {
    //TODO
  }
  
  /**
   * Add a certificate.
   * @param c Certificate.
   * @throws InvalidCertificateException if the certificate does not
   * match class signature.
   */
  public void addCert(final Certificate c) 
    throws InvalidCertificateException {
    //TODO
  }
  
  /**
   * Write class to output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  public void writeTo(final OutputStream os) 
    throws IOException {
    //TODO
    // ...
  }
  

  /**
   * Write class certificates to output stream.
   * This creates a certificate file.
   * @param os Output stream.
   * @throws IOException .
   */
  public void writeCert(final OutputStream os) throws IOException {
    // TODO Auto-generated method stub
    
  }
  
  /**
   * Get all certificates of this class.
   * @return Iterator.
   */
  public Iterator<Certificate> getCertificates() {
    //TODO
    //...
    return null;
  }
  
  /**
   * Get class file.
   * @return Class file.
   */
  public C getClassFile() {
    //TODO
    //...
    return null;
  }
}
