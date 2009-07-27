package mobius.cct.certificates;

import java.util.HashMap;
import java.util.Map;

import mobius.cct.classfile.MethodName;

/**
 * Object used to create CertificatePacks.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class CertificatePackBuilder {
  /**
   * Class certificate.
   */
  private ClassCertificate fClassCert;
  
  /**
   * Method certificates.
   */
  private final Map<MethodName, MethodCertificate> fMethodCerts;
  
  /**
   * Constructor. Creates a builder with given class certificate
   * and no method certificates.
   * @param cert Class certificate.
   */
  public CertificatePackBuilder(final ClassCertificate cert) {
    fClassCert = cert;
    fMethodCerts = new HashMap<MethodName, MethodCertificate>();
  }
  
  /**
   * Create certificate pack.
   * @return Certificate pack.
   */
  public CertificatePack toCertificatePack() {
    return new CertificatePack(fClassCert, fMethodCerts);
  }
  
  /**
   * Add new class certificate 
   * (it is merged with current certificate).
   * @param c New certificate.
   */
  public void mergeClassCert(final ClassCertificate c) {
    fClassCert = fClassCert.merge(c);
  }
  
  /**
   * Add method certificate. If another certificate for the same
   * method is present in this builder, the certificates are merged.
   * @param m Method certificate.
   */
  public void addMethodCert(final MethodCertificate m) {
    final MethodName mn = m.getMethod();
    if (fMethodCerts.containsKey(mn)) {
      fMethodCerts.put(mn, fMethodCerts.get(mn).merge(m));
    } else {
      fMethodCerts.put(m.getMethod(), m);
    }
  }
}
