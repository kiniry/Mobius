package mobius.cct.certificates;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import mobius.cct.classfile.MethodName;
import mobius.cct.util.Version;

/**
 * Class certificate with corresponding method certificates.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class CertificatePack {
  /**
   * Class certificate.
   */
  private final ClassCertificate fClassCert;
  
  /**
   * Method certificates.
   */
  private final Map<MethodName, MethodCertificate> fMethodCerts;
  
  /**
   * Constructor. 
   * @param cert Class certificate.
   * @param m Collection of method certificates.
   */
  public CertificatePack(
    final ClassCertificate cert,
    final Collection<? extends MethodCertificate> m) {
    
    fClassCert = cert;
    fMethodCerts = new HashMap<MethodName, MethodCertificate>();
    final Iterator<? extends MethodCertificate> i = m.iterator();
    while (i.hasNext()) {
      final MethodCertificate mc = i.next();
      fMethodCerts.put(mc.getMethod(), mc);
    }
  }

  /**
   * Constructor. 
   * @param cert Class certificate.
   * @param m Map of method certificates.
   */
  public CertificatePack(
    final ClassCertificate cert,
    final Map<MethodName, ? extends MethodCertificate> m) {
    
    fClassCert = cert;
    fMethodCerts = new HashMap<MethodName, MethodCertificate>(m);
  }
  
  /**
   * Get class certificate.
   * @return Class certificate.
   */
  public ClassCertificate getClassCertificate() {
    return fClassCert;
  }
  
  /**
   * Get method certificates.
   * @return Iterator.
   */
  public Iterator<MethodCertificate> getMethodCerts() {
    return fMethodCerts.values().iterator();
  }
  
  /**
   * Get certificate of a method. If there is no certificate
   * for this method, null is returned.
   * @param m Method name.
   * @return Method certificate or null.
   */
  public MethodCertificate getMethodCertificate(final MethodName m) {
    if (fMethodCerts.containsKey(m)) {
      return fMethodCerts.get(m);
    } else {
      return null;
    }
  }
  
  /**
   * Merge with another certificate pack.
   * Class certificates and certificates 
   * for each method are merged.
   * @param cp Certificate pack.
   * @return Merged certificate pack.
   */
  public CertificatePack merge(final CertificatePack cp) {
    final CertificatePackBuilder cb = 
      new CertificatePackBuilder(fClassCert);
    cb.mergeClassCert(cp.getClassCertificate());
    final Iterator<MethodCertificate> i = getMethodCerts();
    while (i.hasNext()) {
      cb.addMethodCert(i.next());
    }
    final Iterator<MethodCertificate> j = cp.getMethodCerts();
    while (j.hasNext()) {
      cb.addMethodCert(j.next());
    }
    return cb.toCertificatePack();
  }

  /**
   * Get type of certificates.
   * @return Type.
   */
  public String getType() {
    return fClassCert.getType();
  }
  
  /**
   * Get version of certificates.
   * @return Version.
   */
  public Version getVersion() {
    return fClassCert.getVersion();
  }
  
  /**
   * Get methods which have a certificate.
   * @return Iterator.
   */
  public Iterator<MethodName> getCertifiedMethods() {
    return fMethodCerts.keySet().iterator();
  }
  
  /**
   * Change class certificate.
   * @param nc New class certificate.
   * @return CertificatePack with changed class certificate.
   */
  public CertificatePack setClassCert(final ClassCertificate nc) {
    return new CertificatePack(nc, fMethodCerts);
  }
  
  /**
   * Change method certificate.
   * @param m New certificate.
   * @return CertificatePack with changed method certificate.
   */
  public CertificatePack setMethodCert(final MethodCertificate m) {
    final Map<MethodName, MethodCertificate> mc = 
      new HashMap<MethodName, MethodCertificate>(fMethodCerts);
    mc.put(m.getMethod(), m);
    return new CertificatePack(fClassCert, mc);
  }
}
