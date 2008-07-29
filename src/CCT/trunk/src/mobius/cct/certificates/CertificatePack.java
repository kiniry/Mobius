package mobius.cct.certificates;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import mobius.cct.repositories.classfile.MethodName;
import mobius.cct.util.ArrayIterator;
import mobius.cct.util.Function;
import mobius.cct.util.MappedIterator;
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
  private final MethodCertificate[] fMethodCerts;
  
  /**
   * Constructor.
   * @param classCert Class certificate.
   * @param methodCerts Method certificates.
   */
  public CertificatePack(final ClassCertificate classCert,
      final Collection<? extends MethodCertificate> methodCerts) {
    fClassCert = classCert;
    fMethodCerts = methodCerts.toArray(new MethodCertificate[]{});
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
    return new ArrayIterator<MethodCertificate>(fMethodCerts);
  }
  
  /**
   * Merge with another certificate pack.
   * Class certificates and certificates 
   * for each method are merged.
   * @param cp Certificate pack.
   * @return Merged certificate pack.
   */
  public CertificatePack merge(final CertificatePack cp) {
    final ClassCertificate cc = 
      fClassCert.merge(cp.getClassCertificate());
    final Collection<MethodCertificate> mm = 
      mergeMethods(getMethodCerts(), cp.getMethodCerts());
    return new CertificatePack(cc, mm);
  }
  
  /**
   * Merge method certificates.
   * @param i1 First set of certificates.
   * @param i2 Second set of certificates.
   * @return Merged certificates.
   */
  private static Collection<MethodCertificate> 
  mergeMethods(final Iterator<MethodCertificate> i1, 
               final Iterator<MethodCertificate> i2) {
    final Map<MethodName, MethodCertificate> methodMap = 
      new HashMap<MethodName, MethodCertificate>();
    mergeMethods(methodMap, i1);
    mergeMethods(methodMap, i2);
    return methodMap.values();
  }
  
  /**
   * Merge method certificates.
   * @param m First set of certificates.
   * @param i Second set of certificates.
   */
  private static void
  mergeMethods(final Map<MethodName, MethodCertificate> mm, 
               final Iterator<MethodCertificate> i) {
    while (i.hasNext()) {
      final MethodCertificate m = i.next();
      final MethodName mn = m.getMethod();
      if (mm.containsKey(mn)) {
        mm.put(mn, mm.get(mn).merge(m));
      } else {
        mm.put(mn, m);
      }
    }
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
    final Function<MethodCertificate, MethodName> getName = 
      new Function<MethodCertificate, MethodName>() {
        @Override
        public MethodName call(MethodCertificate args) {
          return args.getMethod();
        }
    };
    return 
    new MappedIterator<MethodCertificate,
                       MethodName>(getMethodCerts(), getName);
  }
}
