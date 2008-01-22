package mobius.cct.certificates;

import java.util.Iterator;
import java.util.Set;

/**
 * Interface of certificates.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface Certificate {
  /** 
   * Get certificate type.
   * @return Certificate type.
   */
  String getType();
  
  /**
   * Get major version number.
   * @return major version number.
   */
  byte getMajorVersion();
  
  /**
   * Get minor version number.
   * @return minor version number.
   */
  byte getMinorVersion();
  
  /**
   * Get names of imported certificates.
   * @return Iterator over certificate names.
   */
  Set<String> getImportedCerts();
  
  /**
   * Return class-level certificate.
   * @return proof section of class-level certificate.
   */
  byte[] getClassCertificate();
  
  /**
   * Return list of methods for which we have a method certificate.
   * @return Iterator over method signatures.
   */
  Iterator<String> getCertifiedMethods();
  
  /**
   * Return certificate for given method.
   * @param name Method signature.
   * @return Certificate content.
   */
  byte[] getMethodCertificate(final String name);
}
