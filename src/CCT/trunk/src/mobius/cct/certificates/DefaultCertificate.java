package mobius.cct.certificates;

import java.util.Iterator;
import java.util.Set;

/**
 * Default implementation of Certificate interface.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultCertificate implements Certificate {

  /**
   * Constructor. Create empty certificate of given type.
   * @param type Certificate type.
   * @param major Major version number.
   * @param minor Minor version number.
   */
  public DefaultCertificate(final String type, 
                            final byte major,
                            final byte minor) {
  }
  
  /** Return class certificate. 
   * @return Class certificate content (as byte array). 
   **/
  @Override
  public byte[] getClassCertificate() {
    return null;
  }

  /**
   * Set class certificate.
   * @param cert Contents of class certificate.
   */
  public void setClassCertificate(final byte[] cert) {
  }
  
  /** Return imported certificates.
   * @return Names of imported certificates.
   */
  @Override
  public Set<String> getImportedCerts() {
    // TODO Auto-generated method stub
    return null;
  }
  
  /** 
   * Return major version.
   * @return Major version number.
   */
  @Override
  public byte getMajorVersion() {
    // TODO Auto-generated method stub
    return 0;
  }
  
  /** 
   * Return minor version.
   * @return Minor version number.
   */
  @Override
  public byte getMinorVersion() {
    // TODO Auto-generated method stub
    return 0;
  }

  /**
   * Return certificate type.
   * @return Certificate type (as string).
   */
  @Override
  public String getType() {
    // TODO Auto-generated method stub
    return null;
  }

  /**
   * Iterate over certified methods.
   * @return Iterator.
   */
  @Override
  public Iterator<String> getCertifiedMethods() {
    // TODO Auto-generated method stub
    return null;
  }

  /**
   * Return certificate of given method.
   * @param name Method signature.
   * @return Method certificate content.
   */
  @Override
  public byte[] getMethodCertificate(final String name) {
    // TODO Auto-generated method stub
    return null;
  }

  /**
   * Add or replace method certificate.
   * @param method Method signature.
   * @param cert Certificate content.
   */
  public void addMethodCert(final String method, 
                            final byte[] cert) {
  }
  
  /**
   * Remove method certificate.
   * @param method Method signature.
   */
  public void removeMethodCert(final String method) {
  }
}
