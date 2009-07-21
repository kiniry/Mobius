package mobius.cct.certificates;

import mobius.cct.util.Version;

/**
 * Class or method certificate.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public abstract class Certificate {
  /**
   * Certificate signature.
   */
  private final CertificateSignature fSignature;
  
  /**
   * Data.
   */
  private final byte[] fData;

  /**
   * Constructor.
   * @param type Certificate type.
   * @param version Certificate version.
   * @param data Certificate data. This 
   */
  public Certificate(final String type, 
                     final Version version,
                     final byte[] data) {
    fSignature = new CertificateSignature(type, version);
    fData = data;
  }
  
  /**
   * Get certificate type.
   * @return Certificate type.
   */
  public String getType() {
    return fSignature.getType();
  }
  
  /**
   * Get certificate version.
   * @return Version.
   */
  public Version getVersion() {
    return fSignature.getVersion();
  }
  
  /**
   * Get certificate signature.
   * @return Sginature.
   */
  public CertificateSignature getSignature() {
    return fSignature;
  }
  
  /**
   * Get certificate data. Returned array should not be modifed.
   * @return Certificate data.
   */
  public byte[] getData() {
    return fData;
  }
}
