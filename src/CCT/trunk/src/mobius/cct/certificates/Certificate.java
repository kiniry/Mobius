package mobius.cct.certificates;

import mobius.cct.util.Version;

/**
 * Class or method certificate.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public abstract class Certificate {
  /**
   * Certificate type.
   */
  private final String fType;
  
  /**
   * Certificate version.
   */
  private final Version fVersion;

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
    fType = type;
    fVersion = version;
    fData = data;
  }
  
  /**
   * Get certificate type.
   * @return Certificate type.
   */
  public String getType() {
    return fType;
  }
  
  /**
   * Get certificate version.
   * @return Version.
   */
  public Version getVersion() {
    return fVersion;
  }
  
  /**
   * Get certificate data. Returned array should not be modifed.
   * @return Certificate data.
   */
  public byte[] getData() {
    return fData;
  }
}
