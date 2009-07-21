package mobius.cct.certificates;

import mobius.cct.util.Version;

/**
 * Certificate type and version.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class CertificateSignature 
  implements Comparable<CertificateSignature> {
  /**
   * Constant used for hashing.
   */
  private static final int HASH_FACTOR = 0xDEAF;
  /**
   * Type.
   */
  private final String fType;
  
  /**
   * Version.
   */
  private final Version fVersion;
  
  /**
   * Constructor.
   * @param type Type.
   * @param version Version.
   */
  public CertificateSignature(final String type, 
                              final Version version) {
    fType = type;
    fVersion = version;
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
   * Equals.
   * @param obj Object to compare.
   * @return .
   */
  @Override
  public boolean equals(final Object obj) {
    if (obj instanceof CertificateSignature) {
      return (fType.equals(((CertificateSignature)obj).getType())) &&
        (fVersion.equals(((CertificateSignature)obj).getVersion()));
    } else {
      return false;
    }
  }
  
  /**
   * Hashcode.
   * @return Hashcode.
   */
  @Override
  public int hashCode() {
    return HASH_FACTOR * fVersion.hashCode() + fType.hashCode();
  }
  
  /**
   * Convert to string.
   * @return String representation of this object.
   */
  @Override
  public String toString() {
    return fType + fVersion.toString();
  }

  /**
   * Compare signatures.
   * @param c Certificate signature.
   * @return Result.
   */
  public int compareTo(final CertificateSignature c) {
    final int r = fVersion.compareTo(c.getVersion());
    if (r == 0) {
      return fType.compareTo(c.getType());
    } else {
      return r;
    } 
  }

}
