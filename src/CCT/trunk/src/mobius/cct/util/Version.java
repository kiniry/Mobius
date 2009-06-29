package mobius.cct.util;

/**
 * Immutable pair (major_verion, minor_version).
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class Version implements Comparable<Version> {
  /** Value used in hashCode(). */
  private static final int HASH_FACTOR = 0xADDBEEF;
  
  /** Major version number. */
  private final int fMajor;
  
  /** Minor version number. */
  private final int fMinor;
  
  /**
   * Constructor.
   * @param major Major version number.
   * @param minor Minor version number.
   */
  public Version(final int major, final int minor) {
    fMajor = major;
    fMinor = minor;
  }
  
  /** 
   * Get major version number.
   * @return Major version number.
   */
  public int getMajor() {
    return fMajor;
  }
  
  /** 
   * Get minor version number.
   * @return Minor version number.
   */
  public int getMinor() {
    return fMinor;
  }
  
  /**
   * Equals.
   * @param obj Object to compare.
   * @return .
   */
  @Override
  public boolean equals(final Object obj) {
    if (obj instanceof Version) {
      return (fMajor == ((Version)obj).getMajor()) &&
        (fMinor == ((Version)obj).getMinor());
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
    return fMajor * HASH_FACTOR + fMinor;
  }
  
  /**
   * Convert to string.
   * @return String representation of this object.
   */
  @Override
  public String toString() {
    return "<" + Integer.toString(fMajor) + "." + 
      Integer.toString(fMinor) + ">";
  }

  /**
   * Compare versions.
   * @param v Version.
   * @return Result.
   */
  // CHECKSTYLE:OFF
  public int compareTo(final Version v) {
    if (fMajor > v.getMajor()) {
      return 1;
    } else if (fMajor < v.getMajor()) {
      return -1;
    } else {
      if (fMinor > v.getMinor()) {
        return 1;
      } else if (fMinor < v.getMinor()) {
        return -1;
      } else {
        return 0;
      }
    }
  }
  // CHECKSTYLE:ON
}
