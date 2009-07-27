package mobius.cct.verifiers;

import mobius.cct.classfile.ClassName;
import mobius.cct.util.Pair;

/**
 * Class name and specification type.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class VerificationRequest {
  /**
   * Class name and specification type.
   */
  private final Pair<ClassName, String> fData;
  
  /**
   * Constructor.
   * @param cls Class name.
   * @param spec Specification type.
   */
  public VerificationRequest(final ClassName cls, 
                             final String spec) {
    fData = new Pair<ClassName, String>(cls, spec);
  }
  
  /**
   * Get specification type.
   * @return Specification type.
   */
  public String getSpecType() {
    return fData.getSecond();
  }

  /**
   * Get class name.
   * @return Class name.
   */
  public ClassName getClassName() {
    return fData.getFirst();
  }
  
  /**
   * Get hash code.
   * @return Hash code.
   */
  @Override
  public int hashCode() {
    return fData.hashCode();
  }
  
  /**
   * Test equality.
   * @param o Object.
   * @return .
   */
  @Override
  public boolean equals(final Object o) {
    if (o instanceof VerificationRequest) {
      return fData.equals(((VerificationRequest)o).fData);
    } else {
      return false;
    }
  }
}
