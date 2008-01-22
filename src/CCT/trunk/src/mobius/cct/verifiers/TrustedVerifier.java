package mobius.cct.verifiers;

import java.util.Collection;

/**
 * Verifier used to check trusted classes (like standard library
 * and classes which were checked previously).
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class TrustedVerifier implements Verifier {
  /**
   * Constructor. Create verifier with empty list 
   * of trusted classes.
   */
  public TrustedVerifier() {
  }

  /**
   * Constructor. Create verifier with given 
   * list of trusted classes.
   * @param t List of trusted classes (FQNs).
   */
  public TrustedVerifier(final Collection<String> t) {
  }
  
  /**
   * Add class to list of trusted classes.
   * @param name class name.
   */
  public void addTrustedClass(final String name) {
  }

  /**
   * Remove class from list of trusted classes.
   * @param name class name.
   */
  public void removeTrustedClass(final String name) {
  }
  
  /**
   * Return Certificate type.
   * @return "mobius.trusted".
   */
  @Override
  public String getCertificateType() {
    return null;
  }
  
  /**
   * Return string passed to the constructor.
   * @return Specification type
   */
  @Override
  public String getSpecificationType() {
    return null;
  }
  
  /**
   * Verify class. The class is assumed to be valid
   * if its name is on the list of trusted classes.
   * Existence of the class (or specification) is NOT checked.
   * @param name Class name.
   * @param env Verification Environment.
   * @return Verification result.
   */
  @Override
  public boolean verify(final String name, 
                        final Environment env) {
    return false;
  }

}
