package mobius.cct.verifiers;

/**
 * Interface of certificate verifiers. 
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface Verifier {
  /**
   * Type of certificates verifiable by this object.
   * @return Certificate type.
   */
  String getCertificateType();
  
  /**
   * Type of specifications associated with certificates
   * verified by this object.
   * @return Specification type.
   */
  String getSpecificationType();
  
  /**
   * Verify certificate of a class in given environment.
   * If specifications of other classes are used they must also
   * be verified.
   * @param name Class to be verified (FQN).
   * @param env Verification environment.
   * @return {@code true} iff given class contains a certificate
   * verifiable by this object and the certificate is valid.
   */
  boolean verify(String name, Environment env);
}
