package mobius.cct.verifiers;

import mobius.cct.certificates.CertificatePack;
import mobius.cct.classfile.ClassFile;
import mobius.cct.classfile.ClassName;
import mobius.cct.util.Version;

/**
 * Interface of certificate verifiers. 
 * @param <C> Type of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface Verifier<C extends ClassFile> {
  /**
   * Type of certificates verifiable by this object.
   * @return Certificate type.
   */
  String getCertificateType();
  
  /**
   * Get type of specification.
   * @return Specification type.
   */
  String getSpecificationType();
  
  /**
   * Lowest version number supported by this verifier.
   * @return Version number.
   */
  Version getMinVersion();

  /**
   * Highest version number supported by this verifier.
   * @return Version number.
   */
  Version getMaxVersion();
  
  /**
   * Verify certificate of a class in given environment.
   * If specifications of other classes are used they must also
   * be verified.
   * @param name Class to be verified (FQN).
   * @param spec Type of specification.
   * @param cert Certificate to be verified.
   * @param env Verification environment.
   * @return {@code true} if the certificate is valid. If type
   * or version of this certificate are not acceptable for
   * this plugin, {@code false} is returned.
   * @throws VerificationException If an error occured.
   */
  boolean verify(ClassName name, 
                 String spec,
                 CertificatePack cert, 
                 Environment<C> env) throws VerificationException;
}
