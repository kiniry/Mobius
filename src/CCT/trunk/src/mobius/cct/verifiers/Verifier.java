package mobius.cct.verifiers;

import java.util.Iterator;

import mobius.cct.certificates.Certificate;
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
   * Type of specifications associated with given certificate.
   * @param cert Certificate. 
   * @return Types of specifications. 
   * If type or version of the certificate is not valid 
   * for this plugin, empty iterator should be returned.
   */
  Iterator<String> getSpecificationTypes(Certificate cert);
  
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
   */
  boolean verify(ClassName name, 
                 String spec,
                 CertificatePack cert, 
                 Environment<C> env);
}
