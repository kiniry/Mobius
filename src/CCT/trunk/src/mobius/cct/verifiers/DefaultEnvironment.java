package mobius.cct.verifiers;

import java.util.Iterator;

import mobius.cct.repositories.ClassFile;
import mobius.cct.repositories.ClassReader;
import mobius.cct.repositories.Repository;

/**
 * Default implementation of verification environment.
 * Uses repository to load classes and list of verifiers
 * to check certificates.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 *
 * @param <C> Type of class files.
 */
public class DefaultEnvironment<C extends ClassFile> 
  implements Environment {
  /**
   * Create environment with given repository.
   * @param repo Repository used to locate classes.
   * @param reader Object used to parse classes.
   * @param defaultVerifiers if this paramater is set to 
   * {@code true}, default list of verifers is added to this 
   * environment. If it set to {@code false}, verifiers must
   * be added manually.
   */
  public DefaultEnvironment(final Repository<C> repo,
                            final ClassReader<C> reader,
                            final boolean defaultVerifiers) { 
  }
  
  /**
   * Create environment using default repository and verifiers.
   * @param reader Object used to parse classes.
   */
  public DefaultEnvironment(final ClassReader<C> reader) { 
  }
  
  /**
   * Iterate over verifiers in this environment.
   * @return Iterator object.
   */
  public Iterator<Verifier> getVerifiers() {
    return null;
  }
  
  /**
   * Add or update verifier. There can be at most one
   * verifier for each certificate type. If a verifier
   * of the same type as given is present, it is replaced.
   * @param v Verifier object.
   */
  public void addVerifier(final Verifier v) {
  }
  
  /**
   * Remove verifier for given certificate type 
   * from environment.
   * @param certType Type of certificates.
   */
  public void removeVerifier(final String certType) {
  }
  
  /** Get verifier for given certificate type. 
   *  @param certType Type of certificates.
   *  @return Verifier applicable to certificates of given type
   *  or {@code null}, if there is no such verifier in this env.
   **/
  public Verifier getVerifier(final String certType) {
    return null;
  }
  
  /**
   * Read class file from used repository.
   * @param name FQN of a class.
   * @return ClassFile object.
   */
  @Override
  public ClassFile getClassFile(final String name) {
    return null;
  }
  
  /**
   * Read certificate file from used repository.
   * @param name FQN of a class.
   * @return ClassFile object.
   */
  @Override
  public ClassFile getCertificateFile(final String name) {
    return null;
  }
  
  /**
   * Verify specification of given ClassFile. 
   * If there are multiple certificates for the desired specification
   * verifiers are tried in oreder in which they were added to the
   * environment. If a specification was already checked in
   * this environment it is not checked again.
   * @param name Class name.
   * @param spec Specification type to be verified.
   * @return (@code true} iff given class file contains a
   * certificate for requested specification type and the
   * certificate is valid.
   * @throws CyclicDependyException See
   * {@link mobius.cct.verifiers.CyclicDependyException 
   * CyclicDependyException}.
   */
  @Override
  public boolean verify(final String name, final String spec)  
    throws CyclicDependyException {
    return false;
  }
  
  /** 
   * Verify multiple specifications. This environment does not use
   * multiple threads.
   * @param name Class names.
   * @param spec Specification types to be verified.
   * @return {@code true} iff all specifications were succesfully
   * verified.
   * @throws CyclicDependyException See
   * {@link mobius.cct.verifiers.CyclicDependyException 
   * CyclicDependyException}.
   */
  public boolean verify(final String[] name, final String[] spec)  
    throws CyclicDependyException {
    return false;
  }  
}
