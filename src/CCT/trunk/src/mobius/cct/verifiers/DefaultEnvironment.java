package mobius.cct.verifiers;

import java.util.Iterator;

import mobius.cct.repositories.ClassFile;
import mobius.cct.repositories.ClassReader;
import mobius.cct.repositories.Repository;
import mobius.cct.verifiers.logging.Logger;

/**
 * Default implementation of verification environment.
 * Uses repository to load classes and list of verifiers
 * to check certificates. It also maintains a list of
 * trusted classes. Verifications of such classes always
 * succeeds, even if the class is not in the repository
 * or does not contain requested certificate. This feature
 * can be used to avoid unnecessary parsing of system 
 * classes and classes which were verified earlier.
 * 
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 *
 * @param <C> Type of class files.
 */
public class DefaultEnvironment<C extends ClassFile> 
  implements Environment<C> {
  /**
   * Create environment with given repository.
   * @param repo Repository used to locate classes.
   * @param defaultVerifiers if this paramater is set to 
   * {@code true}, default list of verifers is added to this 
   * environment. If it set to {@code false}, verifiers must
   * be added manually.
   */
  public DefaultEnvironment(final Repository<C> repo,
                            final boolean defaultVerifiers) { 
  }
  
  /**
   * Create environment using default repository and verifiers.
   */
  public DefaultEnvironment() { 
  }
  
  /**
   * Iterate over verifiers in this environment.
   * @return Iterator object.
   */
  public Iterator<Verifier> getVerifiers() {
    return null;
  }
  
  /**
   * Add verifier to the environment. 
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
  public Verifier<C> getVerifier(final String certType) {
    return null;
  }
  
  /**
   * Add class to list of trusted classes.
   * @param name Class name (FQN).
   */
  public void addTrustedClass(final String name) {
  }
  
  /**
   * Remove class from list of trusted classes.
   * If the class was not on the list, nothing is done.
   * @param name Class name (FQN). 
   */
  public void removeTrustedClass(final String name) {

  }
  
  /**
   * Iterate over all trusted classes.
   * @return Iterator.
   */
  Iterator<String> getTrustedClasses() {
    return null;
  }
  
  /**
   * Read class file from used repository.
   * @param name FQN of a class.
   * @return ClassFile object.
   */
  @Override
  public C getClassFile(final String name) {
    return null;
  }
  
  /**
   * Read certificate file from used repository.
   * @param name FQN of a class.
   * @return ClassFile object.
   */
  @Override
  public C getCertificateFile(final String name) {
    return null;
  }
  
  /**
   * Verify specification of given ClassFile. 
   * If there are multiple certificates for the desired specification
   * verifiers are tried in order in which they were added to the
   * environment. If a specification was already checked in
   * this environment it is not checked again. A class is not checked
   * (or even loaded) if its name is on the list of trusted classes.
   * @param name Class name.
   * @param spec Specification type to be verified.
   * @return (@code true} iff given class file contains a
   * certificate for requested specification type and the
   * certificate is valid.
   * @throws CyclicDependencyException See
   * {@link mobius.cct.verifiers.CyclicDependencyException 
   * CyclicDependyException}.
   */
  @Override
  public boolean verify(final String name, final String spec)  
    throws CyclicDependencyException {
    return false;
  }
  
  /** 
   * Verify multiple specifications. This environment does not use
   * multiple threads.
   * @param name Class names.
   * @param spec Specification types to be verified.
   * @return {@code true} iff all specifications were succesfully
   * verified.
   * @throws CyclicDependencyException See
   * {@link mobius.cct.verifiers.CyclicDependencyException 
   * CyclicDependyException}.
   */
  @Override
  public boolean verify(final String[] name, final String[] spec)  
    throws CyclicDependencyException {
    return false;
  }
  
  /**
   * Get logger used by this environemnt.
   * @return Logger.
   */
  @Override
  public Logger getLogger() {
    return null;
  }
  
  /**
   * Set logger used by this environemnt.
   * @param logger Logger.
   */
  public void setLogger(final Logger logger) {
  }
}
