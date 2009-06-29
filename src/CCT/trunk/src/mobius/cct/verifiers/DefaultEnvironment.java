package mobius.cct.verifiers;

import java.io.IOException;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import mobius.cct.cache.Cache;
import mobius.cct.cache.InfiniteCache;
import mobius.cct.certificates.CertificateCollector;
import mobius.cct.certificates.CertificatePack;
import mobius.cct.certificates.CertificateParser;
import mobius.cct.certificates.DefaultCertificateParser;
import mobius.cct.classfile.ClassFile;
import mobius.cct.classfile.ClassName;
import mobius.cct.repositories.NotFoundException;
import mobius.cct.repositories.Repository;
import mobius.cct.verifiers.logging.DefaultLogger;
import mobius.cct.verifiers.logging.Logger;

/**
 * Default implementation of verification environment.
 * Uses repository to load classes and list of verifiers
 * to check certificates. It also maintains a list of
 * trusted classes. Verification of such classes always
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
   * Repository used to load classes and certificates.
   */
  private final Repository<? extends C> fRepo;
  
  /**
   * Set of trusted classes.
   */
  private final Set<ClassName> fTrusted;
  
  /**
   * Certificate parser.
   */
  private CertificateParser<? super C> fParser;
  
  /**
   * Cache of parsed certificates.
   */
  private final Cache<CertificateCollector<C>> fCache; 
  
  /**
   * Set of active verification requests.
   */
  private final Set<VerificationRequest> fActive;

  /**
   * Set of successful verification requests.
   */
  private final Set<VerificationRequest> fVerified;
  
  /**
   * Verifiers.
   */
  private final VerifierMap<C> fVerifiers;
  
  /**
   * Logger.
   */
  private Logger fLogger;
  
//  /**
//   * Create environment with given repository.
//   * @param repo Repository used to locate classes.
//   * @param defaultVerifiers if this parameter is set to 
//   * {@code true}, default list of verifiers is added to this 
//   * environment. If it set to {@code false}, verifiers must
//   * be added manually.
//   */
//  public DefaultEnvironment(final Repository<? extends C> repo,
//                            final boolean defaultVerifiers) { 
//    fRepo = repo;
//    fTrusted = new HashSet<ClassName>();
//    fLogger = new DefaultLogger();
//    fParser = new DefaultCertificateParser<C>();
//    fCache = new InfiniteCache<CertificateCollector<C>>();
//    fClassCache = new InfiniteCache<C>();
//    fActive = new HashSet<VerificationRequest>();
//    fVerified = new HashSet<VerificationRequest>();
//  }

  /**
   * Create environment with given repository and no verifiers.
   * @param repo Repository used to locate classes.
   */
  public DefaultEnvironment(final Repository<? extends C> repo) { 
    fRepo = repo;
    fTrusted = new HashSet<ClassName>();
    fLogger = new DefaultLogger();
    fParser = new DefaultCertificateParser<C>();
    fCache = new InfiniteCache<CertificateCollector<C>>();
    fActive = new HashSet<VerificationRequest>();
    fVerified = new HashSet<VerificationRequest>();
    fVerifiers = new VerifierMap<C>();
  }
  
  /**
   * Iterate over verifiers in this environment.
   * @return Iterator object.
   */
  public Iterator<Verifier<C>> getVerifiers() {
    return fVerifiers.getVerifiers();
  }
  
  /**
   * Add verifier to the environment. 
   * @param v Verifier object.
   */
  public void addVerifier(final Verifier<C> v) {
    fVerifiers.addVerifier(v);
  }
  
  /**
   * Add class to list of trusted classes.
   * @param name Class name (FQN).
   */
  public void addTrustedClass(final ClassName name) {
    fTrusted.add(name);
  }
  
  /**
   * Remove class from list of trusted classes.
   * If the class was not on the list, nothing is done.
   * @param name Class name (FQN). 
   */
  public void removeTrustedClass(final ClassName name) {
    fTrusted.remove(name);
  }
  
  /**
   * Iterate over all trusted classes.
   * @return Iterator.
   */
  Iterator<ClassName> getTrustedClasses() {
    return fTrusted.iterator();
  }
  
  /**
   * Read class file from used repository.
   * @param name FQN of a class.
   * @return ClassFile object.
   * @throws IOException If thrown during class reading.
   * @throws NotFoundException If class was not in the repository.
   */
  public C getClassFile(final ClassName name) 
    throws NotFoundException, IOException {
    return fRepo.getClassFile(name);
  }
  
  /**
   * Read certificate file from used repository.
   * Return null if there is no certificate file for 
   * the requested class.
   * @param name FQN of a class.
   * @return ClassFile object or null.
   * @throws IOException If thrown during class reading.
   */
  public C getCertificateFile(final ClassName name) 
    throws IOException {
    return fRepo.getCertFile(name);
  }

  /**
   * Verify specification of given class.
   * Verifiers for requested specification type are scanned 
   * in order in which they were added to the environment. 
   * First verifier for which a suitable certificate
   * exists in the class is run.
   * If a specification was already checked in
   * this environment it is not checked again. A class is not checked
   * (or even loaded) if its name is on the list of trusted classes.
   * @param name Class name.
   * @param spec Specification type to be verified.
   * @return (@code true} iff given class file contains a
   * certificate for requested specification type and the
   * certificate is valid.
   * @throws VerificationException .
   */
  public boolean verify(final ClassName name, final String spec)  
    throws VerificationException {
    if ((name == null) || (spec == null)) {
      throw new IllegalArgumentException();
    }
    final VerificationRequest req = 
      new VerificationRequest(name, spec);
    if (fActive.contains(req)) {
      throw new CyclicDependencyException(name, spec);
    }
    if (fTrusted.contains(name) || (fVerified.contains(req))) {
      return true;
    } else {
      try {
        final Iterator<CertificatePack> i = 
          loadCertificates(name).getAllCertificates();
        while (i.hasNext()) {
          final CertificatePack p = i.next();
          final Verifier<C> v = findVerifier(p, spec);
          if (v != null) {
            return verify(req, p, v);
          }
        }
        throw new 
        VerificationException("Verifier or certificate not found");
      } catch (IOException e) {
        throw new VerificationException(e);
      } catch (NotFoundException e) {
        throw new VerificationException(e);
      }
    }
  }
  
  /**
   * Verify a certificate pack using given Verifier.
   * @param req Verification request.
   * @param p Certificate pack.
   * @param v Verifier.
   * @return Verification result.
   * @throws VerificationException .
   */
  private boolean verify(final VerificationRequest req,
                         final CertificatePack p,
                         final Verifier<C> v) 
    throws VerificationException {
    
    fActive.add(req);
    final boolean result;
    try {
      result = 
        v.verify(req.getClassName(), req.getSpecType(), p, this);
    } catch (VerificationException e) {
      fActive.remove(req);
      throw e;
    }
    if (result) {
      fVerified.add(req);
    }
    fActive.remove(req);
    return result;
  }
  
  /** 
   * Verify multiple specifications. This environment does not use
   * multiple threads.
   * @param name Class names.
   * @param spec Specification types to be verified.
   * @return {@code true} iff all specifications were succesfully
   * verified.
   * @throws VerificationException .
   */
  public boolean verify(final ClassName[] name, final String[] spec)  
    throws VerificationException {
    for (int i = 0; i < name.length; i++) {
      if (!verify(name[i], spec[i])) {
        return false;
      }
    }
    return true;
  }
  
  /**
   * Get logger used by this environment.
   * @return Logger.
   */
  public Logger getLogger() {
    return fLogger;
  }
  
  /**
   * Set logger used by this environment.
   * @param logger Logger.
   */
  public void setLogger(final Logger logger) {
    fLogger = logger;
  }
  
  /**
   * Get object used to parse certificates.
   * @return CertificateParser used by this environment.
   */
  public CertificateParser<? super C> getCertificateParser() {
    return fParser;
  }
  
  /**
   * Set object used to parse certificates.
   * @param cp New certificate parser.
   */
  public void 
  setCertificateParser(final CertificateParser<? super C> cp) {
    fParser = cp;
  }

  /**
   * Get all certificates of given type from a class and
   * its certificate file (if present).
   * @param name Class name.
   * @param type Certificate type.
   * @return Iterator.
   * @throws IOException 
   * @throws NotFoundException 
   * @throws IOException If thrown during class reading.
   * @throws NotFoundException If class was not in the repository.
   */
  public Iterator<CertificatePack> 
  getCertificate(final ClassName name, final String type) 
    throws NotFoundException, IOException {
    return loadCertificates(name).getCertificates(type);
  }
  
  /**
   * Load data from class and certificate file.
   * @param clsName ClassName.
   * @return {@link CertificateCollector} with all certificates.
   * @throws IOException .
   * @throws NotFoundException . 
   */
  private CertificateCollector<C> 
  loadCertificates(final ClassName clsName) 
    throws NotFoundException, IOException {
    final String n = clsName.internalForm();
    if (fCache.hasKey(n)) {
      return fCache.lookup(n);
    } else {
      final C cls = getClassFile(clsName);
      final C cert = getCertificateFile(clsName);
      final CertificateCollector<C> c = 
        new CertificateCollector<C>();
      c.collect(fParser, cls);
      if (cert != null) {
        c.collect(fParser, cert);
      }
      fCache.update(n, c);
      return c;
    }    
  }
  
  /**
   * Find verifier for given certificate and specification.
   * @param c Certificate.
   * @param spec Specification type.
   * @return Verifier or null.
   */
  private Verifier<C> findVerifier(final CertificatePack c,
                                   final String spec) {
    return fVerifiers.getVerifier(
       c.getClassCertificate().getSignature(), 
       spec
    );
  }
}
