package mobius.cct.verifiers;

import java.util.Iterator;

import mobius.cct.certificates.CertificatePack;
import mobius.cct.classfile.ClassFile;
import mobius.cct.classfile.ClassName;
import mobius.cct.verifiers.logging.Logger;

/**
 * Interface of verification environments - objects used
 * to manage verifiers and repositories.
 * @param <C> Type of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface Environment<C extends ClassFile> {
  /**
   * Read class file.
   * @param name FQN of a class.
   * @return ClassFile object or null.
   */
  C getClassFile(ClassName name);

  /**
   * Read certificate file.
   * @param name FQN of a class.
   * @return ClassFile object or null.
   */
  C getCertificateFile(ClassName name);
  
  /**
   * Get all certificates of given type from
   * a class and its certificate file (certificates are
   * merged if present in both sources).
   * @param name FQN of a class.
   * @param type Certificate type.
   * @return Certificates.
   */
  Iterator<CertificatePack> getCertificate(ClassName name, 
                                           String type);
  
  /**
   * Verify specification of given ClassFile.
   * @param name Class name.
   * @param spec Specification type to be verified.
   * @return (@code true} iff given class file contains a
   * certificate for requested specification type and the
   * certificate is valid.
   * @throws CyclicDependencyException See
   * {@link mobius.cct.verifiers.CyclicDependencyException 
   * CyclicDependyException}.
   */
  boolean verify(ClassName name, String spec) 
    throws CyclicDependencyException;
  
  /**
   * Verify specifications of given classes. This method may
   * use multiple threads.
   * @param name Class names.
   * @param spec Specification types to be verified.
   * @return {@code true} iff all specifications were succesfully
   * verified.
   * @throws CyclicDependencyException See
   * {@link mobius.cct.verifiers.CyclicDependencyException 
   * CyclicDependyException}.
   */
  boolean verify(ClassName[] name, String[] spec)
    throws CyclicDependencyException;
  
  /**
   * Get object used to log messages.
   * @return Logger.
   */
  Logger getLogger();
}
