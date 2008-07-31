package mobius.cct.verifiers;

import java.io.IOException;
import java.util.Iterator;

import mobius.cct.certificates.CertificatePack;
import mobius.cct.classfile.ClassFile;
import mobius.cct.classfile.ClassName;
import mobius.cct.repositories.NotFoundException;
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
   * @return ClassFile object.
   * @throws NotFoundException if the class cannot be found.
   * @throws IOException if it is thrown during class reading.
   */
  C getClassFile(ClassName name) throws IOException, 
                                        NotFoundException;

  /**
   * Read certificate file. Return null if there is no certificate
   * file for this class.
   * @param name FQN of a class.
   * @return ClassFile object or null.
   * @throws IOException if it is thrown during class reading.
   */
  C getCertificateFile(ClassName name) throws IOException;
  
  /**
   * Get all certificates of given type from
   * a class and its certificate file (certificates are
   * merged if present in both sources).
   * @param name FQN of a class.
   * @param type Certificate type.
   * @return Certificates.
   * @throws IOException If thrown during class reading.
   * @throws NotFoundException If class was not in the repository.
   */
  Iterator<CertificatePack> 
  getCertificate(ClassName name, String type)
    throws IOException, NotFoundException;
  
  /**
   * Verify specification of given ClassFile.
   * @param name Class name.
   * @param spec Specification type to be verified.
   * @return (@code true} iff given class file contains a
   * certificate for requested specification type and the
   * certificate is valid.
   * @throws VerificationException If an error occured.
   */
  boolean verify(ClassName name, String spec) 
    throws VerificationException;
  
  /**
   * Verify specifications of given classes. This method may
   * use multiple threads.
   * @param name Class names.
   * @param spec Specification types to be verified.
   * @return {@code true} iff all specifications were succesfully
   * verified.
   * @throws VerificationException If an error occured.
   */
  boolean verify(ClassName[] name, String[] spec)
    throws VerificationException;
  
  /**
   * Get object used to log messages.
   * @return Logger.
   */
  Logger getLogger();
}
