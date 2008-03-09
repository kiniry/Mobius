package mobius.cct.verifiers;

import mobius.cct.repositories.ClassFile;
import mobius.cct.verifiers.logging.Logger;

/**
 * Interface of verification environments - objects used
 * to manage verifiers and repositories.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface Environment {
  /**
   * Read class file.
   * @param name FQN of a class.
   * @return ClassFile object or null.
   */
  ClassFile getClassFile(String name);

  /**
   * Read certificate file.
   * @param name FQN of a class.
   * @return ClassFile object or null.
   */
  ClassFile getCertificateFile(String name);
  
  /**
   * Verify specification of given ClassFile.
   * @param name Class name.
   * @param spec Specification type to be verified.
   * @return (@code true} iff given class file contains a
   * certificate for requested specification type and the
   * certificate is valid.
   * @throws CyclicDependyException See
   * {@link mobius.cct.verifiers.CyclicDependyException 
   * CyclicDependyException}.
   */
  boolean verify(String name, String spec) 
    throws CyclicDependyException;
  
  /**
   * Verify specifications of given classes. This method may
   * use multiple threads.
   * @param name Class names.
   * @param spec Specification types to be verified.
   * @return {@code true} iff all specifications were succesfully
   * verified.
   * @throws CyclicDependyException See
   * {@link mobius.cct.verifiers.CyclicDependyException 
   * CyclicDependyException}.
   */
  boolean verify(String[] name, String[] spec)
    throws CyclicDependyException;
  
  /**
   * Get object used to log messages.
   * @return Logger.
   */
  Logger getLogger();
}
