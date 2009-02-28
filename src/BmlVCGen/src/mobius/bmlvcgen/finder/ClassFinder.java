package mobius.bmlvcgen.finder;

import mobius.bmlvcgen.bml.ClassFile;
import mobius.bmlvcgen.finder.exceptions.FinderException;

/**
 * Interface of objects used to find and parse
 * class files.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface ClassFinder {
  /**
   * Find and load a class file.
   * @param fqn Fully qualified class name.
   * @return Classfile instance.
   * @throws FinderException If class file cannot be found 
   *                         or is invalid.
   */
  ClassFile findClass(final String fqn) throws FinderException;
}
