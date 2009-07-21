package mobius.bmlvcgen.main;

import mobius.bmlvcgen.bml.ClassFile;

/**
 * Interface of objects used to process classes.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface ClassProcessor {
  /**
   * Process a class file.
   * @param name Class name.
   * @param clazz Class to be processed.
   * @return True, unless an error was encountered.
   */
  boolean processClass(String name, ClassFile clazz);
}
