package mobius.bmlvcgen.main;

import mobius.bmlvcgen.finder.ClassFinder;
import mobius.bmlvcgen.logging.LoggerFactory;

/**
 * Instances of this class hold values of global variables, 
 * such as logger factories, arguments, class finders etc. 
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public final class Env {
  private final LoggerFactory loggerFactory;

  private Args args;
  private ClassFinder classFinder;
  
  /**
   * Constructor.
   * @param loggerFactory Logger factory.
   */
  public Env(final LoggerFactory loggerFactory) {
    this.loggerFactory = loggerFactory;
  }

  /**
   * Get logger factory.
   * @return Logger factory.
   */
  public LoggerFactory getLoggerFactory() {
    return loggerFactory;
  }

  /**
   * Get parsed arguments.
   * @return Arguments.
   */
  public Args getArgs() {
    return args;
  }

  /**
   * Set parser arguments.
   * @param args Arguments.
   */
  public void setArgs(final Args args) {
    this.args = args;
  }

  /**
   * Get object used to load class files.
   * @return ClassFinder.
   */
  public ClassFinder getClassFinder() {
    return classFinder;
  }

  /**
   * Set object used to load classes.
   * @param classFinder New ClassFinder.
   */
  public void setClassFinder(final ClassFinder classFinder) {
    this.classFinder = classFinder;
  }

  
}
