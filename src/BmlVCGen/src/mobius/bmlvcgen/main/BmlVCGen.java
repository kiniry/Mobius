package mobius.bmlvcgen.main;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import mobius.bmlvcgen.bml.ClassFile;
import mobius.bmlvcgen.finder.ClassFinder;
import mobius.bmlvcgen.finder.exceptions.FinderException;
import mobius.bmlvcgen.logging.Logger;

/**
 * Class responsible for processing class files
 * and generating proof obligations.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class BmlVCGen {
  // Possible outcomes of class processing.
  private enum Result {
    OK, ERROR, ALREADY_PROCESSED
  }
  
  // Logger.
  private final Logger logger;
  // Object used to find class files.
  private final ClassFinder classFinder;
  // Classes to be processed.
  private final Collection<String> classes;
  // Set of classes for which processClass() was called.
  private final Set<String> processed;
  // Object used to process class files.
  private ClassProcessor classProcessor;
  
  /**
   * Constructor.
   * @param env Environment - set of global variables.
   */
  public BmlVCGen(final Env env) {
    logger = env.getLoggerFactory().getLogger(this.getClass());
    classFinder = env.getClassFinder();
    classes = env.getArgs().getClassNames();
    processed = new HashSet<String>();
    classProcessor = new DefaultClassProcessor(env);
  }
  
  /**
   * Start VCGen.
   */
  public void run() {
    int okCount = 0;
    int errCount = 0;
    for (final String className : classes) {
      logger.info("Processing class: %1$s", className);
      switch (processClass(className)) {
        case OK: 
          okCount++; 
          break;
        case ERROR: 
          errCount++; 
          break;
        default:
          // Ignore.
          break;
      }
      logger.info("Finished processing: %1$s", className);
    }
    logger.info("Classes successfully processed: %1$d", okCount);
    if (errCount == 0) {
      logger.info("No errors.");
    } else {
      logger.warn(
        "Classes not processed because of errors: %1$d", errCount);
    }
  }
  
  // Process class name.
  private Result processClass(final String className) {
    if (processed.contains(className)) {
      return Result.ALREADY_PROCESSED;
    }
    final ClassFile clazz;
    
    try {
      clazz = classFinder.findClass(className);
    } catch (FinderException e) {
      logger.error("Exception: %1$s", e);
      logger.exception(e);
      return Result.ERROR;
    }
    
    return processClassFile(className, clazz);
  }
  
  // Process class file.
  private Result processClassFile(final String name,
                                  final ClassFile clazz) {
    if (classProcessor.processClass(name, clazz)) {
      return Result.OK;
    } else {
      return Result.ERROR;
    }
  }
  
  /**
   * Change object used to process classes.
   * @param classProcessor New class processor.
   */
  public void setClassProcessor(final ClassProcessor classProcessor) {
    this.classProcessor = classProcessor;
  }
  
}
