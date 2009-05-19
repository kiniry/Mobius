package mobius.bmlvcgen.finder;

import mobius.bmlvcgen.bml.ClassFile;
import mobius.bmlvcgen.bml.bmllib.BmllibClassFile;
import mobius.bmlvcgen.bml.debug.LoggingClassVisitor;
import mobius.bmlvcgen.finder.exceptions.FinderException;
import mobius.bmlvcgen.logging.Logger;
import mobius.bmlvcgen.main.Env;
import mobius.bmlvcgen.util.StringUtil;

import org.apache.bcel.util.Repository;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;

import annot.bcclass.BCClass;
import annot.io.ReadAttributeException;

/**
 * Class responsible for finding and loading
 * class files.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class DefaultClassFinder implements ClassFinder {
  private final Logger logger;
  private final ClassPath classpath;
  private final SyntheticRepository repository;
  
  /**
   * Constructor.
   * @param env Environment.
   */
  public DefaultClassFinder(final Env env) {
    logger = env.getLoggerFactory().getLogger(this.getClass());
    if (env.getArgs().isAddSystemPath()) {
      final String sys = StringUtil.concatPaths(
                           System.getProperty("sun.boot.class.path", ""),
                           System.getProperty("java.class.path", ""));
      final String cp =
        StringUtil.concatPaths(env.getArgs().getClasspath(), sys);
      classpath = new ClassPath(cp);
    } else {
      classpath = new ClassPath(env.getArgs().getClasspath());
    }
    repository = SyntheticRepository.getInstance(classpath);
  }
  
  /**
   * Find and parse class file.
   * @param fqn Fully qualified class name.
   * @return BmlLib classfile instance.
   * @throws FinderException If the class file is not valid.
   */
  public ClassFile findClass(final String fqn) throws FinderException {
    final BmllibClassFile result;
    final BCClass bc;
    
    logger.debug("Loading class: %1$s", fqn);
    try {
      bc = new BCClass(repository.loadClass(fqn));
    } catch (ReadAttributeException e) {
      throw new FinderException("Unable to parse class.", e);
    } catch (ClassNotFoundException e) {
      throw new FinderException("Class not found: " + fqn, e);
    }
    result = new BmllibClassFile(bc);
    logClass(result);
    return result;
  }
  
  /**
   * Get BCEL repository.
   * @return Repository.
   */
  public Repository getRepo() {
    return repository;
  }
  
  // Log basic information from class file.
  private void logClass(final BmllibClassFile clazz) {
    final LoggingClassVisitor printer = 
      new LoggingClassVisitor(logger);
    clazz.accept(printer);
  }
  
}
