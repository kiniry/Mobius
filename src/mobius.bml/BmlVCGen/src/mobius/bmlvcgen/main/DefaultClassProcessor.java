package mobius.bmlvcgen.main;

import java.io.File;

import mobius.bmlvcgen.bml.ClassFile;
import mobius.bmlvcgen.logging.Logger;
import mobius.bmlvcgen.util.StringUtil;
import mobius.bmlvcgen.vcgen.BmlAnnotationGenerator;
import mobius.directvcgen.bico.AnnotationCompiler;
import mobius.directvcgen.formula.Lookup;

/**
 * Default implementation of a class processor.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class DefaultClassProcessor implements ClassProcessor {
  private final Logger logger;
  private final BmlAnnotationGenerator annotGenerator;
  private final String classpath;
  private final File output;
  
  /**
   * Constructor.
   * @param env Environment.
   */
  public DefaultClassProcessor(final Env env) {
    logger = env.getLoggerFactory().getLogger(this.getClass());
    annotGenerator = new BmlAnnotationGenerator(env);
    // Ugly - copied from DefaultClassFinder
    if (env.getArgs().isAddSystemPath()) {
      final String sys = StringUtil.concatPaths(
                           System.getProperty("sun.boot.class.path", ""),
                           System.getProperty("java.class.path", ""));
      classpath =
        StringUtil.concatPaths(env.getArgs().getClasspath(), sys);
    } else {
      classpath = env.getArgs().getClasspath();
    }
    output = new File(env.getArgs().getOutputDir());
  }
  
  /** {@inheritDoc} */
  public boolean processClass(final String name, 
                              final ClassFile clazz) {
    Lookup.clear(annotGenerator);
    final AnnotationCompiler ac = 
      new AnnotationCompiler(output, name, classpath, annotGenerator);
    try {
      ac.start();
      //CHECKSTYLE:OFF
    } catch (final Exception e) {
      logger.exception(e);
      return false;
    }
  //CHECKSTYLE:ON
    return true;
  }
}
