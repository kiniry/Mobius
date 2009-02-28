package mobius.bmlvcgen.logging;

/**
 * Interface of objects used to create loggers.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface LoggerFactory {
  /**
   * Get logger instance for given class.
   * 
   * It is not necessary to return different
   * loggers for different classes.
   * @param clazz Class object.
   * @return Logger instance.
   */
  Logger getLogger(Class<?> clazz);
}
