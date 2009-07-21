package mobius.bmlvcgen.logging;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Date;

/**
 * Default implementation of logger factory. Always returns the same logger,
 * which prints all messages to stderr and saves them to file named
 * 'bmlvcgen-DATE.log'.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class DefaultLoggerFactory implements LoggerFactory {
  /** Format of log file name. */
  private static final String LOGFILE = "bmlvcgen-%1$td-%1$tm-%1$ty.log";

  /** Default logging level. */
  private static final Logger.Level loglevel = Logger.Level.DEBUG;

  /** Instance of logger factory. */
  private static final DefaultLoggerFactory instance = new DefaultLoggerFactory();
  
  /** Logger instance to be returned by getLogger(). */
  private final Logger loggerInstance;

  /** Constructor. */
  protected DefaultLoggerFactory() {
    Logger fileLogger = null;

    final Logger stderrLogger = 
      new SimpleLogger(loglevel, System.err);
    try {
      final OutputStream logfile = 
        new FileOutputStream(String.format(LOGFILE, new Date()), true);
      fileLogger = new SimpleLogger(loglevel, logfile);
    } catch (IOException e) {
      fileLogger = null;
    }
    if (fileLogger == null) {
      loggerInstance = stderrLogger;
    } else {
      loggerInstance = new CompositeLogger(stderrLogger, fileLogger);
    }
  }

  /**
   * Get logger factory instance.
   * @return Instance.
   */
  public static DefaultLoggerFactory getInstance() {
    return instance;
  }
  
  /**
   * Return logger instance.
   * @param clazz Ignored.
   * @return Logger instance.
   */
  public Logger getLogger(final Class<?> clazz) {
    return loggerInstance;
  }
}
