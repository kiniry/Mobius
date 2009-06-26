package mobius.bmlvcgen.logging;

import java.io.OutputStream;
import java.io.PrintStream;
import java.util.Date;

/**
 * Simple logger implementation which writes all messages to an output stream.
 * Messages are printed only if their level is greater than or equal to the
 * minimal level set for used logger. Limited control of message formatting is
 * possible.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class SimpleLogger implements Logger {
  private static final String DEFAULT_FORMAT = 
    "%3$td/%3$tm/%3$ty %3$tH:%3$tM:%3$tS - %2$-5s : %1$s\n";

  private final PrintStream outputStream;

  private final String messageFormat;

  private final Logger.Level minLevel;

  /**
   * Constructor. Uses default message format.
   * @param minLevel Minimal message level.
   * @param outputStream Output stream.
   */
  public SimpleLogger(final Logger.Level minLevel, 
                      final OutputStream outputStream) {
    this.minLevel = minLevel;
    this.outputStream = new PrintStream(outputStream);
    this.messageFormat = DEFAULT_FORMAT;
  }

  /**
   * Constructor.
   * @param minLevel Minimal message level.
   * @param outputStream Output stream.
   * @param messageFormat Format string.
   * This string is passed to String.Format with
   * following arguments:
   *  - Message body
   *  - Loglevel (instance of Logger.Level).
   *  - Timestamp (as date object).
   */
  public SimpleLogger(final Logger.Level minLevel, 
                      final OutputStream outputStream,
                      final String messageFormat) {
    this.minLevel = minLevel;
    this.outputStream = new PrintStream(outputStream);
    this.messageFormat = messageFormat;
  }

  /** {@inheritDoc} */
  public void debug(final String fmt, final Object... args) {
    log(Logger.Level.DEBUG, fmt, args);
  }

  /** {@inheritDoc} */
  public void error(final String fmt, final Object... args) {
    log(Logger.Level.ERROR, fmt, args);
  }

  /** {@inheritDoc} */
  public void info(final String fmt, final Object... args) {
    log(Logger.Level.INFO, fmt, args);
  }

  /** {@inheritDoc} */
  public void warn(final String fmt, final Object... args) {
    log(Logger.Level.WARN, fmt, args);
  }
  
  /** {@inheritDoc} */
  public void exception(final Throwable e) {
    if (minLevel.value <= Level.ERROR.value) {
      e.printStackTrace(outputStream);
      outputStream.flush();   
    }
  }
  
  private void log(final Logger.Level level, final String fmt,
                   final Object... args) {
    if (level.value >= minLevel.value) {
      final String message = String.format(fmt, args);
      outputStream.printf(messageFormat, message, level,
                          new Date());
      outputStream.flush();
    }
  }

}
