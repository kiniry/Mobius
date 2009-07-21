package mobius.bmlvcgen.logging;

/**
 * Interface of objects used to print logging messages. Arguments of all logging
 * methods are processed using String.format().
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface Logger {
  /**
   * Possible levels of log messages.
   */
  static enum Level {
    /** 
     * Used for debugging, these messages should
     * not be printed in production environment.
     */
    DEBUG(10),
    /**
     * Informational message.
     */
    INFO(20),
    /**
     * Warning - non-fatal error.
     */
    WARN(30),
    /**
     * Important error.
     */
    ERROR(40);

    /**
     * Priority of a loglevel.
     */
    // CHECKSTYLE:OFF
    public final int value;
    // CHECKSTYLE:ON

    Level(final int value) {
      this.value = value;
    }
  }

  /**
   * Log 'info' message.
   * @param fmt Format string.
   * @param args Arguments.
   */
  void info(String fmt, Object... args);

  /**
   * Log 'debug' message.
   * @param fmt Format string.
   * @param args Arguments.
   */
  void debug(String fmt, Object... args);

  /**
   * Log 'warning' message.
   * @param fmt Format string.
   * @param args Arguments.
   */
  void warn(String fmt, Object... args);

  /**
   * Log 'error' message.
   * @param fmt Format string.
   * @param args Arguments.
   */
  void error(String fmt, Object... args);
  
  /**
   * Log an exception.
   * @param e Exception to be logged.
   */
  void exception(Throwable e);
}
