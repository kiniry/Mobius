package mobius.bmlvcgen.logging;

/**
 * A logger composed of other loggers.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class CompositeLogger implements Logger {
  /** Array of loggers. */
  private final Logger[] loggers;

  /**
   * Constructor.
   * @param loggers Array of loggers. All messages
   * are passed to these loggers (in order in which 
   * they appear in the array).
   */
  public CompositeLogger(final Logger... loggers) {
    this.loggers = loggers;
  }

  /** {@inheritDoc}} */
  public void debug(final String fmt, final Object... args) {
    for (final Logger logger : loggers) {
      logger.debug(fmt, args);
    }
  }

  /** {@inheritDoc}} */
  public void error(final String fmt, final Object... args) {
    for (final Logger logger : loggers) {
      logger.error(fmt, args);
    }
  }

  /** {@inheritDoc}} */
  public void info(final String fmt, final Object... args) {
    for (final Logger logger : loggers) {
      logger.info(fmt, args);
    }
  }

  /** {@inheritDoc}} */
  public void warn(final String fmt, final Object... args) {
    for (final Logger logger : loggers) {
      logger.warn(fmt, args);
    }
  }
  
  /** {@inheritDoc}} */
  public void exception(final Throwable e) {
    for (final Logger logger : loggers) {
      logger.exception(e);
    }
  }
}
