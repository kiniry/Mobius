package mobius.cct.verifiers.logging;

/**
 * Default implementation of {@link Logger} interface.
 * Prints all messages using System.err.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 *
 */
public class DefaultLogger implements Logger {
  /**
   * Log tracing message.
   * @param msg Message text.
   */
  public void trace(final String msg) {
    System.err.println("TRACE: " + msg);
  }
  
  /**
   * Log debug message.
   * @param msg Message text.
   */
  public void debug(final String msg) {
    System.err.println("DEBUG: " + msg);
  }

  /**
   * Log informational message.
   * @param msg Message text.
   */
  public void info(final String msg) {
    System.err.println("INFO: " + msg);
  }
  
  /**
   * Log warning message.
   * @param msg Message text.
   */
  public void warn(final String msg) {
    System.err.println("WARNING: " + msg);
  }
  
  /**
   * Log error message.
   * @param msg Message text.
   */
  public void error(final String msg) {
    System.err.println("ERROR: " + msg);
  }

  /**
   * Log fatal error message.
   * @param msg Message text.
   */
  public void fatal(final String msg) {
    System.err.println("FATAL: " + msg);
  }
}
