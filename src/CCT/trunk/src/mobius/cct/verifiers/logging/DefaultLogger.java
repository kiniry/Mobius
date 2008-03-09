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
  @Override
  public void trace(String msg) {
    System.err.println("TRACE: "+msg);
  }
  
  /**
   * Log debug message.
   * @param msg Message text.
   */
  @Override
  public void debug(String msg) {
    System.err.println("DEBUG: "+msg);
  }

  /**
   * Log informational message.
   * @param msg Message text.
   */
  @Override
  public void info(String msg) {
    System.err.println("INFO: "+msg);
  }
  
  /**
   * Log warning message.
   * @param msg Message text.
   */
  @Override
  public void warn(String msg) {
    System.err.println("WARNING: "+msg);
  }
  
  /**
   * Log error message.
   * @param msg Message text.
   */
  @Override
  public void error(String msg) {
    System.err.println("ERROR: "+msg);
  }

  /**
   * Log fatal error message.
   * @param msg Message text.
   */
  @Override
  public void fatal(String msg) {
    System.err.println("FATAL: "+msg);
  }
}
