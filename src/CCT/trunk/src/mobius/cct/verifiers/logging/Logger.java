package mobius.cct.verifiers.logging;

/**
 * Interface of objects used to log information 
 * during class verification.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface Logger {
  /**
   * Log tracing message.
   * @param msg Message text.
   */
  void trace(String msg);
  
  /**
   * Log debug message.
   * @param msg Message text.
   */
  void debug(String msg);

  /**
   * Log informational message.
   * @param msg Message text.
   */
  void info(String msg);
  
  /**
   * Log warning message.
   * @param msg Message text.
   */
  void warn(String msg);
  
  /**
   * Log error message.
   * @param msg Message text.
   */
  void error(String msg);

  /**
   * Log fatal error message.
   * @param msg Message text.
   */
  void fatal(String msg);
}
