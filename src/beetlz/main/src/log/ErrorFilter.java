/**
 * Package for logging and output.
 */
package log;

import java.util.logging.Filter;
import java.util.logging.Level;
import java.util.logging.LogRecord;

/**
 * A filter for the Logging system that filters out
 * all messages except for severe errors.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class ErrorFilter implements Filter {

  /**
   * Only allow (sever) error messages to be loggable.
   * @see java.util.logging.Filter#isLoggable(java.util.logging.LogRecord)
   * @param a_record log record to be tested
   * @return true if log record should be logged.
   */
  @Override
  public boolean isLoggable(final LogRecord a_record) {
    if (a_record.getLevel() == Level.SEVERE) {
      return true;
    }
    return a_record.getLevel() == CCLevel.COMPILATION_ERROR;
  }
}
