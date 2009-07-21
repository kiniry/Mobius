/**
 * Package for logging and output.
 */
package log;

import java.util.logging.Filter;
import java.util.logging.Level;
import java.util.logging.LogRecord;

/**
 * A filter for the Logging system that filters out
 * messages based on the user settings.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class OutputFilter implements Filter {
  /** Print errors?  */
  private final boolean my_errors;
  /** Print warnings?  */
  private final boolean my_warnings;
  /** Print jml errors and warnings?  */
  private final boolean my_jml;
  /** Print java errors and warnings?  */
  private final boolean my_java;
  /** Print general info?  */
  private final boolean my_info;
  /** Print debug info?  */
  private final boolean my_debug;

  /**
   * Creates a new filter with user settings.
   * @param a_print_err print errors?
   * @param a_print_warn print warnings?
   * @param a_print_jml print JML errors and warnings?
   * @param a_print_java print Java errors and warnings?
   * @param a_print_info print general info?
   * @param a_print_debug print debug info?
   */
  public OutputFilter(final boolean a_print_err, final boolean a_print_warn,
                      final boolean a_print_jml, final boolean a_print_java,
                      final boolean a_print_info, final boolean a_print_debug) {
    my_errors = a_print_err;
    my_warnings = a_print_warn;
    my_jml = a_print_jml;
    my_java = a_print_java;
    my_info = a_print_info;
    my_debug = a_print_debug;
  }

  /**
   * Determines whether a log record is loggable based on user settings.
   * @see java.util.logging.Filter#isLoggable(java.util.logging.LogRecord)
   * @param a_record log record to be checked
   * @return true if record should be logged
   */
  @Override
  public boolean isLoggable(final LogRecord a_record) {
    if (a_record.getLevel() instanceof CCLevel) {
      if (a_record.getLevel() == CCLevel.GENERAL_NOTE) {
        return true;
      }
      if (a_record.getLevel() == CCLevel.JAVA_ERROR) {
        return my_errors && my_java;
      }
      if (a_record.getLevel() == CCLevel.JAVA_WARNING) {
        return my_warnings && my_java;
      }
      if (a_record.getLevel() == CCLevel.JML_ERROR) {
        return my_errors && my_jml;
      }
      if (a_record.getLevel() == CCLevel.JML_WARNING) {
        return my_warnings && my_jml;
      }
    }
    if (a_record.getLevel() == Level.WARNING) {
      return true;
    }
    if (a_record.getLevel() == Level.INFO) {
      return my_info;
    }
    if (a_record.getLevel() == Level.CONFIG) {
      return my_debug;
    }
    return false;


  }



}
