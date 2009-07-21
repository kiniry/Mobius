package jml2bml.utils;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.util.Calendar;

/**
 * Logger class.
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @version 0.0-1
 */
public final class Logger {
  /**
   * Error message logging level.
   */
  private static final int ERROR = 5;

  /**
   * Info message logging level.
   */

  private static final int INFO = 3;

  /**
   * Debug message logging level.
   */

  private static final int DEBUG = 1;

  /**
   * All logging levels turned on.
   */

  private static final int ALL = 0;

  /**
   * Current logging level.
   */
  private static final int CURRENT = ALL;

  /**
   * Print STREAM for this logger.
   */
  private static PrintStream STREAM;

  /**
   * The log file. If null, System.out will be used.
   */
  private static final String LOG_FILE = null;

  /**
   * Calendar (to determine current time).
   */
  private static Calendar calendar = Calendar.getInstance();

  /**
   * Name of class corresponding to this logger.
   */
  private String className;

  /**
   * Hidden constructor.
   * @param c class, for which the logger is created.
   */
  private Logger(final Class < ? > c) {
    if (STREAM == null) {
      try {
        if (LOG_FILE == null) {
          STREAM = System.out;
        } else {
          STREAM = new PrintStream(new File(LOG_FILE));
        }
      } catch (FileNotFoundException e) {
        STREAM = System.err;
      }
    }
    className = c.getSimpleName();
  }

  /**
   * Returns a new logger for the given class.
   * @param c class, for which the logger should be created
   * @return Logger instance
   */
  public static Logger getLogger(final Class < ? > c) {
    return new Logger(c);
  }

  /**
   * Returns if the debug logging level is enabled.
   * @return if the debug logging level is enabled.
   */
  public boolean isDebugEnabled() {
    return CURRENT <= DEBUG;
  }

  /**
   * Returns if the info level is enabled.
   * @return if the info logging level is enabled
   */
  public boolean isInfoEnabled() {
    return CURRENT <= INFO;
  }

  /**
   * Prints debug information to the logger (if debug level is enabled).
   * @param message
   */
  public void debug(final String message) {
    if (CURRENT <= DEBUG) {
      STREAM.println(calendar.getTime() + " DEBUG: " + className + " " +
                     determineLocation() + " " + ": " + message);
      STREAM.flush();
    }

  }

  /**
   * Prints an info to the logger (if info level is enabled).
   * @param message message to print
   */
  public void info(final String message) {
    if (CURRENT <= INFO) {
      STREAM.println(calendar.getTime() + " INFO: " + className + " " +
                     determineLocation() + " " + ": " + message);
      STREAM.flush();
    }
  }

  /**
   * Prints an error message to the logger. Error messages are always printed
   * @param message message to print
   */
  public void error(final String message) {
    STREAM.println(calendar.getTime() + " ERROR: " + className + " " +
                   determineLocation() + " " + ": " + message);
    STREAM.flush();
  }

  /**
   * Determines where the logger was invoked.
   * @return serialized place, where the logger was invoked
   */
  private String determineLocation() {
    final Throwable t = new Throwable();
    final StackTraceElement[] stack = t.getStackTrace();
    if (stack.length >= 3)
      return "[" + stack[2].getMethodName() + " line " +
             stack[2].getLineNumber() + "]";
    return "";
  }
}
