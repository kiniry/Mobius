package ie.ucd.autograder.util;

import ie.ucd.autograder.AutoGraderPlugin;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

/**
 * A utility class for Eclipse logging.
 * 
 * @author Daniel M. Zimmerman
 */
public final class Log {
  
  /**
   * Private constructor to prevent instantiation.
   */
  private Log() {
    // do nothing
  }
  
  /**
   * Logs an error message.
   * 
   * @param the_message The message.
   * @param the_throwable A throwable to accompany the message, if applicable.
   */
  public static void error(final String the_message, final Throwable the_throwable) {
    AutoGraderPlugin.getDefault().getLog().log
      (new Status(IStatus.ERROR, AutoGraderPlugin.PLUGIN_ID,
                  the_message, the_throwable));
  }
  
  /**
   * Logs an error message.
   * 
   * @param the_message The message.
   */
  public static void error(final String the_message) {
    error(the_message, null);
  }
  
  /**
   * Logs an informational message.
   * 
   * @param the_message The message.
   * @param the_throwable A throwable to accompany the message, if applicable.
   */
  public static void info(final String the_message, final Throwable the_throwable) {
    AutoGraderPlugin.getDefault().getLog().log
      (new Status(IStatus.INFO, AutoGraderPlugin.PLUGIN_ID,
                  the_message, the_throwable));
  }
  
  /**
   * Logs an informational message.
   * 
   * @param the_message The message.
   */
  public static void info(final String the_message) {
    info(the_message, null);
  }
}
