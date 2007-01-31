/** Public domain. */

package freeboogie.util;

/**
 * @author rgrig 
 * @author reviewed by TODO
 *
 */
public class Err {
  /**
   * Writes <code>m</code> and exits with error code 1.
   * @param m the error message
   */
  public static void msg(String m) {
    msg(m, 1);
  }

  /**
   * Writes <code>m</code> and exits with error code <code>code</code>.
   * @param m the error message
   * @param code the exit code
   */
  public static void msg(String m, int code) {
    System.err.println(m);
    System.exit(code);
  }
  
  /** Aborts execution. */
  public static void notImplemented() {
    new Exception().printStackTrace();
    msg("not implemented", 255);
  }
}
