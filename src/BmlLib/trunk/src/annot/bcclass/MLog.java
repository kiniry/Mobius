package annot.bcclass;

import java.io.PrintStream;

/**
 * A standard logging utility. Use this instead of writing
 * anything to stdout (except tests classes). All messages
 * with priority : priority & mask  >  0 will be displayed to
 * stdout, all others will be ingnored.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public final class MLog extends MessageLog {

  /**
   * Message type filter. It's not final, so it can be
   * changed eg. by automated tests.
   */
  private static int LOG_MASK = PNORMAL;

  /**
   * The standard logging facility is the standard output.
   */
  private static PrintStream LOG_STREAM = System.out;

  /**
   * An empty private constructor to disallow the creation of instances.
   */
  private MLog() {
  }

  /**
   * Displays a line of a message to the standard log stream
   * iff it is important enough.
   *
   * @param priority - message priority,
   * @param msg - message text.
   */
  public static void putMsg(final int priority, final String msg) {
    if ((priority & LOG_MASK)  >  0) {
      LOG_STREAM.println(msg);
    }
  }

  /**
   * Displays a message to the standard log stream
   * iff it is important enough. This does not end a line
   *
   * @param priority - message priority,
   * @param msg - message text.
   */
  public static void putBitOfMsg(final int priority, final String msg) {
    if ((priority & LOG_MASK)  >  0) {
      LOG_STREAM.print(msg);
    }
  }

  /**
   * Returns the value of the current logging level mask.
   *
   * @return the current value of the logging level mask
   */
  public static int getLogMask() {
    return LOG_MASK;
  }

  /**
   * Sets the value of the current logging level mask.
   *
   * @param amask the new value of the logging level mask
   */
  public static void setLogMask(final int amask) {
    LOG_MASK = amask;
  }
}
