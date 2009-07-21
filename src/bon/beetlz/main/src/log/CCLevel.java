/**
 * Package for logging and output.
 */
package log;

import java.util.logging.Level;

/**
 * Customized Levels for Logging.
 * Our levels:
 * SEVERE (1000)  -file not found, parsing unsuccessful etc
 * WARNING (900)  -custom file not found, usage options
 * INFO (800)     -what are we doing
 * JAVA_ERROR (790) -major java error
 * JAVA_WARNING (780) -minor java error
 * JML_ERROR (760) - major assertion error
 * JML_WARNING (740) -minor assertion error
 * CONFIG (700)   -debug
 * FINE (500)
 * FINER (400)
 * FINEST (300)
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
@SuppressWarnings("serial")
public class CCLevel extends Level {
  /** Major compilation error. */
  public static final Level COMPILATION_ERROR = new CCLevel("JAVA_ERROR", 792); //$NON-NLS-1$
  /** General comment. */
  public static final Level GENERAL_NOTE = new CCLevel("GENERAL_NOTE", 791); //$NON-NLS-1$
  /** Java errors, ie major comments. */
  public static final Level JAVA_ERROR = new CCLevel("JAVA_ERROR", 790); //$NON-NLS-1$
  /** Java warning, ie minor errors. */
  public static final Level JAVA_WARNING = new CCLevel("JAVA_WARNING", 780); //$NON-NLS-1$
  /** JML error, ie major jml violation. */
  public static final Level JML_ERROR = new CCLevel("JML_ERROR", 760); //$NON-NLS-1$
  /** JML warning, ie monor violation. */
  public static final Level JML_WARNING = new CCLevel("JML_WARNING", 740); //$NON-NLS-1$

  /**
   * Create a new logging level.
   * @param a_name name of level
   * @param a_value level of value
   */
  protected CCLevel(final String a_name, final int a_value) {
    super(a_name, a_value);
  }




}
