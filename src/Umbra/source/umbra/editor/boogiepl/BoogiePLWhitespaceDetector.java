package umbra.editor.boogiepl;

import org.eclipse.jface.text.rules.IWhitespaceDetector;

/**
 * New definition of whitespace
 *
 * @author Samuel Willimann (wsamuel@student.ethz.ch)
 * @version a-01
 */
public class BoogiePLWhitespaceDetector implements IWhitespaceDetector {

  /**
   * TODO
   * @param a_char TODO
   * @return TODO
   */
  public final boolean isWhitespace(final char a_char) {
    return (a_char == ' ' || a_char == '\t' || a_char == '\n' ||
            a_char == '\r');
  }
}
