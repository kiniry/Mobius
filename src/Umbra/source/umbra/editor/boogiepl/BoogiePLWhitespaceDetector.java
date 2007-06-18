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
   */
  public final boolean isWhitespace(final char c) {
    return (c == ' ' || c == '\t' || c == '\n' || c == '\r');
  }
}
