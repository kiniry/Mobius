package umbra.editor.parsing;

import org.eclipse.jface.text.rules.IWhitespaceDetector;

/**
 * New definition of whitespace
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeWhitespaceDetector implements IWhitespaceDetector {

  /**
   * This method defines which characters are whitespace characters
   *
   * @param c the character to determine if it is whitespace
   */
  public final boolean isWhitespace(final char c) {
    return (c == ' ' || c == '\t' || c == '\n' || c == '\r');
  }
}
