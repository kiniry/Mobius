/*
 * Created on 2005-04-25
 *
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.rules.IWordDetector;

/**
 * TODO
 *
 * @author Wojciech Wąs  (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeWordDetector implements IWordDetector {

  /**
   * TODO
   */
  public final boolean isWordStart(final char c) {
    return Character.isLetter(c);
  }

  /**
   * TODO
   */
  public final boolean isWordPart(final char c) {
    return (Character.isLetterOrDigit(c) || c == '_');
  }
}
