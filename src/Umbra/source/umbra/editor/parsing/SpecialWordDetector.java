/*
 * Created on 2005-04-30
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.rules.IWordDetector;



/**
 * Detector used for finding type symbols in bytecode (like '(V)').
 * See {@ref BytecodeStrings#KEY_TYPE_CHARS} for more type symbols.
 * TODO ???
 *
 * @author Wojciech Wąs  (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class SpecialWordDetector implements IWordDetector {

  /**
   * TODO.
   *
   * @param a_char TODO
   * @return TODO
   */
  public final boolean isWordStart(final char a_char) {
    return (Character.isWhitespace(a_char));
  }

  /**
   * TODO.
   *
   * @param a_char TODO
   * @return TODO
   */
  public final boolean isWordPart(final char a_char) {
    for (int i = 0; i < BytecodeStrings.KEY_TYPE_CHARS.length; i++) {
      if (a_char == BytecodeStrings.KEY_TYPE_CHARS[i]) return true;
    }
    return (a_char == '[' || a_char == '(' || a_char == ')');
  }

}
