/*
 * Created on 2005-04-30
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.rules.IWordDetector;



/**
 * Detector used for finding type symbols in bytecode (like '(V)').
 * TODO ???
 *
 * @author Wojciech Wąs  (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class SpecialWordDetector implements IWordDetector {

  /**
   * TODO
   */
  public final boolean isWordStart(final char c) {
    return (Character.isWhitespace(c));
  }

  /**
   * TODO
   */
  public final boolean isWordPart(final char c) {
    for (int i = 0; i < IBytecodeStrings.keys.length; i++) {
      if (c == IBytecodeStrings.keys[i]) return true;
    }
    return (c == '[' || c == '(' || c == ')');
  }

}
