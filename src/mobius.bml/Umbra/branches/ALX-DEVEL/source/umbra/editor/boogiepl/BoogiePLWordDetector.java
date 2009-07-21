/*
 * @title       "BoogiePL in Umbra"
 * @description "BoobiePL support for Umbra bytecode editor"
 * @copyright   ""
 * @license     ""
 */
package umbra.editor.boogiepl;

import org.eclipse.jface.text.rules.IWordDetector;

/**
 * This class offers an implementation of methods that check if particular
 * characters can occur in different positions in a word.
 *
 * @author Samuel Willimann (wsamuel@student.ethz.ch)
 * @version a-01
 */
public class BoogiePLWordDetector implements IWordDetector {

  /**
   * This method returns true when the character is a legal character to start
   * a word. In this case it means it is a letter.
   *
   * @param a_char a character to check
   * @return <code>true</code> when the character can start a word
   */
  public final boolean isWordStart(final char a_char) {
    return Character.isLetter(a_char);
  }

  /**
   * This method returns <code>true</code> when the character is a legal
   * character in a word. In this case it means it is a letter, a digit or
   * an underscore ('_').
   *
   * @param a_char a character to check
   * @return <code>true</code> when the character can occur in a word
   */
  public final boolean isWordPart(final char a_char) {
    return (Character.isLetterOrDigit(a_char) || a_char == '_');
  }
}
