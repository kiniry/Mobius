/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.rules.IWordDetector;

/**
 * The class implements the way the words are scanned in the Eclipse scanners
 * used in the Umbra editor.
 *
 * @author Wojciech Wąs  (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeWordDetector implements IWordDetector {

  /**
   * This method returns true when the character is a legal character to start
   * a word. In this case it means it is a letter.
   *
   * @param a_char a character to check
   * @return <code>true</code> when the character can start a word,
   *   <code>false</code> otherwise
   */
  public final boolean isWordStart(final char a_char) {
    return Character.isLetter(a_char);
  }

  /**
   * This method returns true when the character is a legal internal character
   * of a word. In this case it means it is a letter, a digit or an underscore
   * sign ('_').
   *
   * @param a_char a character to check
   * @return <code>true</code> when the character can occur inside a word,
   *   <code>false</code> otherwise
   * @see org.eclipse.jface.text.rules.IWordDetector#isWordPart(char)
   */
  public final boolean isWordPart(final char a_char) {
    return (Character.isLetterOrDigit(a_char) || a_char == '_');
  }
}
